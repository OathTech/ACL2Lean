# Performance profile — the OODA-loop measurement (task #65)

_Created 2026-06-11, branch `mdd/perf-pass`. The measurement stage of the
perf+G3 arc: numbers first, then the order of attack (harness/caching wins
vs G3 consolidations) is decided BY the profile, per the MDD-approved plan._

Optimization model (MDD): pipeline latency for a FRESH OR UPDATED ACL2 proof
(capture → parse → reconstruct → replay → kernel check) is the core OODA
loop and must be minimized; library build time is secondary. Session data
point that triggered the bump: coverage sweep ≈5 min/run; an EvalLemmas edit
recompiles the whole dependent chain (≈10 min edit→gate cycle).

## Measurement axes

1. **Per-file sweep wall times** (instrumented in `Tests/DriverCoverage.lean`,
   logged separately from the golden-compared report): which corpus files
   dominate the sweep, and is the cost replay, leaf discharge, or per-file
   hoists (reflectWorld / buildTotalEnv)?
2. **The base-layer edit cascade**: after a trivial `EvalLemmas.lean` change,
   the rebuild cost of each downstream target
   (Driver → NativeMirrors → DriverTests → DriverCoverage), measured
   one target at a time.
3. **Within-theorem decomposition** (run 2, finer timers on the top files
   only): tryReplay vs tryDischarge vs the per-file hoists vs `Meta.check`.

## Results

### Axis 1 — per-file sweep wall times (measured 2026-06-11)

Total sweep ≈ 1361 s of elaboration. **Five files are 99% of it, and they
are exactly the FRONTIER files** (theorems/leaves that fail or get assumed):

| file | ms | share | what it is |
|---|---|---|---|
| 03-linear | 967,838 | 71% | linear-chain: DP leaves at the simp/omega limit (#50), ◌-assumed |
| 11-custom-measure | 206,776 | 15% | custom measure → proveTotality frontier |
| 16-three-way | 79,527 | 6% | len-zip3: 3 tau-contradiction leaves, frontier replay |
| 12-multi-controller | 50,990 | 4% | multi-controller induction frontier |
| 02-rev | 46,248 | 3% | 8 theorems incl. replayed inductions + frontiers |
| all 13 others | ~10,000 | <1% | incl. every cheap REPLAYED file (ms each) |

**Reading: successful replay is CHEAP (the whole `simple.proof-log`
inductive replay is 289 ms). The sweep's cost is overwhelmingly FAILED or
ASSUMED work** — heartbeat-capped DP-tactic attempts and frontier
replay/totality attempts that burn their full budget before failing. A
cache does not fix this; the fix is making FAILURE cheap (budget tuning,
not re-attempting known-frontier work per run) and/or G3-style
consolidation where the attempt itself is the cost.

### Axis 2 — base-layer edit cascade (measured 2026-06-11)

Probe: a COMMENT-ONLY append to EvalLemmas.lean, then per-target rebuilds:
EvalLemmas 33 s; Driver 3 s; NativeMirrors 1 s; DriverTests 2 s;
DriverCoverage 1 s. **Finding P4: Lake content-hashes the .olean — a
no-op (comment/docstring) change does NOT propagate; downstream rebuilds
were skipped.** So the painful ~10-min G2 edit cycles were entirely the
SUBSTANTIVE-change case: downstream re-elaboration (NativeMirrors re-runs
ten driver mirrors, DriverTests replays trees, DriverCoverage re-runs the
whole sweep), and the sweep is ~22 min of which ~95% is the DP-leaf burn
(P3) + linear-chain's composed attempt. Conclusion: there is no separate
"cascade problem" — fixing P3 collapses the edit cycle too (sweep
projected ≈ 1–3 min if leaves cost ~1 s).

### Axis 3 — within-theorem decomposition

**03-linear (968s) decomposed** (scratch profiler under matched conditions —
outer `maxHeartbeats 0`, statuses reproduce the golden exactly):

| component | ms | note |
|---|---|---|
| linear-chain `tryReplay` | **860,554** | the COMPOSED tau-contradiction discharge node runs `proveDpFact` (simp/omega on the rational lift) to failure — **one known-failing tactic attempt, gated on #50, is 63% of the ENTIRE corpus sweep** |
| len2-cdr-smaller leaf (✓) | 50,730 | a SUCCEEDING leaf that takes 50 s — the slowest legitimate success; caps cannot be tuned below this without flipping it ✗ |
| len2-nonneg `tryReplay` (✓) | 8,687 | successful replay incl. composed discharge + lazy totality |
| len2-nonneg leaf (✓) | 4,744 | |
| linear-chain leaf (◌) | 4,426 | the SECOND attempt of the same failing tactic (assumed) |
| reflectWorld + buildTotalEnv | 47 | the hoists are NOISE — caching them is worthless |

**Finding P1 (harness bug): the per-call heartbeat caps do not bind.**
Control experiment: under a default outer budget the same leaf tripped
"runtime" at 8.5 s; under the harness's outer `maxHeartbeats 0` it ran 50 s
to SUCCESS — i.e. the `withOptions (maxHeartbeats := …) <|
Core.withCurrHeartbeats` wrappers in tryReplay/tryDischarge do not enforce
the documented per-call budgets. The "bounded per-theorem/per-leaf budget"
comments are false in practice. (This also explains why the first scratch
run, under lean's default command budget, FAILED theorems the sweep
replays: the effective bound was the un-rebased OUTER budget, not the
intended per-call one.)

**Finding P2: failed tactic attempts dominate; proof assembly and the
hoists are noise.** Caching (reflected worlds, totality envs) attacks <1%
of the cost. The OODA fix is (a) make the caps real (P1), (b) stop paying
twice for the same known-failing leaf (the composed attempt inside
tryReplay AND the standalone leaf attempt), (c) make the failing/slow
tactic itself cheaper (the simp_all on rational lifts — measure where the
860 s goes inside the tactic before acting).

**The other four hot files, decomposed** (same matched-conditions scratch):

| file | tryReplay (all thms) | leaves | leaf cost |
|---|---|---|---|
| 11-custom-measure | 16 ms (frontier throw) | ◌67.4s ◌50.7s ✓46.3s | **164 s — ALL of it** |
| 16-three-way | 1 ms | ◌19.3s ◌22.0s ◌21.3s | 62.6 s |
| 12-multi-controller | 1 ms | ◌18.9s ◌21.2s | 40.1 s |
| 02-rev | 0.3 s total (5 thms, incl. app-assoc REPLAYED at 128 ms) | ✓36.2s ✓5.0s ✓5.0s | 46.2 s |

**Finding P3 — the profile's headline: `replayDischargeLeaf` costs 5–67 s
PER LEAF, for SUCCEEDING leaves as much as assumed ones** (02-rev's three ✓
leaves: 46 s; 11's ✓ leaf: 46 s). The shared cost of ✓ and ◌ is the
machinery both run: the per-opaque totWalk derivation attempts +
`dpFactStmt` construction + `proveDpFact`'s `dpSplitVars`-then-tactic loop
(simp_all+omega per case-split leaf — candidate combinatorial blowup in
the number of clause variables/opaques). Successful REPLAY (induction,
chains, clausify) is genuinely cheap — app-assoc end-to-end is 128 ms.
Next decomposition needed: timers INSIDE replayDischargeLeaf (totWalk vs
dpFactStmt vs proveDpFact vs closeOver) on 11's worst leaf.

### Axis 3b — INSIDE the worst leaf (11-custom-measure `*1/5'`, 67 s)

| component | ms |
|---|---|
| totWalk derivation attempts | 1 |
| dpFactStmt | 2 |
| **DIRECT un-split tactic attempt (FAILS)** | **38,458** |
| dpSplitVars | 10 (→ 64 leaf goals) |
| split-leaf tactic runs (63 closed, 1 failed) | 1,664 (26 ms/leaf) |

**Finding P5 — the smoking gun: `proveDpFact`'s fast-path is the slow
path.** The direct attempt (one big `simp_all <;> omega` on the un-split,
SExpr-symbolic goal) costs ~40 s WHEN IT FAILS — 20× the entire split
fallback that then succeeds. Every expensive leaf in the corpus fits this
signature; linear-chain's 860 s composed attempt is the same direct simp_all
churning on the rational lift. The hoists/caching candidates from TODO are
all noise (≤ 10 ms each).

## Decision

**Fix: reorder `proveDpFact` to SPLIT-FIRST** (split ≤ 3 quantified values
— the existing bound — close each concrete leaf at ~26 ms; the direct
attempt remains ONLY for arities past the split bound). Still a fixed,
deterministic policy per the carve-out — no search. Splitting is sound case
analysis, and each split leaf carries strictly more constructor information
than the un-split goal, so anything the direct attempt closed should still
close; the GOLDEN GATE is the empirical guard (outcomes must stay
byte-identical).

Projected effect: per-leaf 5–67 s → ~2 s; linear-chain's composed attempt
860 s → seconds (the split loop aborts at the first unclosable leaf);
sweep ~22 min → ~2 min; the substantive edit→gate cycle collapses with it.

## As built (2026-06-11, commits 8628466 + 3e9dc1b)

Split-first ALONE was insufficient (a gated sweep still ran 20+ min): the
heavy leaves' cost was NOT the tactic but **P6 — the ambient context**.
`proveDpFact` runs inside the caller's vop/hconv/htp telescopes, and
`simp_all` on EVERY split leaf re-churned those hypotheses (types carrying
the reflected world): 23 s vs 1.7 s for the SAME closed statement
(literal-vs-constant world measured as noise, ~8% — that TODO candidate is
refuted). Fix: prove the (always-closed) fact statement under
`Meta.withLCtx {} #[]`; a `stmt.hasFVar` branch is a defensive fail-safe.

**Final: sweep elaboration 1361 s → ~82 s (16.5×), wall 119 s including the
Driver rebuild; golden gate BYTE-IDENTICAL outcomes.** Worst leaf
23.2 s → 0.99 s. New per-file distribution: 16-three-way 21.3 s,
12-multi-controller 20.3 s, 08-equality 18.1 s, 03-linear 14.4 s, 02-rev
3.4 s, 11-custom-measure 2.8 s, everything else ≤ 0.7 s.

Residuals / follow-ups (stage-2 material, diminishing returns for now):
- **08-equality REGRESSED 3.1 → 18.1 s (the known trade):** its four
  proveDpFact calls were fast DIRECT successes; equal-trans's total=3 fact
  now enumerates 512 splits ≈ 15 s (×2: composed + standalone). Candidate:
  a bounded-direct-first hybrid — blocked on P1 (making per-attempt
  heartbeat caps actually BIND; today 200k user-units ≈ tens of seconds).
- **16/12's ~17 s leaves did not get the P6 win** — their cost is
  apparently NOT proveDpFact (under investigation: suspects are the
  totWalk derivation attempts walking zip2/zip3 bodies before failing, or
  a stmt that trips the hasFVar fail-safe).
- The known-failing linear-chain leaf still pays twice (composed +
  standalone) at ~seconds each — acceptable.
- G3 consolidations confirmed NOT the bottleneck (successful replay is
  128 ms end-to-end for app-assoc) — G3 proceeds on its own merits as
  stage 2, not as a perf fix.
