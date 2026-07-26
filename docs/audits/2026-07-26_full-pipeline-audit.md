# Full-pipeline adversarial audit — 2026-07-26

Top-to-bottom audit of the whole pipeline at `main` = `fc693a4` (acl2 submodule
`da1f5336a4`, branch `acl2-lean-output`), run at the user's request after the
S2b arc closed.

**Method.** Six decorrelated adversarial reviewers (Opus, read-only, one per
dimension), each pointed at primary sources and given a skeptical persona, with
no access to my framing or to each other's conclusions. Every top finding then
went to an independent skeptic instructed to **default to refute**. I
independently reproduced the highest-stakes survivors myself and contributed
findings of my own. Dimensions: D1 trusted core, D2 mirror-statement integrity,
D3 replay shortcuts, D4 fork emission truthfulness, D5 gate integrity, D6
outside view.

Verdict tags below: **CONFIRMED** / **PARTLY CONFIRMED** (core survived,
framing corrected) / **REFUTED**. `[mine]` marks findings I established myself.

**Cost and outcome.** 28 agents, 0 errors, ~2.53M subagent tokens, 1064 tool
calls. 28 findings raised; 22 went through refutation:
**2 CONFIRMED, 17 PARTLY CONFIRMED, 3 REFUTED**. The refutation pass earned its
cost — it corrected the diagnosis of the tamper failure, refuted the provenance-gate
finding outright, and **refuted a finding of my own** (F8) that would have sent
someone hunting a trust hole that does not exist.

---

## Ground truth (all verified during this audit, not read from prose)

| Fact | Value |
|---|---|
| `lake build` | exit 0, 6294 jobs |
| `just diff-test` (interpreter vs real ACL2) | **399 match, 167 unsupported, 10 known-bug, 15 refuse, 0 FAIL**, exit 0 |
| Golden coverage table | REPLAYED **62/79** (28 unconditional + 34 conditional); DP leaves ✓32 ◌4 ✗0 of 36 |
| `sorry` / `axiom` / `native_decide` in Lean sources | none live (22 grep hits are all doc comments or `WorldGen`'s *generated stub* text) |
| Pinned real mirrors' axioms | `[propext, Classical.choice, Quot.sound]` |
| `docs/BUGS.md` open bugs | 8 (009, 010, 011, 013, 015, 016, 017, 018) |
| ACL2 fork delta vs upstream `master` | +3090 / −381 across 10 `.lisp` files; 157 `TRACE-LOG[…]` tags |
| `just ci` locally | green (this is what the arc close-outs record) |
| **GitHub CI on `main`** | **RED for the last 4 merges** — see F0. Last green was `bc7f767` (2026-07-21). |

*(An earlier draft of this table asserted CI "runs `just ci` and `just diff-test`
on every push". Those steps exist but have not executed since 2026-07-23; see F0.
The claim was wrong and is corrected here.)*

The engineering hygiene here is genuinely strong, and the audit should be read
against that background: reviewers hunting hard across 34k lines of Lean and a
3k-line Lisp diff surfaced **one** soundness-class defect, **one** dark gate,
and a set of fidelity/process issues — with no false theorem kernel-certified
anywhere.

---

## F0 — PROCESS: GitHub CI has not reached a single gate since 2026-07-23

**CONFIRMED** (reviewer D5; I verified the mechanism by reading and the outcome
against the GitHub API).

The CI capture step (`.github/workflows/lean_action_ci.yml:70-103`) regenerates
the gitignored `.proof-log` corpus on the runner. It captures exactly:

1. `acl2_samples/simple.lisp` + `acl2_samples/recon-tests/*.lisp`, and
2. sorting books **derived from `include_str "…sorting/…"` references**.

It does **not** capture `acl2_samples/pattern-tests/`. But three pattern-tests
logs *are* `include_str`'d by tracked Lean sources —
`cov-let-lambda.proof-log`, `p2-beta-preprocess.proof-log`,
`p2-beta-iff-context.proof-log` (the S2/S2b ci pins) — and all three are
gitignored (`*.proof-log`) and untracked, so a clean checkout does not have them.

The step then runs `./scripts/check-proof-logs.sh`, which scans **every**
`include_str "…proof-log"` reference without filtering by directory. It exits 1
on those three. Under `defaults.run.shell: bash -euo pipefail` that fails the
step, so **`just ci` and `just diff-test` — the next two steps — never run.**

**There were in fact two distinct breakages** (the verifier reconstructed the
history; my first pass conflated them):

1. **2026-07-23, `d501c8e`** — `b1414ad` added `check-pattern-map` to the `ci`
   recipe (`Justfile:37`). That script's "logs present" check requires a captured
   `.proof-log` for **every one of the 52 pattern books** — and CI captures none
   of them. So `just ci` **ran and failed**, and the differential gate was
   *skipped*.
2. **2026-07-25, `3fd03f5`** — `b329744` added the three `include_str` refs at
   `Tests/DriverTests.lean:879,929,931`, so the capture step's own trailing
   `check-proof-logs.sh` now exits 1 and the step dies **before `just ci` starts**.

That matters for the fix: it is not enough to capture the three `include_str`'d
logs — `check-pattern-map` needs all **52**.

Verified against the GitHub API:

```
fc693a4  completed  failure  2026-07-26   ← current HEAD
3fd03f5  completed  failure  2026-07-25   ← S2 merge
4e1dd2a  completed  failure  2026-07-24
d501c8e  completed  failure  2026-07-23   ← mapping-arc merge
bc7f767  completed  success  2026-07-21   ← last green
```

**Four merges have been pushed onto a red CI.** Every "ci 0/0 / gates green"
claim in the arc close-outs since 2026-07-23 was `just ci` **locally**, where the
developer's `recapture-all` had already put the pattern-tests logs on disk. The
local/remote split is invisible precisely because the local run is green.

This compounds F2: it is not only the tamper suite that has been dark — the
entire remote gate suite has, including the differential ratchet that protects
the trusted core.

**Fix.** Derive the capture list from *all* `include_str` references (the same
scan `check-proof-logs.sh` already does) rather than a `sorting/`-filtered
subset — the workflow comment already articulates this principle ("DERIVE …
rather than a hardcoded list (a stale hardcoded list is exactly what let isort's
log go uncaptured)"); it was applied to one directory and not the others. Same
clone-hazard shape as F3/F7/F8.

---

## F1 — SOUNDNESS: `encapsulate` local witnesses enter the World, and the mirror is about the witness

**CONFIRMED** (reviewer D2; verifier could not refute it; **I reproduced it
independently**).

`ACL2Lean/ClauseTree.lean:146` binds every `.defun` event into the World
unconditionally:

```lean
| .defun name formals body _ _ => { w with defs := w.defs.insert { name := name } (formals, body) }
```

The adjacent `.groundZeroDefun` arm (`:147-149`) *does* filter — so the missing
provenance check here is a conspicuous asymmetry.

The log gives it nothing to filter on. `acl2_samples/pattern-tests/cov-encapsulate.proof-log:27`:

```
(:DEFUN CF :FORMALS (X) :BODY '0)
```

That is the **discarded local witness** of

```lisp
(encapsulate (((cf *) => *))
 (local (defun cf (x) (declare (ignore x)) 0))
 (defthm cf-numberp (acl2-numberp (cf x))))
```

emitted with **no `:SOURCE` field and no encapsulate marker anywhere in the
log** — the boundary is simply not emitted, so it is indistinguishable from an
ordinary top-level admission.

Reproduced (`just replay acl2_samples/pattern-tests/cov-encapsulate.proof-log`):

```
• cov-encapsulate  (world: 2 defun(s), 2 theorem(s))
    CF-NUMBERP   → REPLAYED ✓  [DISCHARGE: Goal:preprocess/type-set-fc ✓ cond[total:(CF X), tp:CF]]
    CF-PLUS-COMM → REPLAYED ✓  [DISCHARGE: Goal:preprocess/tau-contradiction ✓ cond[…]]
— 2/2 replayed (2 unconditional + 0 conditional); DP leaves ✓2 ◌0 ✗0 of 2
```

ACL2 proved `(equal (+ (cf a) (cf b)) (+ (cf b) (cf a)))` for **every** function
satisfying the constraint. Our mirror asserts it only for `λx. 0` — and with
`cf` concrete, the statement is provable by evaluation alone. Both mirrors are
`addDecl`'d as `CoverageMirrors.mirror_<book>_<thm>` (`Runner.lean:278-283`),
axiom-clean, **unconditional**, and reported as the imported ACL2 theorem.

The verifier added the sharpest evidence: the same derived world validates
`(EQUAL (CF X) '0)`, and real ACL2 **explicitly refuses** that as a theorem
(`*** FAILED ***`). Since `tp:CF` is a real hypothesis binder
(`Harness.lean:242`), the DP leaf is discharged conditional on a proposition
ACL2's own world refutes.

**Scope.** Extends beyond encapsulate: `cov-meta-rule` gives
`KEEP-TERM-META → REPLAYED ✓ cond[total:MEV]` over `MEV`'s `defevaluator`
witness body, and `cov-clause-processor` gives `USE-ID-CP → REPLAYED ✓`
(unconditional) over `CPEV`'s witness. `defattach` is **not** in the blast
radius — those books halt at capture, i.e. fail closed.

**Not in CI today.** No pattern-tests book is in the `DriverCoverage` corpus, and
the one CI book touching constrained functions (`sorting/sorts-equivalent`)
carries `SORTFN1/2`, `SSORTFN1/2` only as `(:DEFTHM … :SOURCE :INCLUDE-BOOK)`
exported constraints with no `:DEFUN`. **The 62/79 golden is not falsified.**
But the protection is an accident of the mapping arc's "no sweep wiring"
decision: the next arc that wires pattern books into the sweep imports a false
green.

**Nothing false is kernel-certified** — both mirrors are true propositions about
the witness world. The defect is *statement substitution* plus an absent
fail-closed guard: exactly the trust-note class.

**Framing correction (honesty).** This is an **escalation, not a discovery**:
`docs/notes/2026-07-20_qsort-frontiers-arc.md:18-27` already records the
mechanism nearly verbatim ("the log records the encapsulate's LOCAL WITNESSES as
plain `:DEFUN`s … the mirror of the constrained theorem is about the witnesses …
Design-review item; NOT started"). What is new and worse is that it does **not**
fail closed on a simple encapsulate book — it reports `2/2 replayed`,
unconditional and axiom-clean. It is **not** in `docs/BUGS.md`.

**Fix.** Fork tags encapsulate-local defuns and emits the exported
`:CONSTRAINT` list; `toWorld` and `developmentTPs` **refuse** a tagged witness
(hard-fail, per "hard-fail at frontiers"). Promote from design note to
`docs/BUGS.md`.

---

## F2 — PROCESS: the tamper suite has never been gated, and it is currently FAILING `[mine]`

Surfaced by a verifier's `.olean`-enumeration; established and run by me.

`Tests/TamperTests.lean` is the project's soundness regression net. Its own
header:

> A tamper that replays anyway is a soundness/fidelity hole and FAILS the build.

It cannot. **It is referenced by nothing** — verified: not imported by
`Tests.lean` (which imports 11 other test modules), the `Tests` lean_lib has no
`globs`, and no Justfile recipe, CI step, or script mentions it. `.olean` absent
after a green `lake build`. `git log -p --all -- Tests.lean | grep TamperTests`
→ **no hits ever**: it has been dark since the day it landed (`4df928c`,
2026-07-05). **179 commits** on `main` since.

Built standalone it fails:

```
$ lake env lean Tests/TamperTests.lean
Tests/TamperTests.lean:111:0: error: TAMPER NOT REJECTED (rule deleted):
  replay succeeded with conditions [rule:PERM-SYMMETRIC, rule:PERM-MEMB, rule:PERM-RM]
```

**Why it fails — and this is worse than a regression.** Reviewer D5 found the
real cause, correcting my first reading. The tampers are **no-ops**: they filter
and match on **lowercase** rule names, but stored rule names are **uppercase**.
The log has `(:RULES (((:REWRITE PERM-SYMMETRIC) …)))`, and the failure message
itself shows `rule:PERM-SYMMETRIC`, while the test says:

```lean
(rules.filter (·.name != "perm-symmetric"))                    -- :91  T1
if r.name == "perm-symmetric" then { r with rhs := quoteNil }   -- :96  T2
if r == (⟨"rewrite", "perm-symmetric", none⟩ : ACL2.Rune)       -- :101 T3
```

So T1 removes nothing, T2 tampers nothing, T3 matches nothing. The replay then
legitimately succeeds with the full rule set, and `assertRejected` reports
"TAMPER NOT REJECTED" — because **no tamper occurred**. Only T4 is live (it keys
on `"hyp-relief"`, a dispatch *tag*, which is correctly lowercase), and the build
aborts at T1 before reaching it.

The lowercase literals almost certainly date from before the **BUG-002** fix
(2026-07-08), which established the invariant that symbol *names* are uppercase
on the identity path while dispatch *tags* are lowercased at the ProofLog
boundary. The tamper suite was written 2026-07-05, three days earlier, and was
never re-run because it was never wired in.

The verifier confirmed the whole finding independently (running
`lake build Tests.TamperTests` → `✖ [3135/3135]`, same T1 error), agreed the
no-op count is **three of four**, and added the detail that seals it: the file was
**mechanically edited four times after it landed** (`e3a12b5`, `6e6942e`,
`866252c` on 2026-07-15/16, `bcb7408` on 2026-07-17) — edited, but never once
run. The only artifacts on disk are two 16-byte `.hash` stubs dated 2026-07-05.

**The driver is not implicated.** My initial reading — that a deleted
stored-rule record degrades to a recomputed hypothesis — was wrong; nothing was
deleted. `dischargeRuleHyp`'s recompute-and-check joint (`Harness.lean:44-58`) is
untested by this suite, not broken by it.

**Three defects, all needing action:**
1. Wire `Tests.TamperTests` into a ci target so it can fail.
2. Fix the three lowercase literals so T1–T3 actually tamper.
3. Then find out what T1–T3 *report* once live — that is the answer to "does the
   replay reject a corrupted emitted record?", and it is currently **unknown**.
   The suite has never validated the joints it was written to validate.

---

## F3 — FIDELITY: const-folded emission records a tautology in place of ACL2's real step

**PARTLY CONFIRMED** (reviewer D4; **I measured the true scope, which is wider
than reported**).

`acl2/rewrite.lisp:17846` builds the emitted `:LHS` as
`(mcons-term* 'if test (sublis-var alist left) (sublis-var alist right))`.
`cons-term1-body` (`acl2/basis-b.lisp:789-796`) const-folds `IF`, and
`cons-term`/`sublis-var` fold ground primitive calls — so when the test and both
branches are (or fold to) quotes, the recorded `:LHS` collapses to equal the
`:RHS`.

My corpus-wide scan of all 82 logs (13,666 `:REWRITE-STEP` records with both
fields) — **167 records where `:LHS` is literally identical to `:RHS`**:

| origin | tautology records | of total |
|---|---|---|
| `REWRITE-IF/CONSTANT-TEST` | **143** | 3488 |
| `RECOGNIZER/FALSE` | 10 | 503 |
| `PREPROCESS/TYPE-SET-FC` | 8 | 65 |
| `RECOGNIZER/TRUE` | 6 | 1612 |

e.g. `:ORIGIN REWRITE-IF/CONSTANT-TEST :EQUIV EQUAL :LHS '4 :RHS '4`
(`p2-beta-quoted-actuals.proof-log:41`). The reviewer found only the first row;
the class spans four origins.

The record says "`'T` rewrites to `'T`" where ACL2 actually collapsed an `IF`.
The replay then proves a vacuous step instead of mirroring the real one — the
node chain is not ACL2's, which violates *"mirror the tree; never shortcut"*.
Not soundness: a tautology composes trivially and cannot make a false statement
provable.

**This is the clone hazard CLAUDE.md names.** S2b inc-3 (`8b67373306`) already
fixed exactly this class in the *preprocess* emitters ("plain (non-normalizing)
`:RHS` instantiation"); the `rewrite-if` twin was missed.

**Fix.** Apply the inc-3 non-normalizing instantiation at the remaining sites,
and add a capture-time integrity check rejecting any emitted `:REWRITE-STEP`
whose `:LHS` equals its `:RHS` — so the class becomes self-enforcing instead of
re-discoverable. Heed the verifier's caution on the recommendation direction.

---

## F4 — FIDELITY: free-variable hyp-relief backtracking is not rolled back

**PARTLY CONFIRMED** (reviewer D4; verifier reproduced it from scratch).

`acl2/rewrite.lisp:19232` — the retry arm that looks for the next type-alist
binding — recurses into `relieve-hyps1-free-1` with
`:ttree (accumulate-rw-cache t ttree1 ttree)` and **no `*structured-rewrite-log*`
restore**; same shape in `relieve-hyps1-free-2`. The only HYP-scope
checkpoint/restore pair (`infra/hyp-log-tail`, `rewrite.lisp:20164-20176` /
`20287-20296`) brackets the *whole* `relieve-hyps` call, so intra-`relieve-hyps`
binding backtracking leaks abandoned steps into the committed HYP block.

Corrections: the "the emitter's comment claims the opposite" framing is
**refuted**, and the realizable outcome is exactly one — a **hard-fail**
(fail-closed), not a wrong proof.

---

## F5 — FIDELITY: the reader ignores Common Lisp's terminating macro characters

**PARTLY CONFIRMED**, downgraded from soundness (reviewer D1).

`ACL2Lean/Parser.lean:72-73` — `isAtomChar` delimits tokens on only `(`, `)`,
space, `\n`, `\r`, `\t`. CL's terminating macro characters `"` `'` `` ` `` `,`
`;` do **not** end a token. `Parser.lean:78-80` (`isCharTokChar`) *does* carry
ACL2's real terminator list (`*acl2-read-character-terminators*`,
`acl2.lisp:1871`) but is used only on the `#\` path — a genuine internal
inconsistency.

Head-to-head, verified: real ACL2 prints `(A B D)` / `(A 'B)` / `(A "b")`; we
print `(A B;C D)` / `(A'B)` / `(A"B")` — **silently**, no error.

Severity is fidelity, not soundness — for a reason worth stating precisely,
because it is load-bearing:

- **`gen-world` is not in the certified pipeline.** `ACL2.loadEventsFromFile` is
  the *only* `.lisp` reader, and it is called solely from `Main.lean:245/253/266/275/285`
  (`eval-in`, `gen-world`, `metadata`) and `Workbench.lean:42`. The replay never
  calls it: `ReplayMain.lean:29` reads the `.proof-log` and `Runner.lean:238`
  builds the world as `dev.toWorld`. All **42** `include_str` sites embed
  `.proof-log`; **zero** embed `.lisp`.
- **The bug *is* inside the trusted core** — `ProofLog.lean:1231` uses the same
  `Parse.parseAll` — but its input is ACL2-*printed* text, and ACL2's printer
  escapes such names (`'|X;HYP|` prints back as `|X;HYP|`, which our whole-token
  `|…|` branch at `Parser.lean:317` reads correctly). The verifier scanned all 82
  logs: every token-char-abutting-`'`/`"` occurrence is inside a string literal
  (`"Goal'"`, `"Subgoal *1.1/1"`) handled by `readString`. Zero unescaped
  abutting terminators, and no ACL2 emitter output could be found that triggers it.
- **It is exercisable today** through `acl2lean eval` / `eval-in` / `gen-world`,
  i.e. it breaks the stage-6 "ACL2 masquerade" peer property with no diagnostic.
- **It becomes a live soundness hole the moment `TODO.md:1091` lands** ("Replace
  the hardcoded frontend with gen-world output").

Distinct from the reader's other known gaps: BUG-010 (interior `|`/`\`) and
BUG-015 (single-colon) both explicitly **hard-fail**; this one is **fail-open**,
which is why it deserves a BUG-NNN of its own.

### F5b — the governing doc is stale about which stage decides the statement

Falling out of the above, and worth its own line: **`CLAUDE.md:41-44` presents
`gen-world` as stage 5, the stage that "decides *what theorem we are proving*".**
It does not — not for anything the kernel checks. The mirror statement comes from
the proof-log path (`dev.toWorld` + `disjoinTerm root.inputClause`). Anyone
auditing "what decides the statement" is pointed at the wrong module, and the
trust note's own emphasis ("suspect any stage") is aimed slightly off-target as a
result. `TODO.md:1091` still lists the wiring as open work. Fix the pipeline
description in `CLAUDE.md`.

---

## F6 — PROCESS: four `Logic.lean` primitives diverge from ACL2, documented as faithful, unlogged

**PARTLY CONFIRMED** (reviewer D1; all oracle values reproduced by the verifier).

- `Logic.lean:223-231` — `evenp`/`oddp` match only `.atom (.number (.int n))`,
  `| _ => .nil`
- `Logic.lean:239-241` — `expt` funnels both args through `toInt`
- `Logic.lean:342-347` — `string_append` returns `""` unless **both** args are strings

Real ACL2 under `(set-guard-checking nil)`, verified: `(evenp nil)`=T,
`(evenp 'abc)`=T, `(evenp "abc")`=T, `(oddp 3/2)`=T, `(expt 1/2 2)`=1/4,
`(string-append "ab" 'c)`="ab".

None is wired into `callBuiltin` today, so all are **latent** — but
`builtinNames` makes wiring a one-line change, the definitions are documented as
faithful, and none is in `docs/BUGS.md`. Either log them as bugs or mark them
explicitly not-yet-faithful at the definition site.

---

## F7 — PROCESS: two divergent copies of `dischargeOrigins`, silently shadowed

**PARTLY CONFIRMED** (reviewer D3).

Two `def` sites: `Runner.lean:58` (5 preprocess origins) and
`Driver/Discharge.lean:33` (those 5 **plus** `simplify-clause/fc-contradiction`
and `rewrite-clause/type-alist-contradiction`, added at S1.3). `Runner.lean:18`
imports the Driver and `:23` opens its namespace, but the unqualified use at
`:65` resolves to the Runner-local copy — **no ambiguity error, no build
assertion tying them**. Consequence: the golden's DP-leaf scoreboard undercounts,
hiding whole-clause FC-contradiction discharges from the gated table. Same clone
hazard as F3.

---

## F8 — largely REFUTED: the DP carve-out on the mirror path *is* axiom-checked `[mine — and mostly wrong]`

I raised this as a clone hazard: `collectProofAxioms` is called at exactly one
site (`Runner.lean:142`, `tryReplay`), while `Runner.lean:185` — `tryDischarge`,
behind the golden's `DP ✓32` — does only `Meta.check`, which the adjacent comment
says accepts `sorryAx`. I framed that as the 2026-07-06 audit fix applied to one
of two structurally identical sites.

**The verifier refuted the important half, and I confirmed the refutation
myself:**

- The **only** `Lean.addDecl` in all of `ACL2Lean/` is `Runner.lean:158`, inside
  `tryReplay` — and that site *does* run `collectProofAxioms`.
- `tryDischarge` returns a **`String`**, consumed only at `Runner.lean:320-323`
  to bump `dpReplayed`/`dpAssumed`. Its proof term is never declared. It is a
  standalone per-leaf **coverage probe**, not a gate.
- The DP carve-out as it actually enters mirror theorems runs through
  `replayDischargeNode` → `proveDpFact`, called from `Core.lean:65,741,757`,
  `Preprocess.lean:203`, `Waterfall/Induction.lean:569` — all under `tryReplay`,
  hence all already axiom-filtered.

So the audit fix was applied at the site that matters, and the two sites are not
structurally identical. The verifier additionally refuted the hazard *route*: in
the pinned Lean 4.28.0, the `runTactic` that `Discharge.lean:337/381` calls does
not assign `sorryAx` to admitted goals in the way I assumed.

**What actually remains** is small and is reporting accuracy, not trust: the
`✓32` figure is type-checked only, so it could in principle overstate leaf health
without any kernel-accepted mirror being affected. Adding the axiom check to
`tryDischarge` is still a cheap, correct hardening — but it is **not** a
carve-out gap, and it should not be counted among the clone hazards. Recorded at
length because acting on my original framing would have sent someone hunting a
trust hole that does not exist.

---

## F9 — PROCESS: two `Imported/` spikes claim COMPLETE but are in no build target

**PARTLY CONFIRMED**, downgraded to quality (reviewer D2).

`FlattenSpike.lean:5-11` and `InterleaveSpike.lean:5-8` carry
"COMPLETE (sorry-free; axioms {propext, Classical.choice, Quot.sound})".
Neither is in `ACL2Lean.lean`'s 22 imports; the lakefile has no `globs`; after a
green `lake build` neither has an `.olean`.

Downgraded because both **accurately self-disclose** the gap
(`FlattenSpike.lean:6-9`: "a J1 VALIDATION ARTIFACT, deliberately NOT in the
root import graph … **not to guard against regression**") and both still build
green standalone with clean axioms — verified. Note the intent did drift:
`docs/notes/2026-07-16_induction-j1-closeout.md:32` said they would be wired
when the driver landed; the driver landed at J2 and the 2026-07-18 header
rewrite retired the wiring intent instead.

This is the same *class* as F2, which is where it actually bites.

---

## F9b — PROCESS/QUALITY: three more gate weaknesses (D5, fault-injected)

D5 probed each gate by **injecting its own fault class** rather than reasoning
about the script. Three did not catch theirs:

- **`check-acl2-tags` passes vacuously over zero files** — real, but the
  scenario is **refuted**. `scripts/check-acl2-tags.sh:18` genuinely has no
  zero-input guard (verified: run from a dir with no `acl2/`, it prints
  "OK: tagging convention satisfied.", exit 0), and it is the only `just ci` gate
  lacking one (`check-no-shadow.sh:29-36`, `check-log-provenance.sh:38-41` have
  them). But `just ci` cannot go green over a missing submodule:
  `check-log-provenance` runs 6th and hard-fails (`git -C …/acl2 rev-parse HEAD`
  → `fatal: cannot change to '…/acl2'`, exit 128), and `just` aborts the chain.
  The `deinit`/worktree variant doesn't escape either — `git -C <empty subdir>
  rev-parse HEAD` walks up to the superproject HEAD, which then mismatches every
  log's `acl2-commit`. So: add the guard for hygiene and defense-in-depth, not
  because a green-over-nothing run is reachable.
- **`check-no-shadow`'s scrape is defeated by a non-leading-`|` arm.**
  `scripts/check-no-shadow.sh:24` scrapes `callBuiltin`'s match arms
  positionally. An injected guarded catch-all (e.g.
  `| n, args => if arithNames.contains n then … else none`) — a natural
  refactor as the 43-entry table grows — **passed** the gate while adding
  builtins absent from `builtinNames`, which is the world-shadowing hazard the
  gate exists to prevent.
- **The 11 `#print axioms` in `DriverTests.lean` are informational, not gating.**
  `#print axioms` logs; it does not fail a build. So the mirror theorems the
  project presents as its product are axiom-*reported*, not axiom-*gated*. (The
  corpus sweep path *is* gated — `collectProofAxioms`, `Runner.lean:142` — so
  this is about the hand-pinned exemplars, and it pairs with F8's gap on the
  DP-leaf path.)

D5 could construct **no** concrete failure scenario for the `tryDischarge` axiom
gap and said so — and its verifier then refuted the finding's premise outright
(see F8).

---

## F10 — OUTSIDE VIEW: the coverage number does not generalize (7% on fresh books)

**PARTLY CONFIRMED** — empirical core replicated independently, framing corrected
(reviewer D6).

D6 ran **7 upstream ACL2 books the map never authored** (144 defthms) through
real ACL2 and the pipeline. Replicated by the verifier:

| layer | result |
|---|---|
| CAPTURE | **7/7** (2 self-reported INCOMPLETE by the integrity net) |
| RECONSTRUCTION | **5/7** — `dump-proof-tree` hard-fails on 4/7 at two messages: `ProofTree.lean:339 collectClausify: expected split/out` and `ProofTree.lean:281 buildProofNodes: unexpected clause-structure event inside a literal` |
| REPLAY | **10/144 (7%)**, 0 unconditional |

against the reported **62/79 (78%)**.

**Every failure was fail-closed at a named frontier** — across 144 defthms and 4
reconstruction crashes, no silent wrong answer, no swallowed event, no
plausible-looking bad proof. That is a real and substantial positive result.

**Two corrections I want on the record:**
- The **driving** corpus is *not* self-authored. `acl2_samples/books.txt` sources
  all 11 sorting books from the `acl2/` submodule unmodified
  (`git -C acl2 diff master...HEAD --stat -- books/` is empty). The 46 *pattern*
  books are authored; the driving corpus is upstream. My own initial framing was
  wrong here.
- **The governing sequencing rests on an inverted premise.**
  `docs/notes/2026-07-23_mapping-plan-impact.md:14-21` says "reconstruction
  handles ~90% of the situation frame while the CAPTURE layer is the narrowest",
  and `TODO.md:35-37` makes that doc govern all next-arc ordering. Fresh-book
  data inverts it: capture 7/7, reconstruction 5/7. The narrow layer is
  reconstruction.

**Refuted** from this dimension: the "both industrialization triggers have fired
unactioned" claim (H2a's trigger is "needed before R4"; R4 is two walls away;
H2c needs two books and only `perm` has a native lift) and the "17–40× cost per
import" ratio (inflated ~2.5–6× by dividing whole-file line counts).

---

## F11 — the statement-anchoring gap, stated precisely `[mine]`

Worth recording because it bounds what `62/79` means.

The certified statement is built solely from the root clause —
`Harness.lean:257-258`: `EvTrue w env (disjoinTerm root.inputClause)`. The
strongest fidelity artifact in the repo is the set of **hand-written statement
pins** in `DriverTests.lean` (`example : <the ACL2 theorem, typed out by hand>
:= <replay result>`), which force the machine-generated type to match a human
rendering of the ACL2 `defthm`. There are **9 such pins, covering 5 named
mirrors**, against **62 replayed rows** — so roughly **8%** of the scoreboard has
its *statement* anchored; the rest is type-checked and axiom-checked but compared
to nothing.

A reviewer proposed cross-checking against the emitted `:DEFTHM :FORMULA`
(currently used only by `dump-proof-tree`, `Main.lean:142`). The verifier's
rebuttal is correct and important: `:FORMULA` is ACL2's *untranslated* formula
and the Goal clause is its *translate* — a full-corpus scan of all 210 clause
proofs found 120 textual differences and **zero** semantic divergences, all pure
translate (`+`→`BINARY-+`, `LET`→`LAMBDA`, …). Equating them would need a Lean
reimplementation of ACL2's `translate` — a new, hundreds-of-lines,
trust-relevant component — and both fields come from the *same untrusted fork*
anyway, so it is intra-artifact defense-in-depth, **not** an anchor to the ACL2
theorem. The only real anchor is the `.lisp` source, which the certified
pipeline never reads.

So: don't build the `translate` bridge for this. Extend the hand-written pins
instead, and say plainly in the docs what the unpinned rows do and do not claim.

---

## Refuted findings (recorded so they are not re-litigated)

- **`check-log-provenance` binds logs to HEAD, not the image** — REFUTED. The
  centrepiece "82 banners disagree with 82 sidecars" is a misread of
  `acl2/acl2-init.lisp`; the recommended fix would break a currently-correct CI.
  (Residual nit: `image-mtime` is written by `capture-proof-log.sh:115` and read
  by nothing.)
- **`DriverTests` validates against hand-built trees, which CLAUDE.md bans** —
  REFUTED. It contains 7 `include_str` of real captured `.proof-log` artifacts
  driven end-to-end (`09-defn-unfold`, `simple`, `perm`, `isort`,
  `cov-let-lambda`, `p2-beta-preprocess`, `p2-beta-iff-context`).
- **`Count.acl2Count` means the wrong obligation is proved** — REFUTED on
  consequence. `mkTotalityHypType` (`Waterfall.lean:33-44`) builds pure
  interpreter convergence with **no measure term at all**. The *naming* is
  genuinely misleading (`Count.lean:7`, `Translator.lean:48`) — real ACL2 gives
  `(acl2-count 100)`=100 where ours gives 0 — and should be renamed, but no
  obligation is misstated.
- **`n/0` reads as integer 0** (`Parser.lean:537-551` → `mkNumber` with `d=0`;
  `(quote 1/0)` → `0` where ACL2's reader hard-errors) — real but unreachable;
  downgraded to `correctness`, latent.
- **Induction trivially-dropped-clause discharge is an unratified fifth DP
  class** — REFUTED. ACL2's `trivial-clause-p` *is* `if-tautologyp`
  (`simplify.lisp:6808`) and `preprocess/trivial-clause` is already in both
  discharge-origin lists.
- **The lexorder order-fact injection is unsound** — REFUTED on severity; it is
  load-bearing and correct, and the proposed fix would regress a currently
  replayed theorem.

---

## Credit where due — genuine strengths, verified

- **Trusted core is faithful on its modeled surface.** D1 generated an
  adversarial cross-product — 30 unary primitives × 22 boundary values plus 9
  binary primitives × 22×22 pairs, **5,016 forms** including `1/2`, `-1/2`,
  `2/4`, characters and strings — against real ACL2, and found no divergence in
  `callBuiltin`'s modeled surface. The differential corpus reproduces green and
  **no passing row depends on the comparator's normalization** (0 of 591).
- **Fail-closed is real, not aspirational.** `replayDischargeNode` (the composed
  path) has no `assumeFact` escape at all. `callBuiltin` returns `none` on
  unknown primitive and on wrong arity, pinned by `#guard`. Across 144 fresh
  defthms every failure was a named frontier.
- **Axiom hygiene is mechanical** on the theorem path: `collectProofAxioms`
  walks the transitive constant graph and rejects anything outside the classical
  trio (cf. F8 for the twin site).
- **Defense-in-depth on the mirror statement.** `Harness.lean:257-259` re-hints
  the replayed proof at the root-clause type precisely so "fidelity must not rest
  solely on each handler".
- **Induction validates recomputation in both directions** and hard-fails on
  divergence (`Induction.lean:266-273`).
- **Native bridges are honest lifts.** `Rep` (`Lifting.lean:118-127`) carries
  injectivity as a field; `enc` is proved both injective and surjective onto
  `true-listp`. Non-liftable TP corollaries are *skipped*, never mis-stated
  (`Harness.lean:206-219`).
- **Ground-zero rules are proved, not assumed** (`Replay/GzRules.lean` from the
  `LexorderOrder` theorems).
- **`:EQUIV` is a hard downstream requirement** — `ProofLog.lean:500-501` throws
  "the emitter must state the step's equivalence; the checker does not infer it".
- **Logs are byte-reproducible** from the current image (re-captured 6 books into
  `$TMPDIR`, identical to committed).
- **Forcing `gstackp` is empirically behavior-preserving** — qsort with
  `gstackp t` vs default differed only in `Time:` lines.
- **L3 world-parametricity is honored in substance**, not nominally.
- **BUG-012's canonical-number design** eliminates the duplicate-representation
  class at the type level.
- **Three gates are genuinely ENFORCING under injected faults** (D5 broke each
  deliberately): `check-bugs.sh` in *both* directions (flipping BUG-010 to
  `fixed` with a live corpus tag → `FAIL … exit 1`; removing a tag → FAIL);
  `check-pattern-map.sh` on all three of its fault classes (book renamed out of
  the map, log deleted, pin signature altered); `check-log-provenance.sh`
  (bogus `acl2-commit:` → `STALE log`; deleted sidecar → `MISSING sidecar`), and
  it has the zero-input guard `check-acl2-tags` lacks.
- **`just ci`'s exit-code plumbing is clean** — verified with a synthetic
  justfile that `just` aborts on the first failing prerequisite and does not run
  the rest.
- **The `include_str` staleness mitigation demonstrably works** — a
  `capture-proof-log.sh` run had deleted `Tests/DriverCoverage.olean`, leaving
  only the `.hash` files, and `lake` correctly re-elaborated.

---

## Recommendations for the remainder of the buildout

Ranked. 0–3 are small and should land before any new feature arc.

0. **Get CI green again (F0), first.** Two things, not one: derive the capture
   list from *all* `include_str` references rather than the `sorting/`-filtered
   subset, **and** capture the 52 pattern books that `check-pattern-map`'s
   logs-present check requires. Nothing else in this list can be trusted to stay
   fixed while the remote gate suite is dark, and four merges have already landed
   on top of it. Then add the remote CI conclusion to `just check-push-ready`, so
   the next merge cannot repeat it.

1. **Fix F1 and generalize it to a provenance invariant.** Fork tags
   encapsulate-local defuns and emits the exported `:CONSTRAINT` list;
   `toWorld`/`developmentTPs` hard-fail on a tagged witness. Then generalize:
   **every world-entering event must carry an explicit recognized provenance, and
   an unmarked or unknown one hard-fails.** That converts a whole class (local
   defuns, witnesses, redefinitions, future event forms) from silent statement
   substitution into a frontier. Add to `docs/BUGS.md`.
2. **Fix F2, all three parts** — wire `Tests.TamperTests` into a ci target, fix
   the three lowercase rule-name literals so T1–T3 actually tamper, then *find
   out what they report*. Whether the replay rejects a corrupted emitted record
   is currently **unknown**; the suite has never validated the joints it was
   written for. Also add the `.olean`-absent-after-green-build enumeration as a
   gate of its own — it is a cheap, repeatable way to find dark files, and it is
   how both F2 and F9 surfaced.
3. **Close the three clone hazards** (F0 capture-list derivation, F3 emitters,
   F7 duplicate `dischargeOrigins`). Each is "the fix landed on one twin, and the
   twin was never checked", and in two of the three the *comment* states the
   right principle while the *code* applies it to one site. CLAUDE.md already
   names this risk; three live instances says the de-dup injunction needs a
   mechanical check, not vigilance. Fold in the cheap hardening while there: the
   `check-acl2-tags` zero-input guard, the `check-no-shadow` scrape, and the
   `tryDischarge` axiom check (F9b/F8) — all defense-in-depth, none of them a
   live hole.
4. **Re-derive the sequencing from fresh-book data.**
   `docs/notes/2026-07-23_mapping-plan-impact.md:14-21` is *governing* per
   `TODO.md:35-37` and its central premise is inverted: capture is robust (7/7),
   **reconstruction is the narrow layer** (5/7), and the two crash sites are
   named and specific (`ProofTree.lean:339`, `ProofTree.lean:281`). Those two
   defects gate more fresh-book throughput than anything currently queued.
5. **Add a second, non-monotone scoreboard.** `62/79` is measured on a corpus
   that books join once they pass; the fresh-book number is 7%. Keep both, gate
   both, and let the wild number be the one that answers "is the pipeline getting
   more general?". Without it, two consecutive arcs can move every gated metric
   by exactly zero (S2 and S2b did) with no instrument registering what they
   bought.
6. **Bound the statement claim honestly (F11).** Do not build a Lean `translate`.
   Extend the hand-written statement pins beyond 5 theorems toward one
   representative row per book, and state in `DriverCoverage`'s header what an
   unpinned `REPLAYED ✓` does and does not assert.
7. **Log F6's four primitives** in `docs/BUGS.md` (or mark them not-yet-faithful
   at the definition site), and rename `SExpr.acl2Count` to say what it is.

**The one thing I would change about the plan.** The trust story rests on
`evalOpt` being ACL2, and the audit's evidence there is genuinely good (5,016
adversarial forms, 399 differential matches, 0 FAIL). The trust story does *not*
rest on the scoreboard, but the *plan* is steered by it — and the scoreboard is
selected, monotone, and was flat across the last two arcs. Recommendations 4 and
5 are the ones that change what gets built next: measure on books you did not
choose, and let that number pick the arc.

**The pattern worth naming.** F0, F2, F3, F7, F9 and F9b are all the same
failure: **a check that exists, is documented, is believed to be running, and
isn't.** The dark tamper suite, the red CI, the vacuous tagging gate, the
defeated shadow scrape, the un-gated axiom prints, the emitter fix applied to one
twin. This project's discipline is unusually strong *in what it writes down* —
the reviewers repeatedly found the code more honest than they expected — and its
exposure is concentrated almost entirely in whether the written-down checks
actually execute. That is a much better problem to have than a wrong proof, and
it is fixable with a day's work, but it does mean the arc close-outs' "gates
green" line has been reporting a local, partial truth since 2026-07-23. Worth
adding to the close-out ritual: paste the *remote* CI conclusion, not the local
`just ci` result.
