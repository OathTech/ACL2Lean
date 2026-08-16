# T1+2 sprint — trip report (2026-08-14 17:10 → 2026-08-16 14:49)

The blow-by-blow record of the autonomous buildout that closed ALL
replay frontiers (Tier 1) and ALL qualification debt (Tier 2) in one
~45.6-hour sprint, per the goal of 2026-08-14 and its charter
(`docs/plans/2026-08-14_t12-sprint-charter.md`). Companion to the
charter's ARC LOG (which carries the ~40 J-numbered judgment calls);
this report carries the narrative, the numbers, and the lessons.

## Start / end state

| metric | sprint start (42d4d29) | sprint end (7b69166) |
|---|---|---|
| golden | 114/116 REPLAYED (98 uncond + 16 cond)* | **116/116 (116 uncond + 0 cond)** |
| FAIL rows | 5 | **0** |
| `tp:`/`total:`/`rule:`/`linear:` row conds | ~40 occurrences | **0** |
| sorries (FORBIDDEN-DEBT) | 5 | **0** |
| Tier-1 mechanisms open | 4 | **0** |

\* the pre-sprint R2 fork batch + the G1 brief were banked on the same
branch line before the goal was set; counting from the R-arc start
(main @ 631c282, 2026-08-13): 113/116 (84+29), 6 sorries, 6 FAIL rows.

## Timeline (commit-stamped)

| when (UTC-ish) | event |
|---|---|
| 08-14 17:10 | Sprint base collected (wave-1 + charter); goal set; branch forked |
| 08-14 ~17:30 | **P1** (D-A ts-algebra consumer, main tree) + **G1-M** (R-lane, worktree) launched IN PARALLEL |
| 08-14 20:09–22:18 | G1-M lands: PERM-TLFIX — the first R-parameterized replay ever; P1 lands: `tp:ACL2-COUNT` ×8 proved-discharged, first sorry down; both collected + combined-verified |
| 08-15 02:08 | **R3** (unified measure table): `total:` 44→23, three more sorries down, five registry fragments → one compiler-enforced table; found+fixed `just ci` unrunnable since R2 |
| 08-15 04:19 | **RT2** (fork round-trip 2): 3 of 4 emission asks shipped (ask 4 refuted by scout — the data already existed); golden zero-movement |
| 08-15 07:28–08:18 | **P3a** (worktree, parallel with RT2): `total:BSORT` retired; the WP5 cross-book root cause diagnosed; exploratory chain honestly reverted |
| 08-15 13:15 | **P3b**: ordinal totality retired (`total:O<`/`O-P` 18→0, sorry #4 down); CLASSIFY-POS green (Tier-1 #4); the trio's blocker re-diagnosed as an emission gap |
| 08-15 15:41 | **P4a**: the trio GREEN with ZERO fork changes — P3b's emission-gap premise refuted (the records were line-wrapped past a single-line grep); FAIL rows 4→1 |
| 08-15 19:38 | **P3c** collected (worktree, ran ~7.2h): the cross-book D1 transfer — worlds verified nesting BEFORE any code; `rule:` chains + `:INCLUDE-BOOK` totals retired; sorry #5 down → **repository at zero sorries** |
| 08-16 02:07 | **P4b**: arithmetic-rune family retired via d5GzRules; CD2-BOUND green (the BUG-009 mask-discount decision); 116/116, zero FAIL; the honest 5-row residue named |
| 08-16 08:43 | **P5a**: routeIff decode + the gz-linear class; 5→3 rows; item-2 widening measured 2-out-3-in and reverted WITH the quiescence insight |
| 08-16 11:05 | **P5b** collected: `tp:QSORT` closed (allTps path + hypothesis-carrying TP mode, every piece tamper-verified); 3→1 rows |
| 08-16 13:54 | **P6**: the widening + quiescence composition; the last row unconditional; **the end state** |
| 08-16 14:49 | Full claim gate TRUE_EXIT=0 (`.gate-runs/7b69166-20260816T135429Z.log`), after full cache invalidation |

## Structure and cost

- **12 executor lanes** (+ the pre-sprint G1 design scout), Opus-class,
  free-order parallelism where file-sets were disjoint: main tree +
  one isolated worktree at a time, collection by patch + 3-way with
  hand-resolved conflicts. Two lanes ran concurrently for most of the
  sprint's wall-clock.
- Executor time: ~52 agent-hours across the 12 lanes (2.2h–7.9h
  each). Token spend: ≈4.7M output tokens as reported by the 12
  sprint executors alone — an UNDERCOUNT of the full buildout (it
  excludes the orchestrator loop, the pre-sprint R0–R2/wave lanes,
  and all verification builds; the true total is a multiple of this
  figure). Verification
  (sweeps/gates) dominated wall-clock: the sorts-equivalent book cost
  ~50→65 min/pass after the transfer landed (P6 improved it to
  ~37 min).
- **~40 J-numbered judgment calls**, all delegated per the goal, all
  logged with rationale in the charter ARC LOG. Five significant
  reverts (exploratory chains that violated the movement rule or the
  wire-later ban) — all measured before reverting, so each revert
  produced the next lane's map.

## What made it work (keep for future buildouts)

1. **The movement rule.** Golden changes only in pre-declared classes
   (condition-retirement / diagnosed-frontier-closure); anything else
   stops the item. This single rule caught every wrong turn cheaply —
   including P5a's 2-out-3-in trade, whose *measurement* became P6's
   design.
2. **Scout-refutes-premise as a success mode.** Three lane premises
   were refuted by contact with the artifact (RT2's ask 4; P3b's
   emission-gap claim; P4b's tp:QSORT map). Each refutation was
   reported as a correction, not worked around — and each SHRANK the
   remaining work. Briefs should keep saying "verify the premise
   in-image/in-log first."
3. **Emission-gated proving (the D-A pattern) generalizes.** Verdict
   selects the lemma; a proved lemma carries the proof; anything
   unemitted stays conditional. Every class retired this sprint
   (ts-algebra, gz rules, gz-linear, routeIff, hypothetical-TP) is an
   instance of this one shape.
4. **Tamper-verification of load-bearingness.** P5b proved each piece
   real by forcing it off and watching the frontier return
   byte-exact. Cheap, decisive, worth demanding in every brief that
   builds multi-piece machinery.
5. **Worktree isolation + report-only goldens.** Two golden-moving
   lanes never fought; the orchestrator merged diagnosed diffs and
   let one verifying sweep arbitrate. The splice-predicted-golden →
   full-sweep-verifies flow (born of necessity — the modules pin
   against the golden via IO) ended up self-checking by construction.
6. **Honest reverts with measurements attached.** The discipline ban
   on unwired infrastructure was enforced by executors on themselves
   (P4b reverted its own allTps plumbing; P5b rebuilt it WIRED a lane
   later). Nothing speculative survived, and nothing measured was
   wasted.

## Footguns hit (and their fixes, now permanent)

- **Shell cwd persistence** silently redirected six orchestrator
  commands into a worktree (a wasted ~1.5h sweep + one WRONG
  accusation against a correct executor report, retracted). Fix:
  absolute paths whenever any worktree exists; recorded in memory.
- **Stale IO-read gate caches.** Twice: `coverage-repin` no-op'd on a
  stale `.actual`; the catalog gate silently didn't run under `just
  ci` (found independently by BOTH P5 lanes). Fixes: repin only from
  fresh assemblies; `invalidate-coverage.sh` now invalidates the
  catalog too; the final claim gate ran after full invalidation.
- **A diagnostic-swallowing kept-condition** (`tp:` frontier messages
  discarded) had blinded two audits and three scouting passes. The
  env-gated TP_DIAG/xbook-diag sinks are permanent — silent drops of
  demanded names or kept frontiers are now visible.
- **Worktree `git diff` omits untracked files** — a new module
  silently missing at collection (caught by the build). Copy new
  files explicitly.
- **Line-wrapped emissions defeat single-line greps** (the trio's
  "missing" records existed all along). Grep proof-logs with
  multiline-aware extraction.

## Numbers for calibration (future sprint budgeting)

- One "condition class" (design + lemmas + wiring + verification):
  0.5–1 executor-lane ≈ 3–7h agent time.
- One fork round-trip (edits + image + 91-book recapture + parser):
  ~2–5h, dominated by recapture.
- The full verifying sweep: ~1.2h end-to-end (sorts-equivalent
  dominates); the full claim gate ~1.5h. Budget ~2 sweeps per
  collection (discovery + verify).
- Collections with two golden-moving lanes need conflict resolution
  at the union of retirements — plan the orchestrator time.
