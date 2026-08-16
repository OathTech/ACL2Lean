<!-- End-of-branch audit report, persisted verbatim from the auditor's final text (2026-08-16). Auditor: A3 — documentation & comments (Opus). Branch: mdd/t12-sprint @ 388089d. Synthesis: docs/audits/2026-08-16_eob-audit-synthesis.md -->

## A3 — DOCUMENTATION &amp; COMMENTS: findings

Ground truth first (all verified, read-only): `Tests/driver-coverage.golden:1` = `REPLAYED 116/116 (116 unconditional + 0 conditional)`, 0 FAIL rows, 122 ✓ rows = 116 theorems + 6 terminations; `.gate-runs/7b69166-20260816T135429Z.log` ends `TRUE_EXIT=0` with `check-golden-current: golden matches the live assembly`; zero real `sorry`/`sorryAx` in Lean sources. **The headline claim is sound.** The drift is in what the docs say *around* it.

---

## TIER 1 — actively wrong, a reader would act on it

**T1-1. `just waypoint-metrics` is BROKEN.** `scripts/waypoint-metrics.sh:37` lists `ACL2Lean/Imported/GzPrelude.lean` in `hand_files`; P4b (c7aa470) deleted that file. Under `set -euo pipefail` the `cat "${hand_files[@]}"` aborts the script mid-run — I ran it: it dies after the census, before "hand lines per native" and "decode coverage". Not caught by `just ci` (the recipe isn't in it). `README.md:240` and `TODO.md` both point readers here as the census command. **Fix: delete line 37.**

**T1-2. The trip report's start-state column is a mid-sprint state.** `docs/notes/2026-08-16_t12-sprint-trip-report.md:14-19` labels the column "sprint start (42d4d29)". Measured at 42d4d29: `113/116 (84 unconditional + 29 conditional)`, **6** FAIL rows, **6** sorries. The report says `114/116 (98+16)`, 5, 5 — which is exactly the post-R3 state (b3f6174, 08-15 02:08, mid-sprint). The footnote makes it worse: it offers "counting from the R-arc start (main @ 631c282): 113/116 (84+29), 6 sorries, 6 FAIL rows" as a *different* baseline, but that is byte-identical to 42d4d29 (R2 and R4-wave-1 moved zero golden rows). Downstream: the timeline's "sorry #4 down" (P3b) and "sorry #5 down → zero sorries" (P3c) should read #5 and #6.

**T1-3. `TODO.md`'s debt registry lists retired debt as open.** `:131-141` "REQUIRED class … `dis_o_lt_total` ONLY" — deleted at P3b (2026-08-15). `:158` TP class lists `dis_acl2_count_tp` — retired at P1 (2026-08-14). `:216-224` "`linear:HOW-MANY-BAD-PAIRS-BNEXT` … the `linear:` class has NO existing unlock" + "NOT mintable and still blocking ORDEREDP-BSORT/HOW-MANY-BSORT", and "R-lane class: `dis_convert_perm`" — retired at P5a/P6 and P3c. Correct text: **the FORBIDDEN-DEBT class is EMPTY as of 2026-08-15; zero `sorry`/`sorryAx` in the repository.**

**T1-4. `TODO.md:3-44`** — the P4a block at the very top of the file (first thing a reader sees) ends `OPEN AFTER IT: CD2-BOUND … tp:QSORT ×3`. CD2-BOUND closed at P4b; `tp:QSORT` closed at P5b.

**T1-5. Six of twelve sprint lanes have no `TODO.md` entry at all**: RT2, P3a, P3b, P3c, P4b, P5b. Those are precisely the lanes that retired the entries T1-3 lists as open (the cross-book transfer, the ordinal route, the D5 arithmetic-rune family, the `tp:QSORT` closure). Present: P4a, R3, G1, P5a, P6. CLAUDE.md makes keeping `TODO.md` current binding.

**T1-6. Five `.pending` catalog entries name live blockers that no longer exist** (`ACL2Lean/Imported/Waypoints/Catalog.lean`), each contradicted by the golden in the same repo:

| site | says | golden |
|---|---|---|
| `:487` ORDEREDP-BSORT | "BLOCKED ON A KEPT CONDITION WITH NO UNLOCK CLASS … the blocker is `linear:HOW-MANY-BAD-PAIRS-BNEXT`, whose CLASS has no existing unlock"; also cites deleted `dis_o_lt_total` | `:97` unconditional |
| `:512` HOW-MANY-BSORT | "only total:BSORT, total:O-P and linear:… are undischarged, and the `linear:` class has no existing unlock" | `:101` unconditional |
| `:407` CONVERT-PERM-TO-HOW-MANY | "BLOCKED ON A RED ROW — the R-lane rung-2 wall … conds are now cond[rule:PERM-TLFIX] — a SINGLE blocker" | `:86` unconditional (PERM-TLFIX retired at G1-M, the sprint's *first* lane) |
| `:365` MSORT-IS-ISORT | "row conds are total:MERGE2, total:MSORT, rule:TRUE-LISTP-RM, rule:CONVERT-PERM-TO-HOW-MANY" | `:151` unconditional |
| `:375` QSORT-IS-ISORT | "row conds total:QSORT, total:O&lt;, tp:QSORT, … rule:ORDEREDP-APPEND" | `:152` unconditional |

The correct pattern is already in the file — BSORT-IS-ISORT (`:386`) was rewritten at P6 to "`.pending` … for that reason, not for a replay one". The other five were missed. These are the entries a mirror-wave executor reads to decide what to build next.

**T1-7. The charter ARC LOG is missing two whole lanes' judgment calls.** No R3 section and no `J-R3a..h` entries exist — yet commit b3f6174 says "J-R3a..h logged" and cites J-R3f/J-R3g/J-R3h by number (`grep -n "J-R3" charter` → zero hits). No P5b section either (01faf39, `tp:QSORT` closed — the last Tier-2 class; its "leaves-in-basicTs fail-closed admissibility" and "double-checked self-call H obligation" decisions are unrecorded). Consequence: the trip report's "**~40 J-numbered judgment calls, all delegated per the goal, all logged with rationale in the charter ARC LOG**" is false, and a reader following the charter alone would conclude `tp:QSORT` is still open (charter §P4b item 3 STOPPED it with a map).

---

## TIER 2 — stale, low act-on risk

**T2-1. `docs/plans/2026-08-13_r-arcs-roadmap.md` records no supersession.** Only R0 carries DONE. R1 exited (15b016d), R2 landed (e5d3fa1), R3 landed as sprint phase 2 (b3f6174), R4 waves 0+1 landed (fc06b33/42d4d29); R5 alone is genuinely open. Also `:80` `Provers.lean:847-848` is a **dead ref** (file is 535 lines after the R3/P4b splits); "the remaining six FORBIDDEN-DEBT sorries" → zero; "R3 … blocks 100% of `total:` debt today" → `total:` row conds are 0.

**T2-2.** Same dead `Provers.lean:847-848` ref at `docs/plans/2026-08-14_t12-sprint-charter.md:46`.

**T2-3. `docs/plans/2026-08-12_master-plan.md` (the GOVERNING plan) Phase B carries no status; B1–B4 all landed.** `:90-92` B1 "`tp:` = 195 kept conditions; retires 14 debt sorries incl. `dis_insert_tp`" → 0/0. `:93` B2 "REQUIRED class, 5" → empty. `:95` B3 → done. `:98` B4 "The linear-class design (**ruling before build**)" → the class was unlocked at P5a/P6 as a delegated judgment call, without the pre-build ruling the plan reserves; `:165` still lists "B4 design" as a live ruling point. Worth an explicit line either way. `:79-81` Phase A4 EXIT "ISORT's row is `.nativeSorried` on `dis_insert_tp`, so the mirror inherits `sorryAx`" → retired 2026-08-13.

**T2-4. BUG-023's fork half moved but isn't recorded.** `docs/BUGS.md:321-355` was untouched by the branch. RT2 shipped `:CR-RUNE` (`acl2/rewrite.lisp:5259/5281`, 361 records). I checked: the entry's named-open item (`:cong-rune` on abbreviation-expansion, `acl2/induct.lisp:158-177`) is *genuinely still open* — different site — so the Status line is not wrong, but it should record the RT2 landing. Correspondingly **`TODO.md:348-352` and `Tests/PatternPins.lean:~57-60` both still say "The *queued* `:CR-RUNE` fork item (brief §Q2 — emit the licensing rune at `find-rewriting-equivalence`'s push site) fixes both lanes' anchor at the source"** — it is no longer queued (shipped 2026-08-15) and it did **not** fix class D's anchor (the SYNP-guarded step is a stored-rule rewrite, not a solidify site). Reduce the claim to what shipped.

**T2-5. "0 conditional" vs "total: 121 / tp: 119" — nothing reconciles them.** The END STATE (charter `:880-897`), the trip report, and the golden header all say zero conditions; `just waypoint-metrics` reports `total: 121, tp: 119` off *the same golden* (DISCHARGE-bracket `cond[…]`s, ruled probe-structural/informational at J6). Neither the LEXICON, the README, nor the golden header distinguishes ROW conditions from DISCHARGE-bracket conditions. One lexicon entry + one line in the script's output closes it.

**T2-6. `docs/LEXICON.md` lacks every piece of the sprint's new vocabulary** — now in commits, the charter, TODO.md and in-code docstrings: **the (cross-book D1) transfer**, **quiescence**, **D5 / the gz class** (defined only in `ACL2Lean/Replay/GzRules.lean:1-27, 112-128`), **emission-gated proving / the D-A pattern**, and the **row condition classes** (`total:`/`tp:`/`rule:`/`linear:`/`usefi:`) themselves. Also `:107` `Debt / FORBIDDEN-DEBT` should note the class is EMPTY as of 2026-08-15.

**T2-7. `TODO.md:3716`** — "## CURRENT PRIORITIES (confirmed with MDD 2026-07-06, post-R1)" heads a section whose scoreboard reads "26/47 = 21 uncond + 5 cond". Roadmap ruling 5 (TODO restructure) was slated for R5, which hasn't run.

**T2-8. Charter Tier-2 scope figures mix two surfaces.** `:37-40` "the `tp:` condition class (129 occurrences / 39 rows at sprint start)" and "the `total:` condition class (38 occurrences)". Measured at 42d4d29: row-level `tp:` = 10, `total:` = 44 (R3's own commit says "total: ROW census 44→23"). 129/119 are the DISCHARGE-bracket surface J6 ruled informational — this mixture is the root of T2-5.

---

## TIER 3 — nits

- **`CLAUDE.md` "225 tags"** → `grep -rn "TRACE-LOG\[" acl2/*.lisp` returns **228** (RT2 added three channels on this branch). "12 files" ✓, "61 authored pattern books" ✓.
- **`CLAUDE.md` "`recon-tests/` 00–16"** → 18 books, 00–17 (`17-rule-application.lisp`, pre-branch at 4df928c). Pre-existing.
- **Charter J2 (`:120`)** "Congruence.lean 523 lines" → 533 (commit 90839d4 says 533).
- **Date slip:** charter labels §P4b "— 2026-08-15" (`:475`) and `docs/BUGS.md:158` dates the third-site note "2026-08-15, T1+2 sprint P4b"; commit c7aa470 is 2026-08-16 02:07 (trip report has 08-16).
- **Cost datum contradicts itself inside the charter:** P3c (`:365`) "~50→65 min"; J-P5a-e (`:770`) "~50 min either way"; P6 "~36.6 min (vs the 50-min datum)". The trip report propagates "50→65 … P6 improved it to ~37 min". Drop the 65 or explain it.
- **Renamed-away names in comments** (P4b's μ-generic widening deleted the non-mu wrappers): `ACL2Lean/Replay/Lemmas/TpClosure.lean:161` ("`tp_2_rec`, `tp_2_rec_snd`") and `ACL2Lean/Replay/Driver/TpProver.lean:425` ("the `tp_3_rec`/`tp_3_rec_snd` shape") → `_mu` forms.
- **`ACL2Lean/Replay/GzRules.lean:1-27`** file header frames D5 solely as the boot-skipped lexorder story ("no replayable ACL2 evidence exists in any capturable image"); the file now also hosts class-(ii) constants whose evidence exists in an uncaptured book. The (i)/(ii) split *is* documented at `:112-128` — the header predates it.
- **`TODO.md:114`** "D5 gz five re-homed to `Imported/GzPrelude.lean`" — dated historical block, fine as record, but a "(MOVED to `Replay/GzRules.lean`, P4b)" saves the next reader a chase.

---

## Verified clean (credit where due)

- **BUG-009 third site is exact.** `docs/BUGS.md:158-177` matches the code line for line: `tsAcl2MaskOk` (`TsFacts.lean:161-164`) discounts index 6 **and only 6** over `List.range 14`; consumed at `TypeSetWalk.lean:844` via `recogVerdictFromTs`; `tsIndex` (`TsAlgebra.lean:44-55`) never returns 6; the deletion condition is repeated in the site docstring (`TsFacts.lean:139-160`). Nothing to fix.
- **IsoGen ladder criterion ↔ kit: exact match.** I enumerated both. The criterion table (`IsoGen.lean:196-204`) lists 12 rungs; `mirror_square_close` (`:345-352`) admits exactly those 12; `LadderPins` (`:314-339`) pins the 10 `rfl` rungs plus `Bool.decide_eq_true`, with `enc_inj_iff` explained as the non-`rfl` plumbing family. Consistent because the mirror layer was genuinely untouched: `git diff 42d4d29..HEAD` over `MirrorProofs/`+`Mirrors/` is empty (only `Imported/` moved).
- **Trip report timeline: all 14 rows match `git log` to the minute.** 42d4d29 @ 08-14 17:10 → e229ef4 @ 08-16 14:49 = 45h39m ≈ the claimed ~45.6h; the 12 lanes enumerate exactly (G1-M, P1, R3, RT2, P3a, P3b, P3c, P4a, P4b, P5a, P5b, P6).
- **10 sampled J-calls, all accurate**: J-P4b-b (`d5Allowed = []` as a named empty slot, `Catalog.lean:763`), J-P4b-c (the WP3 pin skips exactly the five by name with all seven rows listed, `DriverTests.lean:920-940`), J-P4b-d, J-P4b-e (exactly six μ-parameterized `tp_*_rec_mu` wrappers, no non-μ survivors), J-P4b-f (one copy: `measure_strong_induction_val` at `Lemmas/Totality:100`, `consCount_strong_induction:109` its instance), J-P5a-a (`eq_of_iff_ne_nil_two_valued`, `Discharge.lean:955`, takes both two-valuedness disjunctions as premises), J-P5a-b, J-P5a-h, J-P6-c (`Macro.lean:149` uses `bookDemandSeed`), J-P6-d (`DevQuery.lean` 88 lines, Harness 1483). **Every ratchet baseline matches actual line counts exactly** (CoreSpine 1539, Node 1650, ProofLog 1238 ≤ 1240, Judgments 1820, Sorting 4165, GzRules 581).
- **13 Props** in `ACL2Lean/Mirrors/Sorting.lean` — R0's "14→13" fix held across the branch. All file references in CLAUDE.md's prose resolve.
- `Runner.lean:405-445` (`bookDemandSeed` / WP5 transfer docstrings) and `Tests/SortingPinsEndgame.lean:26-34` are current, dated, and honest — the deletion+rewiring notes are exactly right.

---

## Could not verify

1. All trip-report cost figures: ~52 agent-hours, 2.2–7.9h/lane, ≈4.7M output tokens, P3c "~7.2h", "full sweep ~1.2h / claim gate ~1.5h". No usage data in the repo; the gate log carries no wall-clock total.
2. The trip report's "**~40 occurrences**" of row conds at sprint start. Measured at 42d4d29: 106 raw row-cond occurrences across 29 conditional rows (46 `rule:`, 44 `total:`, 10 `tp:`, 6 `linear:`); unique class:name pairs = 29. No reading yields ~40. Probably another post-R3 figure (see T1-2), but I could not reconstruct which.
3. Whether the tree currently builds warning-free / `just ci` is green — I did not run a build (read-only, ~30 min). I verified the committed gate artifact only.
4. `Tests/PatternPins.lean:40-48`'s claim that THIN/PRUNE "currently frontier at the NESTED-admission-induction shape … the recorded route is NOT yet exercised by this book". The pin is **count-only** (2/2), so it could not have detected a post-R3/P4a change; confirming needs a build. Flagged as a plausible stale comment.
5. How many J-calls are missing overall — I can show R3's eight and P5b's are absent, not the total shortfall.
6. The trip report's "five significant reverts". The charter records the three premise refutations exactly (RT2 ask 4, P3b's emission gap, P4b's `tp:QSORT` map), but I could not enumerate exactly five reverts from the commit record.