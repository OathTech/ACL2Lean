<!-- End-of-branch audit report, persisted verbatim from the auditor's final text (2026-08-16). Auditor: A2 — claims verification (Opus, refute-by-default, cold worktree build). Branch: mdd/t12-sprint @ 388089d. Synthesis: docs/audits/2026-08-16_eob-audit-synthesis.md -->

Audit complete. All checks run in the isolated worktree at `mdd/t12-sprint` HEAD `388089d` (fast-forwarded from `15b016d`; `.lake/packages` symlinked, 91 `.proof-log{,.meta}` rsynced, `acl2/` submodule empty).

## Per-claim verdicts

**CLAIM 1 — Golden 116/116, 116 unconditional + 0 conditional, zero FAIL: CONFIRMED (re-derived from scratch).**

Ran `scripts/invalidate-coverage.sh`, then a cold `lake build` (6432 jobs, exit 0) + `lake build Tests.DriverCoverage` (3204 jobs, exit 0) in the fresh worktree. Live output:
```
Driver coverage — REPLAYED 116/116 (116 unconditional + 0 conditional)
aggregate OK: 29 books, sections tile the golden; covDeps verified against the logs
```
Byte comparison of the freshly assembled `.actual` against the committed golden:
```
$ cmp Tests/driver-coverage.golden Tests/driver-coverage.actual  → IDENTICAL
10c8c19de71c9dafc478650fb50f63323dadff0fcd8f148d3d0cc33d84bd7542  (both)
```
Per-book sums from my own run: 29 books, Σ = 116/116. Mechanical parse of the golden: 153 lines = 1 header + 1 probe header + 29 book bullets + **122** theorem rows, all `→ REPLAYED`; **0** occurrences of `FAIL`; **35** `cond[` occurrences, **all 35 inside `[DISCHARGE: …]` brackets, 0 before them** (i.e. 0 row-level conds). 122 − 6 `termination:` rows = **116**, which is exactly the harness's counting rule (`Tests/Coverage/Harness.lean:277` filters `termination:` out of `thmRows`).

**CLAIM 2 — Zero sorry/sorryAx/native_decide: CONFIRMED.**

Cold build: **0 warnings, 0 errors, 0 `sorryAx`/"declaration uses sorry"** across all three build logs. Grep adjudication over tracked `.lean`:
- 63 hits for `sorry|sorryAx` — 62 are comments/docstrings. The **one** live hit is `ACL2Lean/WorldGen.lean:172`, a *string literal* the `gen-world` CLI emits into generated (gitignored) source: `s!"… := sorry"`. `gen-world` is not in the certified pipeline. Not a sorry in any built proof.
- `native_decide`: 1 hit, a comment in `Waypoints/Catalog.lean:637`. `admit`: 6 hits, all prose. `^axiom `: 1 hit, prose.

Axiom receipts: my from-scratch build emitted **77** `depends on axioms` lines; joining wrapped lines gives `77 × [propext, Classical.choice, Quot.sound]` — no exceptions. The 77 constant names **diff clean against the gate log's 77**.

Direct `#print axioms` on a 12-constant sample (via `lake env lean`, importing `Tests.DriverCoverage`) — all `[propext, Classical.choice, Quot.sound]`:
`replayed_sorting_sorts_equivalent_{BSORT,QSORT,MSORT}_IS_ISORT`, `replayed_sorting_convert_perm_to_how_many_{PERM_TLFIX,CONVERT_PERM_TO_HOW_MANY}`, `ReplayedTermination.term_11_custom_measure_CD2`, `replayed_11_custom_measure_CD2_BOUND`, `term_06_measure_COUNT_DOWN`, `term_07_mutual_recursion_MY_EVENP`, `replayed_sorting_qsort_PERM_QSORT`, `replayed_02_rev_APP_ASSOC`, `replayed_sorting_bsort_ORDEREDP_BSORT`.

All **14** mirror `#guard_msgs` receipts are green by construction (build had 0 errors): 6 product theorems in `MirrorProofs/Basics.lean` (`app_assoc_int`, `app_nil_int`, `len_app_int`, `len_revAcc_int`, `rev_app_int`, `rev_rev_int`) pinned to the trio, and 8 iso squares in `MirrorProofs/Sorting.lean` pinned to trio or `[propext]`.

Structural corroboration beyond the pins: `ACL2Lean/Replay/Runner.lean:283-291` runs `collectProofAxioms` on **every** row's proof and returns `FAIL` on anything beyond the trio; ASSUMED-conditioned composed replays are never `✓` and never registered (`:301-305`). So the axiom property holds for all 122 rows, not only the 77 pinned ones.

**CLAIM 3 — Gate artifact `.gate-runs/7b69166-20260816T135429Z.log`: CONFIRMED.**

The file is in the main tree only (`.gate-runs/*.log` is gitignored). It records, in order: 13 static checks, `lake build` (6432 jobs), `lake build Tests` (= `just test`), `lake build Tests.DriverCoverage`, then `cmp golden actual` → `check-golden-current: golden matches the live assembly.`, and terminates `TRUE_EXIT=0` (line 648). **0 lines matching `warning:|error:`**, 0 matching `sorry|native_decide`. The coverage modules genuinely re-ran (real timings, e.g. `BSsortsEquivalent (2777s)`, `BSqsort (501s)`) — not cached, corroborating the "full invalidation first" claim.

Commit binding verified indirectly and it holds: `git diff --stat 7b69166 e229ef4` = **1 docs file**; `7b69166..388089d` = **2 docs files**. So the gate at `7b69166` carries to the branch tip for all code purposes.

**CLAIM 4 — Five golden rows vs real proof logs: CONFIRMED (5/5).**

| Row | Log evidence |
|---|---|
| `termination:COUNT-DOWN`, `COUNT-DOWN-ZERO` (06-measure) | `recon-tests/06-measure.proof-log:38` `(:DEFUN COUNT-DOWN … :TERMINATION-CLAUSES (((O-P (NFIX N))) ((ZP N) (O&lt; (NFIX (BINARY-+ '-1 N)) (NFIX N)))) … :SOURCE :ADMITTED)`; `:466` `(:DEFTHM COUNT-DOWN-ZERO :FORMULA (EQUAL (COUNT-DOWN 0) NIL))`. 1 `:DEFTHM` = golden's "1 theorem(s)". |
| `termination:MY-EVENP`, 2 theorems (07-mutual-recursion) | `:38`/`:42` both MY-EVENP/MY-ODDP carry `:TERMINATION-CLAUSES`; `:46` `MY-EVENP-3-IS-NIL`, `:54` `MY-ODDP-3-IS-T`. |
| `termination:CD2`, `CD2-BOUND` (11-custom-measure) | `:605` CD2 `:TERMINATION-CLAUSES (((O-P (NFIX N))) ((ZP N) (EQUAL N '1) (O&lt; (NFIX (BINARY-+ '-2 N)) (NFIX N))))`; `:609` `(:DEFTHM CD2-BOUND :FORMULA (&lt;= (CD2 N) (NFIX N)) :TFORMULA (NOT (&lt; (NFIX N) (CD2 N))))`. **All three DISCHARGE-bracket leaves match verbatim**: `:627` CLAUSEID `"Subgoal *1/5'"` ORIGIN `PREPROCESS/TAU-CONTRADICTION`; `:629` `"Subgoal *1/4"` same; `:631` `"Subgoal *1/3"` ORIGIN `PREPROCESS/TYPE-SET-FC`. |
| `PERM-TLFIX` (convert-perm-to-how-many) | `:13591` `(:DEFTHM PERM-TLFIX :FORMULA (PERM (TLFIX X) X))`, real induction: Goal PUSH-CLAUSE → `Subgoal *1/2`/`*1/2'` → `*1/1`/`*1/1'` → QED at `:14158`. Golden says 13 theorems; log has 14 `:DEFTHM`s — the extra is `PERM-IS-AN-EQUIVALENCE`, correctly attributed to the `sorting/perm` section. |
| `BSORT-IS-ISORT` (sorts-equivalent) | `:8032` `(:DEFTHM BSORT-IS-ISORT :FORMULA (IMPLIES (TRUE-LISTP X) (EQUAL (BSORT X) (ISORT X))))`; `:8034` Goal `APPLY-TOP-HINTS-CLAUSE :RESULT :PROVED`; exactly one `PREPROCESS/TAU` record after it, matching the bracket's `Goal:preprocess/tau`. |

**BSORT-IS-ISORT bracket-internality: CONFIRMED, three independent ways.** (a) Row construction is `s!"    {cp.name} → {status}{tag}{disTag}"` (`Runner.lean:939-940`) — `status` carries the row's own cond, `disTag` is appended probe text. (b) `tryDischarge` (`Runner.lean:628-668`) calls `replayDischargeLeaf … (assumeFact := true)` over an independently-quantified `env` and its proof **is never `addDecl`'d** (comment at `:648-651`: "This probe's proof is never addDecl'd … this is REPORTING accuracy for the DP scoreboard, not a trust gate"). (c) The header count strips `"  [DISCHARGE:"` before searching for `" cond["` (`Harness.lean:279-282`). Independently, the strongest artifact: `Tests/SortingPinsEndgame.lean:344-349` is a **premise-free** `example : ∀ env, EvTrue sortsEqSweepWorld env (IMPLIES (TRUE-LISTP X) (EQUAL (BSORT X) (ISORT X))) := ReplayedStatements.replayed_sorting_sorts_equivalent_BSORT_IS_ISORT` — the hand-transcribed statement typechecks against the sweep's own registered constant, which is trio-clean.

I also printed the actual **types** of three constants: all are `∀ (env : ACL2.Env), ACL2.Replay.EvTrue …` with **no hypothesis telescope**, and `CD2_BOUND`'s conclusion formula is literally `(NOT (&lt; (NFIX N) (CD2 N)))` — byte-for-concept identical to the log's `:TFORMULA`. Not weakened, not vacuous.

**CLAIM 5 — Provenance: CONFIRMED for everything verifiable here; 11 source-hash checks unverifiable.**

Submodule pointer at HEAD: `160000 commit e8d78e513d6867d04002f0df644da1723cc96e89`. Re-implemented `check-log-provenance.sh` verbatim with HEAD supplied explicitly:
- **91/91** `.meta` files stamped `e8d78e513d6867d04002f0df644da1723cc96e89` (single distinct value, no `-dirty`).
- **91/91** log banners `(Git commit hash: …)` = the same commit → no image skew.
- **91/91** `log-sha256` recomputed independently: `checked=91 bad=0`.
- Source/include hash checks: 80 logs verified clean; **11** (the `sorting/*` books, whose `source-path` is `acl2/books/sorting/*.lisp`) could not be checked — submodule not checked out. All 63 `INCLUDE-MISSING` + 11 `SUBMODULE-SOURCE` lines were exclusively `acl2/`-prefixed paths; nothing else failed.

Static gates run here: **9/12 PASS** (`check-bugs`, `check-no-shadow`, `check-gz-agreement`, `check-mirrors-pure`, `check-dark-files`, `check-file-weight`, `check-proof-logs`, `check-no-getd-done`, `check-pattern-map`). The 3 failures (`check-acl2-tags`, `check-log-provenance`, `test-provenance-gates`) are exactly the submodule-dependent ones and they **fail closed** with the correct diagnostic.

**CLAIM 6 — Receipts: PARTIAL. "77" CONFIRMED exactly; "23" REFUTED.**

- **77 is real and re-derivable.** It is the count of `depends on axioms` info lines emitted per build phase — 77 in the gate log's `lake build` phase, 77 in its `lake build Tests` phase, and **77 in my independent cold build, with identical names**. Raw grep of `#print axioms` in tracked `.lean` gives 100 tokens; the 23-token gap decomposes exactly: 15 wrapped in `#guard_msgs` (which swallows the info message: 6 Basics + 8 Sorting + 1 `Tests/SpikeTauOmega.lean`), 6 in modules outside the info-emitting set (`FlattenSpike`, `InterleaveSpike`, `Catalog`, `Replay/Driver`, `WorldDefsTest`, and 1 more), and 2 prose mentions in `DriverTests.lean`.
- **"23 #guard_msgs mirror receipts" does not correspond to anything real.** 23 is the raw count of the *string* `#guard_msgs` in tracked `.lean` files. Of those, **8 are prose mentions** (`Catalog.lean` ×2, `EquisortParametric.lean`, `IsoGen.lean`, `Sorting.lean` ×2, `Basics.lean`, `ParametricPins.lean`) and 1 is `Tests/SpikeTauOmega.lean` (not a mirror). The actual count of **mirror `#guard_msgs` axiom receipts is 14**: `ACL2Lean/MirrorProofs/Basics.lean` lines 206/244/295/345/359/378 (6) and `ACL2Lean/MirrorProofs/Sorting.lean` lines 372/387/395/432/449/458/489/497 (8), each immediately preceding a `#print axioms`.

## Discrepancies, ranked

1. **`23 #guard_msgs mirror receipts` (P5b) is wrong — the real figure is 14.** The claimed number counts prose. Low severity (it's a scoreboard figure, not a soundness claim), but it is a claim reported as fact and it is false.
2. **The `116/116` headline silently drops 6 rows.** The golden lists **122** `→ REPLAYED ✓` rows; the header counts only the 116 non-`termination:` ones. This is by design (`Harness.lean:277`) and the 6 termination rows are individually visible and individually axiom-checked, but a reader mapping "116/116" onto "every row in the file" will be off by six. Worth one clarifying word in the header text.
3. **The gate artifact has no in-log commit stamp.** The claim-gate recipe (`Justfile:165-172`) names the file from `git rev-parse --short HEAD` and `exit 0`s unconditionally; nothing inside the log records the commit or the tree's cleanliness. I closed this gap by other means (the post-gate diffs are docs-only, and I re-derived the golden myself). Flagging as an observation, **not** a recommendation to harden — it is a deterrent-standard artifact and the honest-mistake case is already covered.
4. **`Mirrors/Sorting.lean` contains no proved product theorem** — only spec `Prop` definitions plus two auxiliary termination lemmas. All 6 proved mirror PRODUCTS are the `mirror_transport%`-generated `*_int` theorems in `MirrorProofs/Basics.lean`; Sorting's 8 receipts pin iso squares, not products. Consistent with the branch's own account, but "ALL mirror theorems" is a smaller set than the name suggests.

## Could not verify

- `check-acl2-tags`, `check-log-provenance`, `test-provenance-gates` — require the `acl2/` submodule checkout (all three fail closed here, correctly).
- Source/include SHA-256 identity for the **11** `sorting/*` logs (sources live at `acl2/books/sorting/*.lisp`). Their acl2-commit stamps, banner cross-checks, and log-byte hashes **were** verified.
- The `.lisp` book text behind the sorting theorem statements (same reason) — so the sorting statement pins were checked against the *logs*, not against upstream ACL2 source.
- The 3 sorting book *sources* backing the trio spot-checks were not needed (those books are in `acl2_samples/recon-tests/`, present and hash-verified).

## What a clean checkout needs to reproduce this

1. `git clone` + `git submodule update --init` pinned to **`e8d78e513d6867d04002f0df644da1723cc96e89`** — without it, 3 of 13 statics cannot run and 11 logs' source identity cannot be checked.
2. **The 91 `.proof-log` + `.proof-log.meta` files, which are gitignored** (`.gitignore` lines `*.proof-log`, `*.proof-log.meta`). A fresh clone has none; the corpus must be regenerated with `just recapture-all` against a fork image built from the pinned submodule commit, or copied from a working tree. `check-proof-logs` fails loudly first, which is the right behaviour.
3. `.lake/packages` (mathlib/batteries/aesop/…) — network or a pre-populated cache.
4. Wall time: the cold build is **~2 h** here. `Tests.Coverage.BSsortsEquivalent` alone took **2950 s** (gate log: 2777 s) and is single-threaded; `BSqsort` ~500 s. Budget accordingly — my first background build was killed at the 1 h harness limit mid-way and had to be resumed.

No tracked file was modified (`git status --short` empty); all audit scratch lives under the gitignored `.tmp/audit/`.