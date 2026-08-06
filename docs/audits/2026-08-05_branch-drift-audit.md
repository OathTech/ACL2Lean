# Branch-wide drift audit — `mdd/sorting-closeout` (2026-08-05)

> COMMITTED RECORD (2026-08-06, pre-merge audit fix M1): this review was
> commissioned by the user ("scrutinize *all* features built on this
> branch for signs of drift from mission"), run by an Opus reviewer, and
> originally delivered in-session only. The in-code DRIFT MARKER /
> expiry citations ("branch drift audit 2026-08-05, item R1/R2/R3/9/15")
> and the golden's frontier text reference THIS document. The text below
> is the reviewer's report verbatim, recovered from the session
> transcript; the fix-list disposition (second kill round) is commit
> 910785a and the close report's "Branch drift audit + second kill
> round" section.

Build green (6328 jobs, TamperTests pass). Imported-layer spot-check returned clean. Here is the audit.

---

# Drift audit — `mdd/sorting-closeout` (`e0d572d..HEAD`, 80 commits)

## Method and ground truth

- `lake build` → **exit 0**, "Build completed successfully (6328 jobs)".
- Golden at HEAD: `REPLAYED 86/116` (88 `✓` rows, of which 2 are display-only `termination:` rows — the header counts theorem rows only, `Tests/DriverCoverage.lean:125-128`), 1 `ASSUMED ◌`, 33 `FAIL`.
- No `sorry`/`admit`/`axiom`/`native_decide` in `ACL2Lean/` (the only `sorry` is a string literal in a `gen-world` stub template, `ACL2Lean/WorldGen.lean:172`, pre-existing).
- **Dependency method**: for each mechanism I diffed `Tests/driver-coverage.golden` at the introducing commit (`git diff C^ C -- Tests/driver-coverage.golden`) and checked the commit's file footprint. Every new mechanism on this branch replaced a `throwError`, so it can only convert a FAIL into progress — it cannot silently substitute a route under an already-green row. That makes the per-commit golden delta an exact dependency read-off, not an inference.

---

## 1. Feature inventory

| # | Mechanism | file:line | Commit | Class | Verdict | Dependent green rows |
|---|---|---|---|---|---|---|
| 1 | Plain-`:use` composition (`useHyps`, `lmiInstance?`, `mkUseHypType`, `dischargeUseHyp`, `theoremUseCitedNames`, the `apply-top-hints` arm) | `Core.lean:1845-1943`, `NodeCore.lean:226-241`, `Discharge.lean:80-87`, `Harness.lean:537-570` | `4c1e37f` | REPLAY | **KEEP** (exemplary) | `LEN2-APP-VIA-USE`, `CONVERT-PERM-TO-HOW-MANY` |
| 2 | `equal-case-split` node arm | `NodeCore.lean:3818-3878` | `6e23a10` | REPLAY | **KEEP** (exemplary) | `EQUAL-CONS`, `ORDERED-PERMS` (+ `ORDEREDP-QSORT` transitively) |
| 3 | Equation-closure **disequality** rung inside `typeSetWalk` | `NodeCore.lean:1837-1875` | `6e23a10` | **INFRA-MIRROR (search)** | **REVISE** | `MEMB-RM`, `ALL-REL-RM-2`, `PERM-IMPLIES-EQUAL-ALL-REL-2`; conds of `PERM-MEMB`/`PERM-RM`/`PERM-TRANSITIVE`/`PERM-IS-AN-EQUIVALENCE`/`ORDEREDP-QSORT` |
| 4 | Ground-hyp KNOWN-TRUE relief (`replayExecGround` on a closed hyp) | `NodeCore.lean:4266-4285` | `a5ca783` | Carve-out-adjacent | **KEEP with note** | `TRUE-LISTP-RM`, `RM-TLFIX`, `PERM-COUNTER-EXAMPLE-TLFIX-2` |
| 5 | Equivalence-rune own-position congruence (`equivOwnPosCongr`, `EquivFullSpec`, `equivFullSpecOfGoal?`, `equivFullHyps`) | `Preprocess.lean:135-197`, `NodeCore.lean:249-292` | `3503379` | REPLAY (rune-anchored) | **KEEP** | `CONVERT-PERM-TO-HOW-MANY` |
| 6 | Complement-tautology close | `Core.lean:1280-1320` | `e5eeab9` | Gray (inference-from-absence) | **KEEP with note** | `TRUE-LISTP-BNEXT` |
| 7 | `builtinRecogFacts` registry (`LEN` → consp-nil/natp-t) + the builtin recognizer/false arm + builtin `compound-recognizer` route | `NodeCore.lean:2472-2479`, `2637-2668`, `3714-3752` | `5beacfe` | INFRA-MIRROR (name registry) | **REVISE** | `termination:BNEXT` |
| 8 | `compound-recognizer` rune→head whitelist `[("NATP-COMPOUND-RECOGNIZER","NATP")]` | `NodeCore.lean:2940` | `5beacfe` | INFRA-MIRROR (rune registry) | **REVISE** | `termination:BNEXT` |
| 9 | `compound-recognizer` **world-fn** route (`logic_natp_t_of_int_tp_fact`) | `NodeCore.lean:2977-3010` | `4e4ac03` | Gray | **KILL or park** | **none** (only `termination:BSORT`, which is `ASSUMED ◌`) |
| 10 | `Totality.mkRecTermInfo` measure-head generalization + all-clause/O-P goal shapes | `Totality.lean:264-296` | `4e4ac03` | REPLAY (recompute-checked vs emitted goal) | **KEEP** | `termination:BNEXT` |
| 11 | Runner `needsRecorded` widening (user-measure fns → recorded route) | `Runner.lean:44-59` | `c6a0912` | REPLAY | **KEEP** | `termination:BNEXT` |
| 12 | `POSP`/`NATP` in `dpUnary` + `dpLiftHeads` | `NodeCore.lean:222-226`, `DpLift.lean:53-55` | `3508704` | REPLAY (pure registration) | **KEEP** | `termination:BNEXT` |
| 13 | μ-route discrimination (`registryCovered := ACL2-COUNT ∥ LEN` + `destructorChainOk`) | `Waterfall/Induction.lean:176-206` | `5beacfe` | INFRA-MIRROR (calibrated heuristic) | **REVISE** | regression-guard for `HOW-MANY-BNEXT` + qsort rows |
| 14 | **tpthm / `:CLASSES` consumer stack** — `matchPatternGo`, `TpThmSpec`, `classesNameTP`, `tpThmHyps`, `mkTpThmHypType`, `dischargeTpThmHyp`, the `replayRecognizer` tpthm arm, the inline `coreBool?` whitelist, the tpthm `ContextDemand` emitter | `NodeCore.lean:154-206`, `2670-2765`, `6337-6355`; `Waterfall.lean:196-201`; `Discharge.lean` | `39169cc` | **INFRA-MIRROR** | **KILL** | **none** |
| 15 | Position-canonical anchoring disambiguation | `NodeCore.lean:5240-5270` | `d136e6a` | Gray (tie-break preference) | **KILL or park** | **none** |
| 16 | Single-summand positive-sum cell (`logic_equal_nil_of_plus1_nonneg1`) | `NodeCore.lean:4571-4589`, `EvalLemmas.lean:3917-3931` | `3404c2d` | Per-case cell | **KILL** | **none** |
| 17 | Term-vs-sum disjointness cells (`logic_equal_nil_of_plus1_self_r/_l`) | `NodeCore.lean:4487-4530`, `EvalLemmas.lean:3933-3954` | `053e131` | Per-case cell | **KILL** | **none** |
| 18 | `type-set-equality` orientation normalization (`flippedEq`) | `NodeCore.lean:4467-4478`, `4605-4612` | `053e131` | Gray | **KILL** (with 16/17) | **none** |
| 19 | Last-position nil-drop + 4 two-valued sources (`re_val_if_t_nil`, `logic_boolwrap_self_{equal,not,t,of_boolean_tp}`) | `Core.lean:594-674`, `EvalLemmas.lean:5742-5765`, `5798-5852` | `99577c4` | Per-case | **KILL** | **none** |
| 20 | L-fold bridge arm (`re_equal_t_fold_l`, `logic_equal_t_equal_l`) | `NodeCore.lean:2810-2823`, `EvalLemmas.lean:5798-5803`, `5866-5890` | `3404c2d` | Per-site | **KILL** | **none** |
| 21 | Boolean-TP fold bridge arm (`logic_equal_t_self_of_boolean_tp`) | `NodeCore.lean:2824-2857`, `EvalLemmas.lean:5854-5864` | `3404c2d` | Gray (consumes emitted TP) | **KILL** (unconsumed) | **none** |
| 22 | `bridgeEqualNilNormDeep` wired at the Core literal-chain end | `Core.lean:1233-1246` | `3404c2d` | Gray | **KILL** (unconsumed) | **none** |
| 23 | `assumedDpFactCond` named constant + `tryReplay` ASSUMED-registration refusal + `Macro.lean` guard + `Meta.check` on condition resolution | `NodeCore.lean:470-473`, `Runner.lean:284-295`, `Mirrors/Macro.lean:141-150`, `Totality.lean:382-388` | `3029890`, `2275400` | Hardening | **KEEP** (credit) | prevents a vacuous green (`termination:BSORT`) |
| 24 | `guardNoUseHint` on every non-use-hint processor arm; multi-payload refusal | `Core.lean:1600-1610`, `1848-1852` | `4c1e37f` | Hardening | **KEEP** | — |
| 25 | DP-leaf F6 (no silent ASSUMED downgrade after a successful `proveDpFact`) | `Totality.lean:1413-1437` | `04120bb` | Hardening | **KEEP** | — |
| 26 | `allBookRules` direct rule-events walk (v1 gap closed) | `Runner.lean:113-131` | `a6f5f77` | REPLAY (consumes more emitted content) | **KEEP** | golden byte-identical |
| 27 | `destructorChainOk` S7 dedupe (explicit `allowCons` reach) | `NodeCore.lean:453-465` | `685de93` | Refactor | **KEEP** | — |
| 28 | Emission-side: `:CLASSES`, `:LMI-LST`, `:TA-DERIVATIONS`, `:FC-DERIVATIONS`, encapsulate brackets, `:CONSTRAINTS`, `witnessDefun`, `Development.scopes` | `ProofLog.lean`, `ClauseTree.lean:93-232`, `838-960` | `e4625bb`, `2c482ea`, `def0415` | Emission (correct direction) | **KEEP**, but see §4 | — |

Also verified: the fork genuinely emits what mechanisms 2 and 8 consume — `EQUAL/CASE-SPLIT-RHS` × 5 and `-LHS` × 2, `NATP-COMPOUND-RECOGNIZER` × 18 in `acl2_samples/`. And `HOW-MANY-BNEXT` went green at `8298966` — the **fork recapture**, not any Lean mechanism. That is the model outcome.

---

## 2. KILL list

All of these have **zero green golden rows**, verified by per-commit golden diff.

### 2a. The whole `phase7-close (11–14/n)` PCE residue — items 16–22

This is the single largest finding, and it is a consequence of the `685de93` tidy-up that the branch's own close report does not draw. When `bridgeIffBoolNorm` and the tlp-cdr demand emitter were killed, `PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS` regressed to the **literal-3 chain frontier at `Subgoal *1/3'`** — a wall *earlier* than every piece the tidy-up KEPT. Confirmed by golden:

- `3404c2d` moved PCE from the literal-3 wall to `Subgoal *1/1.2`; `99577c4` and `053e131` moved it further; `685de93` put it back at the literal-3 wall.
- Each of those four commits changed **exactly one golden line** (PCE's) with a footprint of `Core.lean` + `NodeCore.lean` + `EvalLemmas.lean` only.

So the KEPT pieces are still compiled and still invoked (the L-fold / boolean-TP-fold arms run and return `none`; the last-position nil-drop is not reached at all — `"literal folded to 'NIL in LAST position"` appears nowhere in the golden), but **not one of them is load-bearing for any `✓`**. They are the per-case accretion the drift test targets, now with the row they were built for removed from under them.

Revert notes:
- `NodeCore.lean:4487-4530` (`sumSelf?` block) and `4467-4478` + `4605-4612` (`flippedEq`) — restore the direct `let .cons (.atom (.symbol eqS)) (.cons x (.cons qc .nil)) := lhs` destructure.
- `NodeCore.lean:4571-4589` — restore the nested-sum-only `numericCell?` match. Note this arm also carried a real match-capture fix (the old nested pattern dead-ended); keep the fix, drop the single-summand sibling.
- `Core.lean:594-674` — restore `throwError "literal folded to 'NIL in LAST position …"`.
- `NodeCore.lean:2810-2857` — drop both new `bridgeEqualNilNorm` arms.
- `Core.lean:1233-1246` — restore the direct `throwError`; `bridgeEqualNilNormDeep` itself **pre-exists the branch** (`4202c06`) and stays.
- Orphaned lemmas to remove with them: `logic_equal_nil_of_plus1_nonneg1`, `logic_equal_nil_of_plus1_self_r/_l`, `re_val_if_t_nil`, `logic_boolwrap_self_equal/_not/_t/_of_boolean_tp`, `logic_equal_t_equal_l`, `re_equal_t_fold_l`, `logic_equal_t_self_of_boolean_tp`.

Replacement is already queued as **fork batch item 5** (literal-boundary iff-context normalization emission). Nothing breaks: PCE is red at the same wall either way.

### 2b. The tpthm / `:CLASSES` consumer stack — item 14

`39169cc` moved exactly one golden line (PCE, FAIL → different FAIL) and touched only `Harness.lean`/`NodeCore.lean`/`Waterfall.lean`. **No row is green because of it.**

Why it is drift, not replay:
- `matchPatternGo` (`NodeCore.lean:154-176`) exists precisely because "ACL2 emits NO substitution (type-set TP-rule applications)". That is an *emission gap*, and the drift test's recompute allowance is scoped to where "the artifact **genuinely cannot** record it". The fork can record a `:SUBST` at a type-set rule application exactly as it does at a rewrite step.
- The inline `coreBool?` whitelist (`NodeCore.lean:2743-2752`) hard-codes `TRUE-LISTP → Logic.trueListp` and `CONSP → Logic.consp` — recognizer knowledge in Lean.
- The tpthm `ContextDemand` emitter (`NodeCore.lean:6337-6355`) hard-codes `TRUE-LISTP` as the demanded hypothesis at every argument of the inner application. This *guesses* the TP rule's hypothesis instead of reading it — and the offered `TpThmSpec.formula` already contains the real `IMPLIES` antecedent, so the guess is not even necessary.

Revert note: `TpThmSpec`, `classesNameTP`, `matchPattern?`/`matchPatternGo`, `tpThmHyps`, `mkTpThmHypType`, `dischargeTpThmHyp`, the `citedTpThms` parameter threading, the `replayRecognizer` tpthm arm, and the tpthm demand block all come out together. The `ClauseProof.classes` **field and its parser stay** (emission-side, correct). `replayRecognizer`'s frontier message reverts to the pre-`39169cc` text.

### 2c. Items 9 and 15

- **Item 9** (`compound-recognizer` world-fn route): supports only `termination:BSORT`, which renders `ASSUMED ◌` — by the branch's own S1/S4 rule, not a green row. Its own construction went through the audit cycle where it briefly *was* a vacuous `✓` (`4e4ac03` → caught NOT-READY at `059d16c` → fixed at `3029890`). Park it behind fork batch item 1 (local `:LINEAR` snapshot), which is the real unblocker.
- **Item 15** (position-canonical disambiguation): only moved `HOW-MANY-RM-GENERAL` from one red to another red. Its own recorded residual (S6) admits it "pins candidate FRAMES but not `preSwap?`/`branchAnchor` across survivors, then **prefers** the branch-anchored one" — a preference among ambiguous readings is search, not read-off. Either revert to the hard-fail or complete it (pin all three, or prove uniqueness) before it acquires a dependent.

---

## 3. REVISE list

### R1 — Equation-closure disequality rung (item 3). Highest stakes: 3 direct green rows.

`NodeCore.lean:1841-1875`. The code's own comment is the honest label:

&gt; `-- This is BOUNDED DETERMINISTIC SEARCH (audit 2026-08-04 F7 — the honest label): candidates in fact order, both orientations, first type-checking connection taken`

Concretely it iterates `disCands` (every in-scope `(EQUAL x y)` literal/segment fact) × 2 orientations, running a BFS `eqChain?` (`for _ in List.range (eqs.length + 1)`, `NodeCore.lean:1691-1707`) from each side of the target to each end of each candidate, and takes the first that type-checks. That is a walk over the clause's own fact set with fact-gated moves — the INFRA-MIRROR definition. The mitigating fact is real: the *target* is pinned by the node's emitted verdict, so the search cannot choose what it proves, only how.

Note the provenance, which sharpens the concern: `MEMB-RM`, `ALL-REL-RM-2` and `PERM-IMPLIES-EQUAL-ALL-REL-2` were **green before** the `8298966` fork recapture and were broken *by* it. The response was to grow a Lean-side search rather than to ask why the recapture stopped emitting the type-alist derivation. (The underlying `eqChain?`/`inScopeEquations`/`composeEqChain` kit pre-dates the branch — `962b4d8` — so what is new is this consumer rung, not the closure machinery.)

**Replacement route.** Fork batch item 3 already exists in the right shape: emit the fc/type-alist entry *provenance* at the expunge call sites. Extend it to the `equal`/type-set-nil verdict: emit the two literals ACL2 actually connected (its type-alist stores the equivalence class and the disequality it contradicted). Then the rung becomes a two-fact lookup + one `congr` composition with no BFS and no candidate loop.

**What breaks meanwhile.** Reverting now costs 3 green rows directly plus 6 rows' `cond` sets — a regression to 83/116. My recommendation is to **hold it under an explicit expiry**: keep it, retitle the comment from "bounded deterministic search" to an unambiguous drift marker, and gate the arc's next merge on fork item 3 landing.

### R2 — `builtinRecogFacts` + the rune→head whitelist (items 7, 8). 1 green row (`termination:BNEXT`).

The gate is decorative in a way worth naming: the arm requires `LEN`'s **emitted nonneg-int TP corollary** to be present, but the content it then uses (`Logic.consp (Logic.len x) = nil`, `Logic.natp (Logic.len x) = t`) is proved from the trusted core and does not follow from that corollary. So the emitted fact authorizes rather than supplies. Combined with `[("NATP-COMPOUND-RECOGNIZER","NATP")]`, this is ACL2's recognizer-alist transcribed into Lean one entry at a time.

**Replacement route.** Fork batch item 2, already queued and correctly scoped: emit `:FALSETS` alongside `:TYPESET`/`:TRUETS` at the two recognizer sites (`rewrite.lisp` ~5556/5618) and snapshot the cited `'recognizer-alist` tuples `(fn, true-ts, false-ts, strongp)`. That makes verdicts data-driven off emitted content — one rule, no per-recognizer code — and subsumes both registries. The close report already commits to this.

**What breaks meanwhile.** `termination:BNEXT` reverts to `FAIL: replayRecognizer: value of (CONSP (LEN X)) does not reduce to NIL`. It is a display row, not in the 86/116 headline.

### R3 — μ-route discrimination (item 13).

`Waterfall/Induction.lean:190` — `registryCovered := cnt.name == "ACL2-COUNT" || cnt.name == "LEN"`, combined with a `destructorChainOk` walk over the emitted decrease arguments, to choose between two Lean-side measure interpretations. The branch's own note calls it "a calibrated heuristic (D7)". It is bookkeeping only (it selects an interpretation, not a proof step), and it currently functions as a *regression guard* for `HOW-MANY-BNEXT` and the qsort rows rather than an enabler. Revising it means: read the route off the emitted `:MEASURE` shape alone (no name whitelist), or remove the `LEN` registration that made the discrimination necessary in the first place. Low urgency; do it when R2 lands, since R2 subsumes the `LEN` special case.

### R4 — Two KEEP-with-note items

- **Item 4, ground-hyp KNOWN-TRUE.** The comment invokes the DP carve-out, and its mechanism attribution was corrected by audit (F1: type-set-rec's built-in recognizer tuple, zero runes added — a genuinely verdict-only step). The stretch to flag: CLAUDE.md's carve-out is written for *clause leaves* ("Where ACL2 itself closes a **clause**"), and this fires on a **hypothesis-relief marker inside a rewrite chain**. The step is verdict-only and the arm hard-fails if the ground value is not exactly `t`, so I am not calling it drift — but the carve-out's scope should be explicitly widened by MDD, or the arm should be re-anchored, rather than being extended by comment.
- **Item 6, complement-tautology close.** `Core.lean:1281-1284`: "a non-closing literal with NO recorded continuation **is how the log shows** ACL2's `add-literal` recognizing the rewritten result's COMPLEMENT". This infers ACL2's step from the *absence* of a record — the inverse of consuming a recorded step. It is saved by being fail-closed (it needs the complement fact in `litFacts` via the type-checked lookup, `Core.lean:1296-1300`) and by composing in one shot. Keep, but the honest fix is for the fork to emit the tautology-close verdict, and the comment should say "we infer from absence" rather than "the mirror:".

---

## 4. Dead / unconsumed code

| Item | file:line | Status |
|---|---|---|
| `:TA-DERIVATIONS` field + parser | `ProofLog.lean:131-136`, `750-762` | Parsed; **all-NIL by the fork's own smoke diagnosis** (`a2b8b22`). Zero consumers. |
| `:FC-DERIVATIONS` / `ClauseItem.fcDerivations` | `ProofTree.lean:227`, `539-541` | Threaded through 6 sites; **every one skips it**. No replay consumer. Documented as Phase-6. |
| `Development.scopes` + `Scope` | `ClauseTree.lean:160-232` | Consumed only by a test pin (`Tests/SortingPins.lean:833-848`). No replay consumer. |
| `encapsulateBegin/End`, `constraints`, `witnessDefun` events | `ClauseTree.lean:93-113` | Recon + `dump-proof-tree` printing only. No replay consumer. |
| `logic_equal_t_equal_l` | `EvalLemmas.lean:5798` | Zero external refs; used only by `re_equal_t_fold_l`, itself in the KILL list. |
| KILL-list lemmas 16-22 | see §2a | Statically referenced, dynamically never load-bearing. |

Confirmed **cleanly removed** by the tidy-up and the audit remediation (no orphans left): `bridgeIffBoolNorm`, `re_if_boolwrap_test`, `re_if_true_test_drop`, `re_not_boolwrap`, `re_not_congr_eval`, `logic_trueListp_cdr`, `tsRecogWalk`, `integerpTWalk`.

The unwired emission surfaces are the *correct direction of travel*, but they are also the banned "build the infrastructure now, wire it later" pattern in its emission form — 3 of the 5 emission-cluster items landed parsers with no consumer. Worth an explicit decision rather than accumulation.

---

## 5. Overall drift assessment

**The branch's direction is right; its tail accreted.**

What is genuinely strong, and should be credited: the plain-`:use` composition (item 1) is textbook replay — it consumes `:LMI-LST`, `:HYPS`, `:CONSTRAINT-CL` and the application clauses, cross-checks `substTerm σ formula` verbatim against the emitted instance, and hard-fails on every non-plain lmi form. `equal-case-split` (item 2) recompute-checks the fork's emitted rhs against the origin's exact construction. `HOW-MANY-BNEXT` greened purely from a fork recapture. The hardening cluster (items 23-25) caught and structurally fixed a *vacuous green* — `termination:BSORT` was reported `REPLAYED ✓` while carrying a machine-refutable `ASSUMED:dp-fact` — and closed the macro-path bypass. The `685de93` tidy-up correctly identified and removed the worst offenders. The Imported product layer is clean: four new native mirrors, no evaluator vocabulary in any statement, one new simulation kit (`bnext`) that is a genuine per-function evaluation lemma, zero `sorry`/`axiom`, both the seam gate and the criterion-1 gate mechanized and green — and the `CONVERT-PERM-TO-HOW-MANY` capstone was correctly left `.pending` with a drafted decode *reverted* rather than shipped as an ornamental import.

Against that, the quantitative signal the project's own carve-out drift test asks for. Counting per-case (non-general) discharge mechanisms added on this branch: items 7, 8, 9, 14, 16, 17, 18, 19, 20 — **nine**, of which **six have zero dependent green rows**. The test says "a growing count fails the test", and this count is growing. The shape is unmistakable in the commit series `3404c2d → 99577c4 → 053e131`: three commits, one row advanced through successive frontier classes, each commit adding a cell or an arm, each changing exactly one golden line. The agent declared the stop-early condition itself at `2b0cd34`, which is the right instinct — but the tidy-up that followed removed the two mechanisms that were *obviously* loops and kept the ones that were *individually* single-shot, without checking whether the row they served still reached them. It does not.

The most consequential single item is R1 (the equation-closure disequality rung), because it is the only new search on the branch that green rows actually depend on, and because of how it arose: a fork recapture broke three previously-green rows and the response was a Lean-side search rather than an emission question. That is the exact inversion the mission forbids, and it is the one place where "tidy without losing useful work" requires a real trade — everything else on the KILL list can be reverted at zero cost to the scoreboard.

Suggested sequencing: (a) revert §2a and §2b now — 12 mechanisms, ~25 lemmas, no golden change beyond the already-red PCE row; (b) park items 9 and 15; (c) hold R1 and R2 under an explicit expiry tied to fork batch items 2 and 3, with their comments retitled as drift markers so they cannot normalize; (d) decide explicitly on the four unwired emission surfaces rather than letting them accumulate.

**What I could not verify.** (i) That the mechanisms I classified as reachable-but-never-firing are truly never *partially* load-bearing inside a green row's proof term — my evidence is that each replaced a `throwError` and that the introducing commits moved exactly one golden line, which is strong but is inference from the golden rather than instrumentation; a definitive check would neutralize each with a `throwError` and confirm a byte-identical golden in one build. (ii) Whether the fork's `equal/case-split-*` and `NATP-COMPOUND-RECOGNIZER` emissions are *faithful* to what ACL2 internally did — I confirmed they are emitted and consumed, not that they are correct. (iii) `bnextBody`'s transcription fidelity against `acl2_samples/sorting/bsort.lisp` (the subagent flagged this too — recommend a direct diff). (iv) I ran `lake build`, not the full `just ci` (pattern-map, bugs, tags, log-provenance, differential gates).
