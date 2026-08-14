<!-- G1 design brief — persisted verbatim from the scout's report
     (read-only design scout, 2026-08-14). THE RULING DOCUMENT for the
     R-parameterized rewrite lane. -->

# G1 DESIGN BRIEF — the R-parameterized rewrite lane (PERM-TLFIX)

**Scout:** G1 design scout, read-only. **Date:** 2026-08-14.
**Artifact pin:** all verbatim quotes below are from `acl2_samples/sorting/convert-perm-to-how-many.proof-log` at `acl2-commit: 56de33b5a1072a9fadbf4d20aa28e1a23ff3ade4`, `captured-at: 2026-08-10T17:33:30Z` (file `sha256 7e188196dc92c4673c952709e35c4ab96b9dfe08e4e8383a232df1c872deedbb`, unmodified in git at scout time). **Concurrency note:** the R2 executor advanced the `acl2/` submodule to `f86e56698f` (TP emission gaps GAP-1/GAP-2/`:ALL-TPS`) *during* this scout and has modified `ACL2Lean/ClauseTree.lean`, `ProofLog.lean`, `ProofLogTypes.lean`, and `acl2_samples/pattern-tests/p8-clausify-detail.proof-log*`. The R2 charter mandates an all-books recapture, so the sorting logs **will** move; every quote here is pinned to the pre-recapture artifact and the shapes must be re-checked after the repin.

---

## 0. Ground truth

### 0.1 Live failure (run 2026-08-14, `just replay`)

```
    PERM-TLFIX → FAIL: replayNode: rune (rewriting-equivalence, NIL) applied under equivalence perm — R-parameterized recipe pending (G1 frontier)
— 6/7 replayed (6 unconditional + 0 conditional); DP leaves ✓0 ◌0 ✗0 of 0; 20606 ms
```
Same text verbatim in `Tests/driver-coverage.golden:80`. It is **1 of only 6 FAIL rows** in the whole golden (the other 5: `CLASSIFY-POS`, three `replayRecognizer` termination rows, `CD2-BOUND`).

### 0.2 The source

`acl2/books/sorting/convert-perm-to-how-many.lisp:69`:
```lisp
(defthm perm-tlfix
  (perm (tlfix x) x))
```
`acl2/books/sorting/perm.lisp` ends with **`(defequiv perm)` and contains NO `defcong` at all.**

### 0.3 The blocking node (tree dump, `Subgoal *1/2'`, literal 3)

```
                          rewrite:CDR-CONS [with-lemma] ⟨if-left in body⟩
                            (CDR (CONS (CAR X) (TLFIX (CDR X)))) => (CDR X)
                            window: (PERM (CDR (CONS (CAR X) (TLFIX (CDR X)))) (RM (CAR (CONS (CAR X) (TLFIX (CDR X)))) X)) @ [ACL2.PathFrame.arg 2 IF]
                            runes: equivalence:PERM-IS-AN-EQUIVALENCE, definition:MEMB, rewrite:CAR-CONS, fake-rune-for-type-set:NIL, type-prescription:TLFIX, definition:TLFIX
                            subst: Y → (TLFIX (CDR X)), X → (CAR X)
                            rewriting-equivalence:NIL [solidify/rewriting-equiv] ⟨rhs⟩
                              (TLFIX (CDR X)) => (CDR X)
                              window: (TLFIX (CDR X)) @ []
                              equiv: (PERM (TLFIX (CDR X)) (CDR X))
                              ⮑ justified by hypothesis literal 2 (the induction hypothesis)
```

### 0.4 The raw emission (verbatim, contiguous)

```
 (:BEGIN-INNER-REWRITE :ORIGIN REWRITE-ENTRY/BEGIN-INNER
                       :EQUIV EQUAL
                       :KIND RHS
                       :TERM (TLFIX (CDR X)))
 (:REWRITE-STEP :PATH ((RHS . Y))
                :RUNE (:REWRITING-EQUIVALENCE NIL)
                :ORIGIN SOLIDIFY/REWRITING-EQUIV
                :EQUIV PERM
                :LHS (TLFIX (CDR X))
                :RHS (CDR X)
                :EQUIV-TERM (PERM (TLFIX (CDR X)) (CDR X))
                :PARENTS NIL)
 (:END-INNER-REWRITE :ORIGIN REWRITE-ENTRY/END-INNER-CLTL2 :EQUIV EQUAL :KIND RHS)
 (:REWRITE-STEP :PATH ((2 . PERM) (1 . CDR))
                :RUNE (:REWRITE CDR-CONS)
                :ORIGIN WITH-LEMMA
                :EQUIV EQUAL
                :GENEQV (PERM)
                :LHS (CDR (CONS (CAR X) (TLFIX (CDR X))))
                :RHS (CDR X)
                :SUBST ((Y TLFIX (CDR X)) (X CAR X))
                :RUNES ((:EQUIVALENCE PERM-IS-AN-EQUIVALENCE)
                        (:DEFINITION MEMB)
                        (:REWRITE CAR-CONS)
                        (:FAKE-RUNE-FOR-TYPE-SET NIL)
                        (:TYPE-PRESCRIPTION TLFIX)
                        (:DEFINITION TLFIX))
                :PARENTS NIL)
```

**The single most consequential finding: the FORK PREREQUISITE IS ALREADY LANDED AND CAPTURED.** The 2026-08-09 R-lane decision brief (`docs/notes/2026-08-09_r-lane-decision-brief.md`) records that "the current emission HARDCODES `:equiv 'equal` at the solidify site, and the enclosing with-lemma step records a false EQUAL equation". Mike ruled option 2 (emission-only). That emission fix **shipped** and is in this log:

- `acl2/rewrite.lisp:5254-5266` (`emit/solidify/rewriting-equiv`) now emits `:equiv (ffn-symb eterm)` with the tag comment *"the earlier hardcoded 'equal under-reported R-steps (equisort-r6 audit / fork-batch item 3, the R-lane prerequisite)"* → `:EQUIV PERM`.
- `acl2/rewrite.lisp:20807-20824` (`emit/with-lemma`) now additionally emits `:geneqv` — *"the AMBIENT geneqv's relation symbols (fork-batch item 3, the R-lane prerequisite): the honest net-step relation when the rhs chain used a weaker R — the rule's :equiv alone under-reports that case (equisort-r6 audit F12)"* → `:GENEQV (PERM)`.

**No fork round-trip is required for the minimal lane.** (One optional fork item is queued in §2.)

**Second consequential finding: the emitted `:GENEQV` field is NOT PARSED.** `grep -n geneqv ACL2Lean/ProofLog.lean` finds only a comment (line 130); `StepProvenance` (`ACL2Lean/ProofLogTypes.lean:73-104`) has `equiv`, `equivTerm`, and no geneqv field. The honest net-step relation ACL2 now emits is being dropped at the parser boundary.

### 0.5 Why the failure is fail-closed today, not a wrong claim

The `CDR-CONS` node has `:EQUIV EQUAL`, so it passes the gate at `ACL2Lean/Replay/Driver/NodeCore/Node.lean:32`. Its recipe (`Node.lean:212-232`) builds `re_cdr_cons_conv : eval (CDR (CONS a b)) = eval b` with `b = (TLFIX (CDR X))`, then walks the RHS-block children to reach the recorded `rhs = (CDR X)`. The solidify child raises the G1 throw first; had it not, `chainReqEq` (`NodeCore/Compose.lean:68`) would reject. The false equation `eval (TLFIX (CDR X)) = eval (CDR X)` is never constructible. The recorded `:EQUIV EQUAL` on the parent step is a **fidelity mislabel that `:GENEQV (PERM)` now corrects**, not a soundness hole.

---

## 1. Inventory

### 1.1 Every step in PERM-TLFIX under a non-EQUAL relation

`Subgoal *1/2'` (`simplify-clause ⇒ proved`), literal 3 chain, in order. Processor runes: `definition:MEMB, definition:PERM, definition:RM, definition:TLFIX, equivalence:PERM-IS-AN-EQUIVALENCE, fake-rune-for-type-set:NIL, rewrite:CAR-CONS, rewrite:CDR-CONS, type-prescription:TLFIX`.

| # | Rune / origin | lhs ⇒ rhs | `:EQUIV` | `:GENEQV` | position | status |
|---|---|---|---|---|---|---|
| 1 | `definition:TLFIX` fncall/abbreviation | `(TLFIX X)` ⇒ `(CONS (CAR X) (TLFIX (CDR X)))` | `PERM` | — | `(3 . PERM)(1 . TLFIX)` | GREEN — composite exemption (`Node.lean:32`, `rty == "definition"`) |
| 2 | `rewrite:CDR-CONS` with-lemma | `(CDR (CONS (CAR X) (TLFIX (CDR X))))` ⇒ `(CDR X)` | `EQUAL` | **`(PERM)`** | PERM arg 1 | **BLOCKED** (its rhs child) |
| 2a | `rewriting-equivalence:NIL` solidify/rewriting-equiv ⟨rhs⟩ | `(TLFIX (CDR X))` ⇒ `(CDR X)` | **`PERM`** | — | `((RHS . Y))` | **THE BLOCKER** |
| 3 | `rewrite:CAR-CONS` with-lemma | `(CAR (CONS …))` ⇒ `(CAR X)` | `EQUAL` | `(EQUAL)` | PERM arg 2 → RM arg 1 | GREEN |
| 4 | `definition:RM` fncall/abbreviation | `(RM (CAR X) X)` ⇒ `(CDR X)` | `PERM` | — | `(2 . PERM)(2 . RM)` | GREEN — composite exemption |
| 5 | `type-alist:NIL` solidify/type-alist | `(PERM (CDR X) (CDR X))` ⇒ `'T` | `EQUAL` | — | PERM application root | GREEN — honest EQUAL (value *is* `t`); rides the `equivrefl:` reflexivity route at `Node.lean:683-714` |

ACL2 cites **`(:EQUIVALENCE PERM-IS-AN-EQUIVALENCE)`** and **no `:CONGRUENCE` rune anywhere** in this proof. That is correct and expected: `acl2/defthm.lisp:6388-6407` (`add-equivalence-rule`) stores, on `fn`'s `'congruences` property,

```lisp
(cons (list 'equal
            (list (make congruence-rule :rune rune :nume nume :equiv fn))
            (list (make congruence-rule :rune rune :nume nume :equiv fn)))
      ...)
```

i.e. for `(perm x y)` under outer geneqv `EQUAL`, **both argument slots carry geneqv `(perm)` under the `:EQUIVALENCE` rune** — R-in = PERM, R-out = EQUAL, no defcong-shaped defthm exists to parse. This is the exact `(fn, position, R-in, R-out)` table row L2 names.

The `*1/1'` base-case branch has zero R content.

### 1.2 Corpus-wide census — is PERM-TLFIX unique or a class?

Full sweep of every `.proof-log` under `acl2_samples/` (record-level extraction).

**Non-`EQUAL`/`IFF` `:EQUIV` values — 13 records total, in 5 files:**

| class | count | records | status |
|---|---|---|---|
| **A — `ABBREVIATION-EXPANSION` R-rule** (preprocess lane) | 5 | qsort ×2 (`PERM-QSORT` at `ALL-REL` arg 2), convert-perm ×2 (`PERM-TLFIX`, `PERM-COUNTER-EXAMPLE-TLFIX-2` at PERM's *own* args), p7 ×1 (`SAME-LN-DUB` at `LN` arg 1) | **all GREEN** via `replayCongCollapse` (rung 2) |
| **B — `FNCALL/ABBREVIATION` definition unfold labelled with the ambient geneqv** | 6 | convert-perm ×3, ordered-perms ×1, p7 ×2 | **all GREEN** — composite exemption |
| **C — `SOLIDIFY/REWRITING-EQUIV` under R** | **1** | **PERM-TLFIX only** | **RED — the G1 frontier** |
| **D — `WITH-LEMMA` R-rule in a SIMPLIFY literal chain** | 1 | `cov-cong-consume`: `(:REWRITE CONS-NORM-SAME-LEN2) :EQUIV SAME-LEN2 :GENEQV (SAME-LEN2)` at `LEN` arg 1 | not in the golden sweep; not pinned; would hit the same `Node.lean:32` gate |

**`:GENEQV` census (2707 records emitted):** `EQUAL` 2107, `IFF` 593, and **exactly 9 non-EQUAL/IFF** — `PERM` ×1 (the PERM-TLFIX `CDR-CONS` step, the *only* one corpus-wide), `SAME-LEN` ×2 (`cov-congruence`), `SAME-LN` ×1 (p7), `SAME-LEN2` ×5 (`cov-cong-consume`).

Critically: the other 8 non-EQUAL `:GENEQV` records are `:EQUIV EQUAL` steps whose recorded `:RHS` **is** the true instantiated rule rhs (e.g. `cov-congruence`: `(CDR (CONS A X)) ⇒ X` under `:GENEQV (SAME-LEN)`) — honest equalities that need no R-lane work. **A non-EQUAL `:GENEQV` alone does not make a step R-only; only an R-step inside the rhs block does. Corpus-wide that is exactly one record.**

Conclusion: **PERM-TLFIX is a class of one today (class C), with one adjacent unexercised member (class D).** Classes A and B are solved.

### 1.3 What PERM's `:EQUIVALENCE` rule emission looks like on our side

`PERM-IS-AN-EQUIVALENCE`'s translated Goal is offered to the replay as a whole-formula hypothesis via `EquivFullSpec` / `equivFullSpecOfGoal?` (`NodeCore/Ctx.lean:321-373`), collected in `Driver/Harness.lean:622-635` **from `depProofs`, deliberately including cross-book** — the comment names *"PERM-IS-AN-EQUIVALENCE is cross-book for convert-perm's consumers"*. It is consumed by `equivOwnPosCongr` (`Driver/Preprocess.lean:146-235`), anchored to the step-cited `(:EQUIVALENCE …)` rune per the BUG-023 discipline (`Preprocess.lean:315-327`).

**That machinery is GREEN TODAY on this exact relation.** `CONVERT-PERM-TO-HOW-MANY → REPLAYED ✓` (golden:86); its `Goal'` preprocess step cites `(:EQUIVALENCE PERM-IS-AN-EQUIVALENCE)` and contains the two class-A own-position `:EQUIV PERM` steps at `(1 . PERM)` / `(2 . PERM)`. So the own-position congruence collapse for PERM is already validated end-to-end; the R-solidify lane reuses it rather than inventing it.

### 1.4 Downstream blast radius

`PERM-TLFIX` gates `cond[rule:PERM-TLFIX]` on `CONVERT-PERM-TO-HOW-MANY` (golden:86), which is the **sole remaining cond** on that row and the sole blocker on its mirror (`Imported/Waypoints/Catalog.lean:363-382`, `.pending`). `rule:CONVERT-PERM-TO-HOW-MANY` in turn appears as a cond on 7 further rows: `WEAK-SORTFN1-IS-SORTFN2`, `STRONG-SSORTFN1-IS-SSORTFN2`, `PERM-QSORT`, `ORDEREDP-QSORT`, `MSORT-IS-ISORT`, `QSORT-IS-ISORT`, `BSORT-IS-ISORT`.

---

## 2. Design questions

### Q1 — Judgment shape: is R already abstract, and what must change?

**The judgment is already L2-conformant.** `ACL2Lean/Replay/Lemmas/Judgments.lean:33-40`:

```lean
def EvRel (R : SExpr → SExpr → Prop) (w : World) (env : Env) (a b : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, ∃ u v,
    evalOpt f w env a = some u ∧ evalOpt f w env b = some v ∧ R u v
```

`R` is an arbitrary value relation; `evrel_trans` takes transitivity as a parameter, `evrel_of_fuel_eq` takes reflexivity as a parameter, and the `if`-congruence lemmas (`evrel_if_then_congr`, `evrel_if_else_congr`) are stated `{R : SExpr → SExpr → Prop} (hrefl : ∀ x, R x x)` — one lemma per table column, uniform in R. **Nothing in the judgment hardwires equal/iff.**

What *is* hardwired to equal/iff lives strictly in the **consumers**:

| site | hardwiring | file:line |
|---|---|---|
| chain payload type `Option (Expr × Bool)` | 2-valued tag — cannot carry a third relation | `NodeCore/Recognizer.lean:643-644` (`NodeRec.rewrites`), `NodeCore/Compose.lean:68` (`chainReqEq`) — **20 call sites** |
| `applyStepSIff` | hand table for `IF`/`IMPLIES` positions only; `siff_refl` baked in as the reflexivity witness | `NodeCore/Node.lean:1600-1663` |
| `congSpecOfFormula?` | `guard (eqS.name == "EQUAL")` on the conclusion — **the promised (fn,pos,R-in,R-out) index has no R-out axis** | `NodeCore/Ctx.lean:157` |
| the frontier gate | `unless prov.equiv == "equal" \|\| rty == "definition" \|\| rty == "lambda-body"` | `NodeCore/Node.lean:32-34` |
| `replayCongCollapse` | `unless prov.origin == "abbreviation-expansion"` + `children.isEmpty` — preprocess lane only | `Driver/Preprocess.lean:260-266` |

**What must change for PERM-TLFIX specifically:** nothing in the judgment, and (see Q4 option M) **not necessarily the chain payload either**. The R-fact needed here is available at the *term* level (`EvTrue w env (PERM A B)` from the IH literal), and the collapse to EQUAL happens at the very next frame out. `EvRel` with a user-R instance — which would drag in the interpreted-relation-on-values construction and its env-independence obligation (the `interpCount` subtlety flagged in `docs/plans/2026-07-29_equiv-lane-design.md` §Ratified core 1) — **is not required by any record in the corpus**.

*Options.*
- **1a — leave `EvRel` untouched; add no user-R instance.** The R never enters a chain payload; it is consumed at the term level and collapsed in place. Zero judgment change.
- **1b — add a user-R `EvRel` instance** `Rperm u v := EvTrue w env (PERM ⟦quote u⟧ ⟦quote v⟧)`, plus the env-independence-on-quoted-arguments lemma, plus per-R reflexivity/transitivity witnesses harvested from the replayed `PERM-IS-AN-EQUIVALENCE`.

**Recommendation: 1a.** 1b is real work with **no record in the corpus that demands it** — exactly the "build the infrastructure now, wire it in later" anti-pattern. 1b becomes necessary the first time an R payload must cross more than one frame or compose with a second R-step (ACL2's Congruence Theorem 5 / `geneqv-lst` recursion) — and 1a does not obstruct it (see Q4).

---

### Q2 — Congruence recipes: what ACL2 emits, what more is needed, what the walker consumes

**What the book establishes.** `(defequiv perm)` and nothing else. The congruence at PERM's own argument positions is ACL2's *built-in* geneqv consequence of the equivalence rule, stored by `add-equivalence-rule` under the `:EQUIVALENCE` rune with **R-out = `equal`**. There is no defcong to parse, and none is needed.

**What ACL2 emits today (all already captured):** `:EQUIV <R>` on the solidify step; `:EQUIV-TERM (R A B)`; `:GENEQV (<R>…)` on the enclosing rule step; the licensing rune in the step's cumulative ttree; the equivalence rule's own replayed statement (`equivfull:` offer, cross-book, green today); the R-fact ↔ source-literal link (`ClauseTree.lean:486-538` `equivSource`, relation-agnostic).

**What is NOT emitted:** the **per-step congruence/equivalence rune at the solidify site**. `find-rewriting-equivalence` (`acl2/rewrite.lisp:5021-5027`) computes `rune := (geneqv-refinementp (ffn-symb equiv-term) geneqv wrld)` — the exact licensing rune — and pushes it into the ttree, but the emitted record at `rewrite.lisp:5262-5269` does not carry it. The replay therefore anchors on the *enclosing* step's cumulative `:RUNES` set, which is a weaker anchor than BUG-023's discipline prefers.

**Fork item for a LATER batch (do not inject into R2):** emit `:CR-RUNE` on the `solidify/rewriting-equiv` record — recompute `(geneqv-refinementp (ffn-symb eterm) geneqv wrld)` at the push site (all values in scope at `rewrite.lisp:5230-5262`). One-liner class. A **tightening, not a prerequisite**. Two further congruence-licensing mechanisms remain uncaptured and are noted (not needed here): `:REFINEMENT` rules, patterned congruences (`'pequivs`) — both already recorded as amendments in `docs/plans/2026-07-29_equiv-lane-design.md` §Ratified core 2.

**What the walker must consume (recipe, additively):**
1. `:EQUIV <R>` on the solidify step → names R.
2. `:EQUIV-TERM (R A B)` + `equivSource` → the R-fact and where it comes from.
3. The enclosing node's relativized `:PATH` last frame → the congruence position (verified against `navigateFrames`, `Reflect.lean:230-262`).
4. The step-cited `(:EQUIVALENCE …)` / `(:CONGRUENCE …)` rune → the license anchor (existing `citedEquivs`/`citedCongs` plumbing).
5. **NEW consumer, zero fork cost:** parse `:GENEQV` into `StepProvenance` and require, at the collapse, that the geneqv list *names* the solidify's R (fail-closed).

*Options for the recipe index.*
- **2a — reuse the existing two-armed dispatch** in `replayCongCollapse` (own-position arm → `equivOwnPosCongr`; defcong arm → `congHyps` filtered by `(fn, pos, R)` ∩ cited runes), factored into a shared `collapseAtCongruenceFrame` consumed by both lanes.
- **2b — add the R-out axis now** (`congSpecOfFormula?` accepting a non-EQUAL conclusion).

**Recommendation: 2a.** The corpus contains **zero** R-out ≠ EQUAL congruence rules. 2b is speculative generalization; it is the axis 1b would need, and both should land together when a record demands them. The 2a factoring is a genuine de-duplication.

---

### Q3 — The soundness story

**What "sound under perm" means here.** The replayed statement is `EvTrue w env (disjoinTerm root.inputClause)` over `evalOpt`. **PERM appears nowhere in it.** R lives entirely in proof plumbing. The obligation is the strictly local, fully value-level fact

> `eval (PERM (CDR (CONS (CAR X) (TLFIX (CDR X)))) (RM … X)) = eval (PERM (CDR X) (RM … X))`

— an equality of two `SExpr` values, from which everything outward composes as ordinary equality.

**How ACL2 justifies it:** the proof sketch written verbatim above `add-equivalence-rule`'s putprop (`acl2/defthm.lisp:6367-6382`): booleanp pins both applications two-valued; symmetry + transitivity give mutual truthiness; two-valued biimplication closes to equality.

**How we mirror it (rather than re-derive it).** `equivOwnPosCongr` (`Driver/Preprocess.lean:146-235`) is that argument, step for step, over the **replayed** `PERM-IS-AN-EQUIVALENCE` statement's four conjuncts (booleanp → `booleanp_truthy_cases`; symmetry → `implies_value_mp`; transitivity → each direction; `boolean_biimpl_eq` → the value equality). Every conjunct arrives by `instantiateEvTrueHypAt` on the offered whole-formula statement, recompute-checked at offer time. **No property of PERM is assumed; each is consumed from a replayed theorem** (`PERM-IS-AN-EQUIVALENCE` is green, perm book 8/8). The verdict (the `:EQUIVALENCE` rune) selects *which* lemma applies; the lemma's content is kernel-checked from the replayed statement.

**The R-fact's own source.** `hR : EvTrue w env (PERM (TLFIX (CDR X)) (CDR X))` comes from the IH clause literal `(NOT (PERM …))` assumed false in the branch — the identical decode the existing solidify arm performs for `(NOT (EQUAL A B))` (`Node.lean:176-190`), generalized from `EQUAL` to an arbitrary head via `evtrue_of_conv_ne_nil` + `logic_not_nil_ne` (both already in the codebase, used at `Node.lean:975-978`).

**Residual risk stated plainly.** The lane rests on `equivFullSpecOfGoal?` correctly identifying the translated defequiv Goal shape and the four conjuncts being the ones ACL2 accepted — both recompute-checked and already exercised green by `CONVERT-PERM-TO-HOW-MANY`. No new trust surface.

---

### Q4 — Scope discipline: the minimal lane vs the general lane

**GENERAL LANE — "R-tagged chains" (L2 in full).** Widen `NodeRec.rewrites`' payload to R-tagged; user-R `EvRel` instance + env-independence; `applyStepR` over a `(fn, pos, R-in, R-out)` registry with the R-out axis; congruence chains (`geneqv-lst` recursion), `:REFINEMENT`, `'pequivs`, multi-element geneqvs. Touches all 20 `chainReqEq` sites, `congSpecOfFormula?`, `Judgments.lean`. The `docs/plans/2026-07-29_equiv-lane-design.md` "rung 3".

**MINIMAL LANE — "R-solidify one-frame collapse" (option M).** The R payload never enters a chain:
1. The rule instance gives the genuine equality (the with-lemma recipe already computes exactly this as `pCore`/`rhsσ`, `Node.lean:1099-1106`; the `CDR-CONS` built-in arm as `re_cdr_cons_conv`, `Node.lean:220-226`). `rhsσ` **is** the R-step's `:LHS` — the split point already exists.
2. Lift through the node's last path frame by ordinary `applyStep`.
3. `equivOwnPosCongr` at `(PERM, argIdx 0)` with `hR` from the IH literal.
4. Chain (2)∘(3); hand to the walker with `liftPath := steps.dropLast` — **the identical shape the preprocess lane already uses** (`Preprocess.lean:447-455`).

Node contents mirrored 1:1 with ACL2's. Nothing skipped, nothing proved by a route the tree does not take.

**Why M does not corner the general lane:** the judgment is untouched and already abstract; the collapse point is read off the emitted `:PATH` + `:GENEQV` + cited rune, never from an example-specific pattern; M produces exactly what the general lane would after its collapse (B can subsume M via the same `collapseAtCongruenceFrame`); everything M cannot handle **hard-fails loudly** (R payload needing >1 frame, two composed R-steps, R-out ≠ EQUAL, multi-element geneqv, R-step not in final position of its rhs block).

**Recommendation: MINIMAL LANE (option M), with the Q2-2a factoring, Q1-1a judgment (no change), and the `:GENEQV` parser consumer.** It closes the one red row and its 8 downstream conds; every mechanism it needs is either already green or a two-line generalization of an existing decode; no fork round-trip.

**Validation targets (decorrelated).** `cov-cong-consume`: a *different* relation (`SAME-LEN2`), *different* license route (a real defcong), *different* R-fact source (a stored rule) in the *same* lane — captured, parses today, not pinned; pin it in `Tests/PatternPins.lean`. Plus a new authored book anchored at PERM-TLFIX's shape as the third.

---

### Q5 — Cost estimate per option

**Option M (recommended).**

| item | files | est. |
|---|---|---|
| parse `:GENEQV` → `StepProvenance.geneqv : List String` | `ProofLogTypes.lean`, `ProofLog.lean` | ~15 lines |
| generalize the solidify literal decode from `EQUAL`-headed to any in-scope equivalence head | `NodeCore/Node.lean` ~:143-205 | ~40 lines |
| factor `collapseAtCongruenceFrame` out of `replayCongCollapse` | `Driver/Preprocess.lean` (1110 lines; stays under norm) | ~60 moved, ~20 new |
| return-type widening: `replayNodeWith`/`NodeRec.node` → `Expr × Option RPayload`, every existing consumer hard-failing on `some` | `Node.lean`, `Rewrites.lean`, `Recognizer.lean` — 2+9 sites | ~1 line each + structure |
| the walker's R-collapse arm (mirror of `Preprocess.lean:447-455`) | `NodeCore/Rewrites.lean` (1439 lines; watch the norm) | ~50 lines |
| pin `cov-cong-consume` + a new R-solidify pattern book | `Tests/PatternPins.lean`, `acl2_samples/pattern-tests/` | 1 book + pin |
| **new judgment/lemma families** | **none** | 0 |
| **fork emissions needed** | **none** (optional `:CR-RUNE` later) | 0 |

Golden movement: `PERM-TLFIX` FAIL→REPLAYED ✓; `cond[rule:PERM-TLFIX]` retires from `CONVERT-PERM-TO-HOW-MANY`. Whether the 7 downstream `rule:CONVERT-PERM-TO-HOW-MANY` conds also retire depends on the discharge pass — unverified; treat "up to 8 rows move" as the upper bound, "2 rows" as the floor.

Risks: (i) the return-type widening touches the driver's most-trodden path — mitigated by hard-fail-on-`some` at every non-consuming site; (ii) `Rewrites.lean` near the 1500 norm — the new arm may need its own module; (iii) **sequencing** — start *after* R2's repin or fight a two-way golden diff.

**Option B (general lane).** Several times M; rewrites the driver's chain composer (the component the 2026-08-09 brief made a checkpoint); `:CR-RUNE` moves toward required; multi-element geneqvs surface. **No corpus record demands it.**

**Option D (defer).** `PERM-TLFIX` stays the sole R-class red; the convert-perm mirror stays `.pending`; the shipped fork emission stays unconsumed.

---

## 3. What I could NOT verify

1. **No prototype was built** — no claim that any option compiles or that the proof object passes the kernel.
2. Whether `PERM-IS-AN-EQUIVALENCE`'s `equivfull:` offer reaches `PERM-TLFIX`'s telescope specifically (mechanism verified cross-book and green for `CONVERT-PERM-TO-HOW-MANY`; not instrumented for PERM-TLFIX).
3. The exact golden movement (2 vs up to 8 rows).
4. Post-recapture stability — every record quoted is from the `56de33b`/2026-08-10 capture; re-check shapes after R2's repin.
5. `cov-cong-consume`'s replay status (not run).
6. Whether the two `PERM-COUNTER-EXAMPLE-*` class-A steps use the own-position arm or the defcong arm (inferred own-position; not traced).
7. `docs/LEXICON.md` was not read; terminology follows CLAUDE.md.
