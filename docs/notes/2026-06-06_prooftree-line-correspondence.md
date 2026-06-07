# `my-len-my-app` reconstructed proof tree — line-for-line correspondence

Created 2026-06-06. Source dump: `docs/notes/2026-06-06_simple-prooftree.txt`
(the complete `dump-proof-tree acl2_samples/simple.proof-log` output; one theorem
section, nothing before/after it).

> ⚠ **Snapshot/line-number note.** The line numbers below reference the dump as it
> was *during* this analysis. Both fixes this analysis motivated have since been
> applied: §E.1–E.2 (renderer: honest labels + induction-as-parent) and §D.1 (ACL2
> source: instantiate `if-simplification` branches via `sublis-var`). The committed
> `…_simple-prooftree.txt` reflects the FIXED state, so its layout/line-numbers and
> the once-formal `(my-len (cdr x))` term differ from the references below; the
> tree structure and this analysis's conclusions are otherwise unchanged.

Goal of this note: account for **every** line of the dump, state its role, and
check that **every** step contributes to justifying the top-level theorem

> **P(x,y) ≔ `(equal (my-len (my-app x y)) (binary-+ (my-len x) (my-len y)))`**

Notation: I track the *current term of the literal being rewritten* in `[[ … ]]`
after each node so the chain is visible as F₀ ⇒ F₁ ⇒ … ⇒ `(quote t)`.

---

## A. Root + induction (the top-level structure)

| line | content | role |
|---|---|---|
| 1 | (blank) | separator |
| 2 | `══ my-len-my-app ══` | **ROOT** = the theorem. (Only one theorem in the whole dump.) |
| 3 | `Induction on (my-app x y) → 2 subgoals` | **THE TOP-LEVEL MOVE** = induction. Its 2 subgoals are its children; everything below is *under* this. |
| 4 | `Scheme:` | header for the induction cases |
| 5 | `Case 0:` | base case (as a clause) |
| 6 | `(consp x)` | Case 0 literal — the recursion guard |
| 7 | `(equal (my-len (my-app x y)) …)` = P | Case 0 literal — the goal. ⇒ Case 0 = `(consp x) ∨ P` ≡ **¬(consp x) → P** (BASE) |
| 8 | `Case 1:` | step case (as a clause) |
| 9 | `(not (consp x))` | Case 1 literal |
| 10 | `(not (equal (my-len (my-app (cdr x) y)) …))` = ¬P(cdr x) | Case 1 literal — the **IH** (negated) |
| 11 | `(equal (my-len (my-app x y)) …)` = P | Case 1 literal — the goal. ⇒ Case 1 = `¬(consp x) ∨ ¬P(cdr x) ∨ P` ≡ **(consp x) ∧ P(cdr x) → P** (STEP) |

**Justification check (the induction principle):** Case 0 (¬consp → P) and Case 1
(consp ∧ P(cdr x) → P) together prove `∀x. P(x,y)` by well-founded (structural,
on `cdr`) induction on `x`. This *is* what justifies the theorem; the two subgoals
below discharge the two cases. ✔

| 12 | (blank) | separator |

---

## B. Subgoal *1/2  =  Case 0  =  BASE  (context: assume ¬(consp x))

| line | content | role |
|---|---|---|
| 13 | `── Subgoal *1/2 ──` | proof of the BASE clause |
| 14 | `Clause (2 literals):` | the disjunction to prove |
| 15 | `[0] (consp x)` | literal 0 |
| 16 | `[1] (equal … )` = P | literal 1 (the goal) |
| 17 | (blank) | sep |
| 18–21 | `Literal 1 … (consp x) → (consp x) (no rewrites)` | **hypothesis literal**: left as-is. It is the disjunct that holds when `(consp x)` is true; proving literal 1's *negation* is the context for literal 2. Role: makes the clause a tautology together with literal 2. ✔ |
| 22 | (blank) | sep |
| 23 | `Literal 2 (notFlg=false):` | the goal literal P, to be driven to `t` under ¬(consp x) |
| 24 | `Input: (equal (my-len (my-app x y)) (binary-+ (my-len x) (my-len y)))` | `[[ F₀ = P ]]` |
| 25 | `Result: (quote t)` | claim: P ⇒ `t` under this case's context |
| 26 | `Proof tree (4 top-level nodes):` | ⚠ **MISLEADING LABEL** — this is the *rewrite chain for this one literal* (4 steps), **not** "the proof tree" and **not** "top-level" of the theorem. (See §E.1.) |

### Node 1 (lines 27–33) — `definition:my-app`,  `(my-app x y) ⇒ y`
| 27 | `definition:my-app [fncall/abbreviation]` | unfold my-app |
| 28 | `(my-app x y) => y` | net effect |
| 29 | `subst: y → (. y), x → (. x)` | formals (x,y) ↦ args (the vars x,y) |
| 30–31 | child `recognizer/false  (consp x) => (quote NIL)` | under ¬(consp x), body's test is NIL |
| 32–33 | child `if-simplification  (if (quote NIL) (cons (car x) (my-app (cdr x) y)) y) => y` | body takes the else-branch |
Effect: rewrite the `(my-app x y)` inside P. `[[ F₁ = (equal (my-len y) (binary-+ (my-len x) (my-len y))) ]]` ✔ advances P.

### Node 2 (lines 34–41) — `definition:my-len`,  `(my-len x) ⇒ (quote 0)`
| 34 | `definition:my-len [fncall/abbreviation]` | unfold my-len |
| 35 | `(my-len x) => (quote 0)` | net effect |
| 36 | `subst: x → (. x)` | formal x ↦ var x |
| 37–38 | child `recognizer/false  (consp x) => (quote NIL)` | ¬(consp x) |
| 39 | `runes: definition:my-app` | dependency annotation (this step rests on my-app's def) |
| 40–41 | child `if-simplification  (if (quote NIL) (binary-+ (quote 1) (my-len (cdr x))) (quote 0)) => (quote 0)` | else-branch |
Effect: rewrite `(my-len x)` in the RHS. `[[ F₂ = (equal (my-len y) (binary-+ (quote 0) (my-len y))) ]]` ✔

### Node 3 (lines 42–52) — `rewrite:unicity-of-0`,  `(binary-+ (quote 0) (my-len y)) ⇒ (my-len y)`
| 42 | `rewrite:unicity-of-0 [with-lemma]` | library rule `(+ 0 z) = (fix z)` |
| 43 | `(binary-+ (quote 0) (my-len y)) => (my-len y)` | net effect (after the fix subtree) |
| 44 | `runes: definition:fix, type-prescription:my-len, definition:my-len, definition:my-app` | dependencies of the step |
| 45 | child `definition:fix [fncall/non-recursive]` | unfold the `(fix …)` produced by unicity-of-0 |
| 46 | `(fix (my-len y)) => (my-len y)` | net effect of fix subtree |
| 47 | `subst: x → (my-len y)` | fix's formal x ↦ `(my-len y)` |
| 48–49 | grandchild `recognizer/true  (acl2-numberp (my-len y)) => (quote t)` | the recognizer fires… |
| 50 | `runes: type-prescription:my-len, …` | **…justified by the consumed `type-prescription:my-len`** (my-len is an integer ⇒ acl2-numberp). This is the one "type fact from ACL2" load-bearing here. |
| 51–52 | grandchild `if-simplification  (if (quote t) x (quote 0)) => x` | fix body with numberp-test true → x = `(my-len y)` |
Effect: `(+ 0 (my-len y)) ⇒ (fix (my-len y)) ⇒ (my-len y)`. `[[ F₃ = (equal (my-len y) (my-len y)) ]]` ✔

### Node 4 (lines 53–54) — `equal-self`,  `(equal (my-len y) (my-len y)) ⇒ (quote t)`
| 53–54 | `equal-self  (equal (my-len y) (my-len y)) => (quote t)` | reflexivity. `[[ F₄ = (quote t) ]]` |
**Base discharged:** under ¬(consp x), P ⇒ `t`, so Case 0 holds. ✔
| 55 | (blank) | sep |

---

## C. Subgoal *1/1  =  Case 1  =  STEP  (context: assume (consp x) and the IH)

| line | content | role |
|---|---|---|
| 56 | `── Subgoal *1/1 ──` | proof of the STEP clause |
| 57 | `Clause (3 literals):` | the disjunction |
| 58 | `[0] (not (consp x))` | literal 0 |
| 59 | `[1] (not (equal (my-len (my-app (cdr x) y)) …))` = ¬P(cdr x) | literal 1 = the IH (negated) |
| 60 | `[2] (equal …)` = P | literal 2 = the goal |
| 61 | (blank) | sep |
| 62–65 | `Literal 1 … (not (consp x)) → (not (consp x)) (no rewrites)` | **hypothesis literal**; its negation `(consp x)` is part of literal 2's context. ✔ |
| 66 | (blank) | sep |

### Literal 2 (lines 67–72) — the IH, normalized (NOT driven to `t`)
| 67 | `Literal 2 (notFlg=true):` | the (negated) IH literal |
| 68 | `Input: (not (equal (my-len (my-app (cdr x) y)) (binary-+ (my-len (cdr x)) (my-len y))))` | the IH as supplied |
| 69 | `Result: (not (equal (my-len (my-app (cdr x) y)) (binary-+ (my-len y) (my-len (cdr x)))))` | RHS sum **commuted** |
| 70 | `Proof tree (1 top-level nodes):` | ⚠ misleading label again (1-step chain) |
| 71–72 | node `rewrite:commutativity-of-+  (binary-+ (my-len (cdr x)) (my-len y)) => (binary-+ (my-len y) (my-len (cdr x)))` | commute the IH's sum |
**Justification:** this is an *equivalence-preserving* rewrite of the assumed IH
into the exact shape literal 3 needs (the `rewriting-equivalence` at line 110–112
matches this commuted form). It contributes to the theorem **indirectly**: it
conditions the IH that the goal literal consumes. ✔ (Not a step toward a literal=`t`;
it prepares an assumption — which is legitimate and necessary here.)
| 73 | (blank) | sep |

### Literal 3 (lines 74–114) — the goal P, driven to `t` under (consp x) ∧ IH
| 74 | `Literal 3 (notFlg=false):` | the goal literal |
| 75 | `Input: (equal (my-len (my-app x y)) (binary-+ (my-len x) (my-len y)))` | `[[ G₀ = P ]]` |
| 76 | `Result: (quote t)` | claim |
| 77 | `Proof tree (5 top-level nodes):` | ⚠ misleading label (5-step chain) |

**Node 1 (78–84) — `definition:my-app`,  `(my-app x y) ⇒ (cons (car x) (my-app (cdr x) y))`**
| 78 | node | unfold my-app |
| 79 | `(my-app x y) => (cons (car x) (my-app (cdr x) y))` | net effect |
| 80 | `subst: y → (. y), x → (. x)` | formals ↦ vars |
| 81–82 | child `recognizer/true  (consp x) => (quote t)` | under (consp x) |
| 83–84 | child `if-simplification  (if (quote t) (cons …) y) => (cons …)` | then-branch |
`[[ G₁ = (equal (my-len (cons (car x) (my-app (cdr x) y))) (binary-+ (my-len x) (my-len y))) ]]` ✔

**Node 2 (85–95) — `definition:my-len [recursive]`,  `(my-len (cons …)) ⇒ (binary-+ (quote 1) (my-len (my-app (cdr x) y)))`**
| 85 | node `[fncall/recursive]` | unfold the recursive my-len call |
| 86 | `(my-len (cons (car x) (my-app (cdr x) y))) => (binary-+ (quote 1) (my-len (my-app (cdr x) y)))` | net effect (correct) |
| 87 | `subst: x → (cons (car x) (my-app (cdr x) y))` | my-len's formal x ↦ the arg |
| 88–89 | child `recognizer/true  (consp (cons …)) => (quote t)` | cons is a consp |
| 90 | `runes: fake-rune-for-type-set:NIL, definition:my-app` | dependencies |
| 91–92 | child `if-simplification  (if (quote t) (binary-+ (quote 1) (my-len (cdr x))) (quote 0)) => (binary-+ (quote 1) (my-len (cdr x)))` | ⚠ **DISCREPANCY** — see §D.1: the `x` shown here is my-len's *formal* (bound at line 87 to `(cons (car x) (my-app (cdr x) y))`), displayed as the theorem's `x`. It should read `(my-len (cdr (cons (car x) (my-app (cdr x) y))))`. |
| 93–95 | child `rewrite:cdr-cons  (cdr (cons (car x) (my-app (cdr x) y))) => (my-app (cdr x) y)` | this child correctly uses the *substituted* arg — **inconsistent with line 92**, which it must operate on. |
Net effect (line 86) is correct: `[[ G₂ = (equal (binary-+ (quote 1) (my-len (my-app (cdr x) y))) (binary-+ (my-len x) (my-len y))) ]]` ✔

**Node 3 (96–103) — `definition:my-len`,  `(my-len x) ⇒ (binary-+ (quote 1) (my-len (cdr x)))`**  (this is the `(my-len x)` in the RHS)
| 96 | node | unfold |
| 97 | `(my-len x) => (binary-+ (quote 1) (my-len (cdr x)))` | net effect (here `x` *is* the theorem var — correct) |
| 98 | `subst: x → (. x)` | formal x ↦ var x (identity) |
| 99–100 | child `recognizer/true  (consp x) => (quote t)` | under (consp x) |
| 101 | `runes: definition:my-len, rewrite:cdr-cons, …` | dependencies |
| 102–103 | child `if-simplification … => (binary-+ (quote 1) (my-len (cdr x)))` | then-branch |
`[[ G₃ = (equal (binary-+ (quote 1) (my-len (my-app (cdr x) y))) (binary-+ (binary-+ (quote 1) (my-len (cdr x))) (my-len y))) ]]` ✔

**Node 4 (104–112) — `rewrite:commutativity-of-+` + nested `commutativity-2-of-+` + the IH**
| 104 | node `rewrite:commutativity-of-+ [with-lemma]` | rearrange the RHS sum |
| 105 | `(binary-+ (binary-+ (quote 1) (my-len (cdr x))) (my-len y)) => (binary-+ (quote 1) (my-len (my-app (cdr x) y)))` | net effect of this subtree |
| 106 | `runes: rewrite:commutativity-2-of-+, definition:my-len, …` | dependencies |
| 107 | child `rewrite:commutativity-2-of-+ [with-lemma]` | `(+ a (+ b c)) = (+ b (+ a c))` |
| 108 | `(binary-+ (my-len y) (binary-+ (quote 1) (my-len (cdr x)))) => (binary-+ (quote 1) (my-len (my-app (cdr x) y)))` | net effect of this child (post-IH) |
| 109 | `runes: definition:my-len, …` | dependencies |
| 110 | grandchild `rewriting-equivalence:NIL [solidify/rewriting-equiv]` | **applies the IH** |
| 111 | `(binary-+ (my-len y) (my-len (cdr x))) => (my-len (my-app (cdr x) y))` | the IH used right-to-left |
| 112 | `equiv: (equal (binary-+ (my-len y) (my-len (cdr x))) (my-len (my-app (cdr x) y)))` | = the commuted IH from literal 2 (lines 69/72) |
Arithmetic: `(+ (+ 1 (my-len(cdr x))) (my-len y))` —[comm-of-+]→ `(+ (my-len y) (+ 1 (my-len(cdr x))))` —[comm-2-of-+]→ `(+ 1 (+ (my-len y) (my-len(cdr x))))` —[IH]→ `(+ 1 (my-len (my-app (cdr x) y)))`.
`[[ G₄ = (equal (binary-+ (quote 1) (my-len (my-app (cdr x) y))) (binary-+ (quote 1) (my-len (my-app (cdr x) y)))) ]]` ✔

**Node 5 (113–114) — `equal-self`,  `⇒ (quote t)`**
| 113–114 | `equal-self  (equal (binary-+ (quote 1) …) (binary-+ (quote 1) …)) => (quote t)` | reflexivity. `[[ G₅ = (quote t) ]]` |
**Step discharged:** under (consp x) ∧ IH, P ⇒ `t`, so Case 1 holds. ✔
| 115 | (blank/EOF) | — |

---

## D. Does the reconstructed tree make sense as a proof?

**Yes — it is a valid structural-induction proof of P**, and every line above maps
to a step that contributes (base/step discharge, hypothesis literals as disjuncts,
the IH normalization that feeds the step). No step fails to justify the theorem.

**One real defect (D.1):** line 92 (node 2's `if-simplification`) shows
`(my-len (cdr x))` where `x` is my-len's *formal* — bound at line 87 to
`(cons (car x) (my-app (cdr x) y))` — but it is rendered as the theorem's `x`,
**colliding** with the theorem variable of the same name. The sibling `cdr-cons`
(line 94) uses the correctly-substituted arg, so lines 92 and 94 are mutually
inconsistent (cdr-cons must operate on the term line 92 produced). The node's *net*
effect (line 86) is correct, so this is (at least) a display/substitution bug in the
child step; it must be checked whether the underlying `ProofNode` data carries the
wrong (unsubstituted) `lhs`/`rhs` for that child, because a replay driver consuming
that child term verbatim would be misled by the `x`-capture. **This is exactly the
class of "misleading input" to fix before driving replay off these terms.**

> ✅ **D.1 RESOLVED at the ACL2 source (2026-06-06).** Root cause: ACL2 logged the
> `if-simplification` branches at the *formal* level. `rewrite.lisp`'s
> `rewrite-if/constant-test` step now applies the rewrite alist (`sublis-var`)
> before logging, so branches are emitted instantiated. The regenerated log shows
> `(my-len (cdr (cons (car x) (my-app (cdr x) y))))` — consistent with the sibling
> `cdr-cons`; the `fix` sub-tree is likewise corrected; identity-subst (base-case)
> steps are unchanged. Logging-only — does not affect ACL2's proving.

---

## E. Proposed improvements to the reconstruction output (as a proof log)

1. **Stop calling a literal's chain "Proof tree (N top-level nodes)."** This is the
   single most misleading label — it presents a leaf-level rewrite chain as *the*
   proof tree and its steps as *top-level*, hiding that the theorem's real top is the
   induction. Rename to e.g. `rewrite chain (N steps)`.
2. **Render the induction as an explicit structural parent**, with the two subgoals
   visibly nested *under* it (indentation), so `theorem → induction → {*1/2, *1/1}`
   is unmistakable rather than a flat header + sibling sections.
3. **Tag each subgoal BASE/STEP and print its case-context assumptions** (e.g.
   `*1/2 [base]: assume ¬(consp x)`, `*1/1 [step]: assume (consp x), and IH P(cdr x)`).
   Today the reader must *infer* the context from `recognizer/false` vs `/true`.
4. **Distinguish hypothesis literals from the goal literal** (e.g. label the
   `(no rewrites)` clause guards as `hypothesis`, and the rewritten one as
   `conclusion ⇒ t`), so their different roles are explicit.
5. **Apply formal→arg substitution consistently in displayed child terms, and
   disambiguate variable capture** (fix D.1). Either substitute the arg into child
   terms, or rename formals on display (e.g. `x✦`), so `(my-len (cdr x))` can't be
   confused with the theorem's `x`.
6. **Show the running whole-literal term after each step** (the `[[ Fᵢ ]]` trace in
   this note). Each node currently shows only its local `lhs => rhs`; surfacing the
   whole-literal state makes "each step advances toward `t`" checkable at a glance —
   and is exactly what a replay driver must thread.
7. **Mark the `rewriting-equivalence` node as "applies IH" and cross-reference the
   literal-2 step** that established the commuted IH — the IH application is the crux
   of the step case and is currently easy to miss.
8. **Demote the `runes:` dependency lines** (they are bookkeeping, not proof steps)
   to a less prominent position, or annotate them as "depends on", so they don't read
   like additional reasoning.
