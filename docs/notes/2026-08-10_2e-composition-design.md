# 2e — consuming expansion DETAIL chains (design for ruling)

For: Mike (per the 2026-08-10 sequencing agreement: rule before the
build; the endgame charter's mandatory-exit trigger enforces it).

## The wall

`runCheckedExpand` composes recorded clausify expansions as dpLiftF
VALUE EQUALITIES: each expansion's from→to is a registry identity and
the walk's kernel fact chains them. An expansion carrying recorded
DETAIL steps (expand-and-or's internal abbreviation pass) hard-fails,
because its from→to is registry-identity ∘ detail-steps — and a
detail step can be `:EQUIV IFF` (`(IF x 'T 'NIL) ⇒ x`), which is NOT
a value equality (the values differ for non-boolean x). Witness:
ORDEREDP-WHEN-BNEXT-CONSTANT *1/4.2''s
`(EQUAL (CONS X1 X4) (CONS X3 X4)) → (EQUAL X1 X3)` via
[CONS-EQUAL registry step; EQUAL-SELF on the cdrs; IF-IFF collapse].

## The design: nil-equivalence at recorded BOOL-tolerant positions

1. **A second composition relation.** `nilEquiv : Option SExpr →
   Option SExpr → Prop` — `some a ≈ some b ↔ (a = nil ↔ b = nil)` —
   with the embedding `nilEquiv_of_eq`. Value equality stays the
   default everywhere it holds today.
2. **Detail chains compose stepwise, validated like the preprocess
   chain core**: the registry identity (equality, embedded), then
   each recorded detail step by its own recipe — equal-self is an
   equality; the IF-IFF collapse is `nilEquiv` by a kernel lemma
   (`cond (toBool x) t nil ≈ x`). An unrecognized detail-step class
   hard-fails.
3. **The relation choice is READ OFF the record, not inferred**: the
   expansion records carry `:BOOL` and the position (`e.pos`), and
   the IFF detail step carries `:EQUIV IFF` — upstream runs this pass
   under `*geneqv-iff*`, so the emitted IFF marker IS the license.
   An IFF step at a position whose recorded class is not
   boolean-tolerant hard-fails.
4. **The walk-level lemma generalizes**: the expandTerm congruence
   fact is re-proved with `nilEquiv` preserved at the tolerated
   positions (the clausify if-spine positions preserve it by
   construction — truth-only evaluation); positions that demand
   equality keep it. This is the substantive kernel work: one
   relation + ~4 lemmas + the generalized walk lemma.

## Soundness argument

Clausify consumes the expanded term only for TRUTH (the disjunction/
if-test positions — upstream's own `*geneqv-iff*` discipline), so
nil-equivalence is exactly the fidelity-faithful relation there: it
is what ACL2 itself maintains at those positions, witnessed per-step
by the emitted `:EQUIV IFF`. No statement weakens — the clause-level
obligations are EvTrue facts, invariant under nil-equivalence of the
lifted term.

## Scope guard (drift watch)

Equality is not globally weakened: `nilEquiv` enters ONLY through a
detail chain carrying a recorded IFF step at a recorded
boolean-tolerant position. No new search; every step is a recorded
node consumed by an existing-recipe class.

Ruling asked: approve this shape (build in the endgame arc, landing
ORDEREDP-WHEN-BNEXT-CONSTANT), amend, or defer 2e past the arc.

## RULED (Mike, 2026-08-10): APPROVED as designed.
