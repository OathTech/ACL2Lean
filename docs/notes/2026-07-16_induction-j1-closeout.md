# Induction-generality J1 close-out (2026-07-16)

J1 of the ratified design (`docs/plans/2026-07-15_induction-generality-design.md`
§6b) is COMPLETE. Deliverables and outcomes:

## 1. The two hand-proof spikes (committed)

- **J1(a)** `ACL2Lean/Imported/FlattenSpike.lean` (`2c40584`):
  `true_listp_flatten_mirror` — env-level motive, TWO IHs from the one
  strong IH, single-var μ, substN bridge, full with-lemma pattern.
- **J1(b)** `ACL2Lean/Imported/InterleaveSpike.lean` (`573d07a`):
  `len_interleave_mirror` — SUM-measure μ-registry instance, the variable
  SWAP as a double env update with the sum decrease from the emitted
  clause, the 2-pair SIMULTANEOUS bridge landing by `rfl` on the tree's IH
  literal, the 2-ary pinning transfer, value-level arithmetic for the
  recorded commutativity chain.

Both: real statements over log-derived worlds in the driver's telescope
shapes; sorry-free; axioms exactly `{propext, Classical.choice,
Quot.sound}` (in-file `#print axioms`); body transcriptions
`#guard`-pinned to the parsed artifacts; **zero unannotatable tactic
moves** (T6) — no stop trigger fired in either proof. Neither file is in
the root import graph yet (deliberate; the arc wires them when the driver
lands).

Named-new items J2/J4 must add, enumerated by construction from the
annotations: `measure_strong_induction` (the scaffold lemma, currently
inlined), `trueListp_boolean`, `len_int`, `plus_int`, the swap-sum Count
lemma (currently an inlined `omega`).

## 2. Restated-C2 verification (per target tree)

C2 (as restated after review IN-2): every IH alist's MEASURED-subset
substitution is covered by an emitted `:TERMINATION-CLAUSES` entry under
the induction term's formal→actual substitution. Verified against the raw
logs:

| Tree | measured | IH (measured part) | covering emitted clause | ✓ |
|---|---|---|---|---|
| 10 FLATTEN | X | X:=(CAR X); X:=(CDR X) | car clause AND cdr clause both present | ✓ |
| 12 ZIP2 | X | X:=(CDR X) (Y rides) | `((IF (ATOM X) (ATOM X) (ATOM Y)) (O< (ACL2-COUNT (CDR X)) (ACL2-COUNT X)))` | ✓ |
| 13 INTERLEAVE | Y,X | X:=Y, Y:=(CDR X) (swap) | `((ATOM X) (O< (+ (ac Y) (ac (CDR X))) (+ (ac X) (ac Y))))` | ✓ |
| 16 ZIP3 | X | X:=(CDR X) (Y,Z ride) | same shape as ZIP2 with the 3-way compound test | ✓ |
| 15 NESTED | Z (outer) | Z:=(CDR Z) | LEN's cdr clause (WP0 gz snapshot) — but the induction INPUT awaits J5's revert semantics | ✓ (clause) / deferred (input shape) |

BONUS finding: ZIP2/ZIP3's clauses carry the decrease under the EXACT
compound IF term the induction's ruling tests use — the covering join for
these trees is term-identical, not merely semantically adequate.

## 3. ZIP2/ZIP3 compound-test-INVERSION lemma statements (T4a — written,
## not proved; J3 proves them)

The step-case branch fact is "the value of the emitted ruling test's
NEGATION is truthy", i.e. the compound IF's value is nil. The value walker
composes the test as nested `cond`s; the decrease needs consp of the
measured variable. Statements, read off the real trees:

```lean
-- shared decode: a nil ATOM value IS a cons
theorem consp_of_atom_nil (v : SExpr) (h : Logic.atom v = SExpr.nil) :
    ∃ a b, v = .cons a b

-- ZIP2's test (IF (ATOM X) (ATOM X) (ATOM Y)), value-composed:
theorem cond_atom2_nil_inv (xv yv : SExpr)
    (h : cond (Logic.toBool (Logic.atom xv)) (Logic.atom xv)
          (Logic.atom yv) = SExpr.nil) :
    Logic.atom xv = SExpr.nil ∧ Logic.atom yv = SExpr.nil

-- ZIP3's test (IF (ATOM X) (ATOM X) (IF (ATOM Y) (ATOM Y) (ATOM Z))):
theorem cond_atom3_nil_inv (xv yv zv : SExpr)
    (h : cond (Logic.toBool (Logic.atom xv)) (Logic.atom xv)
          (cond (Logic.toBool (Logic.atom yv)) (Logic.atom yv)
            (Logic.atom zv)) = SExpr.nil) :
    Logic.atom xv = SExpr.nil ∧ Logic.atom yv = SExpr.nil
      ∧ Logic.atom zv = SExpr.nil
```

(The generic J3 shape: invert a nested-`cond` test value to per-component
facts; unavailable inversion ⇒ hard-fail, per I5.)

## 4. Next: J2

The scaffold core lands in the driver — `MeasureImage(Nat)`, the
pool-shaped `measure_strong_induction`, the μ registry, the env-update
layer, the covering join — with BOTH spikes as its executable
specification. Gate: refactor-under-identity per T2 (green induction
rows' golden lines byte-identical; red rows' new frontier messages
predicted in advance), plus a proof-term-size prediction.
