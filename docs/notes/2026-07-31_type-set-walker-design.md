# The bounded value-level type-set walker (epicycle consolidation design)

Mandated by the sorting-completion-2 amended criteria (MDD 2026-07-31):
"the type-set closure kits consolidated into a bounded value-level
type-set walker, whole-clause dedup, CAR/CDR-symmetric silent
refutation."

## The kits today (the near-clones to fold)

1. `deriveNilFact cfg ctx t depth` (NodeCore ~1459): `v(t) = nil` from
   direct falsity facts (lit/seg/false-branch), EQUATION transport (a
   false `(not (equal p q))` pins vp = vq), and the car/cdr-of-non-cons
   completion defaults. Depth-bounded (3), fail-closed.
2. `deriveConspT cfg ctx w` (~1556): `Logic.consp v(w) = t` from a
   syntactic-cons value, `conspEvidence?`, or an IF with both branches
   consp (recursive).
3. `conspEvidence? ctx w vW` (~289): direct `(not (consp w))`-falsity,
   truthy `(consp w)` branch fact, the truthy-(CDR w) route.
4. The TRUTHY scans: the solidify/type-alist truthy arm (a truthy branch
   fact on the term itself, landed with HOW-MANY-QSORT), the
   tautology-absorption arm's source list (Compose ~179-197), the
   recognizer arm at ~1892.
5. The equation closure: `inScopeEquations` / `eqChain?` /
   `composeEqChain` (solidify's clause-context equations, truthy-equal
   edges — BUG-027's subject).

## Target shape

One `typeSetWalk (cfg ctx) (req : TsReq) (depth)` with
`TsReq := | isNil (t) | isTruthy (t) | isConspT (t)` returning the
kernel proof for the request, recursing ONLY through the request forms
above (each rung total and type-checked, shared depth bound, identical
fact channels for every consumer: litFacts + segFacts + branchFacts +
the equation closure). Consumers (`type-alist` nil/truthy arms,
`type-set-equality`'s consp demand, the definition/recognizer arms, the
absorption arm) each become one `typeSetWalk` call. The dedup criterion:
no consumer-local fact-channel scan survives outside the walker.

- WHOLE-CLAUSE DEDUP: the walker sees every in-scope channel once —
  consumer-local re-scans (the absorption arm's hand-built `sources`
  list) fold in.
- CAR/CDR SYMMETRY: `deriveNilFact`'s completion rung derives
  `(car u) = nil` / `(cdr u) = nil` from `(consp u) = nil`; the
  SYMMETRIC silent refutation (the rewrite-equal component protocol's
  car/cdr phases) consumes the same rung rather than its own copy.
- BUG-027 gate: the truthy-equal edges stay behind the closure until the
  ratify-or-narrow decision at the merge review; the walker keeps them
  in ONE place so the decision lands as one diff.

## Non-goals

- No new derivation power: the walker's rungs are exactly the kits'
  existing rungs, moved. Behavior-preserving = sweep byte-identical.
- The swap inventory is NOT part of this consolidation (see the census's
  marker-experiment negative result — it is target-directed
  recompute-and-check, a general rule, retained).
