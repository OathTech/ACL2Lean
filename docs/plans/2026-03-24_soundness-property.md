# The Soundness Property

Created: 2026-03-24

## What ACL2 theorems mean

```lisp
(defthm my-len-my-app
  (equal (my-len (my-app x y))
         (+ (my-len x) (my-len y))))
```

This claims: for all values of x and y, evaluating the formula
produces T. The evaluator `eval` is the ground truth semantics.

## How ACL2 proves theorems

ACL2 proves theorems by symbolic reasoning — applying proof rules
to terms with free variables. No evaluation happens; the variables
have no concrete values. The proof is a tree of rule applications,
where each rule transforms a term or introduces structure
(induction, case split). When every leaf of the tree is trivially
true, the theorem is established.

Our instrumentation emits a trace recording these rule applications.

## Two properties that make this work

### Referential transparency (property of the evaluator)

ACL2's semantics is standard Lisp: every expression evaluates to a
value, function application follows lambda-calculus-style binding,
and there are no side effects. This gives **referential
transparency**: `eval` is compositional. If you replace a
subexpression with one that has the same value, the enclosing
expression has the same value. This is an unconditional property
of the evaluator — it holds always, with no hypotheses.

Formally: for any subexpressions `a`, `b`, and enclosing term `C[·]`,
```
eval(a) = eval(b)  →  eval(C[a]) = eval(C[b])
```

where `C[·]` is any term with a hole at a subexpression position.

This is proved once about `eval` and used at every proof step.

### A note on QUOTE and head symbols

Earlier analysis worried about QUOTE bodies and function head
symbols as "exceptions" to referential transparency. They are not.

**QUOTE** (`'0`, `'T`, etc.) is Lisp syntax for literal values.
The content of a QUOTE is ground data (numbers, symbols, constant
lists) — not a subexpression. There are no free variables or
function calls inside a QUOTE to match against, so the question
of replacing inside one simply doesn't arise. QUOTE is a value
constructor, like a numeric literal in any language.

**Head symbols** (`f` in `(f x y)`) are binding references — names
looked up in the world to retrieve a definition. This is standard
lambda-calculus-style application: look up the function, bind the
formals, evaluate the body. The head symbol is a name, not a
subexpression. A rewrite pattern like `(MY-APP X Y)` is a compound
expression and would never match a bare symbol in head position.

Neither case is an exception to referential transparency. They are
simply not subexpression positions. Referential transparency is
about replacing evaluated subexpressions with equal ones; these
positions contain syntax (literals, names) rather than
subexpressions.

### Contextual equality (property of each proof step)

When ACL2 proves a theorem, it establishes equalities under
conditions. Inside a branch where `x < 7`, the proof shows
`eval(lhs) = eval(rhs)` — but only for environments where
`x < 7` holds. This is **contextual equality**: `lhs = rhs`
holds in proof context Γ.

Formally: for a given proof step in context Γ,
```
∀ env satisfying Γ, eval(lhs) = eval(rhs)
```

### How they combine

Referential transparency is the unconditional glue. Contextual
equality is the conditional fact. Together:

1. The proof establishes `eval(lhs) = eval(rhs)` under Γ.
2. Referential transparency says: therefore `eval(C[lhs]) = eval(C[rhs])`
   under Γ (the replacement preserves the enclosing expression).

The proof context Γ restricts which environments we reason about.
As we descend into branches, Γ gets stronger (more hypotheses,
fewer environments). As we exit, it weakens back. At the root, Γ
is empty, giving the universal theorem.

## What we build

**A checker** (a Lean program) that takes the World (function
definitions, previously proved theorems) and a proof trace, and
either accepts or rejects.

```
replayTrace : World → Trace → Option SExpr
```

The checker is purely syntactic. It does not evaluate terms, it does
not see variable bindings, it runs in bounded time on bounded input.

**A soundness proof** (a Lean theorem) that says: if the checker
accepts, the theorem holds under evaluation.

```
replayTrace_sound :
  replayTrace w T = some result →
    ∀ env, ∃ N, ∀ f ≥ N, eval f w env result = eval f w env formula
```

This is directly analogous to a type-safety proof: the checker is
a type checker, the soundness proof shows well-typed programs don't
go wrong. The checker runs; the proof reasons about the checker.

## The proof tree and hypothesis context

The proof is a single tree. At each node, a rule fires. The proof
context Γ accumulates hypotheses as we descend:

- **Clause assumptions**: when working on literal Lᵢ in a clause
  `L₁ ∨ ... ∨ Lₙ`, we assume `¬Lⱼ` for all j ≠ i.
- **Branch conditions**: entering an IF-true branch adds the test
  as a hypothesis; IF-false adds its negation.
- **Induction hypotheses**: the inductive case has the IH available.
- **Previously proved theorems**: available as rewrite rules.
- **Function definitions**: from the World.

These are all entries in Γ. The rewriter can use any of them to
justify a step. A `:REWRITE` step might reference a built-in axiom,
a user-proved theorem, or the induction hypothesis — same mechanism.

Hypotheses are scoped: entering a branch extends Γ, leaving it
restores the parent's Γ. The tree structure is marked in the trace
by BEGIN/END events.

## The soundness argument

The soundness proof is a simulation. For each node in the proof
tree, we show that the ACL2 proof state lifts to a valid Lean
proof state. The lifting maps ACL2's proof context to Lean
hypotheses about `eval`.

This lifting exists only in the proof — the checker never computes
it. The checker verifies syntactic side conditions (function exists,
axiom recognized). The proof constructs the semantic justification
from those conditions.

The argument has three parts:

**1. Per-rule soundness.** For each proof rule type, a theorem: if
the checker accepts a step of this type, then in the current
context Γ, `eval(lhs) = eval(rhs)` (for sufficient fuel). Proved
once per rule type.

**2. Referential transparency.** `eval(a) = eval(b)` implies
`eval(C[a]) = eval(C[b])` for any enclosing expression C.
Unconditional property of the evaluator — proved once, used at
every step.

**Combining 1 and 2**: per-rule soundness gives a contextual
equality (`eval(lhs) = eval(rhs)` under Γ). Referential
transparency lifts this to the enclosing expression
(`eval(term[lhs]) = eval(term[rhs])` under Γ). The context Γ
passes through unchanged — referential transparency doesn't
add or remove hypotheses.

**3. Simulation invariant.** By induction over the proof tree: the
lifting is preserved at every node. Each step: per-rule soundness
gives `eval(lhs) = eval(rhs)`; referential transparency gives
`eval(term') = eval(term)`. Context management (Γ extension and
restoration) is handled by the tree structure.

## Fuel

`eval` takes a fuel parameter for termination. The soundness
statements use existential fuel: "there exists N such that for all
f ≥ N, the property holds." Fuel monotonicity (once eval converges,
more fuel doesn't change the result) ensures these bounds compose
across steps.

## What the trace must provide

For each rule application, the trace must provide enough information
to reconstruct the Lean proof of that rule. This means:

- **`:DEFINITION fn`**: the function name (to look up the
  definition), the LHS/RHS, and the IF-TEST events (recording
  which branches were taken, justified by hypotheses in Γ).

- **`:REWRITE thm`**: the theorem name (to look up the Lean lemma)
  and the LHS/RHS.

- **Structural events**: BEGIN/END for scope management, induction
  schemes, clause structure.

The current instrumentation is a flat trace with depth filtering.
This is an approximation of the proof tree. A future proof-tree
representation would make the structure explicit and eliminate known
gaps (inner step leakage, branch combination loss).

## Open questions

1. **Formal definition of the lifting**: what exactly maps ACL2
   clause contexts and IF-TEST events to Lean propositions about
   eval?

2. **Fuel monotonicity**: needs to be proved for the evaluator.
   Standard structural induction mirroring eval's definition.

3. **Referential transparency**: needs to be formalized for the
   evaluator. Should follow directly from eval's compositional
   structure — each eval case combines results of sub-evaluations,
   so equal sub-results give equal results.

4. **Trace sufficiency**: does the current instrumentation provide
   enough for each rule type? Known gap: inner steps (e.g., FIX
   elimination) may be elided. Future proof-tree instrumentation
   would fix this.

5. **Induction**: how does the induction scheme from the trace
   translate to a Lean induction principle?

6. **Rule instantiation**: when `:REWRITE` applies a universally
   quantified theorem (e.g., commutativity of +), how is the
   instantiation verified? The trace provides the LHS/RHS but
   not the substitution explicitly.
