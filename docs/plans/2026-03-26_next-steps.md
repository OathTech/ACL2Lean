# Next Steps: Foundations First

Created: 2026-03-26
Updated: 2026-03-26 — Completed workstream A. Dropped `eval` in favor of `evalOpt`.

## Where we are

The soundness experiment (branch `mdd/soundness-experiment`) explored
a "check-and-replace" architecture: evaluate both sides of a rewrite
step, compare them, apply syntactic replacement, prove this preserves
evaluation. The top-level chain (`replaySteps_sound`) was proved by
induction on the step list, conditional on a congruence lemma
`evalReplace_sound`.

**That congruence lemma is false.** See the analysis below and the
counterexample.

The operational rewriter (Rewriter.lean) works fine — it applies trace
steps and produces correct results (357/371 on sorting corpus). The
issue is purely in the soundness proof layer.

## The evalReplace_sound counterexample

The theorem:
```lean
theorem evalReplace_sound (f : Nat) (w : World) (env : Env)
    (term lhs rhs : SExpr)
    (h_eq : evalOpt f w env lhs = evalOpt f w env rhs) :
    evalOpt f w env (evalReplace term lhs rhs) = evalOpt f w env term
```

is false because of eval's fuel decrement. When `evalOpt` processes a
compound term at fuel `f+1`, it evaluates subexpressions at fuel `f`.
So `lhs` as a standalone term is evaluated at fuel `f`, but `lhs` as a
subterm of `term` is evaluated at fuel `f - k` (where k ≥ 1 is the
nesting depth). The hypothesis gives the equality at the wrong fuel
level.

**Counterexample:** Let `f(x) = x` and `g(x) = x` be identity
functions. Let `env = {x ↦ 42}`, fuel = 2.

- `lhs = (f x)`, `rhs = x`, `term = (g (f x))`
- Hypothesis (fuel 2): `evalOpt 2 (f x) = some 42 = evalOpt 2 x` ✓
- `evalReplace (g (f x)) (f x) x = (g x)`
- `evalOpt 2 (g x)`: fuel'=1, eval `x` at 1 → 42, result `some 42`
- `evalOpt 2 (g (f x))`: fuel'=1, eval `(f x)` at 1: fuel'=0,
  eval `x` at 0 → `none`. Result: `none`
- `some 42 ≠ none` ∎

This affects the original `eval` too (same structure, different
failure value).

## The correct theorem (from soundness-property.md)

The soundness property doc already identified the right form:

```
∀ env, ∃ N, ∀ f ≥ N, eval f w env result = eval f w env formula
```

The existential fuel is essential: pick a fuel level large enough that
everything converges. A correct congruence lemma:

```lean
theorem evalReplace_sound_corrected
    (w : World) (env : Env) (term lhs rhs : SExpr)
    (h_eq : ∃ N, ∀ f ≥ N, evalOpt f w env lhs = evalOpt f w env rhs) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (evalReplace term lhs rhs)
                  = evalOpt f w env term
```

This requires **fuel monotonicity** as infrastructure.

## Plan

Two independent workstreams, then a dependent third.

### Workstream A: Evaluator properties

Goal: establish the basic metatheory of `eval`/`evalOpt`. These
properties are reusable infrastructure regardless of how the proof
replay is structured.

**A1. Fuel monotonicity for evalOpt**

```lean
theorem evalOpt_fuel_mono (f : Nat) (w : World) (env : Env) (t : SExpr) (v : SExpr) :
    evalOpt f w env t = some v → evalOpt (f + 1) w env t = some v
```

Once eval converges, more fuel doesn't change the result. Proof by
structural induction on `f` and case analysis on `t`, mirroring
evalOpt's definition. Standard but tedious — each case of evalOpt
(atoms, IF, LET, function call, builtins) needs its own lemma or
sub-case.

Estimated: 100-200 lines. This is the single most important
infrastructure lemma.

**A2. evalOpt agrees with eval**

```lean
theorem evalOpt_some_eq_eval (fuel : Nat) (w : World) (env : Env)
    (term : SExpr) (v : SExpr) :
    evalOpt fuel w env term = some v → eval fuel w env term = v
```

Already stubbed in EvalOpt.lean:82 with sorry. Same proof structure
as A1 — induction on fuel, case analysis, use the fact that evalOpt
and eval have identical structure.

Estimated: 50-100 lines.

**A3. Convergence composition**

Corollary of A1. If `evalOpt N t = some v`, then for all `f ≥ N`,
`evalOpt f t = some v`. This is the usable form of monotonicity.

```lean
theorem evalOpt_ge_fuel (f N : Nat) (w : World) (env : Env) (t : SExpr) (v : SExpr) :
    evalOpt N w env t = some v → f ≥ N → evalOpt f w env t = some v
```

Estimated: 10-20 lines (iterated application of A1).

**A4. Audit eval/evalOpt structural agreement**

Currently, evalOpt is claimed to be "structurally identical" to eval.
Verify this holds for all cases, especially:
- LET/LET* binding evaluation
- Builtin dispatch (does evalOpt call the same `callBuiltin`?)
- Arity mismatch handling

This is a review task, not a coding task.

### Workstream B: Corrected congruence

Goal: prove the correct version of the replacement-preserves-eval
theorem.

**B1. Corrected evalReplace_sound**

Using the existential-fuel formulation from above. The proof:
1. From `h_eq`, extract N such that lhs and rhs agree at all fuel ≥ N
2. By induction on `term`, show that for large enough fuel (accounting
   for nesting depth), the replacement preserves evalOpt
3. Each inductive case uses fuel monotonicity (A1/A3) to shift from
   the top-level fuel down to the sub-expression fuel

Key sub-cases:
- **Whole-term match** (term = lhs): immediate from h_eq
- **QUOTE**: evalReplace skips inside QUOTE, so trivial
- **Symbol-headed cons** (function call / IF / LET): recurse into
  arguments. Need to show evalOpt of the argument list is preserved.
  Uses A1 to align fuel levels.
- **Non-symbol-headed cons**: needs well-formedness precondition (all
  real ACL2 terms have symbol heads on function calls)

Depends on: A1, A3
Estimated: 100-150 lines

**B2. Corrected replaySteps_sound**

Restate and re-prove the step-chain theorem with existential fuel.
The current proof structure (induction on step list) should carry over
with minimal changes — the key difference is that each step produces
an existential fuel bound, and we take the max.

```lean
theorem replaySteps_sound (w : World) (env : Env)
    (steps : List RewriteStep) (term result : SExpr) (fuel : Nat)
    (h : replaySteps w env steps term fuel = some result) :
    ∃ M, ∀ f ≥ M, evalOpt f w env result = evalOpt f w env term
```

Depends on: B1
Estimated: 30-50 lines (adaptation of existing proof)

**B3. checkStep at sufficient fuel**

The current `checkStep` evaluates at a single fuel level. With
monotonicity, this is fine: if `checkStep` passes at fuel N, then the
equality holds at all fuel ≥ N.

```lean
theorem checkStep_sufficient (w : World) (env : Env)
    (step : RewriteStep) (N : Nat)
    (h : checkStep w env step N = true) :
    ∀ f ≥ N, evalOpt f w env step.lhs = evalOpt f w env step.rhs
```

Depends on: A1
Estimated: 10-20 lines

### Workstream C: Proof tree replay (future)

This is the larger refactor. NOT part of the immediate plan, but
worth scoping now so that A and B are designed to support it.

The flat trace (a list of RewriteStep) has two independent problems:
1. **4% failure rate** on the sorting corpus (14/371 cases) due to
   information loss when serializing the tree to a sequence
2. **Soundness architecture** — the correct proof is a tree with
   scoped hypothesis contexts, not a fold over a flat list

The soundness-property doc (2026-03-24) describes the right
architecture:
- Per-rule soundness (one theorem per rule type)
- Referential transparency (the congruence from B1)
- Simulation invariant (induction over the proof tree)

What this requires on the ACL2 side:
- Explicit sub-proof boundaries in the trace (BEGIN-SUBPROOF /
  END-SUBPROOF)
- Scope information (which hypotheses are active)
- Assumption bindings (variable substitutions in effect)

What this requires on the Lean side:
- A tree-shaped proof trace type (replacing the flat List RewriteStep)
- A tree-walking replay function (replacing the fold)
- Per-rule soundness theorems
- Context/hypothesis management

The work in A and B directly supports C:
- Fuel monotonicity (A1) is needed for composing fuel bounds across
  tree nodes
- The corrected congruence (B1) is the "referential transparency"
  component
- evalOpt agreement (A2) bridges back to the user-facing eval

## What was done (2026-03-26)

### Workstream A: completed

**A1. Fuel monotonicity** — proved. The key insight: factor `evalOpt`
into `evalOptStep` (non-recursive body) + `evalOpt` (fuel-bounded
recursion). Then `evalOptStep_mono` is a one-shot proof about a
non-recursive function, and `evalOpt_fuel_mono` is a 5-line corollary.

**A2. evalOpt_some_eq_eval** — dropped. We decided to standardize on
`evalOpt` as the sole evaluator. `eval` (plain SExpr return) was
deleted. The bridge lemma is no longer needed.

**A3. evalOpt_ge_fuel** — proved. 3-line proof using `Nat.le` induction.

### Consolidation: eval → evalOpt

`eval` and `Evaluator.eval` were both deleted. `evalOpt` is now the
canonical ACL2 evaluator. Rationale: `evalOpt` distinguishes fuel
exhaustion (`none`) from legitimate nil (`some .nil`), which is
essential for soundness proofs. Having two evaluators created a bridge
obligation with no payoff.

Files removed:
- `ACL2Lean/Eval.lean` — replaced by `EvalOpt.lean`
- `ACL2Lean/Evaluator.lean` — legacy partial evaluator
- `Tests/EvaluatorTest.lean` — tests for old evaluator

`bindArgs` and `callBuiltin` (pure utilities) were moved into
`EvalOpt.lean`. All downstream code (`Rewriter.lean`, `WorldGen.lean`,
`SimpleWorld.lean`, `Main.lean`) updated to use `evalOpt`.

### Current sorry inventory

| File | Sorry | Status |
|------|-------|--------|
| `EvalOpt.lean` | (none) | Clean |
| `RewriterSoundness.lean` | `evalReplace_sound` | Known false; left for proof-tree refactor |
| `SimpleWorld.lean` | `my_len_my_app` | Generated stub |
| `WorldGen.lean` | Template generates sorry | By design |
| `DSL.lean` | Test/example code | Not proof-relevant |

### What's next

Workstream C: proof checker + soundness.

## What was done (2026-03-27)

### Workstream C steps 1-2, 4-5: completed

**Proof tree types and parser** — `ProofTree.lean` defines recursive
`ProofNode` tree with `StepProvenance` (origin, runes, parents, subst,
equivTerm). Parser uses `BEGIN/END-INNER-REWRITE` markers to build
tree from flat trace. `dump-proof-tree` CLI command for inspection.

**ACL2 structured trace** — complete instrumentation:
- 44 logging points with unique `:ORIGIN` tags and `TRACE-LOG[id]`
  comments across `rewrite.lisp` (31) and `simplify.lisp` (13)
- `BEGIN/END-INNER-REWRITE` markers scope definition body/RHS rewriting
- `BEGIN/END-IF-REWRITE` markers scope unknown-case IF branch processing
- Transaction rollback for abandoned definition expansions
- All depth-zero suppression removed; events emit at all depths
- `:RUNES` (type-prescription provenance) on type-alist/recognizer/
  lemma steps
- `:SUBST` (formal→actual mapping) on definition expansion steps
- `:EQUIV-TERM` on rewriting-equivalence steps
- `:FORMULA` and `:SOURCE` on DEFTHM events (imported vs local)
- Hyphenated keywords renamed to prevent printer line-wrapping

**Corpus validation** — 648 theorems across 10 sorting corpus books,
0 parse errors. Proof tree audit on simple.lisp confirms correct
structure with full provenance.

### Files deprecated by the new architecture

The old flat rewriter and its soundness proof are superseded:
- `Rewriter.lean` — `replaceFirst`/`evalReplace`/`applyRewriteSteps`
  replaced by proof tree checker (the checker verifies steps, not
  computes them)
- `RewriterSoundness.lean` — `evalReplace_sound` (known false) and
  `replaySteps_sound` replaced by soundness theorem over the checker

These should be deleted when the checker is working.

## Workstream C step 3: Proof checker

### Architecture

The checker replaces the old rewriter. Instead of:
```
trace → flat steps → replaceFirst fold → result term
```
the new pipeline is:
```
trace → ProofNode tree → checker verifies each node → accept/reject
```

The checker doesn't transform terms. The proof tree already contains
the LHS/RHS of every step. The checker verifies that each step is
VALID — that the claimed equality holds under the proof context.

### What the checker verifies per node type

For each `ProofNode` with `rune`, `lhs`, `rhs`, `children`, and
`provenance`:

**definition expansion** (rune = `(:DEFINITION fn)`):
1. Look up `fn` in World → formals, body
2. `provenance.subst` gives the formal→actual mapping
3. Verify: applying the substitution to the body and following the
   branch decisions (from children) yields the RHS
4. Children are sub-proof nodes that justify the body simplification

**rewrite rule** (rune = `(:REWRITE name)`):
1. Look up `name` in the World's proved theorems (or axiom library)
2. Extract the rule's formula (e.g., `(EQUAL (+ 0 X) (FIX X))`)
3. Match the rule's LHS pattern against the step's LHS → substitution σ
4. Verify: σ applied to the rule's RHS gives (the start of) the step's
   RHS. Children may further simplify the RHS.

**recognizer / anonymous rule** (rune = `(:FAKE-RUNE-FOR-...)`):
1. If `provenance.runes` has type-prescription runes: verify the
   type-prescription is in the World and the conclusion follows
2. If `provenance.runes` is empty: this is a clause assumption.
   Verify: the negation of the step's conclusion matches a clause
   literal (the literal being assumed false).

**equal-self** (rune = `(:EQUAL-SELF)`):
1. Verify: LHS is `(EQUAL x x)` and RHS is `T`

**if-simplification** (rune = `(:IF-SIMPLIFICATION)`):
1. Verify: LHS is `(IF test then else)` where test is a constant
   (`'T` or `'NIL`), and RHS is the appropriate branch

**executable-counterpart** (rune = `(:EXECUTABLE-COUNTERPART fn)`):
1. Verify: LHS is a ground term (no variables), evaluate it via
   `evalOpt` with sufficient fuel, check result matches RHS

**rewriting-equivalence** (rune = `(:REWRITING-EQUIVALENCE)`):
1. `provenance.equivTerm` gives the equality formula
2. Verify: the equiv-term matches a negated clause literal (the IH
   or a branch assumption)

**clause-context-resolution** (rune = `(:CLAUSE-CONTEXT-RESOLUTION)`):
1. The literal was resolved by the clause context. Verify: the
   result follows from the other clause literals.

### What the checker needs beyond the proof tree

**A World with:**
- Function definitions (already in `World.defs`)
- Proved theorem formulas (from DEFTHM events with `:SOURCE :LOCAL`)
- Imported theorem formulas (from DEFTHM events with `:SOURCE :INCLUDE-BOOK`)
- Built-in axiom formulas (CAR-CONS, CDR-CONS, UNICITY-OF-0, etc.)

Many built-in axioms already exist in `Logic.lean` as simp lemmas.
We need to register them as rewrite rule formulas in the World.

**Pattern matching:**
First-order matching of a rule's LHS pattern against a step's LHS
to extract the substitution σ. This is decidable and straightforward
for SExpr terms.

### Implementation plan

**Step 3a: ProofChecker.lean — checker function**

New file. Takes `World` + `TheoremProof` → `Bool`.
Walk the proof tree, verify each node by the rules above.
Start with just simple.lisp: definition expansion, rewrite rules,
equal-self, if-simplification, executable-counterpart.

Test: `checkTheoremProof simpleWorld simpleProof = true`

**Step 3b: Axiom library**

Register built-in ACL2 axioms as theorem formulas accessible to the
checker. Start with the ones used in simple.lisp:
- UNICITY-OF-0: `(EQUAL (+ 0 X) (FIX X))`
- CDR-CONS: `(EQUAL (CDR (CONS X Y)) Y)`
- COMMUTATIVITY-OF-+: `(EQUAL (+ X Y) (+ Y X))`
- COMMUTATIVITY-2-OF-+: `(EQUAL (+ X (+ Y Z)) (+ Y (+ X Z)))`

**Step 3c: Pattern matching**

First-order matching for rewrite rule application:
`match? (pattern : SExpr) (term : SExpr) : Option (List (Symbol × SExpr))`
Returns the substitution if the pattern matches.

**Step 3d: End-to-end test on simple.lisp**

Parse simple.proof-log → build TheoremProof → check with World →
should return true for all cases.

### After the checker: proof-producing replay (steps 6-8)

The direct approach: write a function (or tactic) that walks the
proof tree and **constructs Lean proof terms** for each node. The
Lean kernel checks each constructed proof. No separate soundness
theorem is needed — if the proof type-checks, it's correct.

This is strictly better than the checker+soundness approach:
- No need to state or prove a soundness theorem
- A bug in the replay produces a type error, not a false theorem
- The Lean kernel IS the soundness checker
- Less code, smaller trusted base

```lean
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f simpleWorld env formula = some SExpr.t := by
  acl2_replay "acl2_samples/simple.proof-log"
```

The `acl2_replay` tactic:
1. Parses the proof log at elaboration time
2. Builds the `TheoremProof` value
3. Walks the tree, constructing proof terms for each node:
   - Definition expansion → unfold evalOpt, follow IF branches
   - Rewrite rule → instantiate the proved theorem, apply
   - Equal-self → `rfl`
   - Recognizer/clause assumption → derive from clause context
   - etc.
4. Composes per-node proofs into the full theorem proof
5. The Lean kernel checks the result

The per-node proof constructions use `evalOpt_fuel_mono` and
`evalOpt_ge_fuel` to compose fuel bounds across the tree.

The Bool checker (step 3) is still useful as a **debugging tool** —
it validates the proof tree has enough information before we invest
in constructing proof terms. But it's not load-bearing for
soundness.

The trajectory:
1. Bool checker — validates completeness, catches design bugs
2. Per-node proof construction — for each node type, build the
   Lean proof term
3. Tactic — `acl2_replay` composes everything

### Open questions (carried forward)

1. **Induction**: The trace gives the scheme (case clauses). How do
   we construct a Lean induction principle from this? Likely via
   `acl2Count` well-founded recursion.

2. **Clause-to-disjunction**: How do we formally state that a clause
   `{L₁, ..., Lₙ}` is valid iff for all env, at least one Lᵢ is
   non-NIL? This is the bridge between clause-level reasoning and
   the evaluator.

3. **Book dependencies**: Theorems from included books are axioms in
   the current book's proof. Processing books in dependency order
   (perm → isort → etc.) ensures each theorem is either proved or
   imported.

## Workstream C historical design notes (superseded)

Updated: 2026-03-26

### Why the flat model fails (recap)

The current rewriter applies a flat list of `RewriteStep` values via
`replaceFirst` in a fold. This serialization loses three kinds of
information:

1. **Scope**: Branch assumptions (e.g., `X1 = A`) are scoped to a
   branch. Steps that use these assumptions only make sense inside
   that scope. The flat model can't express this.

2. **Nesting**: Definition expansion creates a sub-proof. Steps inside
   the expansion reference subterms that exist only in the expanded
   body, not in the literal. The flat model leaks these into the
   literal-level step list.

3. **Combination**: When both IF branches are processed (UNKNOWN
   case), the combined result is a new term that the flat model can't
   compose from the branch results.

All 14/371 (4%) failures are caused by these. The tree model fixes
all three by making the nesting explicit.

### ACL2's proof structure (what the tree represents)

ACL2's simplifier processes a theorem through these levels:

```
Theorem
  └── Induction (optional)
      └── Case₁ (clause: disjunction of literals)
      │   └── Literal₁: no rewrites needed (passes through)
      │   └── Literal₂: rewrite chain → T
      │       ├── Step: defn-expand MY-APP → body
      │       │   └── IF branch decision: (CONSP X) false
      │       ├── Step: defn-expand MY-LEN → '0
      │       │   └── IF branch decision: (CONSP X) false
      │       ├── Step: rewrite UNICITY-OF-0
      │       └── Result: (EQUAL (MY-LEN Y) (MY-LEN Y)) = T
      └── Case₂ (with IH)
          └── ...
```

Key structural observation: the trace we already emit contains
almost all of this. The current events — BEGIN/END-LITERAL,
BEGIN/END-BRANCH, CASE-SPLIT, IF-TEST-TRUE/FALSE/UNKNOWN,
REWRITE-STEP, REWRITTEN-LITERAL — form the SKELETON of this tree.
What's missing is sub-proof boundaries inside the rewriter.

### What the trace currently provides vs. what we need

**Already emitted:**
- Clause structure: `:INPUT-CLAUSE` gives the literal list
- Literal boundaries: `BEGIN-LITERAL`/`END-LITERAL`
- Branch structure: `BEGIN-BRANCH`/`END-BRANCH`, `CASE-SPLIT`
- IF decisions: `IF-TEST-TRUE/FALSE/UNKNOWN` with test and justification
- Rewrite steps: `REWRITE-STEP` with rune, LHS, RHS
- Literal results: `REWRITTEN-LITERAL` with original and result
- Induction: `:INDUCTION` with scheme and subgoal count
- Branch substitutions: `BRANCH-SUBSTITUTION`, `CONTEXT-SUBST`

**Not emitted (causes the 4% failures):**
- Sub-proof boundaries for definition expansion (where the body
  rewriting begins and ends)
- IF branch rewriting boundaries (when UNKNOWN, both branches are
  rewritten; the sub-proofs for each branch are invisible)
- Steps inside definition expansions (suppressed by depth counter)

### Proposed representation: two levels

Rather than emitting the full rewriter recursion tree (which would
be enormous and fragile), we propose a two-level design:

**Outer level (already exists, minor changes):**
```
Theorem → Induction → [Case]
Case → Clause → [LiteralProof]
LiteralProof → Literal → [JustifiedStep] → Result
```

This maps directly to the existing trace structure. No ACL2 changes
needed for this level.

**Inner level (the new part):**

Each `JustifiedStep` is a rewrite step enriched with its
justification. The current flat `RewriteStep` (rune + LHS + RHS)
becomes:

```lean
structure JustifiedStep where
  rune : String × String
  lhs : SExpr
  rhs : SExpr
  branchDecisions : List BranchDecision  -- IF decisions inside this step

inductive BranchDecision where
  | true (test : SExpr) (justification : BranchJustification)
  | false (test : SExpr) (justification : BranchJustification)

inductive BranchJustification where
  | clauseAssumption   -- test's truth follows from a negated literal
  | typeSet            -- test's truth follows from type reasoning
  | rewrittenConstant  -- test rewrote to 'T or 'NIL
  | hypothesis         -- test matches an assumption from a branch
```

The key insight: **the IF-TEST events that currently precede each
REWRITE-STEP in the flat trace ARE the branch decisions**. They're
already emitted in the right order. We just need to associate them
with their step instead of treating them as independent events.

This association can be done entirely in the Lean parser — no ACL2
changes for 96% of cases.

### Handling the 4% failures

The three failure types need different solutions:

**Scope loss (bsort, 1 case):** An equivalence from
`find-rewriting-equivalence` fires inside a definition expansion.
The depth counter suppresses it.

Fix: Remove the depth counter for `find-rewriting-equivalence`
logging. These events are lightweight (just variable substitutions)
and carry their own justification. Emit them at all depths, and let
the Lean parser associate them with the enclosing step.

**Inner step leakage (qsort, 6 cases):** Steps reference subterms
from inside a definition expansion.

Fix: Add `BEGIN-EXPANSION`/`END-EXPANSION` markers around definition
body rewriting in `rewrite-fncall`. Steps inside the expansion are
grouped into the expansion node. The Lean parser builds a sub-tree
for the expansion; only the outermost LHS/RHS are visible at the
literal level.

**Branch combination loss (qsort, 7 cases):** Both IF branches are
rewritten but the combined result requires further simplification.

Fix: Add `BEGIN-IF-BRANCH`/`END-IF-BRANCH` markers around the
TRUE/FALSE branch rewriting in `rewrite-if-finish` (the UNKNOWN
case). The combined result is already logged. The Lean parser builds
a sub-tree for the IF processing.

### ACL2 changes (acl2/ submodule)

Three targeted changes in `rewrite.lisp`:

1. **`rewrite-fncall`** (~line 19766): Add `BEGIN-EXPANSION`/
   `END-EXPANSION` markers around the definition body rewriting.
   Remove the depth increment (or keep it but don't use it to
   suppress logging).

2. **`rewrite-if-finish`** (~line 17277): Add `BEGIN-IF-BRANCH`/
   `END-IF-BRANCH` markers around the UNKNOWN-case branch rewriting.
   The existing `IF-TEST-UNKNOWN` + combined-result logging stays.

3. **`rewrite-solidify-rec`** (~line 4750): Remove the depth check
   for `find-rewriting-equivalence` logging so it emits at all
   depths.

Estimated: ~30 lines of changes across 3 functions. All existing
logging stays; we're adding boundary markers and removing
suppressions.

### Lean types

```lean
/-- A proof of a single theorem. -/
structure TheoremProof where
  name : String
  formula : SExpr
  induction : Option InductionScheme
  cases : List CaseProof

/-- Proof of one induction case (or the single case if no induction). -/
structure CaseProof where
  clauseId : String
  clause : List SExpr        -- input clause (disjunction)
  targetLiteral : Nat        -- which literal simplifies to T
  literalProof : LiteralProof

/-- Proof that a literal simplifies to T under clause assumptions. -/
structure LiteralProof where
  literal : SExpr
  steps : List JustifiedStep
  result : SExpr              -- should be 'T or (EQUAL X X)
```

### Lean proof checker

```lean
/-- Check a theorem proof. Returns true if all steps are valid. -/
def checkTheoremProof (w : World) (proof : TheoremProof) : Bool

/-- Check a single justified step against the world. -/
def checkStep (w : World) (step : JustifiedStep)
    (clauseAssumptions : List SExpr) : Bool
```

The checker verifies:
- For `defn-expand`: function exists in world, branch decisions are
  consistent with unfolding the body under clause assumptions
- For `rewrite`: rule exists (in world's proved theorems or as an
  axiom), LHS matches the rule's LHS pattern
- For `type-set`: the type reasoning is valid
- For `equal-self`, `if-simplify`, `exec-counterpart`: trivially
  checkable

### Lean soundness theorem

```lean
theorem checkTheoremProof_sound (w : World) (proof : TheoremProof) :
    checkTheoremProof w proof = true →
    ∀ env, ∃ N, ∀ f ≥ N,
      evalOpt f w env proof.formula = some SExpr.t
```

Proved by structural induction on the proof:
1. **Induction**: from the scheme, derive a Lean induction principle
   on SExpr (using acl2Count). Apply it to decompose into cases.
2. **Per case**: the clause is `{L₁, ..., Lₙ}`. Assume `¬Lⱼ` for
   j ≠ targetLiteral. Show the target literal evaluates to T.
3. **Per step**: per-rule soundness. Each rule type gets its own
   lemma (proved once):
   - `defnExpand_sound`: unfolding + branch decisions preserve eval
   - `rewriteRule_sound`: rule application preserves eval
   - `typeSetResolve_sound`: type reasoning preserves eval
4. **Composition**: chain steps using evalReplace + fuel monotonicity
   (from workstream A).

### Per-rule soundness lemmas needed

**`defnExpand_sound`**: If `f` is defined with body `b` and formals
`xs`, and the branch decisions are consistent with evaluating `b`
under the clause assumptions, then
`evalOpt f w env (f args) = evalOpt f w env result`.

This is the most complex per-rule lemma. It requires:
- Unfolding evalOpt for function calls
- Following IF branches according to the branch decisions
- Using clause assumptions to justify the branch choices
- Composing fuel bounds

**`rewriteRule_sound`**: If theorem `thm` is proved (in the world or
as an axiom), and LHS matches `thm`'s LHS under substitution σ,
then `evalOpt f w env LHS = evalOpt f w env RHS`.

This requires:
- Pattern matching to extract σ
- Instantiating the theorem with σ
- Showing the instantiation is correct

**`equalSelf_sound`**: `(EQUAL X X)` evaluates to T. Trivial.

**`ifSimplify_sound`**: IF with constant test simplifies. Trivial
from evalOpt's IF case.

**`execCounterpart_sound`**: Ground function application evaluates
to a known result. Follows from evalOpt + callBuiltin.

### Implementation order

1. **Lean types**: Define `TheoremProof`, `CaseProof`,
   `LiteralProof`, `JustifiedStep`, `BranchDecision` types.
   No dependencies.

2. **Lean parser**: Parse the current trace format into the new
   types. The parser associates IF-TEST events with REWRITE-STEPs.
   Test on simple.lisp (should work with current trace).

3. **Lean checker**: Implement `checkTheoremProof`. Start with a
   simple version that just verifies syntactic conditions. Test on
   simple.lisp.

4. **ACL2 changes**: Add `BEGIN-EXPANSION`/`END-EXPANSION` markers.
   Remove depth-counter suppressions. Re-capture proof logs for the
   sorting corpus.

5. **Lean parser update**: Handle the new markers, build sub-trees
   for expansions. Test on the 4% failure cases.

6. **Per-rule soundness**: Prove `defnExpand_sound`,
   `rewriteRule_sound`, etc. These use `evalOpt_fuel_mono` and
   `evalOpt_ge_fuel` from workstream A.

7. **Main soundness theorem**: Prove `checkTheoremProof_sound` by
   composing the per-rule lemmas.

8. **End-to-end**: Prove `my_len_my_app` from simple.lisp with no
   sorry.

9. **Scale**: Run on sorting corpus. Debug remaining issues.

### Open questions

1. **Induction**: How does the induction scheme from the trace map
   to a Lean induction principle? The trace gives us the recursion
   pattern and case conditions, but we need to construct a
   well-founded recursion argument in Lean.

2. **Rule instantiation**: When a rewrite rule is applied, the trace
   gives us LHS/RHS but not the substitution explicitly. We need to
   reconstruct it by matching the rule's pattern against the step's
   LHS. This is first-order matching (not unification) — decidable
   and straightforward.

3. **Hypothesis tracking**: When a rewrite step uses the induction
   hypothesis (which is a negated literal in the clause), how do we
   formally connect this to the Lean IH? The IH is `¬Lᵢ`, which
   gives us `evalOpt f w env Lᵢ = some .nil`, which is equivalent
   to the equality the step claims.

4. **Axioms**: Built-in ACL2 axioms (CAR-CONS, CDR-CONS, etc.) need
   to be proved once in Lean and made available to the checker. Many
   already exist in Logic.lean as simp lemmas.

5. **Previously proved theorems**: When a rewrite references a
   user-proved theorem from the same book, we need that theorem's
   proof to be available. This creates a dependency order — theorems
   must be proved in book order.
