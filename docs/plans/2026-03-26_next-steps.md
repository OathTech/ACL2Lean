# Next Steps: From Bool Checker to Proof Replay

Created: 2026-03-26
Updated: 2026-03-27 — Rewrote with accurate failure analysis and architectural roadmap.

## End goal

For every theorem in an ACL2 book, produce a Lean proof term that the
kernel checks. ACL2 is an untrusted oracle; Lean is the sole trust
anchor. No `sorry`.

```lean
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f world env formula = some SExpr.t := by
  acl2_replay "acl2_samples/simple.proof-log"
```

## Where we are

### Infrastructure (complete)

- **Evaluator**: `evalOpt` (fuel-bounded, Option-returning). Sole
  canonical evaluator. `eval` and `Evaluator` deleted.
- **Fuel monotonicity**: `evalOpt_fuel_mono` and `evalOpt_ge_fuel`
  proved, sorry-free. Factored via `evalOptStep` (non-recursive body).
- **Proof tree types**: `ProofNode` (recursive tree with
  `StepProvenance`), `LiteralProof`, `CaseProof`, `TheoremProof`.
- **ACL2 instrumentation**: 46 logging points with unique `:ORIGIN`
  tags. `BEGIN/END-INNER-REWRITE` markers for tree structure.
  Transaction rollback for abandoned explorations. Full provenance
  (origin, runes, parents, subst, equivTerm).
- **DEFUN emission**: ACL2 emits macro-expanded function bodies
  using `(body name t (w state))`. The Lean parser builds World
  from proof log DEFUN events — no source files needed.
- **425 `#guard` tests** across 14 files. `just ci` is the
  conformance gate.

### Bool checker (ProofChecker.lean)

A per-node checker that dispatches on rune type. 57 guard tests.
Validates that proof tree nodes are sound reasoning steps. Handles:

| Rule type | What it checks |
|---|---|
| `definition` | Unfold body, apply subst, chain children → match RHS |
| `rewrite` | Look up formula, pattern-match LHS, apply subst → match RHS |
| `executable-counterpart` | Ground eval via `evalOpt`, match result |
| `equal-self` | `(EQUAL x x) → 'T` |
| `if-simplification` | `(IF const then else) → branch` |
| `if-same-branches` | `(IF test x x) → x` |
| `type-set-equality` | `(EQUAL a b) → 'T` or `'NIL` (well-formedness only) |
| `fake-rune-for-anonymous-enabled-rule` | Clause context, recognizer, or type-prescription |
| `rewriting-equivalence` | equiv-term matches negated clause literal (IH) |
| `clause-context-resolution` | Literal resolved by clause context |
| `type-alist` | Same as anonymous rule |

### Corpus results

**591 passed, 58 failed** out of 649 theorems (91%).

| Book | Pass | Fail | Total | Notes |
|---|---|---|---|---|
| simple | 1 | 0 | 1 | Baseline: fully checked |
| qsort | 543 | 12 | 555 | 98% — best large book |
| isort | 15 | 3 | 18 | Missing axioms + body mismatch |
| bsort | 14 | 9 | 23 | Included book deps |
| msort | 15 | 7 | 22 | Included book deps |
| convert-perm-to-how-many | 1 | 13 | 14 | Included book deps |
| perm | 0 | 8 | 8 | All functions from included book |
| ordered-perms | 2 | 6 | 8 | Included book deps |

Books with 0 local theorems (definitions only): orderedp, how-many,
sorts-equivalent.

### Failure analysis (1,991 debug trace lines)

| Category | Count | % | Root cause |
|---|---|---|---|
| Unknown function | 1,403 | 70.5% | DEFUN from included book not in proof log |
| Unknown rewrite rule | 417 | 20.9% | Formula from included book or missing axiom |
| Rewrite RHS mismatch | 85 | 4.3% | Conditional rewrite hypotheses not checked |
| Defn body mismatch | 28 | 1.4% | IF branch resolution not replayed |
| Can't extract rewrite | 23 | 1.2% | Non-EQUAL conclusion formulas |
| Pattern match failed | 18 | 0.9% | Formula needs macro expansion |
| Rewrite+children mismatch | 15 | 0.8% | Cascading IF resolution in children |
| Unknown rune type | 2 | 0.1% | `compound-recognizer` not handled |

**91% of failures are missing data, not missing logic.** Functions and
theorems from included books aren't available because we process each
book in isolation. The remaining 9% are genuine checker capability gaps.

#### Missing data: functions (top 10)

memb (356), all-rel (152), rel (131), merge2 (126), rm (121),
orderedp (100), perm (78), how-many (71), true-listp (51), bnext (33)

#### Missing data: axioms/rules

lexorder-reflexive (147), lexorder-transitive (138), default-cdr (57),
default-car (51), fold-consts-in-+ (16), cons-car-cdr (8)

## Architecture

### The soundness argument

The soundness of the replay rests on two properties:

**Referential transparency** (property of `evalOpt`): if
`evalOpt f w env a = evalOpt f w env b`, then
`evalOpt f w env (C[a]) = evalOpt f w env (C[b])` for any
enclosing term `C[·]`. This is unconditional — proved once, used at
every rewrite step. It is the corrected form of the false
`evalReplace_sound` lemma, using existential fuel.

**Per-rule proof construction**: for each rule type, a function
that constructs a Lean proof term establishing the step's claimed
equality under the proof context (clause assumptions, branch
conditions, IH).

These compose: per-rule construction gives contextual equality
proofs; referential transparency lifts them to the enclosing term;
fuel monotonicity composes fuel bounds across the tree. The Lean
kernel checks every constructed proof term — no metatheorem needed.

### Architecture: direct proof-term construction

The replay constructs proof terms directly. A tactic walks the proof
tree and, for each node, calls a per-rule proof constructor. If the
constructed term type-checks, the theorem is proved. Lean's kernel
is the sole trust anchor.

```lean
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f world env formula = some SExpr.t := by
  acl2_replay "acl2_samples/simple.proof-log"
```

**Why not a reflected checker + soundness metatheorem?** A reflected
checker requires proving a complex metatheorem: "if this function
returns true, then the semantic property holds." That metatheorem is
an inductive proof over the checker code, with one case per rule
type — each case requiring exactly the same per-rule proof
construction that direct construction uses. The metatheorem adds an
indirection layer with no payoff: the per-rule knowledge is
identical either way, but the reflected approach wraps it in an
extra proof obligation about the checker function itself.

Direct construction is simpler: same per-rule proof work, no
metatheorem overhead, and bugs produce type errors (safe) rather
than soundness proof breakage (hard to debug).

**The Bool checker's role**: The existing `ProofChecker.lean` is a
debugging and validation tool. It validates that the proof tree
contains sufficient information before we invest in constructing
proof terms. It shares the same dispatch structure as the tactic
(dispatch on rune type, process children, compose). The checker is
the dry run; the tactic is the real thing.

**Designing the checker for proof construction makes it correct.**
If each Bool check answers "could I construct a proof term from
this node?", then the checker's correctness condition is
self-evident — it checks precisely the preconditions of the
corresponding proof constructor. There is no gap between what the
checker validates and what the tactic needs. A checker designed in
isolation might verify the wrong things; one designed as a dry run
of proof construction can't. This means Phase 1 (completing the
checker) directly shapes the proof constructors in Phase 3.

### Dependency chain architecture

ACL2 books form a DAG via `include-book`. To prove theorem T in book
B that references theorem R from included book A, we need R's proof
available as a Lean lemma.

Processing order: bottom-up through the DAG.

```
orderedp.lisp   (definitions only, no theorems to prove)
perm.lisp       (memb, rm, perm — prove 8 theorems)
how-many.lisp   (definitions only)
isort.lisp      (uses orderedp + perm + how-many — prove 18 theorems)
bsort.lisp      (uses orderedp + perm + how-many — prove 23 theorems)
...
```

Each book's proof log provides both DEFUNs and DEFTHMs. The checker/
replay processes books in dependency order, accumulating a World and
a set of proved theorems.

**For the Bool checker (immediate)**: accept multiple proof logs on
the CLI. Build the World and formula map cumulatively. Only check
theorems from the final log.

**For the replay (future)**: process each book's proof log to produce
a Lean file with proved theorems. Later books `import` earlier ones.

### Definition expansion: the hard problem

The checker treats children as flat find-and-replace rewrites. This
works for 98% of cases but fails when the expanded body contains IF
branches that the children resolve.

Example: expanding `memb` with args `(x1, it)` produces:
```
(IF (EQUAL x1 (CAR it)) 'T (MEMB x1 (CDR it)))
```

ACL2's rewriter knows from the clause context that `(EQUAL x1 (CAR it))`
is false, so it takes the else-branch, yielding `(MEMB x1 (CDR it))`.

The children in the proof tree contain nodes that resolve this IF test
(via clause assumption or type reasoning) and take the branch. The
checker needs to actually walk the IF structure, match children against
IF tests, and collapse branches.

This is the core of "guided evaluation" — and it's exactly what the
proof-producing replay will need to do. The Bool checker's IF walk is
the prototype for the proof term construction.

For proof replay, definition expansion decomposes into:
1. `evalOpt f w env (fn a1..an) = evalOpt (f-1) w env body[formals/actuals]`
   (definitional, from evalOpt's function-call case)
2. For each IF in the body: prove the test evaluates to T or NIL
   (from clause assumptions or type reasoning), take the branch
3. Recursively handle sub-simplifications in the branch

### Induction

ACL2's induction scheme tells us:
- The recursion variable and pattern
- Base case conditions
- Step case conditions and recursive call structure

We need to construct a Lean induction principle from this. The
natural approach: well-founded recursion on `acl2Count` (SExpr
structural size). ACL2's scheme tells us how the recursive call
decreases size; we prove the measure decreases.

This is the least-explored area. The existing `acl2Count` and
termination lemmas in `Count.lean` are the foundation, but the
mechanism for converting ACL2 schemes to Lean induction is open.

### Clause semantics

ACL2 proves theorems by showing clauses are valid. A clause
`{L₁, ..., Lₙ}` is a disjunction: at least one literal evaluates
to non-NIL. When working on literal Lᵢ, the prover assumes ¬Lⱼ
for j ≠ i.

The formal bridge:
```
∀ env, ∃ N, ∀ f ≥ N,
  evalOpt f w env L₁ ≠ some .nil ∨
  evalOpt f w env L₂ ≠ some .nil ∨ ... ∨
  evalOpt f w env Lₙ ≠ some .nil
```

Simplifying one literal Lᵢ to T, under the assumption that all other
literals evaluate to NIL, establishes the disjunction. The clause
structure maps directly to Lean's `Or` type.

## Work plan

### Phase 1: Complete the Bool checker

Goal: 649/649 pass. This validates that the proof tree contains
sufficient information for replay.

**Every failure in the Bool checker is a gap that would also block
proof-producing replay.** Phase 1 isn't busywork — it validates the
data pipeline.

#### 1a. Multi-proof-log loading

Change `check-proof` to accept dependency proof logs:
```
lake exe acl2lean check-proof target.proof-log dep1.proof-log dep2.proof-log ...
```

Build World (DEFUNs) and formula map (DEFTHMs) cumulatively from all
logs. Only check theorems from the target (last) log.

*Fixes*: 1,403 unknown-function + ~300 unknown-rewrite-rule errors.
*Expected impact*: ~70% of failures resolved.

#### 1b. Add missing built-in axioms

Add to `builtinAxioms`:
- `lexorder-reflexive`: `(IMPLIES (NOT (CONSP X)) (LEXORDER X X))`
  and the consp cases
- `lexorder-transitive`: `(IMPLIES (AND (LEXORDER X Y) (LEXORDER Y Z)) (LEXORDER X Z))`
- `default-car`: `(IMPLIES (NOT (CONSP X)) (EQUAL (CAR X) NIL))`
- `default-cdr`: `(IMPLIES (NOT (CONSP X)) (EQUAL (CDR X) NIL))`
- `fold-consts-in-+`: `(EQUAL (+ c1 (+ c2 X)) (+ (+ c1 c2) X))`
  where c1, c2 are constants
- `cons-car-cdr`: `(IMPLIES (CONSP X) (EQUAL (CONS (CAR X) (CDR X)) X))`

Note: some of these are conditional rewrites (IMPLIES with non-trivial
hypotheses). This overlaps with 1d.

*Fixes*: remaining ~120 unknown-rewrite-rule errors.

#### 1c. Conditional rewrite rules

`extractRewriteRule` currently only handles:
- `(EQUAL lhs rhs)`
- `(IMPLIES hyp (EQUAL lhs rhs))`

Extend to handle:
- `(IMPLIES (AND h1 h2 ...) (EQUAL lhs rhs))` — multiple hypotheses
- `(IMPLIES hyps conclusion)` where conclusion is not EQUAL — rewrite
  `conclusion` to `'T` when hypotheses hold
- Hypothesis discharge: verify each hypothesis is satisfied by the
  clause context (negated clause literal matches, or ground-true)

*Fixes*: 23 can't-extract + 85 RHS-mismatch errors.

#### 1d. Definition expansion with IF resolution

Replace the flat find-and-replace child application with a structured
IF walk:

1. Expand body and apply formal→actual substitution
2. Walk the result looking for IF nodes
3. For each IF: check if a child resolves the test (child's LHS is
   the test, child's RHS is `'T` or `'NIL`)
4. If resolved: replace the IF with the taken branch
5. Continue walking the branch
6. Apply remaining children as term rewrites

This must handle nested IFs (cascading branch resolution).

*Fixes*: 28 defn-body-mismatch + 15 rewrite+children-mismatch errors.

#### 1e. Formula macro expansion

Apply `macroExpand` to formula LHS patterns before pattern matching.
The formulas from the proof log use expanded forms (BINARY-+), but
built-in axiom formulas may use raw forms (+).

*Fixes*: 18 pattern-match-failed errors.

#### 1f. Compound recognizer

Add handler for `compound-recognizer` rune type. These derive type
information from recognizer predicates.

*Fixes*: 2 unknown-rune-type errors.

#### 1g. Validation

After all fixes:
- Run checker on full sorting corpus: all 649 theorems pass
- Run `just ci`: all 425+ guard tests pass
- The proof tree contains sufficient information for every step

### Phase 2: Foundational lemmas

Prove the building blocks that the per-rule proof constructors will
use. These are reusable infrastructure.

#### 2a. Referential transparency (congruence)

The corrected form of the false `evalReplace_sound`:

```lean
theorem evalOpt_congr (w : World) (env : Env) (term lhs rhs : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env lhs = evalOpt f w env rhs) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (replace term lhs rhs)
                  = evalOpt f w env term
```

Proof by structural induction on `term`. Each case uses
`evalOpt_fuel_mono` to align fuel levels across sub-expressions.
The key insight: choose M = max(N, depth(term)) to ensure all
sub-evaluations converge.

Depends on: `evalOpt_fuel_mono`, `evalOpt_ge_fuel` (both proved).

This is used by the tactic at every step to lift a local equality
to the enclosing expression.

#### 2b. Clause semantics bridge

Formalize the bridge between clause-level reasoning and the evaluator:

```lean
-- A clause is valid iff for all env, at least one literal is non-NIL
def clauseValid (w : World) (clause : List SExpr) : Prop :=
  ∀ env, ∃ N, ∀ f ≥ N,
    clause.any (fun lit => evalOpt f w env lit ≠ some .nil)

-- If one literal simplifies to T assuming others are NIL, clause is valid
theorem clause_valid_of_literal_true (w : World) (clause : List SExpr)
    (i : Nat) (hi : i < clause.length)
    (h : ∀ env, (∀ j, j ≠ i → j < clause.length →
            ∃ N, ∀ f ≥ N, evalOpt f w env clause[j] = some .nil) →
          ∃ N, ∀ f ≥ N, evalOpt f w env clause[i] = some SExpr.t) :
    clauseValid w clause
```

This connects the per-literal proof construction to the theorem's
universal statement. The tactic uses it to assemble per-case proofs
into the full theorem.

#### 2c. Definition expansion lemma

The tactic's definition expansion constructor needs:

```lean
theorem evalOpt_defn_unfold (w : World) (env : Env) (fn : Symbol)
    (formals : List Symbol) (body : SExpr) (args : List SExpr)
    (h_def : w.defs.get? fn = some (formals, body))
    (h_arity : args.length = formals.length) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (mkCall fn args) =
      evalOpt f w (bindFormals formals args env) body
```

This unfolds `evalOpt`'s function-call case. The tactic then
constructs proofs about the body (IF resolution, sub-rewrites)
guided by the proof tree's children.

#### 2d. IF branch resolution lemma

```lean
theorem evalOpt_if_true (w : World) (env : Env) (test thn els : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env test ≠ some .nil) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w env (mkIf test thn els) = evalOpt f w env thn
```

(And the symmetric `evalOpt_if_false`.) Used during definition
expansion to follow IF branches as directed by the proof tree.

#### 2e. Built-in axioms as Lean theorems

Each built-in axiom (CAR-CONS, CDR-CONS, etc.) needs a Lean proof:

```lean
theorem car_cons_eval (w : World) (env : Env) (x y : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (mkCall "car" [mkCall "cons" [x, y]]) =
      evalOpt f w env x
```

These are used by the tactic when a rewrite step cites a built-in.
Many already exist as simp lemmas in `Logic.lean`; they need to be
restated in the `evalOpt`-with-fuel form.

### Phase 3: Per-rule proof constructors

Each rule type gets a tactic/function that constructs the proof term
for that step. These mirror the Bool checker's dispatch but produce
proofs instead of booleans.

#### 3a. Easy constructors (start here)

These are direct applications of foundational lemmas:

- **equal-self**: `(EQUAL x x) → T`. Proof: unfold evalOpt for
  EQUAL, apply decidable equality. Nearly `rfl`.
- **if-simplification**: `(IF 'T a b) → a`. Proof: apply
  `evalOpt_if_true` with the constant test.
- **if-same-branches**: `(IF test x x) → x`. Proof: case split on
  test, both branches give `x`.
- **executable-counterpart**: Ground eval. Proof: `evalOpt` on the
  ground term produces `some result`, which is definitional.

These are the proving ground for the tactic infrastructure: how
does the tactic receive the proof context, construct the term, and
return it? Get this working on simple.lisp first.

#### 3b. Rewrite rule constructor

Given a proved theorem `thm : ∀ env, ∃ N, ∀ f ≥ N, evalOpt f w env formula = some SExpr.t`
and a pattern match producing substitution σ:

1. Instantiate the theorem with the substituted environment
2. Extract the equality `evalOpt f w env lhs = evalOpt f w env rhs`
3. Apply congruence to lift to the enclosing term

This handles both built-in axioms (Phase 2e) and previously proved
user theorems. The substitution σ from pattern matching becomes
environment manipulation in the proof term.

#### 3c. Definition expansion constructor

The most complex constructor. For a step `(fn a1..an) → rhs`:

1. Apply `evalOpt_defn_unfold` to get `eval(call) = eval(body[subst])`
2. Walk the body's IF structure guided by children:
   - Each child that resolves an IF test contributes a sub-proof
     (via `evalOpt_if_true`/`evalOpt_if_false`)
   - Each child that rewrites a subterm contributes via congruence
3. Compose sub-proofs into `eval(body[subst]) = eval(rhs)`
4. Chain: `eval(call) = eval(body[subst]) = eval(rhs)`

The Bool checker's IF-walk (Phase 1d) is the prototype for this
constructor. Every check the Bool version performs maps to a proof
obligation in this constructor.

#### 3d. Clause assumption / IH constructors

- **anonymous-rule** (clause assumption): The proof term negates a
  clause literal. Since we're working under the assumption that
  literal Lⱼ evaluates to NIL, the step follows directly.
- **rewriting-equivalence** (IH application): The equiv-term matches
  a negated clause literal. The IH is available as a hypothesis in
  the Lean proof context (introduced by the induction step).

These are straightforward once the clause semantics bridge (2b) is
in place, but require the tactic to track hypotheses correctly.

### Phase 4: Tactic composition

#### 4a. Single-theorem replay on simple.lisp

Prove `my_len_my_app` with no sorry:

```lean
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f world env formula = some SExpr.t := by
  acl2_replay "acl2_samples/simple.proof-log"
```

The `acl2_replay` tactic:
1. Reads and parses the proof log at elaboration time
2. Builds proof context (world, clause, etc.)
3. For each case: applies induction (if needed), then for each
   literal: chains per-rule proof constructors
4. Lean's kernel checks the composed proof term

#### 4b. Book-level replay

Generate a Lean file for each book in dependency order:

```lean
-- Generated: IsortWorld.lean
import ACL2Lean.Imported.PermWorld
import ACL2Lean.Imported.HowManyWorld

namespace ACL2.Imported.Isort
def world : World := ...  -- extends perm + how-many worlds
theorem orderedp_insert (env : Env) : ... := by acl2_replay ...
theorem orderedp_isort  (env : Env) : ... := by acl2_replay ...
...
```

Each theorem becomes a Lean lemma available for later books'
proofs. The dependency chain is enforced by Lean's import system.

#### 4c. Induction (the open frontier)

For theorems proved by induction, we need to construct the induction
principle. ACL2's scheme gives us case splits and recursive call
patterns. We need to map these to well-founded recursion on
`acl2Count`.

This is the least-understood part of the architecture. Possible
approaches:

- **Structural**: If ACL2 inducts on `(CDR x)`, map to Lean
  induction on list-like structure via `acl2Count` decrease.
- **Custom measure**: ACL2's measure function (if available in the
  proof log) could be lifted to Lean as a well-founded measure.
- **Reflection**: Encode the induction scheme as data, prove a
  generic induction principle parameterized by the scheme.

This needs investigation. The existing `acl2Count` infrastructure
and termination lemmas in `Count.lean` are the starting point.

## Soundness gaps to close

Current known gaps in the Bool checker where we accept steps without
fully verifying them. For proof-producing replay, each gap must be
resolved — either by constructing a proof, or by getting additional
information from ACL2.

1. **Type-prescription anonymous rules**: Accepted if provenance
   runes reference known functions. We don't re-derive the type
   conclusion. For replay: we need either (a) the type-prescription
   formula from ACL2 (so we can instantiate it as a lemma), or
   (b) enough information to derive the conclusion from first
   principles.

2. **Type-set-equality**: Accepted if LHS is EQUAL and RHS is
   constant. Don't verify the type reasoning. For replay: need to
   construct a proof that `(EQUAL a b)` evaluates to T or NIL.
   May require type information from ACL2 (e.g., "a and b are both
   integers" → EQUAL by computation).

3. **Type-alist**: Delegated to anonymous rule logic. Same gap as #1.

These gaps likely require additional ACL2 instrumentation — the
proof tree must carry enough information for independent
reconstruction. The Bool checker identifies where these gaps are;
the replay will force us to close them.

## What was completed

### 2026-03-26

- **Fuel monotonicity** (`evalOpt_fuel_mono`, `evalOpt_ge_fuel`):
  proved sorry-free via `evalOptStep` factoring
- **Evaluator consolidation**: dropped `eval` and `Evaluator`,
  standardized on `evalOpt`

### 2026-03-27 (early)

- **Proof tree types and parser**: `ProofNode`, `LiteralProof`,
  `CaseProof`, `TheoremProof` in `ProofTree.lean`
- **ACL2 instrumentation**: 46 logging points, transaction rollback,
  full provenance
- **DEFUN emission**: ACL2 emits expanded bodies, Lean builds World
  from proof log
- **Bool checker**: Per-node checking, 57 guard tests, 591/649
  theorems pass on sorting corpus

### Files deprecated

- `Rewriter.lean` — `replaceFirst`/`evalReplace`/`applyRewriteSteps`
  (import commented out)
- `RewriterSoundness.lean` — `evalReplace_sound` (known false)
- `Eval.lean`, `Evaluator.lean`, `Tests/EvaluatorTest.lean` — deleted

### Current sorry inventory

| File | Sorry | Status |
|---|---|---|
| `EvalOpt.lean` | (none) | Clean |
| `RewriterSoundness.lean` | `evalReplace_sound` | Known false, to be deleted |
| `SimpleWorld.lean` | `my_len_my_app` | Target for Phase 4a |
| `WorldGen.lean` | Template generates sorry | By design (stubs) |
| `DSL.lean` | Test/example code | Not proof-relevant |
| `Log2Replay.lean` | (none) | Clean (hand-written replay) |

## Open questions

1. **Induction principle construction**: How does ACL2's induction
   scheme (case splits + recursive call patterns) map to Lean
   well-founded recursion? See Phase 4c.

2. **Type-prescription verification**: Can we construct proofs for
   type-prescription conclusions from the proof tree data, or do
   we need additional ACL2 instrumentation? See soundness gaps.

3. **Tactic performance**: Will elaboration-time proof construction
   be fast enough for large books (qsort has 555 theorems)? If not,
   we may need caching, compiled tactic code, or incremental
   elaboration.

4. **Macro expansion completeness**: The current `macroExpand` handles
   `+`, `*`, `-`, and bare integers. Are there other ACL2 macros that
   appear in function bodies but not in the expanded trace form?

5. **Book DAG discovery**: Currently the dependency order must be
   specified manually on the CLI. Should we parse `include-book`
   events to discover the DAG automatically?

6. **Previously proved theorems as rewrites**: When theorem T from
   book A is used as a rewrite rule in book B's proof, the replay
   for B needs T as a Lean lemma. This creates a compile-time
   dependency — book B's Lean file must import book A's. The
   generation pipeline must respect this order.

7. **Proof term size**: Do constructed proof terms stay manageable,
   or do they blow up for complex theorems? If terms become large,
   we may need intermediate lemmas or proof irrelevance to keep
   the kernel check tractable.
