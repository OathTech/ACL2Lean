# Road to a Sound Proof Checker

Created: 2026-03-28

## Main principle

**We do NOT do inference in Lean.** ACL2 already did the work. Lean
replays ACL2's proof — deterministically, step by step, with no
heuristics, no search, no "figure it out" logic. Every reasoning
step the checker performs must be directed by the proof tree. If
the proof tree doesn't contain enough information to replay a step,
that is a bug in the ACL2 instrumentation, not a reason to add
inference to the checker.

No exceptions. No "try to derive type-prescriptions from function
bodies." No "search the clause for a matching literal." No
"simplify and hope it matches." If ACL2 resolved an IF test via
forward chaining, the proof tree must say so — with the conclusion
and the rule used. If ACL2 used a type-prescription, the proof log
must contain the type-prescription formula. The checker follows
instructions; it does not improvise.

This keeps the checker simple, deterministic, and easy to prove
sound. Every failure points to missing data from ACL2, which we fix
at the source. The checker never grows heuristics that might
accidentally accept unsound steps.

**Corollary: the easiest checker to prove sound is one that always
rejects** (trivially sound, but useless). We build upward: every
check we add expands the set of cases the checker *soundly accepts*.
The checker must NEVER accept a step it can't construct a proof term
for. Failures are honest — they mean "the proof tree doesn't tell
me enough." The fix is always in the data, never in adding guessing.

## Current state

**595/649 theorems pass** across the sorting corpus + simple.lisp.
Zero soundness gaps. Every failure is a hard failure:

| Category | Hits | Cause |
|---|---|---|
| Type-prescription (anonymous rule) | ~350 | ACL2's type reasoning; conclusions not in trace |
| Rewrite hypothesis (forward chaining) | ~400 | Conditional rewrite hyps need forward-chaining derivation |
| Definition body mismatch | ~280 | IF walk incomplete — children not fully replayed |
| Type-set-equality | ~7 | Type-incompatibility reasoning not available |
| Pattern match failed | ~25 | Macro expansion, expression-form rune names |
| Rewrite+children mismatch | ~15 | Cascading IF resolution in children |
| Compound-recognizer | 2 | Unhandled rune type |
| Unknown function (o-p) | 6 | Missing built-in definition |

(Hit counts are debug-trace occurrences, not theorem counts.
Multiple hits typically belong to one failing theorem.)

## The two worlds

The checker operates at the boundary between two worlds:

**What ACL2 knows.** ACL2 has a rich reasoning engine: type-set
reasoning (tracking what types a term can be), type-prescriptions
(what types each function returns), forward chaining (deriving
consequences of known facts), and the rewriter itself. The rewriter
uses all of these to justify proof steps.

**What the proof tree contains.** The proof tree records the
rewriter's conclusions (LHS → RHS) and the rune that justified each
step, plus provenance (substitutions, parent runes, equiv-terms).
But it does NOT record the intermediate reasoning that justified
the step — e.g., it doesn't record "forward chaining derived
(LEXORDER B A) from (LEXORDER A B) via lexorder-total."

Every checker failure is a case where ACL2 used reasoning whose
conclusion isn't in the proof tree. The fix is always one of:
1. Have ACL2 emit the conclusion so the checker can verify it
2. Replicate the reasoning in the checker (harder, more code)
3. Both (emit a hint, verify it)

Option 1 is almost always preferred: minimal trusted code, maximum
information for proof construction.

## What "sound" means for each check

For each check, we ask: given what the proof tree provides, can we
construct a Lean proof term that establishes `∃ N, ∀ f ≥ N,
evalOpt f w env lhs = evalOpt f w env rhs`?

### Current violations of the main principle

The checker currently contains logic that searches or infers
rather than replaying. These are technically sound (they only
accept valid steps) but they violate the deterministic-replay
principle and should be refactored:

- **`resolveIfTests`**: Searches the clause for literals that
  match an IF test, then resolves the IF. This is inference —
  the proof tree should tell us which clause literal justifies
  each IF resolution. Currently the proof tree's children DO
  contain this information (as anonymous-rule or type-alist
  nodes), but the checker also applies `resolveIfTests` as a
  fallback when child matching fails. The fallback should be
  removed once child matching is complete.

- **`simplifyTerm`**: Applies car-cons, cdr-cons, consp-cons,
  IF-constant-test reductions unconditionally after each child
  rewrite. These reductions are always valid, but applying them
  "just in case" is inference. The proof tree's children should
  include explicit nodes for each of these reductions (as
  `rewrite:car-cons`, `if-simplification`, etc.). Once child
  matching is complete, `simplifyTerm` becomes unnecessary — each
  reduction is directed by a child node.

- **Hypothesis free-variable matching** (path 5 in `verifyHyp`):
  Searches clause literals to find bindings for free variables in
  rewrite hypotheses. This is the checker improvising. The proof
  tree should tell us the binding (ACL2 knows what Y is in
  `lexorder-transitive`). Until ACL2 emits this, the search is
  a necessary workaround, but the target is explicit data.

These are acceptable as scaffolding while we bring up the checker,
but the target architecture has zero search: every step is
directed by the proof tree or proof log.

### Checks that are sound today

These checks verify enough to construct a proof term.

**equal-self**: `(EQUAL x x) → 'T`
- Proof term: unfold `evalOpt` for EQUAL, apply `BEq.refl`.
- Sound: the checker verifies `a == b` structurally.

**if-simplification**: `(IF 'T a b) → a` / `(IF 'NIL a b) → b`
- Proof term: unfold `evalOpt` for IF, test is constant.
- Sound: the checker verifies the test is a quoted constant.

**if-same-branches**: `(IF test x x) → x`
- Proof term: case split on test, both branches yield same result.
- Sound: the checker verifies `thn == els` structurally.

**executable-counterpart**: `(f '1 '2) → '3` (ground eval)
- Proof term: `evalOpt` computation on ground terms is definitional.
- Sound: the checker runs `evalOpt` and compares the result.

**rewriting-equivalence**: IH application
- Proof term: the induction hypothesis (a negated clause literal)
  provides the equality directly.
- Sound: the checker verifies the equiv-term matches a negated
  clause literal (including EQUAL symmetry).

**clause-context-resolution**: literal resolved by clause
- Proof term: the clause assumption directly gives the result.
- Sound: the checker verifies via `clauseJustifies`.

**rewrite rule (unconditional)**: `(F X Y) → (G X Y)` via theorem
- Proof term: instantiate the proved theorem with σ.
- Sound: the checker verifies the formula exists, pattern-matches
  the LHS, and the substituted RHS matches.

**rewrite rule (conditional, hypotheses verified)**: same, with
  hypothesis discharge
- Proof term: instantiate theorem, discharge each hypothesis from
  clause context or children.
- Sound: the checker verifies each hypothesis is satisfied.

**anonymous rule (clause context)**: predicate resolved by clause
- Proof term: clause assumption.
- Sound: `clauseJustifies` checks structural match.

**anonymous rule (recognizer trivial)**: `(CONSP (CONS a b)) → 'T`
- Proof term: unfold `evalOpt` for CONSP and CONS.
- Sound: the checker verifies constructor structure.

**type-set-equality (ground constants)**: `(EQUAL '0 '1) → 'NIL`
- Proof term: `decide` on quoted values.
- Sound: the checker unquotes and compares.

**definition expansion (body matches after children + simplify)**:
  `(F a b) → result` via unfolding + child chain
- Proof term: unfold `evalOpt` for function call, apply children
  as congruence steps, apply `simplifyTerm` reductions (each has
  a Lean lemma: car-cons, cdr-cons, if-true, if-false, etc.).
- Sound: the checker unfolds, substitutes, applies children,
  simplifies, and verifies the result matches.

**resolveIfTests**: IF tests resolved by clause context
- Proof term: clause assumption proves test is T/NIL, then IF
  reduces to the appropriate branch.
- Sound: `clauseJustifies` checks structural match.

**simplifyTerm reductions** (applied after child rewrites):
- Each reduction corresponds to a provable Lean lemma.
- Sound: the reductions are unconditionally valid.

### Checks that fail today (future work)

Each of these is a hard failure. To make them pass, we need
additional information from ACL2 or additional reasoning in the
checker.

**F1. Anonymous rule — type-prescription** (~350 hits)

The step claims `(pred arg) → 'T` or `'NIL`, justified by a
type-prescription rune. ACL2's type-prescription system tracks
what types each function returns (e.g., "CONSP always returns
a boolean", "MY-LEN always returns a non-negative integer").

The proof tree contains: the rune name (e.g.,
`type-prescription:my-len`) and the conclusion. It does NOT
contain the type-prescription formula.

**What's needed from ACL2**: Emit the type-prescription formula
alongside the DEFUN, just as DEFTHM formulas are emitted alongside
theorems. Type-prescriptions are theorems — they belong in the
proof log. See Phase 0 above.

**Proof term**: prove the type-prescription once per function in
Lean (by induction on `acl2Count` over the function body), then
instantiate it at each use site.

**F2. Rewrite hypothesis — forward chaining** (~400 hits)

A conditional rewrite rule's hypothesis requires facts derived by
ACL2's forward-chaining engine. Example: `lexorder-transitive`
needs `(LEXORDER a b)` which follows from `(LEXORDER b a)` via
`lexorder-total`, but this derivation isn't in the proof tree.

The proof tree contains: the conditional rewrite's rune and the
provenance runes (which mention `forward-chaining:lexorder-total`).

**What's needed from ACL2**: Emit forward-chaining conclusions
when they're used to discharge a rewrite hypothesis:

```
:FORWARD-CHAIN-CONCLUSION (LEXORDER a b)
  :FROM (LEXORDER b a)
  :VIA lexorder-total
```

This gives the checker a chain: clause has `(NOT (LEXORDER b a))`,
so `(LEXORDER b a)` is TRUE, forward-chaining via `lexorder-total`
gives `(LEXORDER a b)`, which discharges the hypothesis.

**Proof term**: instantiate `lexorder-total` with the clause
assumption, derive the forward-chaining conclusion.

**F3. Definition body mismatch** (~280 hits)

The definition expansion checker applies children as flat rewrites
and simplifies. This fails when children operate on terms nested
inside IF branches that haven't been resolved yet, or when the
body requires deeper guided evaluation.

The proof tree contains: the children with their LHS/RHS, the
substitution, and the expected final RHS.

**What's needed**: No ACL2 changes. This is a checker logic issue.
The fix is to walk the expanded body structurally, matching
children to the sub-expressions they operate on:

1. After substitution and macro-expansion, walk the body's AST
2. At each IF node, check if a child resolves the test
3. If so, take the branch and continue in the branch body
4. At each non-IF node, check if a child rewrites it
5. Apply `simplifyTerm` after each step

This is a tree walk, not a flat fold. The current code does a
flat fold with `replaceInTerm` which misses cases where children
refer to sub-expressions that only exist after earlier children
have simplified the structure.

**Proof term**: sequence of `evalOpt` unfolding, IF resolution
(via clause assumptions), and congruence steps.

**F4. Type-set-equality** (~7 hits)

Claims like `(EQUAL '0 (BINARY-+ '1 x)) → 'NIL` — zero can't
equal a positive. This requires type-set reasoning about the
range of `BINARY-+`.

**What's needed from ACL2**: Emit the type-set derivation:

```
:TYPE-SET-DERIVATION
  :TERM (BINARY-+ '1 x)
  :TYPE-SET <positive-integer>
  :THEREFORE (NOT (EQUAL '0 (BINARY-+ '1 x)))
```

**Alternative**: prove a Lean lemma that `BINARY-+` of a positive
and a non-negative is positive. This is provable from `evalOpt`'s
arithmetic case. Then `(EQUAL '0 positive) → 'NIL` follows.

**F5. Mechanical fixes** (~50 hits)

These require no ACL2 changes and no new reasoning:

- **Pattern match on unexpanded formulas** (~25 hits): Apply
  `macroExpand` to axiom formula patterns before matching.
  Expression-form rune names like `(+ y x)` reference built-in
  arithmetic lemmas by their LHS — match against axiom formulas
  by expression form.

- **Compound-recognizer** (2 hits): Add handler for this rune type.
  Examine the 2 instances to determine what's claimed and how to
  verify it.

- **Missing o-p definition** (6 hits): Add the full `o-p` built-in
  definition (requires `o-first-expt`, `o-first-coeff`, `o-rst`,
  `o<`). Or have ACL2 emit it via DEFUN.

### Structural checks to add

These don't correspond to specific rune types but are needed for
proof construction:

**S1. Literal chain connectivity**

`checkLiteralProof` currently checks that every node is
individually valid but does NOT verify that the nodes form a
connected chain from the input literal to the result. A collection
of individually valid but unrelated nodes would pass.

For proof construction: the tactic chains rewrites via congruence.
Node 1 rewrites a subterm of the literal, node 2 rewrites a
subterm of the result of node 1, etc. The checker should verify
this chain.

**What to check**: Each node's LHS must be a subterm of the
"current expression" (the literal after applying all prior nodes'
rewrites). This is what `replaceInTerm` does during definition
expansion; the same logic applies at the literal level.

**S2. Induction verification**

Currently, the checker trusts ACL2's induction structure — it
checks each case independently but doesn't verify that the cases
cover all possibilities or that the induction is well-founded.

For proof construction: we need a well-founded induction principle
that maps to ACL2's scheme. The proof tree provides the scheme
(case conditions and recursive call patterns). We need to verify:
- The cases are exhaustive
- Each recursive call decreases the measure

This is the hardest open problem and is deferred, but should be
planned for. The existing `acl2Count` infrastructure provides the
measure; the induction scheme provides the case structure.

## Existing infrastructure

**Fuel monotonicity** (proved, sorry-free):
- `evalOpt_fuel_mono`: `evalOpt f w env t = some v → evalOpt (f+1) w env t = some v`
- `evalOpt_ge_fuel`: `evalOpt N w env t = some v → f ≥ N → evalOpt f w env t = some v`
- `evalOptStep_mono`: monotonicity of the non-recursive step function

These compose fuel bounds across proof steps.

**Congruence properties** in `EvalOpt.lean`:
- `evalOptStep_mono` establishes that equal sub-evaluations yield
  equal results — the foundation for referential transparency.
- Full congruence theorem `evalOpt_congr` (replacing a subterm with
  an equal-valued one preserves the enclosing evaluation) is the
  next major infrastructure piece to prove.

**Logic lemmas** in `Logic.lean`:
- `car_cons`, `cdr_cons`, `consp_cons`, etc. as simp lemmas
- These need `evalOpt`-with-fuel forms for the proof constructor.

## Implementation order

The order is determined by: soundness first, coverage second.
Each step adds new *sound* checking capability.

**Priority target: simple.lisp** — our hello world example. It
currently fails on exactly one issue: `(ACL2-NUMBERP (MY-LEN Y))`
resolved via type-prescription. Fixing this ONE case restores
simple.lisp to passing and validates the end-to-end pipeline.

### Phase 0: Restore simple.lisp (highest priority)

The sole blocker: `(acl2-numberp (my-len y)) → 'T` via
`type-prescription:my-len`.

**The right fix: ACL2 emits type-prescription formulas.**

A type-prescription is a theorem about a function's return type.
ACL2 already derived it — we don't re-derive it. We just need ACL2
to tell us the *statement*, same as it tells us theorem formulas
via DEFTHM events. Type-prescriptions are theorems; they belong
in the proof log.

The architecture is identical to how we handle every other ACL2
claim: ACL2 states a fact, we independently verify it. For
type-prescriptions:
1. ACL2 emits the formula (e.g., `(ACL2-NUMBERP (MY-LEN X))`)
2. The checker records it as a known theorem
3. When a proof step cites `type-prescription:my-len`, the
   checker instantiates the formula and verifies the conclusion
4. For proof construction, we prove the type-prescription once
   in Lean from the function definition, then instantiate it

This is not a hack — it's the same principled pipeline we use
for DEFTHM. ACL2 is the untrusted oracle that tells us what to
prove; Lean proves it from the definition.

**ACL2 change**: When a function is admitted, emit its
type-prescription alongside the DEFUN:
```
(:TYPE-PRESCRIPTION MY-LEN
  :FORMULA (ACL2-NUMBERP (MY-LEN X))
  :ORIGIN TYPE-PRESCRIPTION/DEFUN)
```

**Checker change**: Parse type-prescription events, store as
theorem formulas. When `checkAnonymousRule` encounters a
type-prescription rune, look up and instantiate the formula.

**Proof constructor**: Prove each type-prescription as a Lean
lemma by induction on `acl2Count` over the function body. This
is a once-per-function proof that mirrors ACL2's own derivation.

### Phase A: Mechanical fixes (no ACL2 changes)

These are low-hanging fruit that expand sound coverage.

1. **Macro-expand formula patterns** before pattern matching
2. **Handle expression-form rune names** by matching against
   axiom formulas
3. **Add compound-recognizer handler**
4. **Add o-p and related built-in definitions**
5. **Improve definition expansion IF walk** (F3) — the biggest
   Lean-side improvement, addressing ~280 hits

After Phase A: expect ~620/649 pass (up from 595).

### Phase B: ACL2 instrumentation

ACL2 already derives facts during proof search. These facts are
theorems. When the proof tree references them, we need their
statements so we can independently verify them. This is the same
pipeline as DEFTHM/DEFUN — ACL2 tells us what it proved, we
check it ourselves.

1. **Type-prescription emission** (F1): Emit the type-prescription
   formula when a function is admitted, alongside the DEFUN.
   Type-prescriptions are theorems about functions — they belong
   in the proof log just like DEFTHM events. The checker stores
   them as known formulas; the proof constructor proves them once
   per function from the definition.

   ACL2 change: in `defun-fn`, after emitting the DEFUN body,
   also emit the type-prescription formula from
   `(getpropc name 'type-prescriptions nil (w state))`.

   Lean change: parse the new event, store as theorem formula,
   instantiate when cited by proof steps.

2. **Forward-chaining conclusion emission** (F2): When the
   rewriter discharges a hypothesis via forward chaining, emit
   the conclusion and the rule used. The checker verifies the
   forward-chaining rule is a theorem and the conclusion follows.

   ACL2 change: ~10 lines in `rewrite.lisp` where
   `relieve-hyp-fc` fires.

   Lean change: parse the new event, verify the forward-chaining
   derivation.

3. **Type-set derivation emission** (F4): When type-set-equality
   resolves an EQUAL, emit the type-set derivation. The checker
   verifies the type conclusion.

   ACL2 change: ~5 lines in `simplify.lisp`.

   Lean change: parse, verify.

After Phase B: expect 649/649 pass.

### Phase C: Structural soundness

1. **Literal chain connectivity** (S1): verify that nodes chain
   from literal to result via subterm replacement.

2. **Induction verification** (S2): verify case exhaustiveness
   and well-foundedness. This is the final piece for full proof
   construction.

## ACL2 instrumentation design principles

When adding ACL2 instrumentation:

1. **Emit conclusions, not derivations.** The checker verifies
   the conclusion independently — it doesn't trust the derivation.
   Emitting `(LEXORDER a b)` as a forward-chaining conclusion is
   enough; the checker will verify it from `lexorder-total` + clause
   context.

2. **Emit only what's needed.** Each emission point corresponds to
   a specific checker gap. Don't emit everything — emit what the
   checker needs to construct a proof term.

3. **Use existing infrastructure.** The proof log format already
   has `:RUNES`, `:SUBST`, `:ORIGIN` etc. New emissions should
   follow the same pattern: keyword-value pairs parseable by the
   existing Lean parser.

4. **Test incrementally.** After each ACL2 change, re-capture the
   affected proof logs and verify the checker accepts the new data.

## What this gives us

When the checker passes a theorem, every step has been verified
to the level needed for proof-term construction:

- Every rewrite rule application: formula exists, pattern matches,
  hypotheses discharged, RHS confirmed
- Every definition expansion: body unfolds correctly, children
  chain to the result
- Every clause assumption: justified by clause context
- Every type-prescription: formula instantiated and verified
- Every forward-chaining conclusion: rule + premises verified
- Every literal: nodes chain from input to result
- Every case: at least one literal proved to T

The `acl2_replay` tactic walks the same structure and constructs
proof terms instead of returning Bool. Each check becomes a proof
term constructor. The Lean kernel checks the constructed terms.
