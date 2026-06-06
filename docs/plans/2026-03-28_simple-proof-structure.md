# Proof Structure for my-len-my-app

Created: 2026-03-28
Updated: 2026-03-28 — incorporated critic feedback, fixed theorem statements

## The theorem

```lean
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f world env my_len_my_appFormula = some SExpr.t
```

where `world` is the specific `World` containing the definitions of
`my-len` and `my-app` (defined in SimpleWorld.lean). The theorem is
about THIS world — it says nothing without these definitions. The
`env` maps free variables `x` and `y` to arbitrary SExpr values.

The proof is by well-founded induction on
`acl2Count (env.getD {name:="x"} .nil)`, which decreases on
recursive calls because `my-app` recurses on `(CDR x)` when
`(CONSP x)`.

## Proof structure from the proof tree

Two cases by induction. In each case, the formula
`(EQUAL (MY-LEN (MY-APP x y)) (BINARY-+ (MY-LEN x) (MY-LEN y)))`
is simplified by a chain of rewrites until both sides are identical,
then `(EQUAL t t) = T` finishes it.

Each rewrite replaces a subterm with an equal-valued term. The
chain is: starting formula → rewrite 1 → rewrite 2 → ... → `(EQUAL t t)` → T.

### Base case: `consp(env(x)) = NIL`

Clause: `[(CONSP x), (EQUAL ...)]`. Assume literal 0 is NIL, i.e.,
`evalOpt f w env (CONSP x) = some .nil`.

Starting term: `(EQUAL (MY-LEN (MY-APP x y)) (BINARY-+ (MY-LEN x) (MY-LEN y)))`

1. Replace `(MY-APP x y)` with `y` [definition expansion: consp=nil → else-branch]
2. Replace `(MY-LEN x)` with `(QUOTE 0)` [definition expansion: consp=nil → else-branch]
3. Replace `(BINARY-+ (QUOTE 0) (MY-LEN y))` with `(MY-LEN y)` [unicity-of-0 + fix]
4. Now both sides are `(MY-LEN y)`: `(EQUAL (MY-LEN y) (MY-LEN y))` → T [equal-self]

### Step case: `consp(env(x)) ≠ NIL`, IH available

Clause: `[(NOT (CONSP x)), (NOT (EQUAL ...ih...)), (EQUAL ...goal...)]`.

Literal 2 rewrites the IH via commutativity:
`(BINARY-+ (MY-LEN (CDR x)) (MY-LEN y))` → `(BINARY-+ (MY-LEN y) (MY-LEN (CDR x)))`

Then literal 3 (the goal):
1. Replace `(MY-APP x y)` with `(CONS (CAR x) (MY-APP (CDR x) y))` [defn expansion]
2. Replace `(MY-LEN (CONS (CAR x) (MY-APP (CDR x) y)))` with `(BINARY-+ (QUOTE 1) (MY-LEN (MY-APP (CDR x) y)))` [defn expansion + cdr-cons]
3. Replace `(MY-LEN x)` with `(BINARY-+ (QUOTE 1) (MY-LEN (CDR x)))` [defn expansion]
4. Replace `(BINARY-+ (BINARY-+ (QUOTE 1) (MY-LEN (CDR x))) (MY-LEN y))` with `(BINARY-+ (QUOTE 1) (MY-LEN (MY-APP (CDR x) y)))` [commutativity-2 + IH]
5. `(EQUAL (BINARY-+ (QUOTE 1) (MY-LEN (MY-APP (CDR x) y))) (BINARY-+ (QUOTE 1) (MY-LEN (MY-APP (CDR x) y))))` → T [equal-self]

## Theorems needed

### T1. Subterm replacement congruence

The `C : SExpr → SExpr` formulation is WRONG — an arbitrary Lean
function can distinguish syntactically different but semantically
equal terms. The correct formulation uses syntactic replacement:

```lean
theorem evalOpt_replace_congr (w : World) (env : Env)
    (term a b : SExpr)
    (h_eq : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w env (replaceSubterm term a b) =
      evalOpt f w env term
```

where `replaceSubterm` replaces the first occurrence of `a` in
`term` with `b` (depth-first, left-to-right, skipping QUOTE bodies
and head symbols — same as `replaceInTerm` in ProofChecker.lean).

Proved by structural induction on `term`, following the evaluator's
recursion pattern. Key: the replacement only targets positions that
`evalOpt` actually evaluates as subexpressions.

This is used at EVERY rewrite step in the proof.

### T2. EQUAL-T implies evaluation equality

```lean
theorem eval_equal_t_implies_eq (w : World) (env : Env)
    (a b : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env (EQUAL a b) = some SExpr.t) :
    ∃ M, ∀ f ≥ M, evalOpt f w env a = evalOpt f w env b
```

If `(EQUAL a b)` evaluates to T, then `a` and `b` evaluate to the
same value. Proof: evalOpt evaluates both to values `va` and `vb`,
then `Logic.equal va vb = .t` implies `va = vb` (from decidable
equality on SExpr), so `evalOpt` of `a` and `b` both give `va`.

Used to extract usable equalities from EQUAL expressions (for IH).

### T3. EQUAL-self

```lean
theorem evalOpt_equal_self (w : World) (env : Env) (t : SExpr)
    (h : ∃ N, ∀ f ≥ N, (evalOpt f w env t).isSome) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (EQUAL t t) = some SExpr.t
```

If `t` converges, `(EQUAL t t)` evaluates to T. Proof: both copies
of `t` evaluate to the same value `v`, and `Logic.equal v v = .t`.

### T4. Definition expansion

```lean
theorem evalOpt_defn_expand (w : World) (env : Env)
    (fn : Symbol) (formals : List Symbol) (body : SExpr)
    (args argVals : List SExpr)
    (h_def : w.defs.get? fn = some (formals, body))
    (h_args : ∃ N, ∀ f ≥ N,
      args.mapM (evalOpt f w env) = some argVals)
    (h_arity : formals.length = argVals.length) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w env (CALL fn args) =
      evalOpt f w (bindArgs formals argVals) body
```

Evaluating a user-defined function call equals evaluating its body
with formals bound to evaluated arguments. The `h_args` hypothesis
uses `mapM` matching what evalOptStep actually does.

### T5. IF-branch resolution

```lean
theorem evalOpt_if_true (w : World) (env : Env) (c t e : SExpr)
    (cv : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (ht : Logic.toBool cv = true) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (IF c t e) = evalOpt f w env t

theorem evalOpt_if_false (w : World) (env : Env) (c t e : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some .nil) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (IF c t e) = evalOpt f w env e
```

### T6. Builtin evaluation

```lean
theorem evalOpt_builtin (w : World) (env : Env)
    (fn : Symbol) (args argVals : List SExpr)
    (h_not_def : w.defs.get? fn = none)
    (h_args : ∃ N, ∀ f ≥ N,
      args.mapM (evalOpt f w env) = some argVals) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w env (CALL fn args) =
      some (callBuiltin fn.normalizedName argVals)
```

For functions not in the world (CONSP, CDR, CAR, EQUAL, BINARY-+),
evaluation calls `callBuiltin` on the evaluated arguments.

### T7. Quote and variable evaluation

```lean
theorem evalOpt_quote (w : World) (env : Env) (v : SExpr) :
    ∀ f, evalOpt (f+1) w env (QUOTE v) = some v

theorem evalOpt_var (w : World) (env : Env) (s : Symbol)
    (v : SExpr) (h : env.get? s = some v) :
    ∀ f, evalOpt (f+1) w env (.atom (.symbol s)) = some v
```

These don't need existential fuel — they work at any fuel > 0.

### T8. Specific axioms (one-time, from Logic.lean)

```lean
-- (+ 0 x) = (FIX x) — or more precisely, at the value level:
-- Logic.plus (intExpr 0) v = Logic.fix v for all v
theorem logic_plus_zero (v : SExpr) :
    Logic.plus (.atom (.number (.int 0))) v = Logic.fix v

-- (CDR (CONS a b)) = b
theorem logic_cdr_cons (a b : SExpr) :
    Logic.cdr (.cons a b) = b

-- (+ x y) = (+ y x) at the value level
theorem logic_plus_comm (x y : SExpr) :
    Logic.plus x y = Logic.plus y x

-- (+ x (+ y z)) = (+ y (+ x z)) at the value level
theorem logic_plus_comm2 (x y z : SExpr) :
    Logic.plus x (Logic.plus y z) = Logic.plus y (Logic.plus x z)

-- FIX of a number is identity
theorem logic_fix_number (n : Number) :
    Logic.fix (.atom (.number n)) = .atom (.number n)

-- MY-LEN returns a number (type-prescription)
-- This is about a SPECIFIC world — it depends on my-len's definition.
theorem my_len_is_number (w : World) (env : Env)
    (h_def : w.defs.get? my_len_sym = some my_len_def) :
    ∀ x : SExpr, ∃ N, ∀ f ≥ N,
      Logic.acl2Numberp (evalOpt f w env (CALL my_len_sym [x])).get!
      = SExpr.t
```

The axiom theorems (T8) are about Logic.* functions directly, NOT
about evalOpt. They get LIFTED to evalOpt equalities via T4/T6
(definition expansion / builtin evaluation). For example:

- To apply `cdr-cons` at the evalOpt level: use T6 (builtin eval)
  to show `evalOpt f w env (CDR (CONS a b)) = some (Logic.cdr (cons va vb))`,
  then use `logic_cdr_cons` to conclude `= some vb`,
  then use T6 again to show `evalOpt f w env b = some vb`.
  Combined: `evalOpt f w env (CDR (CONS a b)) = evalOpt f w env b`.

### T9. Fuel composition helper

```lean
theorem fuel_join {P Q : Nat → Prop}
    (h1 : ∃ N, ∀ f ≥ N, P f) (h2 : ∃ N, ∀ f ≥ N, Q f) :
    ∃ N, ∀ f ≥ N, P f ∧ Q f
```

## SExpr notation needed

The theorems reference `CALL`, `QUOTE`, `IF`, `EQUAL`, `BINARY-+`
as SExpr constructors. These need to be defined:

```lean
def QUOTE (v : SExpr) := mkCall "quote" [v]
def IF (c t e : SExpr) := mkCall "if" [c, t, e]
def EQUAL (a b : SExpr) := mkCall "equal" [a, b]
def CALL (fn : Symbol) (args : List SExpr) :=
  .cons (.atom (.symbol fn)) (SExpr.ofList args)
```

## Gaps identified by expert critique (2nd round)

The following are additional proof rules and theorems identified
by detailed analysis of the proof tree. Each corresponds to a
specific mechanism the proof-producing checker needs.

### T10. Induction scheme

The proof tree says "Induction on (my-app x y) → 2 subgoals."
This is a PROOF RULE — arguably the most important one because it
provides the skeleton that everything else plugs into.

```lean
-- For my-app's recursion pattern: induct on acl2Count of env(x).
-- Base: ¬consp(env(x)) → P(env)
-- Step: consp(env(x)) ∧ P(env with x↦cdr(env(x))) → P(env)
theorem acl2_induction_consp (w : World) (env : Env)
    (P : SExpr → Prop)  -- property parameterized by x's value
    (base : ∀ v, Logic.consp v = .nil → P v)
    (step : ∀ v, Logic.consp v ≠ .nil → P (Logic.cdr v) → P v) :
    ∀ v, P v
```

Proved by well-founded induction on `acl2Count v`. When
`consp v ≠ nil`, `v` is a cons cell, so `acl2Count (cdr v) <
acl2Count v`.

The proof tree tells us the induction scheme. The proof-producing
checker constructs this induction principle from the scheme data.

### T11. Clause structure

ACL2 proves theorems via clauses (disjunctions). A clause
`[L₁, ..., Lₙ]` is valid if at least one literal is non-NIL.
The proof shows one literal is T assuming the others are NIL.

```lean
-- NOT(e) = NIL implies e is truthy
theorem not_nil_means_arg_truthy (w : World) (env : Env) (t : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env (NOT t) = some .nil) :
    ∃ M, ∀ f ≥ M, ∃ v, evalOpt f w env t = some v ∧ v ≠ .nil

-- EQUAL only returns T or NIL (needed to upgrade "truthy" to "= T")
theorem equal_returns_t_or_nil (w : World) (env : Env) (a b : SExpr)
    (v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env (EQUAL a b) = some v) :
    v = SExpr.t ∨ v = .nil
```

These combine to extract the IH: `NOT(EQUAL ...) = NIL` →
`EQUAL ... = T` → eval equality (via T2).

### T12. Type-prescription proof rule

Type-prescriptions are theorems about function return types,
proved by induction on the function body's branch structure.
ACL2 emits the proof data (leaf terms + type-sets). The
proof-producing checker replays this.

```lean
-- For a specific function f with body (IF test then-branch else-branch):
-- If every branch returns a value of type T, then f returns type T.
-- This is proved by induction on acl2Count (matching the function's
-- recursion pattern). Each leaf's type is justified by either:
-- (a) it's a constant of the claimed type
-- (b) it's a builtin call whose return type is known
-- (c) it's a recursive call (IH)
--
-- For my-len specifically:
theorem my_len_returns_number (env : Env) (xv : SExpr) :
    ∃ N, ∀ f ≥ N,
      ∃ v, evalOpt f world (({} : Env).insert x_sym xv) my_lenBody = some v
        ∧ Logic.acl2Numberp v = SExpr.t
```

This is proved by induction on `acl2Count xv`, following the
body's IF tree. Base case: `¬consp(xv)` → body returns 0 →
`acl2Numberp 0 = T`. Step case: `consp(xv)` → body returns
`1 + my-len(cdr(xv))` → by IH, `my-len(cdr(xv))` is a number
→ `1 + number` is a number.

### T13. Trivial recognizer

```lean
theorem consp_cons (a b : SExpr) : Logic.consp (.cons a b) = SExpr.t
```

Used in the step case for `(CONSP (CONS ...)) → T`.

### T14. Macro expansion preserves evaluation

The World's function bodies may use `+` while the proof tree uses
`BINARY-+`. If these differ, we need:

```lean
theorem evalOpt_macroExpand (w : World) (env : Env) (t : SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (macroExpand t) = evalOpt f w env t
```

Alternatively, ensure the World's bodies are already macro-expanded
(which they are when built from proof log DEFUN events). In that
case this theorem is unnecessary for proof-log-sourced worlds.

## Complete theorem inventory

| # | Theorem | Proof tree node | Difficulty |
|---|---------|----------------|------------|
| T1 | `evalOpt_replace_congr` | Every rewrite step (lifts local eq to context) | Hard |
| T2 | `eval_equal_t_implies_eq` | IH extraction from EQUAL=T | Medium |
| T3 | `evalOpt_equal_self` | `equal-self` nodes | Easy |
| T4 | `evalOpt_defn_expand` | `definition:*` nodes | Medium |
| T5 | `evalOpt_if_true/false` | `if-simplification` children | Medium |
| T6 | `evalOpt_builtin` | Builtin calls (CONSP, CDR, etc.) | Medium |
| T7 | `evalOpt_quote/var` | Quote and variable evaluation | Easy |
| T8 | Logic axioms (5) | `rewrite:*` nodes (value-level) | Easy-Medium |
| T9 | `fuel_join` | Composing existential fuel bounds | Easy |
| T10 | `acl2_induction_consp` | Induction scheme from proof tree | Medium |
| T11 | `not_nil_means_truthy` + `equal_t_or_nil` | Clause literal assumptions | Medium |
| T12 | `my_len_returns_number` | `type-prescription` steps | Medium |
| T13 | `consp_cons` | Trivial recognizer children | Easy |
| T14 | `evalOpt_macroExpand` | Body normalization (if needed) | Medium |

### T15. Variable substitution respects evaluation

This is the single most important missing theorem, identified by
round-3 critique. It closes TWO fundamental gaps at once:

```lean
theorem evalOpt_subst_var (w : World) (env : Env) (s : Symbol)
    (v : SExpr) (term : SExpr)
    (hv : ∃ N, ∀ f ≥ N, evalOpt f w env (QUOTE v) = some v) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w (env.insert s v) term =
      evalOpt f w env (substVar term s (QUOTE v))
```

where `substVar` replaces free occurrences of variable `s` with
`(QUOTE v)` (a quoted literal for the value).

**Why this matters:**

(a) **Definition expansion env bridging.** T4 gives us:
`eval(CALL fn args) = eval_body_env(body)`. T15 converts this
back: `eval_body_env(body) = eval_orig_env(body[formals/quoted-vals])`.
This lets T1 (congruence) work in a single environment.

(b) **IH env conversion.** Structural induction gives IH about
`env[x := cdr(env(x))]`. T15 converts: evaluating `term` in the
modified env = evaluating `term[x/(QUOTE cdr(xv))]` in the
original env. Since `term[x/(QUOTE cdr(xv))]` in the original
env behaves like `term[x/(CDR x)]` when `env(x) = cons(a, d)`,
this bridges the IH to the form the proof tree uses.

Proved by structural induction on `term`, following evalOpt's
recursion. Each variable lookup either matches `s` (replaced) or
doesn't (unchanged). Function calls, IF, etc. distribute.

### T16. Fuel-existential transitivity

```lean
theorem fuel_chain_eq (w : World) (env : Env) (a b c : SExpr)
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env b = evalOpt f w env c) :
    ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env c
```

Combines two fuel-existential equalities by transitivity. Used to
chain rewrite steps.

### T17. acl2Numberp elimination

```lean
theorem acl2Numberp_elim (v : SExpr)
    (h : Logic.acl2Numberp v = SExpr.t) :
    ∃ n : Number, v = .atom (.number n)
```

Needed to convert type-prescription results into structural facts
(e.g., `Logic.fix v = v` when `v` is a number).

### T18. Variable lookup (unbound case)

```lean
theorem evalOpt_var_unbound (w : World) (env : Env) (s : Symbol)
    (h : env.get? s = none) (h_not_t : s.isNamed "t" = false) :
    ∀ f, evalOpt (f+1) w env (.atom (.symbol s)) = some .nil
```

Handles variables not in env (evaluator returns .nil).

Total: ~24 theorems. T1 (congruence), T10 (induction), and T15
(variable substitution) provide the proof skeleton. Everything
else fills in specific steps.

## Key composition patterns

**Pattern A: Top-level rewrite chain.** Each top-level proof node
is a rewrite `lhs => rhs` where `lhs` is a subterm of the current
formula. Apply T1 to replace `lhs` with `rhs` in the formula.
Chain by transitivity. Final step uses T3 (equal-self).

**Pattern B: Definition expansion with children.** T4 unfolds the
call to body evaluation (in a new env with bindArgs). Children
justify simplifications WITHIN the body (IF resolution via T5,
recognizer via T13, etc.). Each child is a T1 application inside
the body. The overall effect: `eval(call) = eval(simplified-result)`.

**Pattern C: Rewrite rule with children.** The rule gives
`eval(lhs) = eval(rule-rhs)`. Children further simplify `rule-rhs`
to the node's final `rhs`. Each child is T1+T8 (or T4, etc.).
Chain: `eval(lhs) = eval(rule-rhs) = eval(final-rhs)`.

**Pattern D: IH application.** T11 extracts the IH from the
negated clause literal. T2 converts EQUAL=T to an eval equality.
T1 applies the equality as a rewrite.

**Pattern E: Type-prescription.** T12 proves the function returns
a specific type. Used inside definition expansion (e.g., FIX
elimination needs `acl2-numberp(my-len y) = T`).

## Dependency graph and implementation sequence

The theorems form layers. Each layer depends only on previous
layers. The proof-producing checker applies them top-down (outer
layers first), but we PROVE them bottom-up (inner layers first).

### Layer 0: Pure infrastructure (no evalOpt)

These are facts about Logic.*, acl2Count, and fuel composition.
No dependency on evalOpt's structure. Can be proved independently.

- **T8**: Logic axioms (plus_comm, cdr_cons, fix_number, etc.)
- **T9**: fuel_join (∃ composition)
- **T13**: consp_cons (Logic.consp (.cons a b) = .t)
- **T10**: acl2_induction_consp (well-founded induction on acl2Count)

### Layer 1: evalOpt atomic steps

These are direct facts about evalOpt's behavior on specific term
shapes. Each follows from unfolding evalOptStep one level. They
need the `isNamed` kernel reducibility fix (already done).

- **T7**: evalOpt_quote, evalOpt_var
- **T5**: evalOpt_if_true, evalOpt_if_false
- **T6**: evalOpt_builtin
- **T4**: evalOpt_defn_expand

These are the HARDEST to prove because they fight evalOptStep's
big match cascade. But each is a one-time proof.

### Layer 2: evalOpt derived rules

These combine Layer 1 theorems into higher-level rules.

- **T3**: evalOpt_equal_self (uses T6 for EQUAL builtin + Logic.equal_self)
- **T2**: eval_equal_t_implies_eq (uses T6 for EQUAL + Logic.equal injectivity)
- **T11**: not_nil_means_truthy (uses T4/T5/T6 for NOT expansion)
- **T14**: evalOpt_macroExpand (if needed — uses Layer 1 structural reasoning)

### Layer 3: Congruence

- **T1**: evalOpt_replace_congr

Depends on: Layer 1 (needs to follow evalOpt's recursion pattern
for each case — IF, function call, builtin, quote, var).

This is the HARDEST theorem. It's proved by structural induction
on `term`, with cases mirroring evalOptStep. The IF case requires
showing that replacement in the untaken branch doesn't matter
(since evalOpt doesn't evaluate it).

### Layer 4: Per-theorem proofs (specific to simple.lisp)

These use Layers 0-3 to prove facts about the specific world.

- **T12**: my_len_returns_number (type-prescription — uses T10 for
  induction, T4/T5/T6/T8 for body analysis)
- **my_len_my_app**: the target theorem (uses T10 for induction,
  T1 for each rewrite step, T2/T11 for IH extraction, T3 to finish,
  T4/T5/T6/T8 for individual rewrites, T12 for type-prescription)

### Proposed implementation sequence

**Phase 1: Layer 0** — prove all pure infrastructure.
No evalOpt involved. Should be straightforward.

**Phase 2: Layer 1** — prove evalOpt atomic steps.
This is where we fight evalOptStep. Start with T7 (easiest),
then T5, then T6, then T4. Each one teaches us how to handle
the evalOptStep dispatch in proofs.

**Phase 3: Layer 2** — prove derived rules.
These compose Layer 1 pieces. Should be mechanical once Layer 1
works.

**Phase 4: T1 (congruence)** — the big proof.
We should attempt this AFTER Layers 1-2 so we understand the
evalOpt proof patterns. The congruence proof mirrors evalOptStep's
case analysis but additionally handles the "dead branch" issue
for IF (replacement in the untaken branch is harmless).

**Phase 5: Layer 4** — prove the actual theorem.
Assemble everything. This is the hand proof of my_len_my_app
that mirrors what the proof-producing checker would construct.

### Critical path

```
                T7 (quote/var)
                    ↓
T10 (induction) → T5 (IF) → T4 (defn expand)
    ↓                            ↓
T15 (var subst) ←——————— needed for env bridging
    ↓
T1 (congruence) ←—— both T1 and T15 induct on term
    ↓
T12 (type-presc) ← T4 + T5 + T10
    ↓
my_len_my_app ← T1 + T4 + T10 + T15 + T2 + T3 + T8 + T12
```

The THREE hardest theorems are:
- **T1** (congruence): structural induction on term, IF dead-branch handling
- **T15** (var substitution): structural induction on term, env manipulation
- **T10** (induction scheme): well-founded on acl2Count

T1 and T15 have similar proof structures (both induct on SExpr
term following evalOpt's recursion). They should be proved
together or one derived from the other.

**Risk mitigation:** If T1 is too hard, we can try the proof
WITHOUT congruence, using T15 directly: instead of "replace
subterm a with b in C[a]", prove the full-term equality
`eval(before) = eval(after)` by unfolding evalOpt far enough
using T4/T5/T6/T7 and T15. This is more verbose but avoids
the congruence abstraction. If this works, we can factor out
T1 later.

Similarly, if T15 is too hard in full generality, we can prove
specific instances for the simple.lisp world (where bodies only
use their formal parameters). This avoids the general case
(bodies with free variables referencing the surrounding env).
