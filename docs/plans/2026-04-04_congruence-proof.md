# Proof Strategy for T1: Congruence (Referential Transparency)

Created: 2026-04-04

## The theorem

**Informal statement**: evalOpt is referentially transparent. If two
subexpressions evaluate to the same value, replacing one with the
other in any context preserves the evaluation result.

**Formal statement (partial correctness)**:

Define partial-correctness equality:
```
pcEq : Option SExpr → Option SExpr → Prop
pcEq (some a) (some b) = (a = b)
pcEq _        _         = True
```

`none` is ⊤ — fuel exhaustion means "don't know", and "don't know"
trivially satisfies any equality. This is the Hoare-logic partial
correctness interpretation.

**The core theorem**:
```
theorem evalOpt_replace_pcEq (f : Nat) (w : World) (env : Env)
    (term a b : SExpr)
    (h_eq : ∀ g, pcEq (evalOpt g w env a) (evalOpt g w env b)) :
    pcEq (evalOpt f w env (replaceSubterm term a b))
         (evalOpt f w env term)
```

For ALL fuel levels `f`: if `a` and `b` are pcEq at every fuel,
then `replaceSubterm term a b` and `term` are pcEq.

**The existential version** (used in the proof chain) is derived:
```
theorem evalOpt_replace_congr (w : World) (env : Env)
    (term a b : SExpr)
    (h_eq : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (replaceSubterm term a b)
                 = evalOpt f w env term
```

Derivation: from the existential hypothesis + fuel monotonicity,
derive the pcEq hypothesis (at fuel < N both might be none which
is pcEq; at fuel ≥ N both converge to the same value which is
pcEq). Then apply the core theorem. At fuel ≥ N, both sides of
the conclusion converge (by monotonicity), so pcEq gives actual
equality.

## Why pcEq eliminates the double induction

Without pcEq, we'd need `∃ N, ∀ f ≥ N, eval f (replace term) = eval f term`.
This requires threading existential fuel through the structural
induction on `term`, taking max at each composition point. The
fuel dimension and term dimension interact.

With pcEq, the theorem holds at EVERY fuel level. At fuel 0, both
sides are `none`, so pcEq is trivially True. At fuel f+1, we
unfold one step of evalOpt and use the IH at fuel f. The structural
induction on term is now INSIDE the fuel case, not interleaved with
it.

## replaceSubterm definition

```
def replaceSubterm (term a b : SExpr) : SExpr :=
  if term == a then b
  else match term with
  | .cons (.atom (.symbol q)) rest =>
    if q.isNamed "quote" then term
    else .cons (.atom (.symbol q)) (replaceSubterm rest a b)
  | .cons x y =>
    let x' := replaceSubterm x a b
    if x' != x then .cons x' y
    else .cons x (replaceSubterm y a b)
  | _ => term
```

Key properties:
- Head symbols of function calls are NOT replaced (only args)
- QUOTE bodies are NOT entered
- For symbol-headed cons: recurses into the argument spine only
- For non-symbol cons: tries left first, then right (first occurrence)

## Proof structure

The proof is by induction on fuel `f`.

**Base case (f = 0)**: `evalOpt 0 = none` for everything. Both sides
are `none`. `pcEq none none = True`. Done.

**Inductive step (f → f+1)**: `evalOpt (f+1) = evalOptStep (evalOpt f)`.
Case split on whether `term == a`:

**Case term == a**: `replaceSubterm term a b = b`. Need `pcEq (evalOpt (f+1) w env b) (evalOpt (f+1) w env a)`. This is `pcEq_symm (h_eq (f+1))`. Done.

**Case term ≠ a**: Case split on term structure.

### Subcase: term is nil, atom, or quote

`replaceSubterm` returns `term` unchanged. `pcEq_refl`. Trivial.

### Subcase: term = .cons (.atom (.symbol q)) rest, q ≠ "quote"

`replaceSubterm` gives `.cons (.atom (.symbol q)) (replaceSubterm rest a b)`.

`evalOptStep` dispatches on `q`:

**q = "if"**: `rest.toList?` should give `[c, t, e]`.
- Original: `evalOpt f w env c >>= fun cv => if toBool cv then evalOpt f w env t else evalOpt f w env e`
- Modified: the replacement is in `rest`, which is the spine `.cons c (.cons t (.cons e .nil))`.
  `replaceSubterm rest a b` modifies one of c, t, or e.

  Subcase: replacement is in `c` (first element of spine).
  Then modified `c' = replaceSubterm c a b`, rest unchanged.
  - `evalOpt f w env c'` pcEq `evalOpt f w env c` (by IH on `c` at fuel `f`).
  - If both converge: same cv, same branch taken, same result.
  - If one doesn't converge: bind produces none, pcEq True.

  Subcase: replacement is in `t` or `e` (later in spine).
  - `c` is unchanged, so same cv, same branch taken.
  - The taken branch has the replacement: IH gives pcEq.
  - The untaken branch might have the replacement: doesn't matter,
    it's never evaluated.

**q = "let" / "let*"**: Similar structure. Bindings are evaluated
sequentially. Replacement in one binding: IH gives pcEq, subsequent
bindings see the same env (because pcEq of some = equal values).

**q is a function name**: `rest.toList?` gives args.
`args.mapM (evalOpt f w env)` evaluates each arg.
- Replacement in one arg: that arg pcEq's (IH).
- If all args converge: same argVals (pcEq of some = equal).
- Dispatch to body with same argVals: same result.
- If any arg doesn't converge: mapM returns none. pcEq True.

### Subcase: term = .cons x y, non-symbol head

`evalOptStep` for non-symbol-headed cons returns `some .nil`.
`replaceSubterm` modifies x or y, but evalOpt ignores the
structure (just returns nil). So both sides return `some .nil`.
pcEq trivially.

Wait — actually evalOptStep only matches `.cons (.atom (.symbol s)) args`.
For `.cons x y` where `x` is not `(.atom (.symbol _))`, it falls
through to `| _ => some .nil`. So both original and modified return
`some .nil`. pcEq holds.

## Key helper lemmas needed

### pcEq is a congruence for Option.bind

```
theorem pcEq_bind (x y : Option SExpr) (f g : SExpr → Option SExpr)
    (h_xy : pcEq x y)
    (h_fg : ∀ v, pcEq (f v) (g v)) :
    pcEq (x.bind f) (y.bind g)
```

More precisely: if `x pcEq y`, and `f v pcEq g v` for all `v`,
then `x.bind f pcEq y.bind g`. This handles the monadic structure
of evalOptStep.

Actually we need a slightly different version: if `x pcEq y` and
whenever `x = some v` we have `f v pcEq g v`, then:
```
theorem pcEq_bind' (x y : Option SExpr) (f g : SExpr → Option SExpr)
    (h_xy : pcEq x y)
    (h_fg : ∀ v, x = some v → pcEq (f v) (g v)) :
    pcEq (x.bind f) (y.bind g)
```

This is needed because the IF branch function depends on the
test value — we need `f v pcEq g v` only when both sides converge
to the SAME `v`.

### pcEq for mapM

```
theorem pcEq_mapM (args1 args2 : List SExpr) (f : SExpr → Option SExpr)
    (h : ∀ i, pcEq (f (args1.get! i)) (f (args2.get! i))) :
    pcEq (args1.mapM f) (args2.mapM f)
```

Or more precisely, for our case where the function is the same
but the argument list has one element replaced:

```
theorem pcEq_mapM_replace ...
```

Actually this might not be needed. The argument list `rest` is a
SPINE (cons chain), not a `List`. The replacement is in the spine
itself. When `evalOptStep` does `rest.toList?` and then `args.mapM`,
the replacement in the spine becomes a replacement in one element
of the list. We need to show `mapM` over the modified list pcEq's
with `mapM` over the original list.

### toList? preserves replacement structure

If `rest.toList? = some args` and `(replaceSubterm rest a b).toList? = some args'`,
then `args'` differs from `args` in at most one element, and that
element is `replaceSubterm (args[i]) a b` for some `i`.

This connects the spine-level replacement to the list-level
replacement needed for the `mapM` argument.

## Estimated complexity

- pcEq infrastructure (refl, symm, bind, mapM): ~30 lines
- Base case (f=0): 1 line
- Case term==a: 3 lines
- Nil/atom/quote cases: 3 lines each
- IF case: ~40 lines (test replacement, branch replacement, untaken branch)
- LET case: ~30 lines (sequential binding evaluation)
- Function call case: ~30 lines (mapM over args, dispatch to body)
- Non-symbol cons case: ~5 lines
- Derivation of existential version: ~15 lines

Total: ~170 lines

## Critical fix: replaceSubterm must preserve spine structure

The original replaceSubterm recursed on the raw cons spine:
```
| .cons (.atom (.symbol q)) rest =>
    .cons (.atom (.symbol q)) (replaceSubterm rest a b)
```

This allows replacing SPINE FRAGMENTS — e.g., replacing
`.cons t (.cons e .nil)` (a tail of the IF argument list) with
an arbitrary `b`. This breaks arity: `(IF c t e)` becomes `(IF c b)`
where `b` might not even be a proper 2-element list. The congruence
theorem is FALSE with the old replaceSubterm.

**Counterexample**: `term = (IF (QUOTE T) 42 NIL)`, `a = .cons 42 (.cons NIL .nil)`,
`b = .nil`. Both `a` and `b` evaluate to `.nil`. Replacement gives
`(IF (QUOTE T))` (wrong arity) → evalOptStep returns `.nil` default.
But the original returns `42`. `pcEq (some .nil) (some 42)` is False.

**Fix**: replaceSubterm now uses `replaceArgs` for symbol-headed
conses, which recurses into INDIVIDUAL arguments while preserving
the spine structure. This ensures `toList?` on the modified spine
always gives the same-length list as the original.

## Open questions

1. **Does the IH have the right shape?** Induction on fuel gives
   IH at fuel `f` for all terms. But we also need structural IH
   on the term (the replacement in a sub-spine). Do we need
   induction on BOTH fuel and term, or can fuel induction alone
   work because evalOptStep only calls evalOpt at fuel `f` (one
   less)?

2. **The toList? interaction**: When `replaceSubterm` modifies the
   spine `.cons c (.cons t (.cons e .nil))`, does `toList?` of the
   modified spine give the right list? `toList?` is structural, so
   modifying one element should give a list with that element
   modified. But we need to verify this.

3. **The IF branch selection**: When the test `c` is replaced by
   `c' = replaceSubterm c a b`, and `evalOpt f c pcEq evalOpt f c'`,
   does the same IF branch get taken? If both converge to the same
   `cv`, yes. If one doesn't converge, the whole IF returns none.
   But what if `c` converges and `c'` doesn't (or vice versa)?
   Then one side returns `cv.bind (branch)` and the other returns
   `none.bind (branch) = none`. pcEq is True. Fine.

4. **The function body evaluation**: After mapM gives the same
   argVals, the body is evaluated at fuel `f` in `bindArgs formals argVals`.
   Since argVals is the same, the body evaluation is identical.
   No replacement happens in the body — the replacement was in the
   args. So this is just reflexivity.
