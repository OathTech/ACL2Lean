# Soundness Experiment Findings

Created: 2026-03-24

## What we built

1. **`EvalOpt.lean`**: Option-returning evaluator (`none` = fuel exhaustion). Structurally identical to `eval` but distinguishes "ran out of fuel" from "returned nil." This fixes the fuel conflation that made `∀ f, eval f lhs = eval f rhs` false at intermediate fuel levels. 18 smoke tests passing.

2. **`evalReplaceOpt` / `evalReplace`** (in `Rewriter.lean`): Eval-aware replacement function that:
   - Skips inside QUOTE bodies (eval doesn't traverse them)
   - Never replaces the head symbol (eval dispatches on it, doesn't evaluate it)
   - Recurses into both car (arguments) and cdr (argument list spine) for non-symbol-headed cons cells

3. **`RewriterSoundness.lean`**: Core soundness theorem + composition:
   - `evalReplace_sound`: If `∀ f, evalOpt f lhs = evalOpt f rhs`, then `evalOpt fuel (evalReplace term lhs rhs) = evalOpt fuel term`
   - `applyEvalRewriteStep_sound`: Single-step wrapper
   - `applyEvalRewriteSteps_sound`: Multi-step composition via fold

## What's proved (no sorry)

- Nil and atom base cases of `evalReplace_sound`
- Whole-term match case (term == lhs → use hypothesis)
- QUOTE case (no replacement → trivial)
- Single-step wrapper (`applyEvalRewriteStep_sound`)
- The proof generalizes fuel via `suffices ∀ f, ...` so the IH applies at any fuel level

## What's sorry'd (the hard parts)

### 1. Function-call argument congruence

When `term = (.cons (.atom (.symbol s)) argsExpr)` and replacement happens inside `argsExpr`:

**Goal**: `evalOpt f w env (.cons (.atom (.symbol s)) args') = evalOpt f w env (.cons (.atom (.symbol s)) argsExpr)` where `args'` is `argsExpr` with one subterm replaced.

**Challenge**: `evalOpt` processes `argsExpr` via `argsExpr.toList?` then maps `evalOpt` over each element. The IH gives `evalOpt f w env (evalReplace argsExpr lhs rhs) = evalOpt f w env argsExpr`, but `argsExpr` as a standalone term evaluates differently than its role as an argument list.

**What's needed**: A congruence lemma connecting `evalReplaceOpt`'s cons-cell recursion through the argument list with `evalOpt`'s `toList? + map` processing. Specifically: if `evalReplaceOpt argsExpr = some args'`, then `args'.toList?` has the same length as `argsExpr.toList?` and each element either is unchanged or evaluates the same (by the IH).

**Estimated difficulty**: Medium. Requires a structural lemma about `evalReplaceOpt` preserving list structure, plus a `List.map` congruence. Maybe 50-100 lines.

### 2. Non-symbol-headed cons

When `term = (.cons a b)` where `a` is NOT `.atom (.symbol _)`:

**Challenge**: `evalOpt` returns `some .nil` for such terms (they're malformed ACL2 terms). But if replacement in `a` changes it from a cons to a symbol atom, `evalOpt` of the new term dispatches differently.

**What's needed**: Either:
- (a) Show this case never arises for well-formed ACL2 terms (practical but not general)
- (b) Add a precondition that `evalReplaceOpt` preserves the "head kind" (symbol/non-symbol)
- (c) Restrict `evalReplaceOpt` to not recurse into the car of non-symbol-headed cons (but this breaks deep argument traversal)

**Estimated difficulty**: This is a real soundness issue, not just a proof gap. Option (a) is the pragmatic path: define "well-formed term" (all function calls have symbol heads) and add it as a precondition. All real ACL2 terms satisfy this.

## Key architectural insights

1. **`evalOpt` (Option return) is essential.** Without it, `∀ f, eval f lhs = eval f rhs` fails at intermediate fuel. With Option, `none = none` at insufficient fuel makes the universal quantification work.

2. **The replacement function must mirror eval's dispatch structure.** Naive `replaceFirst` (recurse everywhere) is unsound at QUOTE bodies and head-symbol positions. The replacement function needs to know which positions eval actually evaluates.

3. **The argument-list congruence is the mathematical core.** eval processes arguments via `toList? + map`, but the replacement recurses via cons-cell structure. Bridging these two views is the main proof obligation.

4. **The proof generalizes over fuel.** By proving `∀ f, ...` and inducting on term structure, the IH applies at any fuel level. This sidesteps the fuel-decrement mismatch (eval uses `fuel - 1` for subterms).

5. **Well-formedness matters.** The non-symbol-headed cons case reveals that `evalReplace_sound` is not true for ALL SExpr — only for well-formed terms where function heads are always symbols. This is fine practically (all ACL2 terms are well-formed) but means the theorem needs a well-formedness precondition or the replacement function needs further restriction.

## Remaining sorry inventory

| Lemma | Status | Estimated size | Description |
|-------|--------|---------------|-------------|
| `evalReplaceOpt_toList` | sorry | 30-50 lines | Structural: evalReplaceOpt preserves toList? structure |
| `evalReplace_sound` cons case | sorry | 20-30 lines | Uses above two lemmas to close the function-call congruence |
| `evalReplace_sound` non-symbol case | sorry | 10-20 lines | Needs well-formedness precondition or restricted recursion |
| `applyEvalRewriteSteps_sound` cons case | sorry | 5 lines | Blocked by sorry propagation; will work once core is proved |
| `evalOpt_some_eq_eval` | sorry | 30-50 lines | Bridge to original eval (needed for final theorem statements) |

## Next steps

1. **Prove `evalReplaceOpt_toList`** — the key remaining structural lemma
2. **Close the function-call congruence** using the two helper lemmas
3. **Handle well-formedness** for the non-symbol-headed case (add precondition or restrict recursion)
4. **Demonstrate on simple.lisp** — prove per-step justifications using rune interpreters
5. **Prove `evalOpt_some_eq_eval`** to connect back to the original `eval`

## Updated 2026-03-24

Proved `mapM_evalOpt_congr` (no sorry): pointwise eval-equivalent lists
give the same result under mapM. This is one of the two lemmas needed
for the function-call congruence case.
