# ACL2Lean Soundness Audit

**Date:** 2026-03-20

Audit of the ACL2Lean translation pipeline for soundness bugs, semantic gaps,
and other issues that could undermine the goal of using Lean as a trust anchor
for ACL2 theorem replay.

---

## Critical Soundness Issues

### 1. `sorry` in Lexorder Antisymmetry and Transitivity

**Files:** `Lexorder.lean:209`, `Lexorder.lean:225`

`lexorder_antisym` and `lexorder_trans` are proved with `sorry`. These are
**load-bearing** for the correctness of all sorting theorems. Every translated
sort (isort, msort, qsort, bsort) uses `lexorder` via `orderedp`, and the
`ordered_perms` theorem — the master bridge proving "two ordered permutations
are equal" — depends on these ordering properties. If `lexorder` weren't
actually antisymmetric or transitive, the entire sorting equivalence argument
collapses.

`lexorder_refl` and `lexorder_total` are fully proved, so the ordering
infrastructure is partially there. The remaining two properties need proofs.

**Risk:** High. These are implicit axioms in the trusted base.

### 2. `let` Not Handled in Batch Translator

**File:** `Translator.lean:118-177`

`translateExpr` has no case for `let` or `let*`. ACL2 code using `let` bindings
falls through to the generic function-call path, generating a call to an
undefined function `let_`. The DSL (`DSL.lean`) handles `let` correctly, but the
batch translator (`Translator.lean`) does not.

Any ACL2 book containing `let` expressions in function bodies or theorem
statements will produce broken Lean output.

**Risk:** High. Silent mistranslation of any `let`-using code.

### 3. `case` Translation Doesn't Handle List Keys

**File:** `Translator.lean:82-94`

ACL2 `case` allows a list of keys: `((sym1 sym2) val)` matches if the test
equals any key in the list. The translator only handles single-symbol keys.
Multi-key case clauses would be silently dropped or misinterpreted, producing
wrong function bodies.

**Risk:** High for any ACL2 code using multi-key case branches.

### 4. Missing `TopExt.lean` Dependency

**File:** `Translated/Qsort.lean:9`

`Qsort.lean` imports `ACL2Lean.Translated.TopExt` but this file doesn't exist
in the repo. This means the Qsort module can't compile.

**Risk:** Build blocker for the qsort path.

### 5. Duplicate Theorem Names Across Translated Files

**Files:** `Translated/OrderedPerms.lean`, `Translated/TermOrderedPerms.lean`

Both files define top-level theorems named `equal_cons`, `car_rm`, and
`true_listp_rm`. Since both are imported transitively (via the Equisort chain),
these will cause name collisions.

**Risk:** Build blocker when both files are imported together.

### 6. Rational/Decimal Arithmetic Silently Wrong

**File:** `Logic.lean:19-22`

```lean
def toInt (s : SExpr) : Int :=
  match s with
  | .atom (.number (.int n)) => n
  | _ => 0
```

`toInt` maps rationals and decimals to 0. This means `(+ 1/2 1/2)` evaluates
to `0` instead of `1`. The `div` function (Logic.lean:45-50) does produce
rational results, but subsequent arithmetic on those results silently treats
them as 0.

Any ACL2 theorem involving rational arithmetic will have incorrect semantics
in the Lean model.

**Risk:** High for any rational-arithmetic corpus; low for the current
integer-only sorting corpus.

### 7. Bitwise Operations Wrong on Negative Numbers

**File:** `Logic.lean:197-219`

`logand`, `logor`, `logxor` convert to `Nat` via `toNat` (which clamps
negatives to 0), then use `Nat.land`/`Nat.lor`/`Nat.xor`. ACL2 uses
two's-complement semantics for bitwise operations on negative integers.

Meanwhile, `lognot` (Logic.lean:209-210) correctly uses the algebraic
formula `-(n) - 1`, creating an internal inconsistency: `logand (lognot x) x`
should be 0 for all integers, but the implementation computes
`logand 0 x = 0` only because `lognot` returns a negative which `logand`
clamps to 0 — giving the right answer for the wrong reason.

**Risk:** High for any bitwise-arithmetic corpus.

### 8. `expt` Placeholder for Negative Exponents

**File:** `Logic.lean:148-152`

```lean
def expt (a b : SExpr) : SExpr :=
  ...
  if y < 0 then .atom (.number (.int 0)) -- Placeholder
  else ...
```

ACL2's `(expt r i)` with negative `i` returns `1/(r^|i|)` as a rational.
The current implementation returns 0.

**Risk:** Medium. Any theorem involving negative exponents has wrong semantics.

### 9. `qsort`, `no_dups_qsort`, and `bsort` Are `partial`

**Files:** `Translated/Qsort.lean:20`, `Translated/NoDupsQsort.lean:12`,
`Translated/Bsort.lean:34`

These are marked `partial` because the translator couldn't prove termination.
In Lean, `partial` defs are opaque — the kernel won't unfold them. This
introduces hidden axioms into the system. Theorems about these functions rely
on `sorry` and can never be kernel-checked by unfolding.

For `qsort`/`no_dups_qsort`: termination requires showing that `filter`
reduces list length. For `bsort`: termination requires the `bnext_size`
measure.

**Risk:** Medium. These are axiomatic functions; proving their theorems
requires additional trust beyond the Lean kernel.

---

## Moderate Issues

### 10. `cond` with Multi-Expression Bodies

**File:** `Translator.lean:97-113`

ACL2 `cond` clauses can have implicit `progn` bodies: `((test body1 body2))`
should evaluate to `body2` (the last expression). The translator only handles
`(test val)` pairs (exactly 2 elements per clause). Multi-body cond clauses
are silently mishandled.

**Risk:** Medium. Depends on whether the ACL2 corpus uses this feature.

### 11. `string_append` Returns `nil` for Non-Strings

**File:** `Logic.lean:191-194`

ACL2's `string-append` has a guard requiring string arguments; on guard
violation it returns `""` (the empty string), not `nil`. The Lean
implementation returns `nil` for non-string inputs, which is a semantic
mismatch.

**Risk:** Low for the sorting corpus; relevant if string-heavy ACL2 code is
imported.

### 12. Symbol Comparison in `lexorder` May Diverge from ACL2

**File:** `Lexorder.lean:30-34`

`lexorder` compares symbols using Lean's `String.<` (lexicographic Unicode
ordering). ACL2 uses `symbol-<` which compares by `symbol-name` then
`symbol-package-name` using character code ordering. These could differ for
non-ASCII symbols.

Additionally, `lexorder` compares raw `name` fields while the rest of the
system normalizes to lowercase via `normalizedName`. If two symbols differ
only in case, `lexorder` sees them as different even though the rest of the
translation treats them as identical.

**Risk:** Medium. Could cause ordering divergence on edge-case symbols.

### 13. `eq` More Permissive Than ACL2's `eq`

**File:** `Logic.lean:57-58`

Both `eq` and `equal` are implemented as structural equality on `SExpr`. In
ACL2, `eq` is restricted to symbols (it's pointer equality with a guard). The
Lean `eq` succeeds on non-symbol comparisons where ACL2 would have a guard
violation. Theorems using `eq` might be provable in the Lean model that
wouldn't hold in ACL2 with guard checking.

**Risk:** Low. ACL2 theorems typically use `equal`.

### 14. Top-Level Namespace Pollution in Translated Code

All translated functions (`insert`, `filter`, `rm`, `memb`, `merge2`, etc.)
are emitted at the top level with `open ACL2 ACL2.Logic`. These can shadow
Lean builtins or conflict across translated files.

**Risk:** Low-medium. Becomes a problem as more books are translated.

---

## Minor / Cosmetic Issues

### 15. `toBool` Docstring Is Backwards

**File:** `Logic.lean:8`

The docstring says "everything except nil is **falsy**" but the implementation
returns `true` for non-nil (i.e., everything except nil is **truthy**). The
code is correct; the docstring is wrong.

### 16. N-ary Folding Direction

**File:** `Translator.lean:62-66`

`foldNary` right-folds: `(+ a b c)` becomes `(plus a (plus b c))`. ACL2
desugars `+` left-to-right via `binary-+`. For integers this is equivalent.
For `and`/`or` the short-circuit semantics also happen to match because the
Lean implementations are strict. No observable difference in practice but
technically a deviation from ACL2's evaluation order.

---

## Recommendations

**Priority 1 — Trust base integrity:**
- Prove `lexorder_antisym` and `lexorder_trans` (or explicitly mark them as
  accepted axioms with documentation)
- Add `let`/`let*` handling to `Translator.translateExpr`
- Add multi-key `case` clause support to `translateCaseClauses`
- Create `Translated/TopExt.lean` stub or remove the import from Qsort
- Namespace the translated output (e.g., `namespace Sorting`) to avoid
  duplicate theorem names

**Priority 2 — Semantic correctness:**
- Implement rational arithmetic (at minimum, `toRational` alongside `toInt`)
- Fix bitwise ops to use two's-complement semantics
- Fix `expt` for negative exponents
- Make `qsort`/`bsort` total with well-founded measures instead of `partial`

**Priority 3 — Robustness:**
- Fix `string_append` to return `""` on non-strings
- Normalize symbol case in `lexorder` to match the rest of the system
- Fix the `toBool` docstring
- Handle multi-body `cond` clauses
