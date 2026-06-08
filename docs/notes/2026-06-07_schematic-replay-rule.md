# The schematic-replay design rule

**Date:** 2026-06-07
**Status:** rule + enforcement + rework plan. The current `my-len-my-app` replay
(`ACL2Lean/Imported/SimpleWorld.lean`) is sorry-free but VIOLATES this rule; the
violations are tagged inline `⚠ NON-SCHEMATIC`. This note is the spec the rework
must satisfy.

## The rule

> The eventual replay **driver** is a fixed, deterministic function from a proof-
> tree node `(rune, lhs, rhs, subst, children)` **together with the proof context
> Γ in scope at that node** to a Lean proof term. Each node is replayed by a
> **fixed per-rune procedure** that applies *that rune's rule*, lifted by
> congruence, possibly consuming facts from Γ — using ONLY: the rune's rule, the
> subst, the facts in Γ, and global world facts. It may NOT improvise a per-node
> justification by computing concrete values and matching them, nor invoke a fact
> that is in none of those sources (e.g. "functionality").

### The four legitimate sources of facts at a node

1. **The rune's rule** — the definition equation / imported lemma / recognizer.
2. **The subst** σ logged at the node.
3. **The proof context Γ** — the constructed set of facts available at that node,
   built by *introducing facts as the driver descends subtrees*: case-split
   assumptions (e.g. `¬(consp x)` in the base subgoal, `(consp x)` in the step
   subgoal), the **induction hypothesis** (introduced at the induction node; the
   tree links the `solidify` node to it explicitly), and **type-alist facts**
   (`type-prescription`, the recognizer/type runes the tree cites). In the Lean
   proof Γ *is* the local hypothesis context at that point; the driver builds it
   by `intro`-ing/deriving facts along the path from the root.
4. **Global world facts** — each defined function is total (admission ⇒ converges),
   and the imported lemmas (with their proven value-equalities).

A fact that is in NONE of these (e.g. a function's value being determined by its
argument value — "functionality") may not be used. The IH and type facts are NOT
violations — they are Γ facts (3); functionality IS a violation.

Why this is forced, not stylistic: the mirror theorem is **universally quantified**
(symbolic `x`, `y`; induction on an arbitrary value `xv`). There is no concrete
value to compute — a proof must reason about arbitrary values, i.e. by rule
application. ACL2's proof *is* term rewriting (apply rune R at subst σ); the
faithful replay of "node tagged R" is "apply R's equation," full stop.

### Per-rune procedures (the driver's dispatch table — the spec to build against)

| Rune / node kind | Schematic replay (produces `eval(before) = eval(after)`) | Side-conditions it may consume |
|---|---|---|
| `:DEFINITION fn`, args = variables | unfold via `substTerm` (identity subst) → `eval(fn args) = eval(body)` | totality of `fn` (converges to SOME value) |
| `:DEFINITION fn`, args compound | **eventual `substTerm` unfold lemma** (NOT YET BUILT) → `eval(fn args) = eval(substTerm formals args body)` | totality of args |
| recognizer (`consp`, `acl2-numberp`, …) | builtin step lemma → `eval(consp t) = some (consp tv)` | arg converges to SOME value |
| if-simplification | `evalOpt_if_true/false` on the (converged, truthy/nil) test | test converges |
| with-lemma `L` (cdr-cons, commutativity, unicity-0, …) | apply `L`'s **proven value-equality** (`logic_cdr_cons`, `logic_plus_comm`, `logic_plus_comm2_int`, …) at subst σ, lifted by congruence | operands converge to SOME value; for arithmetic, to SOME **int** (`type-prescription`) |
| rewriting-equivalence / solidify (IH) | convert the IH `P(σ)` to goal-env terms via the `substTerm` substitution lemma, then `eval_equal_t_implies_eq` → the IH *is* the eval-equality | (none beyond the IH) |
| `equal-self` | `evalOpt_equal_self` | subterm converges to SOME value |
| `:executable-counterpart` / ground eval | compute (this is the one rune where computing a value IS the fixed procedure) | — |

Values stay **existential** ("converges to some [int] value") for every rule-
application rune; only the eval-rune computes. Congruence lifting
(`evalOpt_congr_unary/_binary_left/_right`) carries a node's eval-equality up
through its context — already schematic and reusable.

## How to enforce it (red-flag checklist)

Positive test: every fact a node consumes must come from one of the four sources
(rune's rule / subst / context Γ / global world facts). A node proof is
**non-schematic** (stop and rework) if any of these hold:

1. It names a value witness and threads it through `fuel_eq_of_conv (lhs → v)
   (rhs → v) …` — i.e. it computes both sides to `v` and matches, instead of
   applying the rune's eval-equality lemma to the *terms*.
2. It invokes a fact in NONE of the four sources — notably a **functionality**
   fact (value determined by argument value), `h_mylen_fn` / `h_myapp_fn`. (NB:
   the **IH** and **type-prescription** are NOT violations — they are Γ facts;
   **totality** is a global world fact. The driver applies rules and consumes Γ;
   it never needs a function's specific value, only Γ/world facts about it.
   Cross-route value identities come from the substitution lemma — which is how
   the driver constructs a Γ fact like the IH in the current node's env.)
3. It does integer/arithmetic bookkeeping (`k_rv = kc + ky`) to discharge a node
   whose rune is a rewrite rule, not arithmetic.
4. The justification doesn't mention the node's rune's rule at all (e.g. cdr-cons
   discharged without `logic_cdr_cons`).

Operationally: the eventual driver should be written as the dispatch table above,
and the hand proof should be expressible as "for each tree node, call the
dispatch entry for its rune." If a node's hand proof can't be phrased that way,
it's non-schematic.

## Rework plan (to make `my-len-my-app` schematic)

Order chosen so each step is checkable and the earlier ones unblock the later.

1. **Build the schematic with-lemma eval-equality lemmas** (driver vocabulary),
   each `(operands converge) → eval(op-before) = eval(op-after)` proved via the
   imported value-lemma + `conv_builtin*` + congruence, operands existential:
   `re_cdr_cons`, `re_plus_comm`, `re_plus_comm2` (int, consumes type-prescription).
2. **Build the eventual compound-arg `substTerm` unfold lemma** (the genuinely
   new piece): `(fn defined, body closed+LET-free, args converge) →
   eval(fn args) = eval(substTerm formals args body)`, via an *eventual* version
   of `evalOpt_substTerm_eq` (agreement at fuel ≥ N + body-depth). No
   functionality; values existential.
3. **Rework the IH solidify (`node4c`)**: substitution lemma converts `ih` at
   `e.insert x (cdr xv)` to the goal-env IH literal; `eval_equal_t_implies_eq`
   yields the eval-equality directly. Delete the `k_rv = kc + ky` arithmetic.
4. **Rework `node2b` cdr-cons** to `re_cdr_cons`; **`node4a/4b`** to
   `re_plus_comm`/`re_plus_comm2`; **`node1/node3`** unfolds to `substTerm` +
   recognizer + if; **`node2a`** to the eventual unfold lemma; **`node5`** to
   totality + equal-self.
5. **Delete `h_mylen_fn` and `h_myapp_fn`** from the generic theorem and the final
   theorem; keep only `h_mylen_int` (type-prescription, existential int) and add a
   **totality** fact (converges to SOME value) where convergence is needed. These
   remain consumed ACL2 facts to discharge later (the type-prescription corollary
   + the admissions).
6. Re-run the adversarial review **with the driver-schematic dimension** (point a
   reviewer at this dispatch table and have it refute "every node = its dispatch
   entry"). Re-verify axioms clean.

The base case gets the same treatment (it already avoids functionality; its
`node3` unicity-0 + fix-elimination also waits on `fix`-as-defined, task #24).

## Already done (dead code from the value-computation framing — deleted)

Removed from `EvalLemmas.lean` (unused, sorried, superseded): the entire generic
`replaceSubterm` / `pcEq` / `pcEqG` / `EvalCtx` / `evalOpt_ctx_pcEq` /
`evalOpt_replace_*` "T1 congruence" cluster; the `substVar` / `evalOpt_substVar`
value-substitution layer; the general sorried `logic_plus_comm2` /
`logic_plus_zero_left` / `callBuiltin_fix_number`. `EvalLemmas.lean` is now
sorry-free.
