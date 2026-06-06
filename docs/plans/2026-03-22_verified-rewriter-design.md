# Design: Verified ACL2 Rewriter in Lean

Created: 2026-03-22

## The Goal

A Lean user has their own functions:
```lean
def myLength : List α → Nat := ...
def myAppend : List α → List α → List α := ...
```

They want to prove `myLength (myAppend xs ys) = myLength xs + myLength ys`.

ACL2 already proved the analogous theorem on cons-lists. We want to
import that proof so the user can leverage it.

## The Approach

ACL2 definitions stay as SExpr data — they are never translated into
Lean control flow. An interpreter gives them meaning. A verified
rewriter replays ACL2's proof trace on SExpr terms. The imported
theorem is stated in terms of the interpreter. The user bridges to
their own types.

## Concrete Walkthrough: simple.lisp

### What ACL2 proved

```lisp
(defun my-len (x) (if (consp x) (+ 1 (my-len (cdr x))) 0))
(defun my-app (x y) (if (consp x) (cons (car x) (my-app (cdr x) y)) y))
(defthm my-len-my-app (equal (my-len (my-app x y)) (+ (my-len x) (my-len y))))
```

### What we produce in Lean

#### Part 1: The ACL2 world (definitions as SExpr data)

ACL2 function definitions are stored as data, not compiled to Lean
functions. They live in a `World` — an environment mapping function
names to (formals, body) pairs.

```lean
def myLenBody : SExpr :=
  sexpr! (if (consp x) (binary-+ (quote 1) (my-len (cdr x))) (quote 0))

def myAppBody : SExpr :=
  sexpr! (if (consp x) (cons (car x) (my-app (cdr x) y)) y)

def simpleWorld : World := {
  defs := { "my-len" ↦ ([X], myLenBody), "my-app" ↦ ([X, Y], myAppBody) }
}
```

#### Part 2: The theorem statement

ACL2's `defthm` proves that a formula holds for all values of its free
variables. The imported theorem says: evaluating the formula in the
ACL2 world yields T for any binding of the free variables.

```lean
def myLenMyAppFormula : SExpr :=
  sexpr! (equal (my-len (my-app x y)) (binary-+ (my-len x) (my-len y)))

theorem my_len_my_app (env : Env) :
    eval simpleWorld env myLenMyAppFormula = .ok SExpr.t
```

The quantification over all `env : Env` captures universality — the
formula holds regardless of what `x` and `y` are bound to. (ACL2
theorems are valid for all values of free variables.)

#### Part 3: How the proof works

The verified rewriter replays the ACL2 proof trace:

```lean
theorem my_len_my_app (env : Env) :
    eval simpleWorld env myLenMyAppFormula = .ok SExpr.t := by
  apply acl2_verified_replay simpleWorld myLenMyAppFormula proofTrace
```

Where `proofTrace` is the parsed ACL2 proof trace, and
`acl2_verified_replay` is a function proved sound once:

1. It processes the trace structure (induction, per-case rewrites)
2. For each rewrite step, the soundness theorem guarantees the
   rewrite preserves evaluation semantics
3. The chain reduces the formula to T
4. The Lean kernel checks the soundness proof

#### Part 4: How the user bridges to their own types

The user wants to connect their Lean functions to the ACL2 theorem.
They need:

- An encoding from their types to SExpr: `encode : List Nat → SExpr`
- Correspondence lemmas showing their functions match the ACL2 ones
  under encoding

```lean
-- Encoding
def encode : List Nat → SExpr
  | [] => .nil
  | n :: ns => .cons (.atom (.number (.int n))) (encode ns)

-- Correspondence: evaluating MY-LEN on encoded input = encoded myLength
theorem myLength_eval (xs : List Nat) :
    eval simpleWorld {X ↦ encode xs} (sexpr! (my-len x))
    = .ok (encode (myLength xs))

-- Correspondence: evaluating MY-APP on encoded inputs = encoded myAppend
theorem myAppend_eval (xs ys : List Nat) :
    eval simpleWorld {X ↦ encode xs, Y ↦ encode ys} (sexpr! (my-app x y))
    = .ok (encode (myAppend xs ys))
```

These are straightforward structural inductions — they just verify
that the Lean function and the ACL2 definition compute the same thing.
No ACL2 proof machinery needed.

With these, the user proves their theorem:

```lean
theorem myLength_myAppend (xs ys : List Nat) :
    myLength (myAppend xs ys) = myLength xs + myLength ys := by
  -- 1. Get the ACL2 result for encoded inputs
  have h := my_len_my_app {X ↦ encode xs, Y ↦ encode ys}
  -- h says: eval(EQUAL (MY-LEN (MY-APP X Y)) (+ (MY-LEN X) (MY-LEN Y))) = T

  -- 2. Rewrite using correspondence lemmas
  -- eval(EQUAL a b) = T  ↔  eval(a) = eval(b)
  -- eval(MY-LEN (MY-APP ...)) = encode (myLength (myAppend xs ys))
  -- eval(+ (MY-LEN X) (MY-LEN Y)) = encode (myLength xs + myLength ys)

  -- 3. By injectivity of encode, extract the Nat equality
  -- encode (myLength (myAppend xs ys)) = encode (myLength xs + myLength ys)
  -- → myLength (myAppend xs ys) = myLength xs + myLength ys
  sorry -- mechanical: correspondence lemmas + encode injectivity
```

## What Needs To Be Built

### Already exists
- `SExpr` type (Syntax.lean)
- `eval` interpreter (Evaluator.lean) — needs cleanup but core is there
- Proof trace parser (ProofLog.lean)
- ACL2 structured output (acl2 submodule)

### Needs to be built

1. **Verified rewriter** — a function that applies a trace step to an
   SExpr term and returns the rewritten term. Must handle:
   - Definition unfolding: replace `(f args)` with body, substituting
     actuals for formals
   - Rewrite rule application: match LHS pattern, apply substitution,
     produce RHS
   - IF branch resolution: given that test evaluates to T or NIL,
     simplify `(IF test then else)` to the appropriate branch

2. **Soundness proof** — prove the rewriter preserves evaluation
   semantics. One-time verification cost, by case analysis on trace
   event type.

3. **Induction handler** — the proof trace starts with induction. Need
   to establish induction principles for functions defined by recursion
   on cons-lists in the SExpr world.

4. **Standard bridge library** — correspondence lemmas for common types:
   - `List ↔ cons-list`
   - `Nat ↔ integer atom`
   - `Bool ↔ T/NIL`
   - `encode` injectivity
   - `eval(EQUAL a b) = T ↔ eval(a) = eval(b)`
   - `eval(BINARY-+ a b) = encode(decode(a) + decode(b))`

5. **Top-level tactic** — `acl2_replay` that orchestrates: parse the
   trace, run the rewriter, apply soundness, produce the kernel-checked
   proof.

## Trust Analysis

The only trusted component is the Lean kernel. The entire ACL2
machinery — SExpr, eval, rewriter, soundness proof, proof trace,
correspondence lemmas, encoding — is untrusted. It is all just
proof-producing code whose output the kernel checks.

The user sees one thing: a Lean theorem statement about their own
functions and types. If it typechecks, it's correct. How it was
proved (ACL2 trace replay, verified rewriter, correspondence lemmas)
is irrelevant to its validity.

A bug anywhere in the pipeline — wrong interpreter, broken rewriter,
bad trace, incorrect correspondence lemma — results in a type error,
never a false theorem.

## Comparison with Current Tactic Approach

| Aspect | Tactic approach | Verified rewriter |
|--------|----------------|-------------------|
| Representation | Hybrid: Lean control flow on SExpr | Pure SExpr data + interpreter |
| Per-theorem effort | Generate tactic sequence | Feed trace to rewriter |
| Arithmetic | Need simp lemmas for each ACL2 rule | Rewriter implements rules directly |
| IF resolution | Need hypothesis manipulation tactics | Rewriter handles natively |
| Definition unfolding | `unfold` + `simp` (loops on recursion) | Rewriter substitutes directly |
| Naming issues | Must map ACL2 names to Lean names | No — works on SExpr directly |
| Trust base | Logic.lean + many simp lemmas | SExpr + eval (smaller) |
| Upfront cost | Low (but hits walls) | Higher (build + verify rewriter) |
| Per-theorem cost | High (fragile tactic generation) | Low (mechanical trace replay) |

## Open Questions

1. **How does induction work in the rewriter?** ACL2's induction is
   structural on cons-lists. In Lean, we need an induction principle
   for "functions defined by recursion on cons-lists" in the SExpr
   world.

2. **Is `eval` partial or total?** The current evaluator uses `partial
   def` with `Except`. For the soundness proof, we may need a total
   version (with a fuel/step parameter), or work within the monad.

3. **How big is the soundness proof?** Each trace event type needs a
   soundness lemma. Definition unfolding: "substituting actuals for
   formals and evaluating = evaluating the call." Rewrite rules: "if
   the rule is a proved equality, then applying it preserves
   evaluation." IF resolution: "if the test evaluates to T/NIL, then
   the IF evaluates to the appropriate branch." These are individually
   small but there are several.

4. **Can we bootstrap?** The soundness proof itself may need reasoning
   about SExpr. If the base lemmas are hard, we'd prove them manually
   first, then use the rewriter for more complex proofs.
