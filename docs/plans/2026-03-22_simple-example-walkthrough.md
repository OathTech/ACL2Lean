# Working Example: simple.lisp End-to-End

Created: 2026-03-22

## Goal

Demonstrate the complete pipeline: ACL2 proves a theorem, we import
it into Lean, and a Lean user can USE the result in their own proofs.

## The Example

ACL2 source (`simple.lisp`):
```lisp
(defun my-len (x) (if (consp x) (+ 1 (my-len (cdr x))) 0))
(defun my-app (x y) (if (consp x) (cons (car x) (my-app (cdr x) y)) y))
(defthm my-len-my-app (equal (my-len (my-app x y)) (+ (my-len x) (my-len y))))
```

The Lean user's code:
```lean
-- The user's own definitions (using normal Lean types)
def myLength : List α → Nat
  | [] => 0
  | _ :: xs => 1 + myLength xs

def myAppend : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

-- The user wants to prove:
theorem myLength_myAppend (xs ys : List α) :
    myLength (myAppend xs ys) = myLength xs + myLength ys
```

The question: how does the ACL2 proof of `my-len-my-app` help the Lean
user prove `myLength_myAppend`?

## The Three Layers

### Layer 1: ACL2 world (SExpr)

ACL2 operates on s-expressions. The functions `my-len` and `my-app`
operate on cons-list s-expressions. The theorem is:
```
∀ x y : SExpr, (equal (my-len (my-app x y)) (+ (my-len x) (my-len y))) = T
```

This is translated to Lean as:
```lean
-- SExpr versions (translated from ACL2)
def my_len (x : SExpr) : SExpr := ...
def my_app (x : SExpr) (y : SExpr) : SExpr := ...

theorem my_len_my_app (x y : SExpr) :
    Logic.toBool (Logic.equal (my_len (my_app x y))
                              (Logic.plus (my_len x) (my_len y))) = true
```

### Layer 2: The bridge

We need to connect the SExpr world to the Lean world. This means:

1. A way to convert between `List α` and `SExpr`
2. Proofs that `my_len` on SExpr corresponds to `myLength` on List
3. Proofs that `my_app` on SExpr corresponds to `myAppend` on List

```lean
-- Convert List Nat to SExpr (a proper cons-list of numbers)
def List.toSExpr : List Nat → SExpr
  | [] => .nil
  | n :: ns => .cons (SExpr.ofNat n) (List.toSExpr ns)

-- The correspondence lemmas:
theorem my_len_corresponds (xs : List Nat) :
    my_len (xs.toSExpr) = SExpr.ofNat (myLength xs)

theorem my_app_corresponds (xs ys : List Nat) :
    my_app (xs.toSExpr) (ys.toSExpr) = (myAppend xs ys).toSExpr
```

### Layer 3: The user's theorem

With the bridge, the user proves their theorem by:

```lean
theorem myLength_myAppend (xs ys : List Nat) :
    myLength (myAppend xs ys) = myLength xs + myLength ys := by
  -- 1. Use the correspondence lemmas to translate to SExpr
  -- 2. Apply the ACL2 theorem (which was proved via proof replay)
  -- 3. Translate back
  have h := my_len_my_app (xs.toSExpr) (ys.toSExpr)
  -- h : toBool (equal (my_len (my_app xs.toSExpr ys.toSExpr))
  --                    (plus (my_len xs.toSExpr) (my_len ys.toSExpr))) = true
  rw [my_app_corresponds] at h
  rw [my_len_corresponds] at h
  rw [my_len_corresponds] at h
  -- Now h connects myLength and myAppend via the SExpr encoding
  -- Extract the Nat equality from the SExpr equality
  ...
```

## What This Reveals About the Architecture

### The ACL2 theorem proof (Layer 1) is self-contained

The proof of `my_len_my_app` only needs:
- `SExpr` type and `Logic.*` operations
- The translated function definitions
- The proof replay from ACL2's trace

This is what we've been building. It doesn't need to know about the
user's types.

### The bridge (Layer 2) is per-use-case

Each user who wants to use ACL2 results needs correspondence lemmas
between their types and `SExpr`. This is NOT part of the automated
pipeline — it's written by the user (or by a separate tool).

However, for common cases (List, Nat, Bool), we can provide standard
bridges.

### The extraction (Layer 3) needs a general mechanism

Going from `Logic.toBool (Logic.equal a b) = true` to `a = b` (at the
SExpr level) and then to the Nat level requires:
- `Logic.equal_iff`: `toBool (equal a b) = true ↔ a = b`
- Injectivity of the encoding: `SExpr.ofNat n = SExpr.ofNat m → n = m`

## Results from Hand-Constructed Example

The file `ACL2Lean/Imported/SimpleExample.lean` demonstrates the full
pipeline. Key findings:

1. **`my_app_ofList` fully proved** — the correspondence between the
   SExpr append and Lean List append is provable by structural induction
   with `unfold` + `simp` on Logic primitives. No ACL2 help needed.

2. **`my_len_ofList` almost proved** — needs one lemma about `Logic.plus`
   and `SExpr.ofNat`: that `plus (ofNat 1) (ofNat n) = ofNat (1 + n)`.
   This is a one-time lemma about the SExpr number encoding.

3. **The bridge pattern works** — `rw [my_app_ofList, my_len_ofList]`
   transforms the ACL2 theorem into one about native Lean functions.

4. **Four sorrys remain:**
   - `my_len_my_app`: the ACL2 proof replay (the main challenge)
   - `my_len_ofList` cons case: needs `plus_ofNat` lemma
   - `equal_ofNat_iff`: needs equality reflection lemma
   - `myLength_myAppend`: the user's theorem (depends on all above)

The first sorry is the proof replay problem. The other three are
one-time library lemmas about the SExpr encoding.

## Attempt 1 Results: Direct Tactic Approach

Tried to prove `my_len_my_app` base case with `unfold` + `simp`:

**What worked:**
- `induction x using my_app.induct` — creates two cases correctly
- `unfold my_app` — expands the definition to an `if` expression
- `simp only [‹¬...›]` — resolves the `if` using the negated hypothesis
- The first two ACL2 steps (unfold my_app → y, unfold my_len → 0)
  can be replicated with `unfold` + `simp [h]`

**What broke:**
- After unfolding and simplifying, the goal has `plus 0 (my_len y)`.
  ACL2 simplifies this to `my_len y` using `UNICITY-OF-0`.
- In Lean, `Logic.plus` is implemented via rational arithmetic
  (`toRat`, `mkNumber`, cross-multiplication). `simp [Logic.plus]`
  expands into a massive term and can't simplify.
- We need `plus_zero_left : plus (int 0) x = x` (when x is numeric)
  but this requires reasoning about the rational implementation.

**Concrete wall:** ACL2's built-in arithmetic rules (UNICITY-OF-0,
COMMUTATIVITY-OF-+, FIX, etc.) operate at a high level. Our Lean
`Logic.plus` implements the low-level rational arithmetic. There's no
bridge between ACL2's "0 + x = x" and our implementation.

**Implication:** The tactic approach requires building a library of
simp lemmas about `Logic.*` that mirror ACL2's built-in rules:
- `plus_zero_left`, `plus_zero_right`
- `plus_comm`, `plus_assoc`
- `car_cons`, `cdr_cons` (these already exist)
- `consp_cons` (exists)
- `equal_refl` (exists)
- etc.

This is feasible but represents significant work — essentially
reproving ACL2's built-in theory in Lean. However, it only needs to
be done ONCE and then it's reusable for all proofs.

**Alternative:** The verified rewriter approach avoids this problem
entirely — it would implement the rules computationally and prove
soundness, rather than fighting with simp on the internal implementation.

## Design Option: Verified ACL2 Rewriter in Lean

Instead of translating ACL2 functions to Lean and then fighting with
tactics, implement ACL2's rewriter directly in Lean and verify it.

### Architecture

```
                    ACL2 (untrusted)
                         |
                    proof trace
                         |
                         v
    +------------------------------------------+
    |              Lean (trusted)               |
    |                                           |
    |  SExpr type         (data)                |
    |  ACL2 interpreter   (semantics)           |
    |  ACL2 rewriter      (replay mechanism)    |
    |  Soundness proof    (rewriter ⊆ interp)   |
    +------------------------------------------+
```

### Component 1: Interpreter (trusted semantics)

```lean
-- Already mostly exists in Evaluator.lean
def eval (env : Env) (term : SExpr) : SExpr
```

This defines what ACL2 terms MEAN. It's the trust anchor.

### Component 2: Rewriter (replay mechanism)

```lean
-- Takes a trace step and applies it to a term
def applyStep (env : Env) (step : TraceEvent) (term : SExpr) : SExpr
```

Steps include: definition unfolding, rewrite rule application,
IF branch resolution, substitution. Each corresponds to a trace event.

### Component 3: Soundness proof (one-time verification)

```lean
theorem applyStep_sound (env : Env) (step : TraceEvent) (term : SExpr) :
    eval env (applyStep env step term) = eval env term
```

### Important subtlety: open terms

The theorem `(equal (my-len (my-app x y)) (+ (my-len x) (my-len y)))`
has free variables `x` and `y`. The rewriter operates on OPEN terms —
it's doing symbolic simplification, not evaluation.

The soundness theorem must say: for all valuations of free variables,
the rewritten term has the same semantics as the original. This is:

```lean
theorem applyStep_sound (env : Env) (step : TraceEvent)
    (term : SExpr) (σ : Var → SExpr) :
    eval env (subst σ (applyStep env step term))
    = eval env (subst σ term)
```

Or equivalently, working with the term-level equality:

```lean
-- The rewriter produces a proof that lhs = rhs under the definitions
-- This is equivalent to: ∀ σ, eval(subst(σ, lhs)) = eval(subst(σ, rhs))
```

Actually, ACL2's rewrite rules are equalities: `(equal lhs rhs)`.
The rewriter applies these equalities to subterms. So the soundness
is really about preserving equality under substitution.

For the verified rewriter, the simplest approach might be:
- Represent the rewrite chain as a sequence of equations
- Each equation is justified by a definition or a previously proved theorem
- The chain proves the goal equation
- Soundness = each step preserves the equality

### Per-theorem proof

For `my-len-my-app`, the proof becomes:

```lean
theorem my_len_my_app :
    eval env (EQUAL (MY-LEN (MY-APP X Y)) (PLUS (MY-LEN X) (MY-LEN Y))) = T := by
  -- The trace gives us the rewrite chain
  -- applySteps reduces the term to T
  -- By soundness, eval of the original = eval of T = T
  exact rewriter_chain_sound env trace_steps
```

### The Bridge Question: Two Sub-Options

**Option A: Theorem about eval (simpler)**

The imported theorem is:
```lean
theorem my_len_my_app (x y : SExpr) :
    eval env (list 'EQUAL (list 'MY-LEN (list 'MY-APP x y))
                          (list 'BINARY-+ (list 'MY-LEN x) (list 'MY-LEN y)))
    = SExpr.t
```

This is directly about the interpreter. No translated Lean functions.
The user interacts with ACL2 terms via the interpreter.

To use this in a Lean proof about native types, the user would need:
1. Encode their data as SExpr
2. Show their function = eval on the corresponding ACL2 term
3. Apply the ACL2 theorem
4. Decode back

This is the "heavy bridge" approach — the user does more work.

**Option B: Theorem about translated functions (familiar)**

Keep the current translated functions (`my_len`, `my_app`) and prove
that they correspond to `eval`:

```lean
-- Automatically generated correspondence
theorem my_len_eval (x : SExpr) :
    my_len x = eval (env_with_my_len) (list 'MY-LEN x)

-- The ACL2 theorem, lifted to Lean functions
theorem my_len_my_app (x y : SExpr) :
    Logic.toBool (Logic.equal (my_len (my_app x y))
                              (Logic.plus (my_len x) (my_len y))) = true
```

The correspondence proof (`my_len_eval`) is mechanical — it just
unfolds both sides and shows they compute the same thing. It could
be generated automatically.

**Tradeoff:**
- Option A: Less code, but the theorem is about `eval` which is less
  natural for Lean users
- Option B: More code (correspondence proofs), but the theorem is
  about familiar Lean functions

**Key insight:** Option A avoids the translation entirely. The "imported
ACL2 theorem" is stated in terms of `eval`. If the user wants to use
it with their own types, THEY write the bridge. This is simpler for us
and more flexible for the user.

Option B is more polished but requires generating correspondence proofs
for every translated function. These proofs should be mechanical (both
sides compute the same thing on SExpr) but might be tricky for
recursive functions where termination arguments differ.

## What We Should Build First

**The proof of `my_len_my_app` in the SExpr world.** This is the hard
part — replaying ACL2's proof. The bridge and extraction are
straightforward once this works.

The hand-constructed example below shows what the complete picture
looks like, with `sorry` for the ACL2 proof replay and real proofs
for everything else.

## What the ACL2 proof replay needs to produce

For `my_len_my_app`, the ACL2 trace says:
1. Induction on `(MY-APP X Y)` → 2 cases
2. Base case (¬consp x): unfold my_app→y, unfold my_len→0, simplify 0+n=n
3. Inductive case (consp x): unfold my_app, unfold my_len, use IH,
   commutativity of +

In Lean, this translates to:
```lean
theorem my_len_my_app (x y : SExpr) :
    toBool (equal (my_len (my_app x y)) (plus (my_len x) (my_len y))) = true := by
  induction x using my_app.induct
  case case2 =>  -- base: ¬(consp x)
    -- unfold my_app: since ¬(consp x), my_app x y = y
    -- unfold my_len: since ¬(consp x), my_len x = 0
    -- goal: toBool (equal (my_len y) (plus 0 (my_len y))) = true
    -- simplify: plus 0 n = n, so equal (my_len y) (my_len y) = T
    sorry
  case case1 =>  -- step: (consp x), IH available
    -- unfold my_app: my_app x y = cons (car x) (my_app (cdr x) y)
    -- unfold my_len on LHS: my_len (cons ...) = 1 + my_len (my_app (cdr x) y)
    -- unfold my_len on RHS: my_len x = 1 + my_len (cdr x)
    -- use IH: my_len (my_app (cdr x) y) = my_len (cdr x) + my_len y
    -- arithmetic: 1 + (my_len (cdr x) + my_len y) = (1 + my_len (cdr x)) + my_len y
    sorry
```

The `sorry`s are what the proof replay fills in. Each one is a sequence
of `unfold`, `simp`, and `rw` steps guided by the trace.
