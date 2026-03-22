# Plan: Verified ACL2 Rewriter — Staged Implementation

Created: 2026-03-22

## Background

ACL2 is a theorem prover for a Lisp-like language. This project imports
ACL2 theorems into Lean 4 with kernel-checked proofs, so Lean users can
leverage ACL2's proof automation.

The project previously attempted a "tactic replay" approach: translate
ACL2 functions to Lean functions (operating on SExpr), then replay
ACL2's proof steps as Lean tactics (simp, rw, unfold). This hit
fundamental walls:
- ACL2's `Logic.plus` on SExpr expands to intractable rational arithmetic
  that `simp` can't handle
- Recursive definitions loop when used as simp rules
- Context-aware IF resolution (ACL2's key mechanism) has no clean tactic
  equivalent

See `docs/plans/2026-03-22_simple-example-walkthrough.md` for the
concrete failure analysis on `simple.lisp`.

The new approach: keep ACL2 definitions as SExpr DATA (not Lean
functions), build a verified rewriter in Lean that replays ACL2's proof
trace directly on SExpr terms, and prove the rewriter sound against an
interpreter.

## Architecture

```
ACL2 source (.lisp)
    │
    ├──▶ ACL2 prover (untrusted) ──▶ proof trace (.proof-log)
    │
    └──▶ World generator ──▶ World definition + theorem statements (.lean)
                                         │
                                         ▼
                              Verified rewriter (replays trace)
                                         │
                                         ▼
                              Kernel-checked proof (no sorry)
                                         │
                                         ▼
                              User bridges to their own Lean types
```

## Key Design Decisions

**ACL2 definitions are SExpr data, not Lean functions.** Previous
approach translated `(defun my-len (x) (if (consp x) ...))` into a
Lean `def my_len (x : SExpr) : SExpr := if toBool (consp x) then ...`.
New approach stores the body as an SExpr value in a World environment.
An `eval` function interprets it.

**The theorem statement uses `eval`.** An imported theorem says:
"for all variable bindings, evaluating this formula in this World
produces T." Example:
```lean
theorem my_len_my_app (env : Env) :
    eval fuel simpleWorld env formulaSExpr = SExpr.t
```

**The rewriter operates on SExpr directly.** No translation gap — the
proof trace from ACL2 contains SExpr terms, and the rewriter
manipulates SExpr terms. No name mapping, no syntax mismatch.

**Trust analysis.** The only trusted component is the Lean kernel.
Everything else — eval, rewriter, soundness proof, proof trace,
correspondence lemmas — is untrusted proof machinery. A bug anywhere
causes a type error, never a false theorem.

## The Working Example: simple.lisp

```lisp
(defun my-len (x) (if (consp x) (+ 1 (my-len (cdr x))) 0))
(defun my-app (x y) (if (consp x) (cons (car x) (my-app (cdr x) y)) y))
(defthm my-len-my-app (equal (my-len (my-app x y)) (+ (my-len x) (my-len y))))
```

The proof trace (from `acl2_samples/simple.proof-log`, viewable with
`python3 scripts/audit-proof-trace.py acl2_samples/simple.proof-log`)
shows:
- Induction on `(MY-APP X Y)` → 2 subgoals
- Base case (¬consp x): unfold MY-APP→Y, unfold MY-LEN→0, arithmetic
  simplification 0+n=n, reflexivity
- Step case (consp x, with IH): unfold MY-APP and MY-LEN, use IH,
  commutativity of +

The end-to-end goal: a Lean user proves
`myLength (myAppend xs ys) = myLength xs + myLength ys` using this.

## Existing Codebase

The project is a Lean 4 Lake project at the repo root.

**Key files (preserved in new design):**

| File | Lines | Contents |
|------|-------|----------|
| `ACL2Lean/Syntax.lean` | 665 | `SExpr` inductive type (nil/atom/cons), `Atom`, `Symbol`, `Number`, `Event` (defun/defthm/etc), `World` (has `defs : HashMap Symbol (List Symbol × SExpr)`), `TheoremInfo` |
| `ACL2Lean/Parser.lean` | 331 | S-expression parser: `parseAll : String → Except String (List SExpr)`. Handles comments, quoting, keywords, numbers, package-qualified symbols. Keywords are lowercased, symbols are lowercased. |
| `ACL2Lean/ProofLog.lean` | 383 | Proof trace types: `RewriteStep` (rune + lhs + rhs as SExpr), `ProofStep` (clauseId, processor, result, runes, rewrites, newClauses), `InductionStep`, `ProofEvent` (defthm/step/induction/qed), `ProofLog`. Parser: `ProofLog.parse` finds `(:BEGIN-PROOF-LOG)` marker and parses all events. Also has tactic generation code that will be replaced. |
| `ACL2Lean/Logic.lean` | 518 | ACL2 primitive operations on SExpr: `toBool`, `if_`, `car`, `cdr`, `cons`, `consp`, `equal`, `plus`, `minus`, `times`, `lt`, etc. Also simp lemmas like `car_cons`, `cdr_cons`. These will be used by the `eval` function for built-in dispatch. |
| `ACL2Lean/Evaluator.lean` | 212 | Current ACL2 evaluator: `partial def eval (w : World) (env : Env) (expr : SExpr) : EvalM SExpr`. Handles variable lookup, IF, QUOTE, LET, function calls (lookup in World, bind formals, recurse), built-ins. Uses `Except String`. Logic will be reused in total evaluator. |
| `ACL2Lean/Count.lean` | 137 | `acl2Count : SExpr → Nat` structural size measure. `acl2Count_cdr_lt_of_consp` lemma for termination. Used for function termination and will be useful for induction. |
| `scripts/capture-proof-log.sh` | 41 | Runs ACL2 with `(set-raw-proof-format :structured)`, captures output. Usage: `./scripts/capture-proof-log.sh file.lisp` |
| `scripts/audit-proof-trace.py` | ~230 | Pretty-prints proof traces with indentation for literal boundaries and branch nesting. Usage: `python3 scripts/audit-proof-trace.py file.proof-log [theorem-name]` |
| `acl2_samples/books.txt` | — | Manifest of ACL2 books to test. Referenced by Justfile targets. |

**Key files (will be modified/replaced):**

| File | Current role | New role |
|------|-------------|----------|
| `ACL2Lean/Translator.lean` (461 lines) | Generates Lean functions from ACL2 defs | Replace with World generator: emit `World` data + theorem statements |
| `ACL2Lean/Tactics.lean` (83 lines) | `acl2_simp`, `acl2_induct`, `acl2_grind` | Replace with `acl2_replay` driving the verified rewriter |
| `Main.lean` (243 lines) | CLI commands | Add `gen-world` command |

**ACL2 submodule** (`acl2/`, branch `acl2-lean-output`): Modified ACL2
that emits structured proof output via `(set-raw-proof-format :structured)`.
Outputs `(:STEP ...)`, `(:INDUCTION ...)`, `(:QED)`, `(:DEFTHM ...)`,
`(:BEGIN-PROOF-LOG)`. Each `:STEP` includes `:INPUT-CLAUSE`,
`:NEW-CLAUSES`, `:RUNES`, and a `:REWRITES` field with detailed events:
- `(:REWRITE-STEP :RUNE r :LHS lhs :RHS rhs)` — individual rewrite
- `(:IF-TEST-TRUE/FALSE/UNKNOWN :TEST t :UNREWRITTEN-TEST ut :JUSTIFICATION j)`
- `(:BEGIN-LITERAL :INDEX n :LITERAL lit :NOT-FLG f)` / `(:END-LITERAL ...)`
- `(:CASE-SPLIT :LITERAL-INDEX n :NUM-BRANCHES k)`
- `(:BEGIN-BRANCH :SEGMENT seg)` / `(:END-BRANCH)`
- `(:REWRITTEN-LITERAL :ORIGINAL o :RESULT r)`
- Processor-specific: `:ELIM-SEQUENCE`, `:FERTILIZE`, `:GENERALIZE`

Build ACL2: `cd acl2 && make LISP=sbcl` (requires SBCL installed).

**Build system:** `lake build` (Lean), `just build-acl2` (ACL2),
`just capture-all-logs` (proof traces), `just translate-all` (current
translator — will change).

## Stage 1: Total evaluator

**Goal:** A total `eval` function on SExpr that defines ACL2 semantics.

**Why first:** Everything depends on this — the theorem statements, the
soundness proofs, and the bridge lemmas are all stated in terms of eval.

**What to build:**
- `eval (fuel : Nat) (w : World) (env : Env) (term : SExpr) : SExpr`
- Total (not `partial def`), using a fuel parameter for termination
- Returns `SExpr.nil` on fuel exhaustion (safe default — makes
  theorems slightly weaker but keeps eval total)
- Handles: variable lookup, function application (lookup in World,
  substitute formals, recurse with fuel-1), IF (eval test, branch),
  QUOTE, and built-in primitives (EQUAL, CONSP, CAR, CDR, CONS,
  BINARY-+, BINARY-*, UNARY--, UNARY-/, NOT, IF, etc.)
- For built-ins, delegate to the existing `Logic.*` functions where
  possible (e.g., `Logic.car`, `Logic.plus`)

**What to reuse:**
- `Evaluator.lean` has the dispatch logic — restructure to be total
- `Syntax.lean` `World` type (has `defs` field mapping names to
  (formals, body) pairs)
- `Logic.lean` primitive implementations

**Key design choice:** The `Env` maps variable symbols to SExpr values.
When calling a user-defined function, eval creates a new env binding
formals to evaluated actuals, then evaluates the body.

**Milestone:** `eval 1000 simpleWorld {x ↦ .nil, y ↦ .nil} formula`
reduces to `SExpr.t` (testable via `#eval` or `#guard`).

**File:** `ACL2Lean/Eval.lean` (new, ~200 lines)

## Stage 2: World generator

**Goal:** Produce `World` definitions and theorem statements from ACL2
source.

**Why second:** Need the World to state theorems and test the evaluator.

**What to build:**
- A command `lake exe acl2lean gen-world file.lisp` that outputs a
  `.lean` file containing:
  - `def world : ACL2.World := ...` with all defun bodies as SExpr
    data (using the `#acl2` or `SExpr.ofList` constructors)
  - For each defthm: `theorem name (env : ACL2.Env) : ACL2.eval fuel world env formula = SExpr.t := sorry`
- The formula SExpr is the raw ACL2 theorem body, stored as SExpr data
- Use `Parser.parseAll` to read the .lisp file, `Event.classify` to
  identify defuns and defthms

**What to reuse:**
- `Parser.lean`, `Syntax.lean` (Event classification)
- `Translator.sanitizeName` for Lean-safe identifiers

**Note on SExpr construction:** The generated file needs to construct
SExpr values. Options: use the `#acl2 { }` DSL macro (in `ACL2Lean/DSL/`),
or generate explicit `SExpr.cons (SExpr.atom ...) ...` constructors.
The DSL is cleaner if it supports the needed forms.

**Milestone:** Generated file for `simple.lisp` compiles with `sorry`s.

**File:** `ACL2Lean/WorldGen.lean` (new, ~150 lines), modify `Main.lean`

## Stage 3: Rewriter core

**Goal:** A function that applies proof trace steps to SExpr terms.

**What to build:**
- `applyStep (w : World) (step : TraceEvent) (term : SExpr) : SExpr`
- Handle the trace event types from `ProofLog.lean`:
  - `REWRITE-STEP` with rune type `"definition"` — look up the function
    in the World, match the call pattern in `term`, substitute actuals
    for formals in the body
  - `REWRITE-STEP` with rune type `"rewrite"` — the trace gives us LHS
    and RHS; find LHS as a subterm of `term`, replace with RHS
  - `IF-TEST-TRUE` — find `(IF test then else)` where `test` matches,
    replace with `then`
  - `IF-TEST-FALSE` — replace with `else`
  - `BEGIN-LITERAL` / `END-LITERAL` — track which clause literal is
    being processed (structural, not a rewrite)
  - `CASE-SPLIT` / `BEGIN-BRANCH` / `END-BRANCH` — track proof tree
    structure
- `applySteps (w : World) (steps : List TraceEvent) (term : SExpr) : SExpr`
  chains steps sequentially
- SExpr pattern matching / subterm replacement utilities

**Important:** The rewrite trace contains the exact LHS that was
rewritten (as an SExpr). The rewriter finds this LHS in the term and
replaces it. This is direct structural matching on SExpr — no
unification needed for the simple cases. For rewrite rules with
variables, pattern matching with variable binding is needed.

**What to reuse:**
- `ProofLog.lean` types (`RewriteStep`, etc.)
- `Syntax.lean` SExpr operations (`toList?`, etc.)

**Milestone:** `applySteps simpleWorld traceSteps formula` produces
`SExpr.t` for the base case of `my-len-my-app`. Testable via `#eval`.

**File:** `ACL2Lean/Rewriter.lean` (new, ~300 lines)

## Stage 4: Soundness proof

**Goal:** Prove that each rewriter step preserves eval semantics.

**Core theorem:**
```lean
theorem applyStep_sound (fuel : Nat) (w : World) (env : Env)
    (step : TraceEvent) (term : SExpr) :
    eval fuel w env (applyStep w step term) = eval fuel w env term
```

This says: evaluating the rewritten term gives the same result as
evaluating the original term (for sufficient fuel).

**What to prove per step type:**

1. **Definition unfolding:** When `(f a1 ... an)` is replaced by
   `body[x1:=a1, ..., xn:=an]` where `f` is defined with formals
   `(x1 ... xn)` and body `body`:
   - `eval fuel w env (f a1 ... an) = eval (fuel-1) w {x1↦eval(a1), ...} body`
   - This is essentially the definition of how `eval` handles function calls

2. **Rewrite rule application:** If we have a previously proved theorem
   `∀ env, eval fuel w env lhs = eval fuel w env rhs`, then replacing
   `lhs` with `rhs` at any position in a term preserves eval.
   - Need a congruence lemma: eval respects subterm replacement

3. **IF resolution:** `eval fuel w env (IF test then else)` equals
   `eval fuel w env then` when `eval fuel w env test` is truthy, and
   `eval fuel w env else` when it's falsy.
   - This follows directly from how `eval` handles IF

4. **Chain:** If each step preserves eval, chaining them does too.

**Key concern:** The fuel parameter. Theorems need to hold for
"sufficient fuel." The simplest approach: quantify over all fuel ≥ some
threshold, or show that if eval terminates with some fuel, the equality
holds for all greater fuel.

**Milestone:** Soundness theorem compiles. Combined with Stage 3:
```lean
theorem my_len_my_app (env : Env) :
    eval fuel simpleWorld env formula = SExpr.t := by
  have chain := applySteps_sound fuel simpleWorld env baseTraceSteps
  -- chain : eval fuel w env formula = eval fuel w env SExpr.t
  simp [eval] at chain  -- eval of T is T
  exact chain
```
(for the base case; inductive case needs Stage 5)

**File:** `ACL2Lean/Rewriter.lean` (extend, ~300 lines of proofs)

## Stage 5: Induction

**Goal:** Handle induction in ACL2 proof traces.

ACL2 proofs typically begin with induction. The trace's `(:INDUCTION
:TERM (MY-APP X Y) :SUBGOAL-COUNT 2 :SCHEME ...)` tells us which
function's recursion pattern to follow.

**What to build:**
- An induction principle for cons-list recursion on SExpr:
  ```lean
  theorem cons_induction (P : SExpr → Prop)
    (hbase : ∀ x, toBool (consp x) ≠ true → P x)
    (hstep : ∀ x, toBool (consp x) = true → P (cdr x) → P x)
    : ∀ x, P x
  ```
  Justified by `acl2Count` decreasing on `cdr`.

- For multi-argument induction (like `MY-APP` which recurses on first
  arg), the induction is on the first argument with the second as a
  parameter. The trace tells us which variables are inducted on.

- After induction, the trace gives separate rewrite chains for each
  case. The rewriter processes each case independently.

**Milestone:** Complete proof of `my_len_my_app` — no sorry. Both
base and inductive cases handled.

**File:** `ACL2Lean/Rewriter.lean` (extend, ~100 lines)

## Stage 6: Bridge library and user-facing proof

**Goal:** A Lean user can prove theorems about their own types using
ACL2 results.

**What to build:**

Standard encoding functions:
```lean
def SExpr.ofList : List SExpr → SExpr  -- already exists in Syntax.lean
def SExpr.ofNat : Nat → SExpr          -- .atom (.number (.int n))
def SExpr.toNat? : SExpr → Option Nat  -- inverse
```

Bridge lemmas (one-time, reusable):
```lean
theorem eval_equal_iff : eval fuel w env (EQUAL a b) = SExpr.t ↔
    eval fuel w env a = eval fuel w env b

theorem eval_plus_nat (n m : Nat) :
    eval fuel w env (BINARY-+ (ofNat n) (ofNat m)) = ofNat (n + m)

theorem ofNat_injective : ofNat n = ofNat m → n = m
```

Correspondence lemma pattern (per user-function pair):
```lean
-- "Evaluating MY-LEN on an encoded list gives the encoded length"
theorem myLength_eval (xs : List SExpr) :
    eval fuel simpleWorld {X ↦ ofList xs} myLenTerm = ofNat (myLength xs)
```

These are proved by structural induction on the list — straightforward
and independent of ACL2 proof machinery.

**Milestone:** Complete end-to-end:
```lean
theorem myLength_myAppend (xs ys : List SExpr) :
    myLength (myAppend xs ys) = myLength xs + myLength ys
```
proved using the ACL2 theorem + correspondence + injectivity. No sorry.

**File:** `ACL2Lean/Bridge.lean` (new, ~200 lines)

## Stage 7: Automation and scaling

**Goal:** Run the pipeline on the sorting corpus.

**What to build:**
- `acl2_replay` tactic or elaborator that, given a World and proof
  trace, produces the Lean proof automatically
- Extend the world generator to handle `include-book` (multi-file books)
- Justfile target: `just replay-all` processes all books in manifest

**Milestone:** All 7 standalone sorting corpus files produce
kernel-checked proofs. No sorry anywhere.

**File:** `ACL2Lean/Tactics.lean` (rewrite), pipeline in scripts

## Summary

| Stage | Deliverable | Depends on | Est. size |
|-------|------------|------------|-----------|
| 1 | Total evaluator | — | ~200 lines |
| 2 | World generator | Stage 1 | ~150 lines |
| 3 | Rewriter core | Stage 1 | ~300 lines |
| 4 | Soundness proof | Stages 1, 3 | ~300 lines |
| 5 | Induction | Stages 3, 4 | ~100 lines |
| 6 | Bridge library | Stages 1, 4, 5 | ~200 lines |
| 7 | Automation | All above | ~200 lines |

**First win condition (Stages 1-5):** `my_len_my_app` from `simple.lisp`
proved in Lean with no sorry, driven by ACL2's proof trace.

**User-facing win (Stage 6):** A Lean user proves a theorem about their
own List/Nat functions using the ACL2 result.

**Scaling win (Stage 7):** Entire sorting corpus imported automatically.

## What gets discarded

- `Translator.translateDefun` / `translateDefthm` / `translateExpr` —
  replaced by World generator
- `Tactics.lean` `acl2_simp` / `acl2_induct` / `acl2_grind` — replaced
  by `acl2_replay`
- Tactic generation code in `ProofLog.lean` (`generateTacticScript`,
  `rewriteStepToTactic`, `stepToTactics`, etc.)
- `ACL2Lean/Imported/SimpleExample.lean` — was a design exploration,
  superseded by the new approach

## What is preserved

- `Syntax.lean` — SExpr, Atom, Symbol, World, Event (all of it)
- `Parser.lean` — s-expression parser (all of it)
- `ProofLog.lean` — proof trace types and parser (keep types + `parse`;
  remove tactic generation)
- `Count.lean` — acl2Count measure (used for induction)
- `Logic.lean` — ACL2 primitives (used by eval for built-in dispatch)
- `Evaluator.lean` — logic reused in total evaluator
- `Lexorder.lean`, `TermOrder.lean` — preserved, independent
- ACL2 submodule — structured proof output (all of it)
- `scripts/` — capture-proof-log.sh, audit-proof-trace.py
- `acl2_samples/` — test corpus and book manifest
- `Justfile` — build targets (some modified)
