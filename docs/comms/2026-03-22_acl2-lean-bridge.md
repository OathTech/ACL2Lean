# ACL2-to-Lean Bridge: Importing ACL2 Theorems with Kernel-Checked Proofs

## Motivation

ACL2 has decades of verified libraries and powerful automation for
first-order reasoning about recursive functions. Lean 4 has a growing
ecosystem and an independently checkable kernel — a small trusted core
that verifies every proof term. We want to connect them: use ACL2 as a
proof-search oracle, then independently verify its results in Lean's
kernel.

The ACL2 proof is never trusted — it guides Lean to reconstruct a
kernel-checked proof. A bug anywhere in the bridge produces a type
error, never a false theorem.

This gives ACL2 users a path to make their results available in the
Lean ecosystem, and gives Lean users access to ACL2's mature
automation without extending their trusted base.

## Architecture

The system has three components:

1. **ACL2 (untrusted)** proves theorems and emits a structured proof
   trace describing exactly what it did — which rules it applied, in
   what order, to which subterms, and how it resolved conditionals.

2. **A verified rewriter in Lean** consumes the trace and replays the
   proof on ACL2's native term representation (s-expressions). The
   rewriter is proved sound against an ACL2 interpreter also
   implemented in Lean.

3. **A bridge library** lets Lean users connect the imported ACL2
   theorem (stated over s-expressions) to their own Lean types and
   functions.

```
  ACL2 book (.lisp)
       │
       ├──▶ ACL2 prover ──▶ proof trace
       │
       └──▶ Lean world generator ──▶ definitions + theorem statements
                                              │
                                    verified rewriter (replays trace)
                                              │
                                    kernel-checked Lean proof
                                              │
                                    user bridges to native Lean types
```

An earlier approach translated ACL2 functions directly to Lean
functions and replayed proofs as tactic sequences. This hit fundamental
limitations with ACL2's arithmetic reasoning and context-aware IF
resolution, motivating the current interpreter-based design.

## The Proof Trace

We have instrumented ACL2's prover to emit a machine-parseable proof
trace. When `(set-raw-proof-format :structured)` is active, ACL2
outputs pure s-expressions describing every reasoning step:

- **Waterfall steps** with input and output clauses
- **Individual rewrites** with rule name, LHS, and RHS
- **Definition expansions** with the call and expanded result
- **IF branch decisions** — whether each conditional was resolved true,
  false, or left unknown, with the original test expression
- **Case-split structure** — branch markers showing the proof tree

This is not a summary — it is a step-by-step record of the rewriter's
decisions, sufficient to mechanically reproduce the proof.

The trace has been tested on the ACL2 sorting textbook corpus (~60
inductions, ~900 waterfall steps across the 7 standalone files that
produce substantive proofs).

**Current scope:** The trace captures the simplifier, destructor
elimination, generalization, cross-fertilization, and induction. It
does not yet cover type-prescription reasoning details, BDD-based
proofs, clause processors, or tau-system reasoning. These could be
added as needed for books that use them. An unsupported proof technique
causes a hard failure — there is no silent fallback.

## The Verified Rewriter (In Design)

The proof trace instrumentation is complete. The verified rewriter is
the next phase, currently in detailed design. The target architecture:

- **An ACL2 interpreter** in Lean that gives meaning to s-expression
  terms — a total recursive evaluator over the `SExpr` type (with a
  fuel parameter for termination), dispatching on built-in functions
  and looking up user definitions in a world environment.

- **A rewriter** that takes a proof trace step and applies it to an
  s-expression term — unfolding a definition, applying a rewrite rule,
  or resolving a conditional branch.

- **A soundness theorem** proving that each rewriter step preserves
  evaluation semantics: if `eval(term) = v`, then
  `eval(rewrite(step, term)) = v`.

The soundness proof is checked by Lean's kernel. The rewriter, the
interpreter, and the ACL2 proof trace are all untrusted — a bug in
any of them causes a type error, never a false theorem.

## User-Facing Interface

The imported ACL2 theorem is stated over s-expressions:

```lean
-- ACL2's (defthm my-len-my-app ...)
-- becomes:
theorem my_len_my_app (env : Env) :
    eval simpleWorld env myLenMyAppFormula = SExpr.t
```

A Lean user who wants to use this with their own `List` functions
writes correspondence lemmas showing their definitions agree with the
ACL2 ones under an encoding. These are structural inductions,
independent of the ACL2 proof machinery.

The ACL2 function definitions in the Lean `World` must faithfully
transcribe what ACL2 defined. An error here produces a correct but
useless theorem — sound, but about the wrong functions.

## Current Status

**Complete:**
- Proof trace instrumentation, tested on the sorting corpus
- S-expression parser and proof log parser in Lean
- ACL2 submodule with structured output mode

**In design:**
- Verified rewriter and soundness proof
- Bridge library for common types

**First target:** `(defthm my-len-my-app ...)` from a simple textbook
example — end-to-end from ACL2 proof trace to kernel-checked Lean
theorem with no sorry.

## What We Would Like To Discuss

The proof trace is generated by modifications to ACL2's source (on a
branch of the ACL2 repository). The changes are additive — roughly 300
net lines across 8 files — and existing behavior is unaffected when
`:structured` mode is not active. The modifications touch `prove.lisp`,
`rewrite.lisp`, `simplify.lisp`, `induct.lisp`, `ld.lisp`,
`basis-a.lisp`, `defthm.lisp`, and `axioms.lisp`.

We would welcome discussion on:

- **Instrumentation approach.** Are there better hooks than modifying
  `rewrite-with-lemma` and `rewrite-fncall` directly? We are aware of
  `brr` and `dmr` but found they did not provide the per-step LHS/RHS
  data in a batch-processable form.

- **Trace completeness.** The trace does not yet capture
  type-prescription reasoning, tau-system reasoning, or BDD-based
  proofs. Are there other proof techniques used in practice that we
  should anticipate?

- **Upstreaming.** Is there interest in incorporating a version of the
  structured output mode into ACL2 proper? The changes are localized
  and the mode is opt-in.
