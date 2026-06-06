# Postmortem: proof-producer reset to `2f180d1` (2026-06-05)

**Audience: the next agent picking up Track B (proof replay). Read this first.**

## What happened (one paragraph)

On 2026-06-05 a large amount of proof-producer work was built and "validated"
against *synthetic, hand-authored* proof nodes and a hand proof whose step case
did not follow ACL2's actual proof. When it was finally run against the **real
reconstructed proof tree**, it replayed **zero** nodes, and was found to lack the
entire recursive driver layer. Rather than salvage it, `main` was reset to
`2f180d1` — the last pre-2026-06-05 commit: the trusted foundation plus an early
producer skeleton. All the discarded work is archived on
`origin/mdd/proof-producer` (tip `bfda555`).

## The single most important thing to internalize

**The ACL2 output we replay is a RECONSTRUCTED PROOF TREE, and it is
recursive/compositional — not a flat list, not independent nodes.**

`ProofLog.parse` → `buildAllTheoremProofs` produces:

```
TheoremProof   (has an induction scheme)
  └─ CaseProof        (a clause; the IH flows from the induction into the step case)
       └─ LiteralProof   (a CHAIN of top-level ProofNodes, composed by congruence
                          to transform the literal — nodes are NOT independent)
            └─ ProofNode  (rune, lhs, rhs, and recursive CHILDREN that justify
                          the rewrite — e.g. a `definition` node's `if-simplification`
                          and `recognizer` children)
```

Inspect the real thing before reasoning about it:
`lake exe acl2lean dump-proof-tree acl2_samples/simple.proof-log`.
NEVER reason from the flat `:REWRITE-STEP` log, and NEVER from hand-built
synthetic nodes — both mislead about real shapes and about how nodes compose.

## How it went wrong (so you don't repeat it)

1. The proof was modeled as flat/independent **three** times (flat log → synthetic
   nodes → "0 of 10 independent nodes"). It is a recursive tree.
2. The node handlers (recognizer / definition / rewrite / equal-self) were built
   and unit-tested **only on synthetic hand-authored `ProofNode`s with bare
   variables** — shapes that do not occur in real trees. Green synthetic tests
   gave false confidence.
3. The hand proof of `my_len_my_app`: the BASE case faithfully replayed the tree's
   4 nodes, but the STEP case took a value-computation + native-`Int`-arithmetic
   shortcut (compute both sides to integers, equate via the IH) **instead of
   replaying the tree's node chain** (recursive definition expansions, `cdr-cons`,
   `commutativity-of-+`, `commutativity-2-of-+`, the `rewriting-equivalence` IH,
   `equal-self`). It proved the theorem but did NOT demonstrate the replay — so it
   was useless as a template.
4. When run against the real tree the producer discharged **0** nodes — and that
   metric was itself wrong, because there is **no recursive driver**: no
   `proveTheoremProof`/`proveCaseProof`, no induction-from-scheme, no per-case
   context (variable bindings + clause-derived facts like `consp x = nil`), no IH
   threading, `ProofCtx.facts` is never populated, and `proveNode` does not recurse
   into children. The producer cannot even *attempt* a real tree.
5. Most of 2026-06-05 was refactoring/extending this broken-on-real-data producer,
   plus a garbage rewrite handler (`cdr-cons` that only matches
   `(cdr (cons VAR VAR))` — a shape that never occurs).

## What the plan SHOULD be (the method is sound; the execution was not)

Hand-prove-then-automate is the right method. In order:

1. **Hand-prove `my_len_my_app` FAITHFULLY following the reconstructed tree, node
   by node** — base AND step case must replay the actual rune chain shown by
   `dump-proof-tree`, using the induction scheme, the recognizer/`if-simplification`
   children, `cdr-cons`, `commutativity-of-+`/`commutativity-2-of-+`, the
   `rewriting-equivalence` IH, and `equal-self`. The hand proof is the TEMPLATE; it
   must MIRROR the tree, never shortcut to the goal. (An early partial hand proof
   and arithmetic lemmas at this commit still carry sorries — finishing it the
   faithful way is the first task.)
2. **Automate DRIVER-FIRST.** Build the recursive descent:
   `proveTheoremProof` (induction from `InductionStep.scheme`) →
   `proveCaseProof` (bind the clause's variables into `ProofCtx`, derive recognizer
   facts from the clause, thread the IH) → compose the literal's node chain →
   `proveNode` (recurse into children). Individual rune handlers only matter once
   this driver exists and is exercised by the real tree.
3. **Drive everything against the real reconstructed tree from day one.** A handler
   "works" only when it discharges a node in the real `dump-proof-tree` output —
   never when a synthetic unit test passes.
4. **Type facts come from ACL2, not Lean inference.** Integer-ness for the
   arithmetic rules is in the emitted `:TYPE-PRESCRIPTION` corollary (already
   parsed) plus `synthTotality`. If the tree lacks needed info, add ACL2
   instrumentation; do not add inference to the checker. Hard-fail at frontiers
   (this discipline WAS respected throughout — no `sorry`/fallbacks were introduced
   in the producer; keep it that way).

## What's on the archive branch `origin/mdd/proof-producer` (tip `bfda555`)

Mineable for ideas, NOT a base to build on:

- The 2026-06-05 producer handlers + converger + `synthTotality1`. `synthTotality1`
  is genuinely general (detection-driven, no hardcoded names) and worth reusing.
- The flawed `my_len_my_app` hand proof (step-case shortcut).
- A detailed per-node triage at `docs/audits/2026-06-05_producer-triage.md` **on
  that branch** — read it for the node-by-node analysis, the 0/10 finding, and the
  conclusions of four adversarial audits.
- `Tests/ProofProducerRealLog.lean`: a real-tree harness (the right idea, but
  flawed — it only checks well-typedness, not that a proof proves the node's
  claimed statement, and it ignores children).

## State of `main` now (`2f180d1`)

Trusted foundation: Layer 1 (SExpr/Logic/Parser/Count), `EvalOpt` + fuel lemmas,
the `ProofLog` parser, `ProofTree` reconstruction, `EvalLemmas` atomic steps +
`acl2_induction_consp`, and an early (2026-04-04) producer skeleton (`proveNode`
dispatch, reflection, ground-eval). Pre-existing sorries remain in
`EvalLemmas`/`SimpleWorld`/`WorldGen`/`DSL` (genuine WIP). The orphan
`RewriterSoundness.lean` (known-false sorry) was deleted in this commit.

There are also persistent agent memories capturing these lessons (reconstructed
tree; work against real data; instrumentation lever for type facts).
