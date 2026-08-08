# Compositional replay at scale (the long-term note)

**Status: DIRECTION AGREED (Mike, 2026-08-08, in discussion following
the Phase 3 W4f term-depth crashes); detailed design OPEN for
ratification.** Pointers: TODO.md backlog; the Phase 3 exit report's
continuation section. A CLAUDE.md pointer follows ratification.

## Why

If ACL2Lean is to be a tool for ACL2-SIZE proofs, it was always going
to need something that scales past naively replaying tactic-by-tactic
into one proof term. The Phase 3 crashes made the ceiling concrete:
the driver builds a single `Expr` mirroring the whole clause tree, so
proof-term depth ∝ proof depth, and every recursive elaborator walk
(inference, checking, fvar collection, abstraction) spends native
stack per nesting level. A single capstone-scale proof already sits
near the OS-stack ceiling; nesting two (the usefi discharge's
parametric rebuild inside the consuming row) aborts the process
(SIGABRT). Time and heartbeat budgets scale the same way.

## What already points the way (the accidental architecture)

The codebase has been converging on compositional structure ad hoc:

- **The D1 mirror registry** — a replayed theorem becomes a named
  constant; same-book consumers APPLY it instead of re-replaying.
- **`ReplayedTermination.*`** — recorded admissions replayed once per
  world, declared, cached, referenced.
- **`UsefiDischarged.*` (W4f)** — the alias-world proof declared at
  single depth so downstream terms reference a small name.
- **`dpLiftF_sound` (G3 Fragment A)** — a genuine certified-checker
  fragment: a verified function plus ONE soundness lemma replacing
  per-node proof chains, exactly the CompCert translation-validation
  shape at fragment scale.

The long-term design makes this deliberate and uniform.

## The design (three layers)

### Layer 1 — per-node lemma decomposition (the default emission shape)

Every waterfall node (clause-id / subgoal) is replayed as its OWN
`addDecl`'d lemma; a parent's proof references its children by NAME.
Proof-term depth becomes ∝ single-node size, permanently, at any book
scale.

Fidelity claim (important): this is not an approximation — it is a
CLOSER mirror. ACL2's waterfall genuinely discharges named subgoals
(`Subgoal *1.1/3''`); naming each as a Lean lemma reproduces ACL2's
own factoring rather than flattening it. "Replaying the logical
equivalent" resolves to LITERAL replay, factored the way ACL2 itself
factors. Every fidelity rule (mirror the tree, no shortcut, no
inference) applies unchanged at node granularity.

Additional wins: caching/reuse for free (the registry pattern
generalized — a subgoal replayed once is referenced everywhere);
failure isolation (a red node names itself); incremental re-replay.

Costs/considerations: environment-name management (sanitized,
collision-guarded — the ReplayedTermination discipline generalized);
kernel checks each chunk (fine — chunks are the scale that passes
today); the conditional-telescope plumbing must thread hypotheses
through constants (the W4f consumer-fvar abstraction pattern: abstract
the telescope fvars into the constant, re-apply at the reference).

### Layer 2 — fragment-local certified checkers (grown per the L1 invariant)

Where a proof REGION is better validated than term-built, write a
checker function over the recorded structure plus one fragment-local
soundness lemma (`check… = true → <judgment>`), and let the node
lemma's proof be the soundness application. Candidates, in rough
order of value: the rewrite-chain walk (the largest term-builder
today), clausify composition, the preprocess chain.

**L1 interaction (binding):** the generality plan §7 L1 PROHIBITS a
monolithic `Derivation` inductive with one soundness theorem. This
layer is therefore explicitly NOT a whole-waterfall certified
replayer: each checker is fragment-local with its own soundness
lemma behind the judgment layer — the `dpLiftF_sound` shape, grown
fragment by fragment. If experience ever argues for widening a
fragment's span materially, that is an L1 amendment to ratify, not a
drift to slide into.

**Lean-specific cost (stated honestly):** CompCert-style validation
leans on trusted fast evaluation (Coq's `vm_compute`). Our analogue,
`native_decide`, is banned as unsound. Plain `decide`/`rfl` means the
KERNEL symbolically evaluates the checker over the recorded data —
fine at fragment/node scale (our world-fact decides already do this),
but a reason to keep checkers fragment-sized: kernel reduction time
would become the new ceiling for a monolithic checker.

### Layer 3 — what stays explicit

Node-level composition glue (small applications of child-lemma
constants), the judgment-layer statements, and everything
statement-derivation-adjacent stay explicit terms: small, auditable,
and where the fidelity story lives.

## Sequencing

1. **D2 first (tactical, this branch):** finish chunking the ONE
   composition that crashes — the usefi discharge — by declaring each
   stage (the parametric rebuild, per-premise discharges if needed)
   as its own constant. Unblocks the two capstones. No architecture
   change required.
2. **Node-decomposition pilot:** convert ONE heavy path (the
   induction-subgoal composition or the discharge re-replays) to
   per-node lemma emission behind the existing driver interface;
   golden byte-identical is the gate.
3. **Default-shape flip (ratification point):** make per-node
   emission the driver's default; retire the depth-limited paths.
4. **Checker fragments:** rewrite-chain first, each its own
   MDD-checkpointed increment per the L1 pattern.

## Ratification questions

1. Approve Layer 1 (per-node lemma decomposition) as the eventual
   DEFAULT emission shape, with the pilot-then-flip sequencing?
2. Approve Layer 2's scope discipline: checkers stay fragment-local
   per L1; any material span-widening is an explicit L1 amendment?
3. Approve the name-management scheme being modeled on the
   ReplayedTermination discipline (sanitized keys, collision guards,
   cache-by-name)?
