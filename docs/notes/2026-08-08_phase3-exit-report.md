# Phase 3 (R7b functional instantiation) — EXIT REPORT

**Exit class: EARLY EXIT** (charter-permitted "at any time, for any
reason"), declared 2026-08-08. Reason: the one remaining item-2 gap is
an in-scope debugging campaign (in-sweep SIGABRT on proof-term depth)
that this session could no longer execute reliably — three consecutive
remediation cycles without landing, at ~10 min build time each. No
fidelity, soundness, or drift concern motivated the exit; the state is
clean, fully committed, and gated.

## Scoreboard delta

- 102/116 → **104/116** (33 unconditional + 71 conditional):
  MSORT-IS-ISORT and QSORT-IS-ISORT — two of the three sorts-equivalent
  capstones — REPLAY conditionally green
  (`cond[total:<sort>, usefi:STRONG-SSORTFN1-IS-SSORTFN2]`), via the
  new FI `:USE-HINT` arm consuming the emitted
  `:LMI-LST`/`:CONSTRAINT-CL` payloads with the recorded constraint
  chains replayed against the concrete rules.
- The canonical-world instantiations of both equisort parametric
  constants landed kernel-checked (partial non-vacuity witnesses;
  deferral D1).
- Golden byte-identical at 104/116 through every subsequent round;
  SEVEN full claim-gates TRUE_EXIT=0 punctuated the phase.

## Queue disposition

1. **Non-vacuity instantiation — PARTIAL, D1 logged.** 41/49 (weak) and
   13/21 (strong) premises kernel-discharged at the canonical world via
   the new `instantiate_parametric%`; the residual chain is documented
   (witness-TP prover class — in-scope; PERM-TLFIX R-lane — a
   pre-ratified user checkpoint).
2. **The FI arm — 2a DONE; 2c one enablement from done, D2 logged.**
   The COMPLETE semantic layer is proven, zero sorries: Lemmas A
   (alias-free invariance), B′ (β-expansion), B″ (β-contraction, with
   the `aliasArgsSimple` soundness condition discovered en route),
   `evtrue_fnalias`, `World.withAliases` + constructive lemmas, the W3
   statement lifts, `conv_defcall`, `defcall_body_inversion`,
   `wrapper_total_1`, `total_fnalias_transport`,
   `fuelEq_fnfree_cross`, `var_conv_ex`, `conv_repack`. The full
   discharger (`mkUseFiDischarger`: parametric rebuild at the alias
   world, premise discharge through the shared engine with
   alias-wrapper totality and consumer-telescope transports, both
   premise-bridging classes, `evtrue_fnalias` crossing) is BUILT and
   WIRED end-to-end (runBook → tryReplay → replayProofConditional →
   the coverage callback) but DISABLED pending the D2 debugging
   campaign. The isolation probe executes the whole composition up to
   the step that needs the real sweep telescope.
3. **MSORT-IS-ISORT — conditionally green** (full closure = D2).
4. **QSORT-IS-ISORT — conditionally green** (full closure = D2).
5. **BSORT-IS-ISORT — sized, D3 logged.** Same tautology-dropped FI
   shape; its weak-variant constraint chain leaves a clausify residual
   closed by a tau leaf that resolves ASSUMED while TRUE-LISTP-BSORT
   stays red in the bsort book — ceiling ◌ until the bsort Phase-1
   frontier family (partially emission-class).
6. **Audit deferrals — untouched, D4 logged** (charter: cover or defer
   IF touched; they were not touched).

## Fidelity posture

Everything consumed is emitted content: the FI substitution verbatim
from `:LMI-LST`, obligations from `:CONSTRAINT-CL` with the recorded
chains, statements pinned (Tests/ParametricPins.lean). The pre-ratified
route (a1) was followed exactly; no trusted-core growth; no per-case
provers (the carve-out drift test was consulted at each dispatch
extension — every route is a uniform class keyed to emitted structure).
One scope-note: `acl2lean-replay`'s minimal build cone excludes
ParametricInstantiate, which let one broken intermediate commit
(W4f-1) claim a wrong-scope fast-gate — caught and fixed next round
(fd828e3); the full gates were unaffected.

## Continuation (in priority order)

1. D2: symbolized-trace the in-sweep SIGABRT; bisect which Expr walk
   overflows; likely chunk the parametric rebuild into its own
   pre-declared constant before composition. Then enable, sweep,
   golden row-review (the two capstone rows' `usefi:` conds flip
   discharged), gate.
2. D1 residual: the witness-TP `dis_*` lemmas (in-scope); the R-lane
   checkpoint is Mike's.
3. D3: the BSORT composition (ceiling ◌).
4. Phase 4 per the arc plan: capstone native mirrors + mutation tests
   + tier-split (an MDD item) + the demo write-up.
