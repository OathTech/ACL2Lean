# Consumer-queue sub-arc audit — 2026-08-05

**Scope:** branch `mdd/consumer-queue`, commits `d136e6a..5053e7c` (8 commits,
base `e3b33e9`): position-canonical anchoring; recorded-termination demand
widening; POSP/NATP DP registration; BNEXT-SIZE layers 3–4 (builtinRecogFacts,
compound-recognizer arm incl. world-fn route, mkRecTermInfo generalization,
termination:BNEXT/BSORT); tsRecogWalk; the zp-falsity integer kit
(integerpTWalk).

**Method:** two decorrelated adversarial Opus reviewers (inside: proof
soundness / fidelity-to-sources; outside: carve-out drift, judged against the
ratified plans), primary sources only, no conclusions fed in. Highest-stakes
findings independently re-verified by the orchestrator (quotes re-read at
source; the vacuity refutation independently reconstructed and machine-checked:
`bsortDpFact_false` accepts with axioms `[propext]`).

**Ground truth** (both reviewers, independently): `just ci` TRUE_EXIT=0 at
HEAD; golden byte-match; no `sorry`/`admit`/`axiom`/`native_decide` in the
diff; headline scoreboard unchanged at REPLAYED 85/116 (the sub-arc's greens
are termination display rows only).

## VERDICT: NOT-READY (both reviewers, independent grounds)

Stop-early conditions 2 (soundness concern; carve-out drift test) and 6
(NOT-READY findings surviving verification) of the arc plan fire. Reported to
MDD; no fold-back.

## Confirmed findings — soundness lane

- **S1 (HIGH, machine-confirmed twice): `termination:BSORT → REPLAYED ✓` is
  VACUOUS.** The `ASSUMED:dp-fact` hypothesis for BSORT's admission leaf
  (Subgoal 1', linear-contradiction) is stated by `dpFactStmt` with each
  opaque application quantified INDEPENDENTLY — severing the
  `(BNEXT-SIZE (BNEXT X))` / `(BNEXT-SIZE X)` functional link that the cited
  linear lemma provides. The resulting ∀-statement is FALSE (counter-instance:
  `dpv2 ↦ 1, dpv3 ↦ 0, dpv1 ↦ (cons nil nil), dpv0 ↦ nil`; refutation
  kernel-checked with `[propext]` by reviewer and orchestrator independently).
  The registered mirror constant therefore carries a false hypothesis; the
  conditional is empty. This is the equisort-r6 audit's F2 vacuous-green class
  (previously caught and reverted in `cd5e44f`) recurring. The catalog entry
  and TODO disclose the ASSUMED dependency but not its refutability.
- **S2 (MED-HIGH): the consumers' refusal of the ASSUMED mirror is
  incidental, not structural** — `Induction.lean`'s hypFVars simply omit dp
  offers; there is no `admissionAssumed` guard beside `admissionCircular`. A
  natural completeness edit would silently green three rows off a false
  hypothesis.
- **S3 (MED): `thmAt` resolves mirror conditions by non-unique string key,
  positionally, without an `isDefEq` type check** ("ASSUMED:dp-fact" is one
  key for many leaves; `tp:` can be emitted twice per fn). Fails closed today
  via `Meta.check`; defect-shaped.
- **S4 (MED): reporting asymmetry** — `tryDischarge` refuses to render an
  ASSUMED leaf as ✓; `tryReplay` renders the composed row ✓ unconditionally.
  The DriverCoverage legend's documented invariant ("the composed row carries
  no ASSUMED cond at all") is now false; this sub-arc broke it
  (orchestrator-verified at `Tests/DriverCoverage.lean:24-27`; exactly one
  such row in the golden).
- **S5 (MED-LOW): the INTEGERP ⇒ 'T arm precedes the cited-rune routes and
  carries no rune gate** (contrast the properly-gated compound-recognizer
  arm) — it can substitute our justification for ACL2's recorded one on a
  node the golden cannot distinguish, or newly hard-throw.
- **S6 (LOW-MED): position-canonical disambiguation pins frames but not
  `preSwap?`/`branchAnchor`** across surviving candidates, then prefers the
  branch-anchored one; unpinned choice, though downstream chain checks likely
  fail closed.
- **S7 (LOW): two `chainOk` clones with deliberately different semantics**
  (Runner vs Induction) — the near-clone class CLAUDE.md warns about.

Soundness lane verified clean: all 10 new lemma statements are model-true AND
ACL2-faithful (zp/natp/integerp/len/plus/lt checked against both Logic.lean
and ACL2's semantics); the mkRecTermInfo generalization is sound (the k-index
cannot mis-associate — recompute-pinned; `interp_decrease_decode` fully
generic in cnt; the O-P clause is inert in `matching` and walked correctly);
tsRecogWalk guard threading correct (no cross-spine leak);
`litFactByTermChecked?` closes the cross-env hole; `re_val_cast`/`Meta.check`
pin the statements; the world-fn compound-recognizer route consumes exactly
the emitted TP corollary; termination:BNEXT is NOT vacuous (its leaves
machine-checked true).

## Confirmed findings — drift lane (drift test: FAILS)

- **D1 (HIGH): the walkers contradict ratified policy, undisclosed.** The
  governing plan (`docs/plans/2026-06-10_generality-design.md` §3(c),
  orchestrator-verified verbatim) directs: "for type-set inside the rewriter
  (assume-true-false, recognizer evidence) prefer *targeted emission* over
  recomputation". `tsRecogWalk`/`integerpTWalk` are recomputation of exactly
  this class; neither commits nor TODO acknowledge §3(c).
- **D2 (HIGH): ACL2's verdict data is ALREADY EMITTED at these nodes and
  unconsumed.** `:TYPESET`/`:TRUETS` ride every recognizer node (e.g.
  `:TYPESET 7 :TRUETS 3072` — the full `type-set-recognizer` derivation);
  parsed into the tree and consumed by nothing. What is missing (`:falsets`;
  recognizer-tuple snapshots) is smaller than what was built.
- **D3 (HIGH): "mirror of assume-true-false" is not a faithful
  characterization.** ACL2: one data-driven recognizer routine over
  recognizer-tuples + ts lattice + type-alist + pruning/union. The walkers:
  per-(recognizer × verdict × leaf-source) code cells with no lattice, no
  type-alist, no pruning. The recursion skeleton matches; the mechanism does
  not.
- **D4 (HIGH): the July-31 MDD-mandated typeSetWalk consolidation's charter
  is violated** ("ONE walker", "no consumer-local fact-channel scan survives
  outside the walker", "no new derivation power"): walkers 1→3;
  `integerpTWalk` scans `litFactByTermChecked?` directly; both add new
  derivation power. `tsRecogWalk .conspNil` is already expressible as a
  `typeSetWalk .isNil` rung. Second accretion cycle five days after the
  mandated fix.
- **D5 (MED-HIGH): design-vs-build divergence one commit apart** — `97190e1`
  designed the general `builtinIntVal?` route; `5beacfe` shipped a second
  per-fn registry (`builtinRecogFacts`) + two per-fn lemmas instead,
  deviation unmentioned.
- **D6 (MED): per-rune whitelist** (`NATP-COMPOUND-RECOGNIZER → NATP`) where
  the head is already in the node and the true-ts already emitted; every
  future compound recognizer needs an entry; ACL2 has no per-recognizer code.
- **D7 (MED): the μ-route discrimination predicate is calibrated on the two
  rows it must not disturb** — a Lean-side heuristic route choice, the shape
  the drift test targets (not a soundness issue).
- **D8 (MED): the trend diverges** — recognizer-name-keyed arms 4→21 since
  07-20 (16→21 this sub-arc), walkers 0→3; 8 of 10 new lemmas are
  per-(recognizer × source) cells; +749 lines for 0 net theorem-row movement.
- **D9 (LOW): no cross-check of the walks' conclusions against the emitted
  `:TYPESET`/`:TRUETS`** — a divergence in *why* is invisible.

Drift lane credit: POSP/NATP DP registration is clean additive registration;
the mkRecTermInfo de-hardwiring is a real artifact-read generalization;
fail-closed discipline genuinely maintained everywhere; the two terminal
walls (local `:LINEAR` gz-collector gap; IF-FINISH window composition) are
precisely diagnosed and correctly queued as fork items.

## Remediation directions surfaced (for MDD decision, NOT decided here)

1. Score ASSUMED-carrying composed replays as `◌ assumed`, never ✓; exclude
   from the lift-coverage gate (S1/S4). Add `admissionAssumed` beside
   `admissionCircular` (S2). Root-cause option: state assumed obligations at
   the actual applications rather than independent opaques (S1 root).
2. MDD the walker question explicitly: amend §3(c) with reasons, or revert
   `tsRecogWalk`/`integerpTWalk` and queue the targeted emission
   (`:falsets` + recognizer-tuple snapshot — both cheap at the already-
   instrumented sites) for the next fork round (D1–D4).
3. Cheap regardless: consume `:TYPESET`/`:TRUETS` as a cross-check (D9);
   rune-gate the INTEGERP arm or move it after the cited-rune routes (S5);
   `isDefEq` at `thmAt` condition application (S3); dedupe `chainOk` (S7).

## Could not verify (union of both reviewers)

Real-ACL2 differential execution of the lemma semantics (no ACL2 run in
sandbox); whether the walkers fire on any node outside the three nfix rows
(a changed justification on a green row is invisible to the golden); whether
the `97190e1` designed route elaborates; tractability/cost of type-set
emission (the survey's "clear hook points" is untested; ACL2's own comments
flag type-set as 50–75% of prover time — emission volume unmeasured); remote
CI.
