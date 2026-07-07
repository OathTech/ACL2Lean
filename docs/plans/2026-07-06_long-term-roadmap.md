# Long-term roadmap — after the two-stage lift lands (PROPOSAL)

*2026-07-06, branch `mdd/r2-isort`. Status: PROPOSAL for MDD review — nothing
here is ratified except where it restates already-ratified decisions (the
sorting-corpus roadmap, the obligation-log model, the two-stage lift design).
Supersedes nothing; extends `2026-06-12_sorting-corpus-roadmap.md` past R7.*

## 0. The platform as it stands (what "all landed" means)

Assumed landed for everything below: `Logic.lexorder` (spec in TODO
priority 3), the R2 isort replay behind it, and stage-1 mechanization of
the two-stage lift (spec in `2026-07-06_two-stage-lift.md` §Next). The
platform then is:

- **Replay**: whole-book conditional replay under the obligation-log model —
  `total:`/`tp:`/`rule:` telescopes, lazy discharge, typed frontiers,
  fail-closed at every seam; the perm book composes 8/8 with an EMPTY
  obligation log; include-book composition (statements + rules without
  proofs) works.
- **Import**: the two-stage lift (exec mirrors + walk corrs + pure-Lean
  simulations), the TP prover, the totality prover, the decode kit; the
  perm book fully imported natively (8 axiom-gated native facts).
- **Ops**: coverage harness as the scoreboard (replay + DP-leaf + axiom
  cleanliness), differential harness vs real ACL2, the tagged fork.

The horizons below are ordered by dependency, not calendar; H2/H3 items are
pulled in exactly when the H1 spine demands them (the corpus-driven rule).

## Horizon 1 — finish the sorting corpus (the spine: R2 → R7)

The ratified corpus roadmap stands. What this proposal adds is the honest
statement of the two ARCHITECTURE items still hiding inside it:

**R2-completion (isort, then structurally done):**
- (a) `lexorder` + isort's 3 theorems replayed; two-stage lift of
  insert/isort/orderedp/how-many (isort's exec layer cites perm's corrs —
  first cross-book lift composition).
- (b) **Included-defun totality** — the termination-machine recomputation
  emission (recorded follow-up, NEEDS MDD RATIFICATION): included defuns
  re-emit the same clauses ACL2 originally proved (deterministic
  recomputation = emission, not inference), killing the D6-kept
  `total:<included-fn>` hypotheses.
- (c) **Cross-book rule discharge** — THE remaining R2 architecture item
  and the biggest open design on the spine. `rule:<included-thm>`
  hypotheses must discharge from the included book's OWN replayed mirror,
  i.e. step 5 of the theorem-dependency design across book boundaries.
  The design question: per-book Developments replay against per-book
  worlds; the consumer's hypothesis is stated over the INCLUDING world.
  Two candidate shapes — (i) world-parametric mirror statements with
  def-hypotheses (the Imported/ layer already prefers this; L3 was
  designed for it), (ii) a world-extension transfer lemma
  (`w ⊑ w' → mirror w → mirror w'`). Requires a design doc BEFORE building
  (the R2 rule); do it when the second book-pair (isort ← perm) makes the
  shapes concrete.

**R3 — the counting argument** (convert-perm-to-how-many + ordered-perms,
19 theorems): expect `:use`-hint shapes and G5 growth; first sustained
exercise of the rule-discharge machinery at scale.

**R4 — msort/bsort** (evens/odds and bubble-pass schemes): G5 induction
shapes; by here the exec-corr command must exist (four new exec functions —
hand-writing them would violate the industrialization intent).

**R5 — qsort**: G4 forcing rounds land here (driven by real logs; the
FORCED-hyp seam in the rule design is already left open for it); the
**arithmetic-3 foreign-rune policy** (MDD decision: replay only runes that
FIRE, each imported as its own replayed lemma or a named frontier — no
blanket trust of an uncertified include); and a scale stress test (6931
rewrite steps — likely forces the pool-subsumption duplication fix).

**R6 — equisort**: encapsulate-as-constraints — constrained functions enter
the World abstractly; per the generality plan this is a statement-builder
change (the L3 dividend). CORE-tier item.

**R7 — sorts-equivalent**: functional instantiation; tier call to ratify at
arrival (build the `:functional-instance` recipe vs import the four
`X-is-isort` theorems conditionally).

**Deliverable/headline at R7**: the classic J Moore sorts-equivalent
development imported end-to-end — every theorem kernel-checked in Lean,
the flagship facts (four sorts sort, and are equivalent) as native
Mathlib-idiomatic statements. This is the natural external-communication
boundary (paper/demo — see H4e).

## Horizon 2 — industrialization (the per-book cadence)

Goal, stated as a metric: **hand-written lines per imported theorem ≈ 10**
(the stage-2 simulation + the native statement), and **book onboarding =
one command + the hand lines**. Items, each pulled in when the spine
demands it:

- (a) **Stage-1 mechanization** (exec-corr elab command) — spec ready;
  needed before R4.
- (b) **Exec-def GENERATION** from World bodies (mechanical; the `eq_def`
  fold already fail-closes shape divergence).
- (c) **Decode-theorem generator** (TODO 3b) — trigger condition met at
  isort (two books exercising the schema): parsed formula + the fn↦corr
  registry → the per-theorem decode emitted, fail-closed outside the
  schema.
- (d) **Obligation dashboard**: promote the obligation log to a first-class
  report (`acl2lean obligations`) — per-book outstanding `total:/tp:/rule:`
  hypotheses with their named frontiers; this is the operational view of
  the "chew through obligations" model.
- (e) **Frontier-lemma drip** (steady, opportunistic): natp-through-+
  value shapes (tp:my-len/tp:len2), the cddr decrease (total:evenlen).

## Horizon 3 — trust consolidation (continuous; one policy, one milestone)

- **Policy — trusted-core growth discipline** (make explicit now, since
  `lexorder` is the first big primitive added since the differential
  harness): every new `Logic`/`evalOpt` primitive requires (i) faithful
  implementation read off the ACL2 source, (ii) differential probes in
  `diff_eval.sh` as the acceptance gate, (iii) inclusion in the next audit.
  Propose a `TRUSTED-CORE.md` manifest: every primitive, its ACL2 source
  anchor, its differential coverage. The trusted core is the ONLY part of
  the pipeline a native theorem's correctness rests on (beyond the kernel);
  its growth should be legible at a glance.
- **Milestone — retiring the trust note for the imported catalog.** Today's
  trust note says stages 2–6 can produce a kernel-accepted proof of a
  subtly wrong MIRROR. Once decode generation (H2c) makes every imported
  theorem native, that caveat retires FOR THE IMPORTED CATALOG: a native
  statement is read in Lean's own terms, so the entire ACL2 pipeline is
  untrusted for it. The residual trust surface = kernel + trusted core +
  reading the native statement. State this in CLAUDE.md when it becomes
  true, not before.
- Residual fidelity items stay tracked: symbol-case/package caveats,
  differential expansion only at trusted-core growth moments.

## Horizon 4 — pushing further (the arcs beyond the corpus)

Ordered by recommended start time, not importance:

- **(a) The live tactic — the North Star.** `acl2_prove` inside a Lean
  proof: reverse-translate a Lean goal (in a supported fragment) to an
  ACL2 defthm, run the instrumented ACL2, capture + replay + decode, close
  the goal natively. Everything downstream of the reverse translation
  EXISTS; the new component is Lean-statement → ACL2-formula translation —
  which is the decode registry's encode direction, so H2c builds most of
  it. Scope v1 to the List/SExpr fragment we already decode. Realistic
  start: prototype after R4 (enough decode surface to be honest);
  productionize after R7.
- **(b) Breadth validation + a second corpus.** The mechanism-frequency
  sweep (old G6) BEFORE any CORE-tier completeness claim; then a
  deliberately different book family (arithmetic-heavy or tau-heavy) to
  de-overfit the machinery from list processing.
- **(c) Feature tiers**, in corpus-driven order once a target book demands
  them: guards/`verify-guards` (the gate to most community books),
  mutual recursion at scale, `defun-sk` (EXTENDED); stobjs/`apply$`/
  metafunctions stay OUT until a driving consumer exists.
- **(d) Upstreaming the instrumentation.** The TRACE-LOG tag discipline
  exists precisely for this. Once the fork stabilizes (post-R7), propose
  the emit/suppress/infra patch set upstream — reduces fork maintenance
  and makes capture reproducible for others.
- **(e) External communication.** R7 is the paper boundary: faithful
  replay (vs. oracle reconstruction), the obligation-log model, and the
  two-stage lift are each novel enough to carry an ITP/CPP-style paper;
  the sorts-equivalent import is the demonstrator.

## Sequencing (the one-line version)

H1 in order; H2 items just-in-time (a before R4, c at isort, d whenever);
H3 policy now, milestone when H2c lands; H4a prototype after R4;
H4b before any completeness claim; H4d/e after R7.

## Decision points for MDD (chronological)

1. **Now**: ratify the trusted-core growth policy (H3) — it governs the
   imminent `lexorder` work.
2. **Now-ish**: termination-machine recomputation emission (R2b).
3. **At isort←perm composition**: the cross-book mirror-transfer design
   (R2c) — design doc first.
4. **At R5**: arithmetic-3 foreign-rune policy.
5. **At R7**: functional-instantiation tier call.
6. **After R4**: whether to start the live-tactic prototype (H4a) or hold
   for R7.
