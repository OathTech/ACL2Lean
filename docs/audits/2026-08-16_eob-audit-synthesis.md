# End-of-branch audit — SYNTHESIS (2026-08-16, mdd/t12-sprint @ 388089d)

Six auditors (A1 TCB/trust Fable-adversarial; A2 claims Opus-cold-build;
A3 docs Opus; A4 stale-material Opus; A5 next-steps Fable; A6 J-call
governance Opus), launched 2026-08-16 post-sprint-exit, raw reports
persisted as `2026-08-16_eob-audit-a{1..6}-*.md`. Synthesis rules: the
overlapping findings cross-confirmed (zero auditor-vs-auditor
contradictions found); the orchestrator spot-checked the two
highest-stakes survivors itself (the 42d4d29 baseline numbers; A1's
attack4 demonstration vs the IsoGen:82-91 claim — both confirmed).

## THE VERDICT

1. **The sprint's headline claims are TRUE** (A2, independent cold-build
   re-derivation): 116/116, 116 unconditional, zero FAIL, golden
   byte-identical from scratch (sha256 match), zero
   sorry/sorryAx/native_decide, all 77 axiom receipts the clean trio,
   the gate artifact genuine (real re-run timings), 5/5 row spot-checks
   verbatim against the real logs, provenance 91/91.
2. **The trust story HOLDS for truth** (A1): no falsity attack was
   constructible; untrusted-layer constants appear only in proof terms,
   never mirror statements (probed by proof-term traversal); every
   sprint semantic surface (BUG-009 discount — verified bit-for-bit
   against upstream ACL2 source; routeIff; gz registries; the transfer;
   hypothetical-TP) terminates in kernel type-hints against
   recomputed-from-emission types. **The "via replay" PROVENANCE story
   is strongly-evidenced engineering, not mathematics** — two
   deliberate-construction bypass routes demonstrated (F1: Prop-valued
   `def` passes the definitions-only unfold gate — the header's
   impossibility claim is FALSE AS WRITTEN; F2: no mirror-level seam
   gate — the property holds today, probed, but nothing enforces it).
3. **Zero judgment calls wrong on the merits** across all ≥63 (A6) —
   the sprint's failures are of process and escalation, not judgment:
   two lanes' J-entries never reached the ARC LOG (orchestrator
   collection misses — the texts exist in the lane reports), and the
   single clearest escalation miss is the BUG-009 discount reversing
   P4a's own out-of-class stop without new information.

## CLAIMS-TIER CORRECTIONS (mandatory, no ruling needed)

- IsoGen:82-91's "Definitional unfolding cannot introduce content" —
  falsified by demonstration; rewrite to the honest bound (A1-F1).
- "23 #guard_msgs mirror receipts" → the real count is 14 (A2-C6).
- The trip report's start-state column is the post-R3 mid-sprint state;
  true baseline 113/116 (84+29), 6 FAIL, 6 sorries — the sprint's
  delta was LARGER than reported. "~40 J-calls" → ≥63. "five reverts"
  unverifiable as counted (A3-T1-2, A6, orchestrator-confirmed).
- The charter ARC LOG gains the R3 and P5b J-entries from the lane
  reports, attributed as an orchestrator collection miss (A6, A3-T1-7).

## THE MECHANICAL REPAIR BATCH (post-audit increment, no rulings)

From A3 (Tier 1): waypoint-metrics.sh:37 delete (script aborts since
GzPrelude's deletion — also A4 #1); TODO.md debt registry + top block
(retired debt listed open; six lanes unlogged); the five stale catalog
`.pending` texts (T1-6 — the next mirror-wave executor's reading
material); Tier-2/3 fix-list as recorded.
From A4 (DELETE-NOW, build-verified before landing): the orphaned pin
vocabulary (~97 lines), synpQuotep duplicate, totality_1/2_rec old
wrappers, MeasureShape.positionsIn (or wire ExecGen to it — flagging
the F13-remedy overstatement), logic_nfix_eq_nfixNat.
From A4 (KEEP-BUT-DOCUMENT): gz_def_* gate note; diag sinks → README;
DISCHARGE-bracket legend beside the stripping code (the bracket has
now misled two reviewers); NodeCore facade 7→8; Driver.lean:22 header
mis-aim; ProofLog baseline 1240→1238.
From A2: one clarifying word in the golden header (116 theorems + 6
terminations = 122 rows); the fresh-clone reproduction inventory →
README (logs are gitignored: a fresh clone has the claim without the
corpus).
From A3-T2: LEXICON entries for the sprint vocabulary (transfer,
quiescence, D5/gz class, D-A pattern, row-vs-DISCHARGE conditions);
roadmap/master-plan supersession statuses; BUG-023's RT2 landing;
pin-docstring consolidation per A4's RETIREMENT-LOG shape.
Plus: persist the four-line canon to the repo (cited as a binding
priority rank; defined nowhere — A6).

## THE RULING QUEUE (Mike)

R-1. **A1-F1/F2 gate decisions** (deterrent standard): reject
     Prop-typed unfold entries (one line)? extend seamReaches over
     MirrorProofs? The docstring correction happens regardless.
R-2. **A6's B1 — the BUG-009 discount**, the one call that reversed a
     recorded out-of-class stop. Code verified exact by two auditors;
     the ruling is whether the mirroring trade stands and whether
     "re-opening a recorded stop" becomes an escalation trigger.
R-3. **A6's future delegation boundary** (five ask-first classes) +
     the two process fixes (J-entries land at collection; canon
     defined) — adopt for future sprints?
R-4. **A4 #8 — the 744-line dead waypoint closure** in
     Imported/Sorting.lean: delete-as-deletion (largest available
     shrink of the grandfathered giant; must not be banked as
     industrialization) or retain deliberately with a comment?
R-5. **A4 #9 — the 15 uncatalogued *_driver theorems**: catalogue or
     record why not (deliverables, never delete).
R-6. **A5's proposed sequence**: rulings batch (W7/W9/enum-registry/
     OrderedEmbed) → R4 wave 2 with the perf arc (D7 transport via the
     proven evalOpt_world_mono + module-DAG sharing; ~20-30 min off
     every sweep; the corpus-scaling prerequisite) in a parallel lane
     → Track FREE acceptance test → LET/lambda round-trip. Note the
     A5-vs-P3c reconciliation item: P3c rejected the transport on the
     hnew side condition; A5 reads D7 as discharging it from
     proveNoShadow facts — settle at build time, fall back to today's
     route, golden byte-identical is the acceptance test.
R-7. The remaining A6 briefs B2-B11 (individually small; B2's D5
     class-extension and B7's pin-regime question the substantive
     ones).

## RULINGS RECORD (Mike, 2026-08-16/17)

The seven queued items, ruled and implemented in the rulings batch on
`mdd/t12-sprint`. This section is the RULING; the implementation
evidence (build, gate probes, deltas) rides in the batch's commits.

### R-1 — the A1-F1/F2 gate decisions: BOTH TAKEN (deterrent standard)

**R-1a — reject Prop-typed unfold entries.** The IsoGen closer's
unfold-list validation used to accept anything with `.defnInfo`,
INCLUDING a `Prop`-valued `def` — a content definition wearing a
definition's clothes. It now additionally rejects Prop-typed entries
(`Lean.Meta.isProp` on the constant's type, at the `.defnInfo` check),
so A1-F1's demonstrated route fails AT THE GATE with a named error
instead of being stopped one hop later by the registry's duplicate
fail-close; the attack is pinned as a NEGATIVE test
(`Tests/IsoGenGateTests.lean`, the tamper-test convention) so the gate
cannot silently regress. The header's impossibility claim was separately
corrected to the honest bound (claims tier, no ruling needed).
**The bound is A1-F1's bound and this fix does not change it:
PROVENANCE only** — a smuggled square is still kernel-true, so no false
mirror is reachable; what such a route costs is the evidence that the
content came via replay. Deterrent standard: a speedbump reviewed by
"does it catch the honest mistake". A determined author still has other
routes — the same audit records A1-F9 on the same page — and no
syntactic check on the invocation can classify content. Do not harden
it.

**R-1b — extend the seam check to the MIRROR level.** F2 was correct
that the property "every mirror's proof consumes a replayed statement"
held only by inspection. It is now mechanized in
`MirrorProofs/SeamGate.lean`: 6 products / 12 seams, by MECHANICAL
ENUMERATION over the mirror namespace (so a new mirror joins the gate
automatically rather than by remembering to list it), negative-probed.
The shared `seamReaches` helper was generalized UPSTREAM to
`Waypoints/Macro.lean` so the mirror gate reuses the one copy —
`MirrorProofs` cannot import the waypoint catalog — with both catalog
call sites unchanged. Same threat model as every other seam gate: a
speedbump against detachment, not a barrier; do not harden it.

### R-2 — the BUG-009 mask discount: BLESSED, and re-attributed

**The trade STANDS.** Discounting exactly type index 6 (and nothing
else) in `tsAcl2MaskOk` is the right call on the merits: the verdict
lemma is proved, `tsIndex` provably never returns 6, the delta was
verified to be exactly that bit, and BUG-009 carries the third-site
note with an explicit deletion condition (a fix to BUG-009 makes index 6
inhabited and the discount must go). Two auditors verified the code
exact.

**THE DECIDER RULE (the general form).** For a cross-check between
ACL2's emitted data and our derivation, the question "may this be
loosened?" is decided ABOVE the lane — by whoever wrote the lane's
brief — not inside it. A lane may *tighten* freely; a lane that wants
to loosen STOPS and reports, and the brief that answers it carries the
acceptance condition in writing (here: "the delta must be exactly bit 6;
any other bit stays fail-closed"). The lane then implements and VERIFIES
against the real emission. That is what happened; what failed was the
record.

**O-NUMBERING (the record fix).** A6-B1's "P4b reversed P4a's own
out-of-class stop one lane later" is an ATTRIBUTION-GAP ARTIFACT: this
was an orchestrator decision taken in P4b's brief, filed under the
implementing lane's J-series. Going forward the ARC LOG carries two
prefixes — `J-…` for EXECUTOR judgment calls (what the delegation
contract makes reviewable) and `O-…` for ORCHESTRATOR decisions made in
a lane's brief, assigned when the brief is written. The entry is
re-attributed in place as **O-1** in the charter ARC LOG, with the old
J-number kept visible so prior citations resolve, and with the honest
limit stated there: the brief was a delegation message, not a repo
artifact, so the re-attribution rests on attestation and cannot be
re-derived from the tree. That is precisely the defect the `O-` prefix
removes for future sprints.

### R-3 — the five ask-first classes: ADOPTED for future sprints

Transcribed from A6 §5. Remain ask-first, even under a sprint goal:

1. **Loosening any cross-check between ACL2's emitted data and our
   derivation** — admissibility guards, verdict comparisons, decode
   admissibility. Tightening stays delegated.
2. **Extending a ratified carve-out to a new KIND** — a new rule class,
   a new discharger family, a new "closes without replayable evidence"
   entry. Adding a *member* to an already-ruled class, with the class's
   own recompute-check, stays delegated (J-P4b-a is the model — and it
   should still say, as it did, exactly why the set did not grow).
3. **Design forks with a lasting architecture or a corpus-wide cost
   profile** (say >10% sweep cost, or a new module family). Present the
   fork with the measurement; do not both propose and accept.
4. **Deleting or re-deciding another track's records** — waypoint decode
   exceptions, provenance registrations, catalog decisions. J-P5a-g's
   PERM-TLFIX `.pending` is the model to copy verbatim: *"classifying a
   row as plumbing vs content is a MIRROR-side call, deliberately NOT
   taken by a driver-layer executor."*
5. **Re-opening an item a prior lane STOPPED as out-of-class or
   fidelity-sensitive.** A recorded stop is an escalation trigger, not a
   to-do.

Explicitly delegated (keep): module moves/ratchets, de-duplication,
env-gated diagnostics, demand-driven cells inside an already-proved
lemma pattern, error-severity policy, parser fail-closed choices, stops,
reverts, premise refutations, sequencing changes.

Both process fixes adopted: **a lane may not be collected until its
J-entries are appended to the ARC LOG** (commit messages are not the
log), and the exit report's J-count is COMPUTED from the log, never
estimated. "The four-line canon" is now DEFINED (persisted to
`CLAUDE.md` in the repair batch), so the charter's priority rank cites
something real.

### R-4 — the dead waypoint closure: DELETE, booked as DELETION

Deleted from `ACL2Lean/Imported/Sorting.lean`, each subtree carrying a
dated tombstone that names the orphaning lane and says in terms that
this is **NOT industrialization**:

- the ORDINAL kit (`o_finp`/`o_fe`/`o_fc`/`o_lt` exec-correspondences and
  support) — orphaned by P3b;
- the ACL2-COUNT kit (`integer_abs`/`length`/`acl2_count`
  exec-correspondences and support) — orphaned by phase 1;
- the generic ORDEREDP exec closure — orphaned by P5a's `routeIff`;
- `relExec_t_or_nil` and `allRelExec_t_or_nil`.

**A4 §8's ranges were TOO WIDE and were corrected before execution**:
`orderedp_sym` is LIVE (read by the ORDEREDP-QSORT native's world
hypothesis) and is deliberately KEPT with a comment saying so;
`filterExec_consCount_le` is LIVE and outside the deletion. Every
subtree root was verified to have zero live consumers before deletion,
and the build is the referee. Because these were waypoint-layer HAND
proofs with no book behind them, the resulting movement in
`waypoint-metrics.sh`'s hand-line count is booked as a DELETION, not as
coverage; `Tests/WaypointCensus`'s watched `corr` number drops by 8 (an
environment-derived print that can never fail a build — record it, do
not chase it). The `Imported/Sorting.lean` file-weight baseline is
TIGHTENED to the new count (ratchets move by MOVE, never by loosening).

### R-5 — the fifteen uncatalogued `*_driver` theorems: CATALOGUED

They are deliverables, never deletable — a waypoint's kernel-check is
its purpose. Executing R-5 surfaced *why* they were uncatalogued, which
is a real structural fact rather than an oversight: `liftCatalog` is
strictly ROW-KEYED (one decision per green golden row, with a
build-failing staleness check on both sides), and none of the fifteen
IS a row. They are (a) alternative READINGS of a row already carrying
its one entry (the `List.Perm` / `List.IsChain` Mathlib forms), (b)
BUNDLES assembled from several rows (`isPerm_equivalence_driver`), or
(c) natives of pattern-test books that have no golden row at all (p7,
p5). A `liftCatalog` entry for any of them — `.native` or `.pending`
alike — fails the gate as either a duplicate key or a stale key.
They are therefore catalogued in the EXISTING companion shape rather
than forced into the row list: the pattern-test pair joins the
`extraSeams` list (the shape built for exactly "a native whose row lives
outside the golden"), and the readings/bundles join a sibling
row-anchored list, both bound by the SAME `seamReaches` seam check and
already covered by the axiom gate's wide `_driver` scan. Net effect:
all 63 declared `_driver` theorems are now gate-bound, and
`Waypoints/Validation.lean` no longer scans as consumerless.

### R-6 — A5's proposed sequence: ENDORSED, with the perf arc profile-first

The four decisions are endorsed as A5 framed them, and the sequence
stands: **rulings batch** (this one — W7/W9/enum-registry/OrderedEmbed)
→ **R4 wave 2 with the perf arc in a parallel lane** → **Track FREE
acceptance test** → **LET/lambda round-trip**.

Two conditions on the perf arc. (1) **PROFILE FIRST** — the measurement
protocol in `docs/notes/2026-06-11_perf-profile.md` runs BEFORE any
optimization lands, and each change is justified against a measured
hotspot, not a suspected one; the ~20–30 min/sweep figure is the
hypothesis, not the result. (2) **TRUST-NEUTRAL, OPPORTUNISTIC SCOPE** —
the perf arc may not move a trust boundary, change what a replay is
permitted to use, or trade fidelity for time; it takes the wins that are
behaviour-preserving and leaves the rest. The acceptance test is the one
the sprint already uses: **golden byte-identical**.

On the noted A5-vs-P3c reconciliation (D7 transport vs re-replay): P3c
rejected the transport on the `hnew` side condition; A5 reads D7 as
discharging it from `proveNoShadow` facts. SETTLE IT AT BUILD TIME —
try it, and if it does not discharge, fall back to today's re-replay
route without further ceremony. Golden byte-identical decides.

### R-7 — B2 retroactively blessed; B7 the pin policy

**B2 (the `:LINEAR` D5 class extension) is RETROACTIVELY BLESSED.** The
content is one definitional unfold, recomputed per rule from the cited
function's own emitted `:DEFUN` body, with the test checked against
`:HYPS` and the rhs against the conclusion before the class lemma is
applied — a genuinely small trust delta, and correct. But A6 is right
that it was a class extension decided in-lane: under R-3 class 2 it
would be ask-first today. Blessed as done, cited as the boundary case.

**B7 — THE PIN POLICY (where a static pin binds).** A static pin is an
independent, hand-written statement checked by the build; a golden row
is produced by the same code the sprint changes and repins. They are
different instruments and the "stronger check" framing was overstated.
The rule:

> Wherever a REGISTRY records a POLICY DECISION — which rules may be
> discharged without replayable evidence, which names are exempt, which
> constants a carve-out covers — its MEMBERSHIP carries a static pin
> asserting the set VERBATIM, so that changing the set is a conscious
> edit to a pin rather than a diff nobody reads. Where the pin would
> require standing up expensive machinery (parsing a 150k-line log
> inside `Tests/`), pin the MEMBERSHIP anyway and let the golden
> live-gate the DISCHARGE; the two are complementary, and the cheap half
> is never skipped because the expensive half exists.

Implemented at the WP3 pin site: the pin-policy line is stated there,
and `d5GzRules` / `d5GzLinearRules` now carry static membership pins of
their registered rune-name sets. Deterrent standard — ONE pin, not a
census; it catches the honest mistake of growing a policy set without
review, and it is not to be hardened.

## CREDIT (verified, not asserted)

BUG-009's record matches its code line-for-line (A1+A3, independently);
the ladder criterion matches the kit exactly (12 rungs, both sides
enumerated); the trip-report timeline matches git to the minute; ten
sampled J-calls all accurate; every ratchet baseline exact; the
mirror layer untouched by diff across the whole sprint; the refusal
boundaries are LIVE (the equisort transfer refusal fires today and
routes to the parametric lane — A5); the sprint machinery is uniformly
mechanism-general / inventory-demand-driven / fail-closed (A5's
census); and the honest two-sentence trust story (A1 §Q4) is
recommended for adoption into README nearly verbatim.
