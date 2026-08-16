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
