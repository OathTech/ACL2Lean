# Pause/resume state (2026-08-16, compute pause mid-rulings-batch)

**RESUMED AND COMPLETED 2026-08-17.** The owed verification ran first
(full `lake build ACL2Lean Tests` — GREEN, 3237 jobs, zero warnings, so
the pause's caveat is discharged), then items 3–7 all landed. Deltas
against the predictions below: the `corr N` census drop was EXACTLY 8
(33 → 25) as predicted, `support/other` 47 → 44; hand lines 6630 → 5870
(−760) and hand-lines-per-native 125 → 110, booked as DELETION;
`Imported/Sorting.lean` 4165 → 3405 with the ratchet tightened. Item 4
(R-5) did NOT fit `liftCatalog` — see the RULINGS RECORD R-5 in the
synthesis for why (the catalog is strictly row-keyed and none of the 15
is a row); they are catalogued in the companion `extraSeams` /
alternate-readings shapes instead, both seam-gated. This note is kept as
the record of the pause, not as live state.

PAUSED between the repair batch (committed e3ea6ba) and the rest of
the rulings-implementation batch. The pipeline on resume:
finish items 3-7 below → full `lake build ACL2Lean Tests` + statics →
fresh full claim gate (full invalidation first) → MERGE to main
(Mike's conditional pre-sign-off stands: clean landings = merge; any
plan shift = pause at the merge point) → then wave 2a + the perf arc
(profile-first per docs/notes/2026-06-11_perf-profile.md;
trust-neutral opportunistic scope; see the synthesis RULINGS RECORD
item R-6 — to be written at item 6).

DONE + verified (committed in the accompanying commit):
- R-1a: the isProp unfold rejection (IsoGen ~:714-736) + the attack
  pinned as a negative test (Tests/IsoGenGateTests.lean) — the A1-F1
  attack now fails AT THE GATE (output verbatim in the handoff).
- R-1b: the mirror-level seam gate (MirrorProofs/SeamGate.lean, 6
  products / 12 seams, mechanical enumeration, negative-probed;
  seamReaches moved upstream to Waypoints/Macro.lean, both catalog
  call sites unchanged).
- CAVEAT: `lake build ACL2Lean` green (3212) with all edits; the FULL
  Tests build was NOT re-run after the Catalog/Macro edits (compute
  pause) — the resume session runs it before any claim.

REMAINING ITEMS (the executor's handoff, verbatim ranges):
3. R-4 deletion with CORRECTED ranges (A4 §8 was too wide):
   subtree A ordinal = 2597-2930; subtree B acl2-count = 2931-3303
   (NOT beyond — filterExec_consCount_le:3327 is LIVE);
   subtree C = ONLY orderedpExec:3741, orderedpExec_t_or_nil:3753,
   orderedp_ns:3763, orderedp_exec_corr:3771-~3858 — orderedp_sym:3761
   is LIVE (consumed by the ORDEREDP-QSORT native at :3866);
   plus relExec_t_or_nil:1338 + allRelExec_t_or_nil:1405.
   Tombstones book it as deletion-not-industrialization.
   Expect Tests/WaypointCensus's watched `corr N` to drop by 8 —
   an environment-derived print, never a build failure; record, don't chase.
4. R-5: catalogue the fifteen *_driver theorems (A4 #9 list).
5. R-7/B7: the pin-policy line + the d5GzRules/d5GzLinearRules
   membership pins.
6. R-2/O-numbering: charter re-attribution (J-P4b-d → O-1) + the
   RULINGS RECORD in the synthesis (match IsoGen's already-written
   R-1a wording).
7. Residuals: PatternPins:197 :CR-RUNE wording; Provers:253 comment
   name → _mu; totality_2_rec_snd liveness (build-verify; delete if dead).

## RESOLVED (2026-08-17)

All items landed; full claim gate TRUE_EXIT=0 on 36f01f2 (artifact:
.gate-runs/36f01f2-20260817T180942Z.log); merged to main under Mike's
sign-off scoped to THIS merge alone. Follow-on arcs (wave 2, perf)
staged as charters, NOT approved, NOT launched.
