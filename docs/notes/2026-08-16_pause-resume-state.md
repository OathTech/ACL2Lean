# Pause/resume state (2026-08-16, compute pause mid-rulings-batch)

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
