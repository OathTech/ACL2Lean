# Mirror-layer provenance audit (2026-08-11) — the thin-Lean ruling

Two Opus classifiers swept the whole mirror layer (`Imported/`) under
Mike's ruling (recorded in the mirror-criterion memory + below). This
file is the synthesis and the purge's disposition record; the full
per-item inventories live in the session audit outputs and are
reproduced in essentials here.

## The ruling (Mike, 2026-08-11)

Lean must be THIN — never re-prove a fact already at hand in ACL2.
Allowed mirror-layer content, no other exceptions:
1. Definitions of Lean-idiomatic versions of the object of study
   (sims/exec fns + auxiliary defs). Definitional termination
   arguments are exempt from the re-proof ban (Lean's checker demands
   its own measure — no ACL2 artifact can stand in).
2. Isomorphism theorems (encode/exec correspondences; the decode
   transport that consumes `driver_replayed%` constants) — to be
   aggressively industrialized, not sorting-coupled.
D5 carve-out (confirmed under the same test): GROUND-ZERO rule content
is axiomatic/bootstrap in ACL2 — there is no capturable proof to
replay — and its content is properties of the trusted-core model, i.e.
the semantics layer. D5 covers PREDEFINED rules ONLY; a discharger for
a book-proven rule is forbidden.

Win states (the success bar that replaces "unconditional native"):
- conditional replay with CLEAR SORRY — acceptable iff the hypothesis
  cannot be replayed yet;
- unconditional via replay — REQUIRED where the hypothesis can be
  replayed.
Forbidden: Lean-side versions of facts ACL2 will eventually give us
for free.

## Root cause (agreed diagnosis)

Completion pressure ("unconditional native" as the bar) met incomplete
replay coverage (the R-lane gap, the registry gap, no TP-replay
discharge); the D5 gz precedent made the `dis_*` pattern look
sanctioned as it widened from gz rules to user content; and the seam
gate checks presence of the replayed input, never absence of forbidden
inputs. Note: the 2026-07-31 criterion already banned bridge lemmas
relating two different functions — this class was drift, not a
sanctioned exception.

## Inventory summary (both auditors, consolidated)

- FORBIDDEN theorems: ~36. Sorting.lean 15 (after D5 reclassification):
  `permExec_eq_convert`, `dis_convert_perm`, `howManyExec_rmExec`,
  `howManyExec_zero_of_membExec_nil`, `dis_insert_tp`,
  `dis_how_many_tp`, `dis_all_rel_tp`, `dis_evens_tp`,
  `dis_append_tp`, `dis_acl2_count_tp`, `dis_merge2_total`,
  `dis_msort_total`, `dis_o_lt_total`, `dis_pce_total`,
  `dis_bnext_total`. Rest: `Lifting.drv_tp_len`; SimpleWorld's hand
  replay + 6 dischargers + 3 drv_total (dead); AppAssoc's hand replay
  + 2; Perm's 4 (all dead); EquisortWitness's 4 TP dischargers.
- FORBIDDEN-SUPPORT: ~25 (file-local; die with their parents).
- D5-CLASS (allowed, mis-homed): `dis_plus_comm`, `dis_plus_comm2`,
  `dis_plus_assoc`, `dis_plus_if_lift`, `dis_equal_if_lift` — gz rule
  content, no subject fn; re-homed to `Imported/GzPrelude.lean` with
  the predefined-only scope guard.
- TAINTED wrappers: 24; catalog `.native` flips: 20 of 44 (CAR-APPEND
  rescued by the D5 reclassification).
- CLEAN throughout: all perm natives (8), all ordered-perms (5),
  PermBook/Tree/P8/Validation-p5, the Lifting transport kit, every
  `*_native_of_replayed` decode (no smuggled content found in any),
  all sims and correspondences.
- Machinery whose only product is forbidden: `derive_exec_tp%`,
  `derive_exec_total%` (ExecGen) — deleted after expanding their call
  sites into explicit sorried statements.

## Dispositions

1. `total:` dischargers + hand replays: DELETE (no sorry) — the
   premises/routes are replayable (with_termination; the driver rows
   for simple/app-assoc are green); consumers rewire to replay routes;
   any total: premise the current machinery cannot yet discharge joins
   the REQUIRED-debt list (must be wired, not sorried indefinitely).
2. Content lemmas + `tp:` dischargers with live consumers: statement
   kept, proof → `sorry`, marked `FORBIDDEN-DEBT (2026-08-11)` with
   the unlock named (TP-replay discharge; the R-lane for
   `dis_convert_perm`). Debt visible as `sorryAx`.
3. Dead forbidden items (incl. supports orphaned by 1–2): deleted
   outright.
4. Catalog: `.native` = unconditional-via-replay (axioms exactly
   {propext, Classical.choice, Quot.sound});
   `.nativeSorried` = clear-sorry debt (axioms exactly those three +
   sorryAx; the debt premises NAMED in the entry).
5. KNOWN CONSEQUENCE (accepted by the ruling): the coverage sweep's
   usefi pre-pass consumed `dis_pce_total`/`dis_how_many_tp`
   (Tests/Coverage/Harness.lean) and the AtCanonical instantiations
   consumed the EquisortWitness dischargers — the three
   `*-IS-ISORT` capstone ROWS regress from ✓ to the honest
   conditional/ASSUMED state until legitimate discharge routes exist.
   The golden re-pin carrying this regression is REVIEWED as such —
   an intended, ruled flip, not silent drift.
6. Enforcement: an in-Lean provenance gate — every `dis_*`/`drv_*`
   constant in the mirror namespaces must be on one of three name
   allowlists (`d5Allowed` / `decodeAllowed` / `debtRegistry`, the
   registry additionally requiring `sorryAx` on each entry so a Lean
   re-proof cannot silently replace a sorry); axiom-exactness per
   catalog class. LIMIT (verification audit 2026-08-11, F2,
   probe-confirmed): the gate triggers on the NAME PREFIX — a content
   lemma under a non-`dis_` name (incl. every deleted item's original
   name) is invisible to it. The gate enforces the convention; renamed
   regrowth is caught only by the shape-gate proposal (framing review
   §4, pending ruling) and by per-book-family provenance audits.
