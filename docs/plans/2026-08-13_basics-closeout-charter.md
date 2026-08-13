# Basics close-out + the transfer kit — charter

Branch `mdd/basics-closeout` off main @ 2edb2cc. Baseline: 113/116
(84 unconditional); sorries 6; mirrors proved 2/6 Basics Props
(app_assoc_int, len_app_int — both trio-clean); LEN-REV-ACC's row
UNCONDITIONAL since the TP finale but with NO waypoint layer; THE
LIST at 7 measured items. Pre-authorized end-to-end (Mike,
2026-08-13: "roll straight into executing — no signoff needed").

THE ARC: finish what Basics can honestly reach, then industrialize
the lifting FROM the measured hand artifacts — still ahead of the
sorting book, the narrow-slice method applied to the kit itself.

## Queue

A. **The revAcc waypoint slice** — derive_exec% + derive_sim% for
   REV-ACC (14-accumulator book) + decode + catalog entry on the
   unconditional row. THIS IS THE TEMPLATE GATE'S DECISIVE CASE (the
   ruled accumulator ambiguity): the aligned reading (revAccL by the
   exec's own recursion) must PASS; as a deliberate negative probe,
   the reassociating reading (reverse ++ acc) must FAIL with the
   ruled message (probe, record, revert). Zero debt inheritance
   expected (the row is unconditional).
B. **len_revAcc — the third mirror**, hand squares one last time
   (the accumulator's map-hom + len squares + transport), extending
   THE LIST to its final measured form. Trio-clean receipt expected.
C. **mirror_iso% v1** — the square generator, built FROM the list's
   hand squares and validated BY RETIREMENT (the derive_sim%
   protocol): every existing hand square in MirrorProofs regenerated
   same-name/same-statement; template-failure-as-gate at the mirror
   level (a reading that doesn't align = hard error; the escape is a
   replayed book theorem).
D. **The transport assembly generator** — app_assoc_int /
   len_app_int / len_revAcc_int regenerated from declarations;
   target user cost ≈ two lines per theorem. Measure and report
   USER-LINES-PER-MIRROR before/after — the number that must fall
   before sorting is attempted.
E. **Honest deferrals**: app_nil (G5 multi-literal frontier),
   rev_app/rev_rev (the rev-family discharger frontiers) — named in
   the spec file's docstrings, Track FREE items, NOT forced.

   > **CORRECTION (appended 2026-08-13, R0 item 7 — the text above is
   > left as the dated record).** Both stated reasons were STALE:
   > - `app_nil` is **not** blocked by the G5 multi-literal frontier;
   >   its sweep row replays green and UNCONDITIONAL.
   > - `rev_app`/`rev_rev` are **not** blocked by "rev-family
   >   dischargers": `tp:REV` was cleared at `bcb181d` (the
   >   BINARY-APPEND→APP→REV cascade) and `rule:CONS-CAR-CDR` has a
   >   working discharger (`gz_rule_cons_car_cdr`) — it is a kept
   >   condition on no golden row. Both rows are green + unconditional.
   >
   > The REAL blocker for all three is the same and is **mirror-side**:
   > there is no rev exec/iso kit, i.e. decode-layer work. The
   > deferrals stand; only their stated reasons were wrong.
F. **Exit audit** (one adversarial claims reviewer): the decisive
   checks — the revAcc template adjudication genuine both ways; the
   generated squares byte-equivalent to the retired hand ones; the
   three mirror receipts re-derived; no Lean induction closing
   mirror content anywhere (the glue-only-closure check on all three
   theorems). Fix round, TRUE_EXIT=0 (behind invalidate-coverage),
   exit report + merge proposal.

## Discipline

Two-tier gating; goldens row-by-row (the only sanctioned change:
the 14-accumulator row MAY gain a [DISCHARGE] annotation or the
catalog entry — no cond changes expected anywhere); the product
ornamental-import ban; check-mirrors-pure green throughout; the
lexicon's vocabulary; every hand artifact logged to THE LIST at the
moment of writing.

## Exit criterion + escape hatch

Done = A–D landed or honestly walled (a template surprise in C is a
STOP-and-report, not a workaround), E logged, F complete with
TRUE_EXIT=0 and the merge proposal. ESCAPE HATCH (binding): early
exit at any time, any reason or none; fidelity over completion.
MANDATORY-EXIT triggers: the reassociating reading passing the
template (the gate's decisive case failing); any Lean induction
closing mirror content; any cond change in the golden; any purity
weakening.

## ARC LOG — COMPLETE (2026-08-13)

**Exit: full claim-gate `TRUE_EXIT=0` on `d72bcb0` (artifact
`.gate-runs/d72bcb0-20260813T191132Z.log`); merged at `4a600c8`.** The
charter's exit criterion was MET.

- **A — the revAcc slice.** The template's decisive case adjudicated
  both ways (the reassociating reading genuinely fails the template;
  the own-definition reading genuinely passes) — the mandatory-exit
  trigger did NOT fire.
- **B — the third mirror.** `len_revAcc_int` landed **trio-clean**
  (axioms `{propext, Classical.choice, Quot.sound}`), taking
  `ACL2Lean/Mirrors/Basics.lean` to 3 of 6 Props proved
  (`app_assoc_int`, `len_app_int`, `len_revAcc_int`).
- **C — `mirror_iso%`.** The rfl-only ladder, criterion pinned; all
  **15/15** retired hand squares regenerated **byte-identical**.
- **D — `mirror_transport%`.** User lines **69 → 28**; **3 lines per
  future mirror** — the measured go/no-go number.
- **Plus:** the naming pass (7 real collisions eliminated; the
  collision linter live with its coverage arm) and the VOCABULARY
  PRACTICE ruled and applied across all three layers (waypoint
  readings / mirror spec bodies / names — now recorded in CLAUDE.md
  and `docs/LEXICON.md`).
- **F — exit audit.** One DEFECT found (an orchestrator over-claim),
  corrected in place; strong verifications otherwise.
- **E — deferrals.** Three named and NOT forced (see the correction
  note appended to item E above).
