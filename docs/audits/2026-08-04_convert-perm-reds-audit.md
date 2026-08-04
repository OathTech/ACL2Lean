# convert-perm reds sub-arc — audit (2026-08-04)

Branch `mdd/convert-perm-reds` (2c5e925..41133b3), close-out Phase 3.
One adversarial Opus reviewer. Verdict **READY-WITH-FIXES**; both fixes
documentation-level, applied in-arc (this file records both).

## Ground truth the reviewer established

- `just ci` exit 0 (all gates); the three changed rows reproduced live
  and byte-matching the golden; the ✓ column verified AXIOM-checked
  (collectProofAxioms before addDecl), not merely type-checked.
- **The geneqv fidelity claim CONFIRMED VERBATIM in ACL2 source**:
  `add-equivalence-rule` (acl2/defthm.lisp:6294, 6398-6407) putprops a
  `congruences` property giving BOTH argument slots of the relation a
  congruence-rule whose `:rune` is the equivalence rune — and ACL2's own
  comment (defthm.lisp:6340-6382) justifies it by exactly the
  booleanp/sym/trans argument `equivOwnPosCongr` reproduces step for
  step. A faithful mirror, not a shortcut.
- All four σ-instantiations in `equivOwnPosCongr` verified by position
  against the defequiv conjunct shapes (both argIdx cases, both
  and-antecedent orders); the four-site telescope alignment clean.
- BUG-023 anchoring verified by TWO tampers (scratch copies): a
  corrupted sym conjunct → the offer refuses + the consumer hard-fails;
  the equivalence rune removed from the step's :RUNES → hard-fail with
  `cited equivalence runes []`. The citation gate is load-bearing.
- Drift test PASSES: both new arms are general (closed-term key; the
  defequiv shape), no per-case checker added.

## Findings → resolution

- **F1 MEDIUM (fixed — comment/rationale).** The ground-hyp arm's
  stated mechanism was FALSIFIED by a live ACL2 probe: KNOWN-TRUE on
  `(TRUE-LISTP 'NIL)` comes from the BUILT-IN RECOGNIZER TUPLE in
  `type-set-rec` (knownp=T, ZERO runes added; `type-set-rec` has no
  ground-evaluation clause) — not the executable counterpart. The
  replay's closed-form evaluation is a ROUTE SUBSTITUTION for a
  verdict-only type-set step (carve-out-shaped, kernel-checked, same
  value) and the comment now says so honestly.
- **F2 LOW-MEDIUM (recorded in the comment).** The arm consumes no
  per-verdict ACL2 justification — but the reviewer's own probe shows
  the verdict adds NOTHING to anchor on (the marker's :TA-RUNES are the
  cumulative incoming set). Keyed on the closed term alone; noted for
  revisit if the class grows.
- **F3 LOW (accepted).** Guard order correct (in-scope falsity facts
  win); a cross-env litFact fall-through now lands in silent computation
  instead of the loud FC error — detectability only.
- **F11 (verified).** The counter-example row IS a consumer gap: the
  failing recognizer node cites `(:TYPE-PRESCRIPTION TRUE-LISTP-RM)`
  verbatim (log lines 5905-5911), TRUE-LISTP-RM is `:CLASSES
  :TYPE-PRESCRIPTION`, RM has no admission TP. The proposed
  TP-classed-theorem consumer is implementable exactly as recorded.
- **F12 MEDIUM (fixed — TODO corrected).** The `:EQUIV EQUAL`
  mislabeling ALSO affects the enclosing WITH-LEMMA step (the rule's
  :equiv against a post-solidify :RHS — a false EQUAL equation, harmless
  today because the solidify child hard-fails first). The fork emission
  fix is upgraded from optional to a PREREQUISITE of the Phase-6 rung-2
  R threading; `chainReqEq`'s payload flag is a Bool with no user-R
  encoding, strengthening the lane assignment.
- **F10 INFO.** CONVERT-PERM-TO-HOW-MANY is green ON two still-red
  premises (`rule:PERM-TLFIX`, `use:` of the counter-example lemma) —
  disclosed, honest D6 conditions; not an unconditional import.
- F8 INFO: equivfull offers draw on full depProofs (bounded — one
  defequiv per relation); the discharge formula check is same-source
  (documented).

## Reviewer's could-not-verify

F1's attribution probed in the ground-zero world (not a live book
trace); pre-existing lemma statements not re-derived; no
false-ground-hyp tamper (fail-closed argued from replayExecGround's
value check); remote CI (sandbox).

## Fold-back gates

Fixes applied; claim-gate TRUE_EXIT recorded in the fold-back commit.
Remaining reds carry their lanes: PERM-TLFIX → Phase-6 rung-2 R
threading (fork emission prerequisite); counter-example row → the
TP-classed-theorem consumer (next increment); HOW-MANY-RM-GENERAL →
the :PATH emission batch.
