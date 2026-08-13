import ACL2Lean.Imported.Waypoints.Basics
import ACL2Lean.Imported.Waypoints.PermBook
import ACL2Lean.Imported.Waypoints.Tree
import ACL2Lean.Imported.Waypoints.Validation
import ACL2Lean.Imported.Waypoints.ConvertPerm
import ACL2Lean.Imported.Waypoints.OrderedPerms
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Qsort
import ACL2Lean.Imported.Waypoints.Msort
import ACL2Lean.Imported.Waypoints.IsChain
import ACL2Lean.Imported.Waypoints.Bsort
-- the pattern-pin natives' seam check (audit F6) needs the native
import ACL2Lean.Imported.Waypoints.P8ClausifyDetail
-- the axiom gate carries the equisort parametric/at-canonical receipts
-- (R5, gate-cruft review 2026-08-11 — they used to be #guard_msgs pins)
import ACL2Lean.Imported.Waypoints.EquisortParametric
-- the provenance gate scans the WHOLE waypoint layer — the witness kits'
-- debt entries must be visible here
import ACL2Lean.Imported.EquisortWitness

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! # THIS CATALOG IS THE REPLAY METRIC, NOT THE PRODUCT
(two-category ruling, Mike 2026-08-12)

Everything in this module — the entries, the "native" decodes they
point at, the gates — is the METRIC layer: ACL2 notions replayed into
ACL2-like Lean notions, useful as the scoreboard of how far the replay
machinery reaches. It is "worthless, and completely forbidden, to
treat these ACL2-like Lean definitions as top-level results": the
statements here are over `SExpr`/`lexorderB` — the ACL2 value universe
in Lean clothes — and are NEVER presented to a user as theorems. The
PRODUCT is the MIRRORS layer (`ACL2Lean/Mirrors/`): user-supplied,
pure-idiomatic-Lean definitions and theorems, proved VIA this
machinery, containing zero ACL2 notions. A MIRROR is ONLY that;
everything catalogued here is a WAYPOINT (naming restored 2026-08-12
— this catalog long mis-used "mirror" for waypoints). Historical
prose below still says "mirror"/"native" for these entries — read
those words as WAYPOINT. -/

/-! ## The LIFT-COVERAGE GATE (W2(a), validator/lifter arc)

Every GREEN row of the sweep golden must carry an explicit lift DECISION:
a waypoint (whose constant must exist), an explicit PENDING marker
(the blocking work named), or replayed-only (no non-vacuous native fact —
reflexive decodes and type-absorbed statements). A NEW green row without a
catalog entry FAILS this build — "replayed but never lifted" can no longer
accumulate silently (the survey's headline finding, now a ratchet). The
golden is the input, so the catalog can never drift from the sweep.

### THE WAYPOINT CRITERION (MDD-ratified 2026-07-31)

A waypoint must be readable and trusted by a Lean user who does not speak
ACL2, with minimal Lean-side trust obligations. Two BANNED antipatterns:

1. **Mixed vocabulary.** The STATEMENT may use only Lean/Mathlib
   notions (`List`, `count`, `++`, `erase`, `headD`, `contains`,
   `IsChain`, `Perm`/`isPerm`, `Bool`, `==`) plus SELF-CONTAINED Lean
   definitions over the `SExpr` inductive (e.g. `lexorderB`, `isortL`,
   `relL` — plain recursive functions with NO reference to the
   EVALUATOR LAYER: `evalOpt`, `EvTrue`, `World`, `boolEnc`, or any
   `*Exec` function; pure SExpr value VIEWS such as `Logic.toRat`,
   reached through `lexorder`'s number comparison, are acceptable —
   audit 2026-07-31 §8 wording fix). Mechanized by the CRITERION-1 GATE
   below. SExpr-level notions are admissible exactly when the imported
   theorem is genuinely ABOUT the ACL2 value universe (the lexorder
   ruling; note the value universe excludes complex rationals —
   BUG-009 — so "every input" quantifiers range over the model);
   where a standard-Lean-type reading exists, prefer it.
2. **Ornamental import.** The PROOF's Lean-side bridge may only
   EVALUATE (per-function simulation lemmas — a program computes its
   own native reading on encoded inputs) and DECODE (two-valuedness,
   projections). Every inter-function fact — the theorem's actual
   content — must flow through the replayed-statement seam. A bridge
   lemma relating two DIFFERENT functions is doing ACL2's job in Lean
   and is banned. Mechanized below: the SEAM GATE checks each native
   entry's proof term transitively consumes its `driver_replayed%`
   constant (deterministic, in-Lean; catches fully-detached proofs —
   the subtler ornamental cases remain an audit item). KNOWN GATE
   LIMITATION (audit 2026-07-31, outside finding §4): the seam is
   matched by NAME reachability, so within one book a mis-paired
   catalog seam that the proof reaches through an in-book rule
   discharge (e.g. ORDEREDP-QSORT reaches orderedpAppendReplayedCond
   via dis_rule_orderedp_append) would pass — the gate rules out
   DETACHMENT, not MIS-PAIRING; seam pairings stay an audit item. -/

private def liftCoverageGolden : String :=
  include_str "../../../Tests/driver-coverage.golden"

inductive LiftStatus where
  /-- A proved waypoint: the theorem constant + its SEAM (the
      `driver_replayed%` constant its proof must consume). Axioms must
      be EXACTLY {propext, Classical.choice, Quot.sound} — unconditional
      via replay, no debt (the thin-Lean ruling's REQUIRED win state). -/
  | native (decl : Lean.Name) (seam : Lean.Name)
  /-- A waypoint carrying CLEAR-SORRY debt (thin-Lean ruling
      2026-08-11): the decode consumes the replayed statement, but one
      or more premises rest on sorried FORBIDDEN-DEBT statements whose
      legitimate replay route does not exist yet. Axioms must be EXACTLY
      the standard three + `sorryAx`; `debt` NAMES the sorried premises
      and their unlocks. Retires to `.native` premise-by-premise as
      coverage arcs land. -/
  | nativeSorried (decl : Lean.Name) (seam : Lean.Name) (debt : String)
  | pending (blockedOn : String)
  | replayedOnly (why : String)

/-- The catalog: one DECISION per green sweep row (book, theorem, status). -/
def liftCatalog : List (String × String × LiftStatus) := [
  ("simple", "MY-LEN-MY-APP", .native ``my_len_my_app_native_driver ``mylenReplayedCond),
  ("00-direct", "GROUND-ARITH", .native ``ground_arith_native ``groundArithReplayedCond),
  ("00-direct", "SQ-OF-3", .native ``sq_of_3_native ``sqOf3ReplayedCond),
  ("00-direct", "SQ-REWRITES", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("01-multi-theorem", "APP-CONS-CAR", .native ``car_cons_native ``appConsCarReplayedCond),
  ("01-multi-theorem", "APP-NIL", .pending "rule:CONS-CAR-CDR discharger + the true-listp hypothesis decode (the row replays green; audit F7 corrected the stale G5 reason)"),
  ("01-multi-theorem", "LEN2-APP", .pending "len2 world dischargers (entry-1 recipe over the 01 world)"),
  ("02-rev", "APP-ASSOC", .native ``app_assoc_native_driver ``appAssocReplayedCond),
  ("02-rev", "TRUE-LISTP-REV", .pending "the flatten-recipe waypoint (the image-of-enc fact, cf TRUE-LISTP-FLATTEN — unconditional, transfers directly)"),
  ("02-rev", "APP-NIL", .pending "rule:CONS-CAR-CDR discharger + the true-listp hypothesis decode"),
  ("02-rev", "REV-APP", .pending "rev correspondence + tp:REV/rule:CONS-CAR-CDR dischargers"),
  ("02-rev", "REV-REV", .pending "rev correspondence + tp:REV/rule:CONS-CAR-CDR dischargers"),
  ("03-linear", "LEN2-NONNEG", .pending "len2 dischargers; Nat form is type-absorbed"),
  ("03-linear", "LEN2-CDR-SMALLER", .pending "len2 dischargers"),
  ("03-linear", "LINEAR-CHAIN", .pending "#50 DP tactic decode"),
  ("04-multi-case-induction", "EVENLEN-BOOLEANP", .pending "boolean-recognizer decode (near type-absorbed)"),
  ("05-hints", "LEN2-APP-HELPER", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-VIA-USE", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-VIA-INDUCT", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-NO-HELPER", .pending "len2 dischargers"),
  ("06-measure", "COUNT-DOWN-ZERO", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("07-mutual-recursion", "MY-EVENP-3-IS-NIL", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("07-mutual-recursion", "MY-ODDP-3-IS-T", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("08-equality-reasoning", "CDR-CONS-REFL", .native ``cdr_cons_native ``cdrConsReplayedCond),
  ("08-equality-reasoning", "EQUAL-SYMM", .native ``equal_symm_native ``equalSymmReplayedCond),
  ("08-equality-reasoning", "EQUAL-TRANS", .native ``equal_trans_native ``equalTransReplayedCond),
  ("09-defn-unfold", "SQ-REWRITES", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("09-defn-unfold", "IDF-REWRITES", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("10-tree-induction", "TRUE-LISTP-APP", .pending "the flatten-recipe waypoint (unconditional — transfers directly)"),
  ("10-tree-induction", "TRUE-LISTP-FLATTEN", .native ``true_listp_flatten_native_driver ``trueListpFlattenReplayed),
  ("12-multi-controller", "LEN-ZIP2", .pending "zip2 correspondence (validator/lifter backlog)"),
  ("13-multi-measured-var", "LEN-INTERLEAVE", .pending "interleave correspondence (backlog)"),
  -- PROMOTED to `.native` 2026-08-13 (Basics-closeout increment A): the
  -- accumulator correspondence exists now — `revAccExec`/`rev_acc_exec_corr`
  -- (derive_exec%) plus the ALIGNED reading's iso `revAccExec_enc`
  -- (derive_sim%, the template gate's decisive case). Zero debt: the row
  -- has been unconditional since the TP finale.
  ("14-accumulator", "LEN-REV-ACC",
    .native ``len_rev_acc_native_driver ``lenRevAccReplayedCond),
  ("15-nested-induction", "NESTED-INDUCTION", .pending "backlog (validator/lifter survey)"),
  ("16-three-way", "LEN-ZIP3", .pending "zip3 correspondence (backlog)"),
  ("17-rule-application", "TLP-APP-NIL", .pending "rule-application family decode (backlog)"),
  ("17-rule-application", "TLP-APP-NIL-TWICE", .pending "rule-application family decode (backlog)"),
  ("sorting/perm", "PERM-CONS", .native ``perm_cons_native_driver ``permConsReplayedCond),
  ("sorting/perm", "PERM-SYMMETRIC", .native ``perm_symmetric_native_driver ``permSymmetricReplayed),
  ("sorting/perm", "MEMB-RM", .native ``memb_rm_native_driver ``membRmReplayed),
  ("sorting/perm", "PERM-MEMB", .native ``perm_memb_native_driver ``permMembReplayed),
  ("sorting/perm", "COMM-RM", .native ``comm_rm_native_driver ``commRmReplayed),
  ("sorting/perm", "PERM-RM", .native ``perm_rm_native_driver ``permRmReplayed),
  ("sorting/perm", "PERM-TRANSITIVE", .native ``perm_transitive_native_driver ``permTransitiveReplayed),
  ("sorting/perm", "PERM-IS-AN-EQUIVALENCE", .native ``perm_refl_native_driver ``permEquivReplayed),
  -- convert-perm-to-how-many (2a — the DEPENDENCY book, in the sweep so
  -- its trees discharge consumer rule: hypotheses cross-book). Its green
  -- rows are the book's internal lemma ladder toward the R7-blocked
  -- CONVERT-PERM-TO-HOW-MANY; the three native-worthy count facts are
  -- PENDING (P3 decides), the tlfix/plumbing rows replayed-only.
  ("sorting/convert-perm-to-how-many", "HOW-MANY-RM",
    .native ``how_many_rm_native_driver ``howManyRmReplayedCond),
  ("sorting/convert-perm-to-how-many", "NOT-MEMB-IMPLIES-RM-IS-NO-OP",
    .native ``not_memb_rm_noop_native_driver
      ``notMembRmNoopReplayedCond),
  ("sorting/convert-perm-to-how-many", "NOT-MEMB-IMPLIES-HOW-MANY-IS-0",
    .native ``not_memb_how_many_0_native_driver ``notMembHowMany0ReplayedCond),
  ("sorting/convert-perm-to-how-many", "HOW-MANY-RM-GENERAL",
    .native ``how_many_rm_general_native_driver
      ``howManyRmGeneralReplayedCond),
  -- PROMOTED to `.native` 2026-08-13 (the ATOM-leg increment): its last
  -- debt, total:PERM-COUNTER-EXAMPLE / `dis_pce_total`, retired by the
  -- replay route, so the row is unconditional and the axiom gate's
  -- sorryAx REQUIREMENT (which fired on this entry) is satisfied by the
  -- promotion.
  ("sorting/convert-perm-to-how-many",
    "PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS",
    .native ``pce_is_counterexample_native_driver
      ``pceIsCounterexampleReplayedCond),
  ("sorting/convert-perm-to-how-many", "TRUE-LISTP-RM",
    .replayedOnly "subsumed by the rm simulation: `true-listp` restricts \
      the input to the enc image (exists_enc_of_trueListp), where \
      corr_rm_enc already yields an encoded List — no native content \
      beyond the sim (the type-absorbed true-listp doctrine; the SAME \
      theorem in the ordered-perms book carries the identical decision)"),
  ("sorting/convert-perm-to-how-many", "RM-TLFIX",
    .replayedOnly "tlfix normalization plumbing (erase commutes with \
      tlfix) — no user-facing content"),
  ("sorting/convert-perm-to-how-many", "PERM-COUNTER-EXAMPLE-TLFIX-1",
    .replayedOnly "tlfix normalization plumbing for the R7 functional \
      instantiation — no user-facing content"),
  ("sorting/convert-perm-to-how-many", "MEMB-TLFIX",
    .replayedOnly "tlfix normalization plumbing (memb ignores the final \
      cdr) — no user-facing content"),
  ("sorting/convert-perm-to-how-many", "PERM-COUNTER-EXAMPLE-TLFIX-2",
    .replayedOnly "tlfix normalization plumbing for the R7 functional \
      instantiation — no user-facing content"),
  ("sorting/equisort", "ORDEREDP-SORTFN1",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "TRUE-LISTP-SORTFN1",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "ORDEREDP-SORTFN2",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "TRUE-LISTP-SORTFN2",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "HOW-MANY-SORTFN1",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "HOW-MANY-SORTFN2",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "ORDEREDP-SSORTFN1",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "TRUE-LISTP-SSORTFN1",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "ORDEREDP-SSORTFN2",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "TRUE-LISTP-SSORTFN2",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "HOW-MANY-SSORTFN1",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("sorting/equisort", "HOW-MANY-SSORTFN2",
    .replayedOnly "canonical-model re-proof at the scope's witness (the \
      R6 catalog doctrine, MDD 2026-08-02): the first-class artifact for \
      this book is the PARAMETRIC constrained-theorem constant (Phase 2 \
      ScopeHolds layer), not a witness-level native — no duplicate \
      natives"),
  ("cov-encapsulate", "CF-NUMBERP",
    .replayedOnly "canonical-model replay of the adversarial encapsulate \
      book (formerly the BUG-019 vacuity alarm — its protection now \
      lives in the parametric-statement layer + the witness-deref \
      hard-fail); coverage pin only, never a native"),
  ("cov-encapsulate", "CF-PLUS-COMM",
    .replayedOnly "canonical-model replay of the adversarial encapsulate \
      book (formerly the BUG-019 vacuity alarm — its protection now \
      lives in the parametric-statement layer + the witness-deref \
      hard-fail); coverage pin only, never a native"),
  ("sorting/equisort", "WEAK-SORTFN1-IS-SORTFN2",
    .replayedOnly "the abstract uniqueness capstone — its FIRST-CLASS \
      artifact is the PARAMETRIC constant \
      `weakSortfn1IsSortfn2Parametric` (EquisortParametric.lean, landed \
      Phase 2 item c per the R6 catalog doctrine): the recorded tree \
      over an abstract w with the constraints' STORED-RULE forms as \
      premises (statement pinned in Tests/ParametricPins.lean), which \
      Phase 3's functional instantiation consumes; a witness-level \
      native is the banned masquerade"),
  ("sorting/equisort", "STRONG-SSORTFN1-IS-SSORTFN2",
    .replayedOnly "the abstract uniqueness capstone — its FIRST-CLASS \
      artifact is the PARAMETRIC constant \
      `strongSsortfn1IsSsortfn2Parametric` (EquisortParametric.lean, \
      landed Phase 2 item c per the R6 catalog doctrine): the recorded \
      tree over an abstract w with the constraints' STORED-RULE forms \
      as premises (pinned in Tests/ParametricPins.lean), which Phase \
      3's functional instantiation consumes; a \
      witness-level native is the banned masquerade"),
  -- sorts-equivalent capstones (MSORT/QSORT/BSORT-IS-ISORT): the
  -- entries RETURN 2026-08-13. They were parked when the rows regressed
  -- to ASSUMED under the thin-Lean purge (2026-08-11: the usefi pre-pass
  -- lost its forbidden Lean-side dischargers). The ATOM-leg increment
  -- re-greened all three — the usefi discharge succeeds now that PCE's
  -- admission replays — so the lift-coverage gate demands a decision
  -- again. HONEST STATUS: `.pending` for all three. No capstone waypoint
  -- native exists (there is no `msortL xs = isortL xs` decode in the
  -- layer, and inventing one to satisfy the gate would be exactly the
  -- fake this catalog exists to prevent); the pre-purge entries were
  -- `.pending` too, and their old text is superseded because the usefi
  -- blocker it named is gone.
  ("sorting/sorts-equivalent", "MSORT-IS-ISORT",
    .pending "the capstone, GREEN again (ATOM-leg increment 2026-08-13 \
      — the FI of the equisort parametric theorem at msort/isort now \
      replays; its row conds are total:MERGE2, total:MSORT, \
      rule:TRUE-LISTP-RM, rule:CONVERT-PERM-TO-HOW-MANY). The waypoint \
      native (`msortL xs = isortL xs`) is NOT BUILT — queued behind the \
      mirror buildout; when built it would be `.nativeSorried` on the \
      REQUIRED-class merge2/msort admission debt plus the R-lane's \
      dis_convert_perm. Statement pin: Tests/SortingPins"),
  ("sorting/sorts-equivalent", "QSORT-IS-ISORT",
    .pending "the capstone, GREEN again (ATOM-leg increment 2026-08-13; \
      row conds total:QSORT, total:O<, tp:QSORT, tp:ACL2-COUNT, \
      rule:TRUE-LISTP-RM, rule:CONVERT-PERM-TO-HOW-MANY, the three \
      arithmetic/if-lift gz rules, rule:HOW-MANY-FILTER-1, \
      rule:HOW-MANY-QSORT, rule:ORDEREDP-APPEND). The waypoint native \
      (`qsortL xs = isortL xs`) is NOT BUILT — queued behind the mirror \
      buildout; tp:QSORT and tp:ACL2-COUNT are the arc's named honest \
      survivors (fork-emission items). Statement pin: Tests/SortingPins"),
  ("sorting/sorts-equivalent", "BSORT-IS-ISORT",
    .pending "the capstone, GREEN again (ATOM-leg increment 2026-08-13; \
      row conds total:BNEXT/BSORT/O</O-P, rule:TRUE-LISTP-RM, \
      rule:CONVERT-PERM-TO-HOW-MANY, rule:ORDEREDP-ISORT, \
      rule:ORDEREDP-BSORT, rule:TRUE-LISTP-BNEXT, rule:TRUE-LISTP-BSORT, \
      rule:HOW-MANY-BSORT, linear:HOW-MANY-BAD-PAIRS-BNEXT — the \
      linear: class still has no unlock, cf HOW-MANY-BSORT). The \
      waypoint native (`true-listp xs → bsortL xs = isortL xs`) is NOT \
      BUILT — queued behind the mirror buildout AND the bsort exec kit. \
      Statement pin: Tests/SortingPinsEndgame"),
  ("sorting/convert-perm-to-how-many", "HOW-MANY-TLFIX",
    .replayedOnly "tlfix normalization plumbing (count ignores the final \
      cdr) — no user-facing content"),
  ("sorting/convert-perm-to-how-many", "CONVERT-PERM-TO-HOW-MANY",
    .pending "BLOCKED ON A RED ROW — the R-lane rung-2 wall (restated \
      against the CURRENT golden, mirror wave 2026-08-11; the previous \
      text also cited use:PCE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS, which \
      is STALE — that cond is gone and that row is now green). The \
      row's conds are now cond[rule:PERM-TLFIX] — a SINGLE blocker \
      (tp:HOW-MANY was retired by the replay route, TP-replay arc \
      increment 1 2026-08-12; total:PERM-COUNTER-EXAMPLE by the \
      ATOM-leg increment, 2026-08-13). `rule:PERM-TLFIX`'s ONLY \
      criterion-clean discharger is PERM-TLFIX's own replayed \
      statement — whose row is RED, verbatim: \"PERM-TLFIX → FAIL: \
      replayNode: rune (rewriting-equivalence, NIL) applied under \
      equivalence perm — R-parameterized recipe pending (G1 \
      frontier)\". A Lean-side bridge would be a new \
      content discharger (banned) / the ornamental-import antipattern. \
      NOT blocked on simulation work: the PCE kit \
      (pceExec/pce_exec_corr/pceExec_enc) exists — its \
      `dis_pce_total` companion is GONE, retired by the replay route — \
      and the book's own PCE row is now a landed native (the ELEMENT \
      reading, ruled 2026-08-11). UNLOCK: the R-lane arc (the \
      R-parameterized rewriting-equivalence recipe) greens PERM-TLFIX"),
  ("sorting/isort", "ORDEREDP-ISORT", .native ``orderedp_isort_native_driver ``orderedpIsortReplayedCond),
  ("sorting/isort", "TRUE-LISTP-ISORT", .replayedOnly "subsumed by the isort simulation (corr_isort_enc/isortExec_enc): the program's value on any encoded input IS an encoded List by the sim — no native content beyond it (the type-absorbed true-listp doctrine)"),
  ("sorting/isort", "HOW-MANY-ISORT", .native ``how_many_isort_native_driver ``howManyIsortReplayedCond),
  ("sorting/ordered-perms", "ORDEREDP-RM", .native ``orderedp_rm_native_driver ``orderedpRmReplayed),
  ("sorting/ordered-perms", "ORDEREDP-MEMB", .native ``orderedp_memb_native_driver ``orderedpMembReplayedCond),
  ("sorting/ordered-perms", "EQUAL-CONS", .native ``equal_cons_native_driver ``equalConsReplayedCond),
  ("sorting/ordered-perms", "ORDERED-PERMS", .native ``ordered_perms_native_driver ``orderedPermsCapReplayedCond),
  ("sorting/ordered-perms", "CAR-RM", .native ``car_rm_native_driver ``carRmReplayed),
  ("sorting/ordered-perms", "TRUE-LISTP-RM", .replayedOnly "subsumed by the rm simulation: `true-listp` restricts the input to the enc image (exists_enc_of_trueListp), where corr_rm_enc already yields an encoded List — no native content beyond the sim (the type-absorbed true-listp doctrine; the flatten recipe applies only where NO simulation exists)"),
  -- 2b (linear-verdicts): the two admission-lemma count rows, GREEN via
  -- the linear-verdict machinery. Their Lean-side content EXISTS as the
  -- Count-library facts the hand msort exec kit already uses
  -- (evensExec_consCount_le/lt); the native form (acl2-count over enc)
  -- is P3's decode decision.
  ("sorting/msort", "ACL2-COUNT-EVENS-WEAK",
    .replayedOnly "internal admission lemma, MEASURE-ABSORBED by the \
      exec-kit simulation (MDD 2026-08-02, the type-absorbed doctrine's \
      measure sibling) — value-level content lives in the Count library \
      (evensExec_consCount_le); a native acl2Count vocabulary enters \
      only if a user-facing count theorem ever needs it"),
  ("sorting/msort", "ACL2-COUNT-EVENS-STRONG",
    .replayedOnly "internal admission lemma, MEASURE-ABSORBED by the \
      exec-kit simulation (MDD 2026-08-02) — value-level content lives \
      in the Count library (evensExec_consCount_lt); see the WEAK \
      entry's rationale"),
  ("sorting/msort", "TRUE-LISTP-MSORT", .replayedOnly "subsumed by the msort simulation (msort_exec_corr/msortExec_enc) — the type-absorbed true-listp doctrine"),
  ("sorting/bsort", "termination:BNEXT",
    .replayedOnly "an internal admission obligation (BNEXT's LEN-measure
      decrease), not a user-facing theorem — the termination:QSORT
      doctrine; its native content is the exec kit's own Lean
      termination"),
  ("sorting/bsort", "TRUE-LISTP-BNEXT",
    .replayedOnly "subsumed by the bnext simulation: `true-listp` \
      restricts the input to the enc image, where bnextExec_enc already \
      yields an encoded List — no native content beyond the sim (the \
      type-absorbed true-listp doctrine, the TRUE-LISTP-RM precedent)"),
  ("sorting/bsort", "HOW-MANY-BNEXT",
    .nativeSorried ``how_many_bnext_native_driver ``howManyBnextReplayedCond
      "total:BNEXT (dis_bnext_total; unlock: with_termination coverage — REQUIRED class)"),
  ("sorting/bsort", "termination:BSORT",
    .replayedOnly "an internal admission obligation (BSORT's BNEXT-SIZE
      measure decrease, via HOW-MANY-BAD-PAIRS-BNEXT's :linear content),
      not a user-facing theorem — the termination:QSORT doctrine"),
  ("sorting/bsort", "HOW-MANY-BAD-PAIRS-BNEXT",
    .nativeSorried ``how_many_bad_pairs_bnext_native_driver
      ``howManyBadPairsBnextReplayedCond
      "total:BNEXT (dis_bnext_total; unlock: with_termination coverage \
       — REQUIRED class); tp:BNEXT-SIZE retired by the replay route, \
       TP-replay arc increment 3 2026-08-13 (the CALLEE-TP shape: its \
       emitted leaf sums a HOW-MANY-SMALLER call, whose own emitted \
       corollary supplies the summand)"),
  ("sorting/bsort", "ORDEREDP-WHEN-BNEXT-CONSTANT",
    .nativeSorried ``orderedp_when_bnext_constant_native_driver
      ``orderedpWhenBnextConstantReplayedCond
      "total:BNEXT (dis_bnext_total; unlock: with_termination coverage \
       — REQUIRED class)"),
  ("sorting/bsort", "ORDEREDP-BSORT",
    .pending "BLOCKED ON A KEPT CONDITION WITH NO UNLOCK CLASS \
      (restated 2026-08-11 after the reuse-vs-mint ruling; tp:BNEXT-SIZE \
      left the row with TP-replay arc increment 3, 2026-08-13). Golden \
      conds: total:BNEXT, total:BSORT, total:O<, total:O-P, \
      linear:HOW-MANY-BAD-PAIRS-BNEXT. Two now \
      discharge (dis_bnext_total, dis_o_lt_total); the blocker is \
      `linear:HOW-MANY-BAD-PAIRS-BNEXT`, whose CLASS has no existing \
      unlock — the ruling caps minting at the classes that already \
      have one (TP-replay, with_termination/total), and `linear:` has \
      neither, so minting it is out of scope for an executor. UNLOCK: \
      the linear/DP replay route for the stored :LINEAR rule (or a \
      ruling extending the mint cap); total:BSORT and total:O-P retire \
      with with_termination admission coverage. Second frontier, \
      behind them: the native `orderedpRec (bsortL l)` needs a bsort \
      kit, whose Lean-side termination artifact IS the bubble-size \
      decrease (P2 admits it by the MEASURE-ABSORBED precedent — and \
      the native measure `bnextSizeL` + its decrease now EXIST as this \
      wave's HOW-MANY-BAD-PAIRS-BNEXT native, so the kit is a build, \
      not a research question) — not attempted in this wave"),
  ("sorting/bsort", "TRUE-LISTP-BSORT",
    .replayedOnly "subsumed by the bsort simulation: the enc image is
      closed under bsortExec (the type-absorbed true-listp doctrine,
      the TRUE-LISTP-RM precedent)"),
  ("sorting/bsort", "HOW-MANY-BSORT",
    .pending "BLOCKED ON A KEPT CONDITION WITH NO UNLOCK CLASS \
      (restated 2026-08-11 after the reuse-vs-mint ruling) — the \
      ORDEREDP-BSORT blocker exactly (tp:HOW-MANY retired by the \
      replay route, TP-replay arc increment 1; tp:BNEXT-SIZE by \
      increment 3). Golden conds: \
      total:BNEXT, total:BSORT, total:O<, total:O-P, \
      linear:HOW-MANY-BAD-PAIRS-BNEXT; only \
      `total:BSORT`, `total:O-P` and \
      `linear:HOW-MANY-BAD-PAIRS-BNEXT` are undischarged, and the \
      `linear:` class has no existing unlock (the mint cap excludes \
      it). Same unlocks, same second frontier (the bsort kit) as \
      ORDEREDP-BSORT; the native would be \
      `(bsortL l).count e = l.count e`"),
  ("sorting/bsort", "HOW-MANY-SMALLER-BNEXT",
    .nativeSorried ``how_many_smaller_bnext_native_driver
      ``howManySmallerBnextReplayedCond
      "total:BNEXT (dis_bnext_total; unlock: with_termination \
       coverage — REQUIRED class)"),
  ("sorting/msort", "HOW-MANY-MERGE2", .nativeSorried ``how_many_merge2_native_driver ``howManyMerge2ReplayedCond
      "total:MERGE2 (dis_merge2_total; REQUIRED — with_termination coverage)"),
  ("sorting/msort", "HOW-MANY-EVENS-AND-ODDS", .native ``how_many_evens_and_odds_native_driver ``howManyEvensOddsReplayedCond),
  ("sorting/msort", "ORDEREDP-MSORT", .nativeSorried ``orderedp_msort_native_driver ``orderedpMsortReplayedCond
      "total:MERGE2/MSORT (dis_merge2_total, dis_msort_total; \
       REQUIRED — with_termination coverage); tp:EVENS retired by the \
       replay route, TP-replay arc increment 2 2026-08-13"),
  ("sorting/msort", "HOW-MANY-MSORT", .nativeSorried ``how_many_msort_native_driver ``howManyMsortReplayedCond
      "total:MERGE2/MSORT (REQUIRED)"),
  ("sorting/qsort", "termination:QSORT", .replayedOnly "an internal admission obligation, not a user-facing theorem: its native content (the filter-count decreases) IS qsortExec own kernel-checked Lean termination proof (filterExec_consCount_le)"),
  ("sorting/qsort", "HOW-MANY-APPEND", .native ``how_many_append_native_driver ``howManyAppendReplayedCond),
  ("sorting/qsort", "ORDEREDP-APPEND", .native ``orderedp_append_native_driver ``orderedpAppendReplayedCond),
  ("sorting/qsort", "HOW-MANY-FILTER-1", .native ``how_many_filter_1_native_driver ``howManyFilter1ReplayedCond),
  ("sorting/qsort", "HOW-MANY-QSORT", .nativeSorried ``how_many_qsort_native_driver ``howManyQsortReplayedCond
      "total:O< (dis_o_lt_total; REQUIRED) + tp:ACL2-COUNT (dis_acl2_count_tp)"),
  ("sorting/qsort", "PERM-QSORT", .nativeSorried ``perm_qsort_native_driver ``permQsortReplayedCond
      "total:O< (dis_o_lt_total; REQUIRED) + tp:ACL2-COUNT + rule:CONVERT-PERM-TO-HOW-MANY (dis_convert_perm; unlock: the R-lane arc); total:PERM-COUNTER-EXAMPLE retired by the replay route, TP-replay arc's ATOM-leg increment 2026-08-13"),
  ("sorting/qsort", "CAR-APPEND", .native ``car_append_native_driver ``carAppendReplayedCond),
  ("sorting/qsort", "ALL-REL-FILTER-1", .native ``all_rel_filter_1_native_driver ``allRelFilter1ReplayedCond),
  ("sorting/qsort", "ALL-REL-FILTER-2", .native ``all_rel_filter_2_native_driver ``allRelFilter2ReplayedCond),
  ("sorting/qsort", "ALL-REL-RM-1", .native ``all_rel_rm_1_native_driver ``allRelRm1ReplayedCond),
  ("sorting/qsort", "ALL-REL-RM-2", .native ``all_rel_rm_2_native_driver ``allRelRm2ReplayedCond),
  ("sorting/qsort", "PERM-IMPLIES-EQUAL-ALL-REL-2", .native ``perm_implies_equal_all_rel_2_native_driver ``permImpliesAllRel2Replayed),
  ("sorting/qsort", "ORDEREDP-QSORT", .nativeSorried ``orderedp_qsort_native_driver ``orderedpQsortReplayedCond
      "total:O< (dis_o_lt_total; REQUIRED) + tp:ACL2-COUNT (dis_acl2_count_tp) + rule:CONVERT-PERM-TO-HOW-MANY (dis_convert_perm); tp:ALL-REL retired by the replay route and rule:ORDEREDP-APPEND's wrapper is CLEAN as of TP-replay arc increments 4-5, and total:PERM-COUNTER-EXAMPLE by the ATOM-leg increment, 2026-08-13; unlock: the ACL2-COUNT tp + the R-lane"),
  ("sorting/qsort", "TRUE-LISTP-QSORT", .replayedOnly "subsumed by the qsort simulation (qsort_exec_corr/qsortExec_enc) — the type-absorbed true-listp doctrine")]

/-- SEAM REACHABILITY — the ONE copy (R4, gate-cruft review 2026-08-11;
    there used to be two cosmetically-divergent inlines). Does `start`'s
    proof term transitively consume `seam`? Only constants inside
    `ACL2.Imported.Waypoints` are expanded; the seam itself is matched by
    NAME and never expanded (its proof object is huge). Deterministic,
    in-Lean. -/
def seamReaches (env : Lean.Environment) (start seam : Lean.Name) : Bool :=
  Id.run do
    let mut frontier : List Lean.Name := [start]
    let mut visited : Lean.NameSet := {}
    let mut found := false
    while !found && !frontier.isEmpty do
      let c := frontier.head!
      frontier := frontier.tail!
      unless visited.contains c do
        visited := visited.insert c
        if c == seam then
          found := true
        else if (`ACL2.Imported.Waypoints).isPrefixOf c then
          if let some ci := env.find? c then
            if let some v := ci.value? then
              frontier := v.getUsedConstants.toList ++ frontier
    return found

open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  -- parse the golden's green rows, book-qualified
  let mut rows : List (String × String) := []
  let mut book := ""
  for line in liftCoverageGolden.splitOn "\n" do
    if line.startsWith "• " then
      book := (((line.drop 2).toString.splitOn " ").headD "").dropSuffix ":" |>.toString
    else if line.startsWith "    " && (line.splitOn " → REPLAYED ✓").length > 1 then
      rows := rows ++ [(book, ((line.trimAscii.toString.splitOn " → ").headD ""))]
  -- every green row has exactly one catalog decision
  for (b, n) in rows do
    match liftCatalog.filter (fun (cb, cn, _) => cb == b && cn == n) with
    | [(_, _, st)] =>
      -- `.nativeSorried` (thin-Lean ruling 2026-08-11) rides the same
      -- existence + seam checks; only the axiom gate distinguishes it
      let declSeam? := match st with
        | .native decl seam => some (decl, seam)
        | .nativeSorried decl seam _ => some (decl, seam)
        | _ => none
      if let some (decl, seam) := declSeam? then
        unless (← getEnv).contains decl do
          throwError "lift-coverage gate: {b}/{n} claims native {decl}, \
            which does not exist"
        -- THE SEAM GATE (waypoint criterion, antipattern 2): the native
        -- proof must transitively CONSUME its replayed statement
        -- (`seamReaches`, the shared helper).
        unless seamReaches (← getEnv) decl seam do
          throwError "lift-coverage gate: {b}/{n}'s native proof does \
            not consume its replayed statement {seam} — the \
            ornamental-import antipattern (waypoint criterion 2)"
    | [] => throwError "lift-coverage gate: green row {b}/{n} has NO \
        catalog decision — add a native entry, a PENDING marker, or a \
        replayed-only justification"
    | _ => throwError "lift-coverage gate: {b}/{n} has multiple catalog \
        entries"
  -- no stale catalog entries (an entry whose row vanished)
  for (b, n, _) in liftCatalog do
    unless rows.contains (b, n) do
      throwError "lift-coverage gate: catalog entry {b}/{n} matches no \
        green golden row (stale — remove or fix)"

-- BUILD-FAILING axiom gate (audit #4; completed to ALL native entries in
-- audit #5; DERIVED from the catalog 2026-08-06 — overall-project audit
-- P2-12/N6): `#print axioms` only prints — this run_cmd THROWS if any
-- native entry ever acquires an axiom beyond the classical trio (sorryAx,
-- native_decide's ofReduceBool, …), so a future edit cannot smuggle a hole
-- into the native layer without failing CI.
--
-- Two layers, no hand lists (gate-cruft review 2026-08-11, R3):
--   (1) a WIDE SCAN over every `_driver`-suffixed theorem under
--       `ACL2.Imported.Waypoints` — catalog natives, their Mathlib-form
--       COROLLARIES, and the pattern-pin natives that live outside the
--       driver-coverage golden alike — bounding all of them by the
--       classical trio + `sorryAx`. This replaces the `corollaries` /
--       `sorriedCorollaries` hand lists AND the extra-natives gate's
--       axiom half; a new corollary is now gated by EXISTING, not by
--       remembering to enumerate it.
--   (2) the catalog-driven REFINEMENT: `.native` ⇒ no `sorryAx` at all,
--       `.nativeSorried` ⇒ `sorryAx` REQUIRED (an entry that loses its
--       debt must be PROMOTED, so the debt registry cannot overstate).
-- The refinement's precision is what the wide scan cannot give: (1) is
-- deliberately the loose outer bound.
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  -- (1) THE WIDE `_driver` SCAN
  let env ← getEnv
  let mut drivers : List Name := []
  for (c, ci) in env.constants.toList do
    if (`ACL2.Imported.Waypoints).isPrefixOf c && !c.isInternalDetail then
      if let .thmInfo _ := ci then
        if (c.componentsRev.headD Name.anonymous).toString.endsWith
            "_driver" then
          drivers := drivers ++ [c]
  for n in drivers do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a =>
      !allowed.contains a && a != ``sorryAx)
    unless bad.isEmpty do
      throwError "native-entry axiom gate: {n} uses forbidden axioms \
        {bad} (a waypoint `_driver` theorem may carry only the classical \
        trio, plus sorryAx where a catalogued debt entry declares it)"
  -- (2) THE CATALOG-DRIVEN REFINEMENT
  let catalogNatives : List Name := liftCatalog.filterMap fun (_, _, st) =>
    match st with
    | .native decl _ => some decl
    | _ => none
  let catalogSorried : List Name := liftCatalog.filterMap fun (_, _, st) =>
    match st with
    | .nativeSorried decl _ _ => some decl
    | _ => none
  for n in catalogNatives do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "native-entry axiom gate: {n} uses forbidden axioms {bad}"
  for n in catalogSorried do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a =>
      !allowed.contains a && a != ``sorryAx)
    unless bad.isEmpty do
      throwError "native-entry axiom gate: sorried entry {n} uses \
        forbidden axioms {bad}"
    unless axs.contains ``sorryAx do
      throwError "native-entry axiom gate: {n} is catalogued \
        .nativeSorried but carries NO sorryAx — its debt is retired; \
        PROMOTE the entry to .native"
  -- (3) THE EQUISORT RECEIPTS (R5, gate-cruft review 2026-08-11): the
  -- four capstone constants' axiom sets, moved here from the
  -- `#guard_msgs` pins in `Waypoints/EquisortParametric.lean` (they are
  -- axiom receipts, not statement pins — one home for axiom facts).
  -- ALL FOUR are trio-clean as of 2026-08-13: the Parametric pair are
  -- the first-class artifacts, and the AtCanonical pair — sorry-backed
  -- from the thin-Lean purge until the ATOM-leg increment drained its
  -- last debt — is now the FULLY-BACKED non-vacuity witness.
  for n in [``ACL2.Imported.Waypoints.weakSortfn1IsSortfn2Parametric,
            ``ACL2.Imported.Waypoints.strongSsortfn1IsSsortfn2Parametric,
            -- PROMOTED 2026-08-13 (the ATOM-leg increment): the
            -- AtCanonical pair's last FORBIDDEN-DEBT discharger
            -- (`dis_pce_total`) retired, its `totals [...]` clause is
            -- gone, and the sorryAx REQUIREMENT below duly failed the
            -- build and forced this review — the promotion-forcing gate
            -- working as designed. The NON-VACUITY WITNESSES ARE NOW
            -- FULLY BACKED: every discharged premise of these two
            -- instantiations arrives by replay.
            ``ACL2.Imported.Waypoints.weakSortfn1IsSortfn2AtCanonical,
            ``ACL2.Imported.Waypoints.strongSsortfn1IsSsortfn2AtCanonical] do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "equisort receipt: {n} uses forbidden axioms {bad} — \
        the parametric capstones are the first-class artifacts and the \
        AtCanonical pair is their fully-backed non-vacuity witness; \
        all four must stay trio-clean. A NEW debt under one of them \
        must be registered and the constant moved back to a \
        sorryAx-required list, never left here."

-- CRITERION-1 GATE — DELETED (two-category ruling, 2026-08-12).
-- It policed the statement VOCABULARY of the waypoint layer as if
-- waypoints were the product. They are not: this whole catalog is the
-- REPLAY METRIC (ACL2-like Lean waypoints; useful as a scoreboard,
-- never a top-level result), and the vocabulary of a metric layer is
-- nobody's concern. It had also already grown an exemption list — the
-- rot sign. The REAL vocabulary gate (zero ACL2 notions, enforced)
-- belongs at the product layer (ACL2Lean/Mirrors/, `just check-mirrors-pure`), where any ACL2-side
-- constant in a statement is definitionally a bug.

/-! ## PROVENANCE GATE (thin-Lean ruling 2026-08-11)

Mechanizes the ban that the mirror-provenance audit found unenforced:
no Lean-side content discharger may exist in the waypoint layer outside
(a) the D5 GzPrelude (ground-zero rule content — the ratified
carve-out) and (b) the registered FORBIDDEN-DEBT set, every member of
which MUST carry `sorryAx` (a from-scratch re-proof sneaking back in
place of a sorry fails the build — the only legitimate retirement of a
debt entry is deletion in favor of a replay route). A NEW `dis_*`/
`drv_*` constant in the waypoint namespaces matching neither list fails.
In-Lean, deterministic (environment scan).
THREAT MODEL (two-standard rule, 2026-08-11): a speedbump against
forgetting the ban, not a barrier against circumvention (a renamed
content lemma passes — known, accepted). DO NOT HARDEN IT. -/
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let d5Allowed : List Name :=
    [``ACL2.Worlds.Sorting.dis_plus_comm,
     ``ACL2.Worlds.Sorting.dis_plus_comm2,
     ``ACL2.Worlds.Sorting.dis_plus_assoc,
     ``ACL2.Worlds.Sorting.dis_plus_if_lift,
     ``ACL2.Worlds.Sorting.dis_equal_if_lift]
  -- the DECODE exception: dis_rule_orderedp_append transports a
  -- replayed statement (hreplayed-consuming) — audited clean
  let decodeAllowed : List Name :=
    [``ACL2.Worlds.Sorting.dis_rule_orderedp_append]
  let debtRegistry : List Name :=
    -- (`dis_insert_tp` and `dis_evens_tp` RETIRED by the replay route,
    -- TP-replay arc increment 2, 2026-08-13 — the CONS return-path shape)
    -- (`dis_all_rel_tp` RETIRED by the replay route, TP-replay arc
    -- increment 4, 2026-08-13 — the arity-3 assembly; `dis_append_tp`
    -- RETIRED by increment 5 — the ARGS-VALUED corollary shape)
    -- (`dis_pce_total` RETIRED by the replay route, TP-replay arc's
    -- ATOM-leg increment, 2026-08-13: PCE's emitted termination clause
    -- rules on `(ATOM X)`, which the branch-fact coverage rule now
    -- reads as `(not (consp X))` — the FIRST REQUIRED-class retirement)
    [``ACL2.Worlds.Sorting.dis_acl2_count_tp,
     ``ACL2.Worlds.Sorting.dis_merge2_total,
     ``ACL2.Worlds.Sorting.dis_msort_total,
     ``ACL2.Worlds.Sorting.dis_o_lt_total,
     ``ACL2.Worlds.Sorting.dis_bnext_total,
     -- (`dis_how_many_smaller_tp` RETIRED by the replay route,
     -- TP-replay arc increment 1, 2026-08-12; the MINTED
     -- `dis_bnext_size_tp` — the bsort-measure TP whose emitted leaf
     -- sums a CALLEE's TP — RETIRED by increment 3, 2026-08-13)
     -- (`dis_sortfn1_insert_tp` / `dis_ssortfn1_insert_tp` RETIRED with
     -- the CONS shape, increment 2; `dis_sortfn1_tp` /
     -- `dis_ssortfn1_tp` — the consp-or-nil class — RETIRED with the
     -- CALLEE-TP shape, increment 3)
     ``ACL2.Worlds.Sorting.dis_convert_perm]
  for n in debtRegistry do
    let axs ← collectAxioms n
    unless axs.contains ``sorryAx do
      throwError "provenance gate: debt entry {n} carries no sorryAx — \
        a Lean-side proof has replaced the sorry. Forbidden (thin-Lean \
        ruling): retire the entry via a replay route instead"
  let env ← getEnv
  let waypointNs : List Name :=
    [`ACL2.Worlds, `ACL2.Imported, `ACL2.Lifting]
  let mut offenders : List Name := []
  for (c, _) in env.constants.toList do
    if waypointNs.any (·.isPrefixOf c) then
      let last := c.componentsRev.headD Name.anonymous
      let s := last.toString
      if s.startsWith "dis_" || s.startsWith "drv_" then
        unless d5Allowed.contains c || decodeAllowed.contains c ||
            debtRegistry.contains c do
          offenders := offenders ++ [c]
  unless offenders.isEmpty do
    throwError "provenance gate: unregistered discharger constant(s) in \
      the waypoint layer: {offenders} — Lean-side content dischargers are \
      forbidden (thin-Lean ruling 2026-08-11); register D5 gz content in \
      GzPrelude or route the fact through a replayed statement"

/-! ## EXTRA-NATIVES SEAM CHECK (audit F6, ruled 2026-08-11; reduced to
the seam half by the gate-cruft review, R3)

Natives whose green row lives OUTSIDE the driver-coverage golden
(pattern-pin books run by `Tests/PatternPins.lean`) cannot take a
row-coupled catalog entry, so nothing pairs them with a seam. This
one-entry list does. Their AXIOMS need no entry here — the wide
`_driver` scan in the axiom gate above already covers them.
THREAT MODEL (two-standard rule): a speedbump against forgetting to
consume the replayed statement — not a barrier. DO NOT HARDEN. -/
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let extraSeams : List (Name × Name × String) :=
    [(``ACL2.Imported.Waypoints.cons_neq_detail_native_driver,
      ``ACL2.Imported.Waypoints.consNeqDetailReplayed,
      "Tests/PatternPins.lean p8-clausify-detail")]
  let env ← getEnv
  for (nat, seam, rowSite) in extraSeams do
    unless seamReaches env nat seam do
      throwError "extra-natives seam check: {nat} does not consume its \
        replayed seam {seam} — the ornamental-import antipattern \
        (row: {rowSite})"

/-! ## DECODE hreplayed-USAGE GATE (ruled 2026-08-11)

Closes the post-purge audit's evasion B: a decode that TAKES a
replayed hypothesis but never uses it would pass every other gate
(the seam gate sees the consumer apply the replayed constant one hop
before the decode) while its native content is proved from scratch —
ornamental import in its purest form. This gate scans every
`*_native_of_replayed` constant (plus the `decodeAllowed` transport)
in the waypoint namespaces and requires: (1) at least one hypothesis
whose type mentions `evalOpt` (the replayed-statement shape), and
(2) every such hypothesis actually OCCURRING in the proof term.
THREAT MODEL (two-standard rule, 2026-08-11): a speedbump against
the honest mistake of proving beside the replayed statement instead
of from it. The pass-to-an-ignoring-auxiliary construction evades it
— known, accepted, PERMANENTLY a non-item. DO NOT HARDEN IT.
The scan's own coverage is a REPORTED NUMBER, not a floor: the decode
count is a `scripts/waypoint-metrics.sh` line (gate-cruft review, R2 —
a build-failing floor over a name pattern buys nothing a watched
metric does not).
TRIPWIRE: when the G2 EvTrue migration lands and this evalOpt-shaped
predicate stops matching, DELETE this gate — do not teach it
EvTrue. -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let waypointNs : List Name :=
    [`ACL2.Worlds, `ACL2.Imported, `ACL2.Lifting]
  let mut decodes : List Name :=
    [``ACL2.Worlds.Sorting.dis_rule_orderedp_append]
  for (c, ci) in env.constants.toList do
    if waypointNs.any (·.isPrefixOf c) && !c.isInternalDetail then
      if let .thmInfo _ := ci then
        let s := (c.componentsRev.headD Name.anonymous).toString
        -- endsWith (not the narrower `_native_of_replayed`): the
        -- R-instance decodes read `_native_<R>_of_replayed`
        -- (perm_cons_native_perm_of_replayed) — census 2026-08-11
        if s.endsWith "_of_replayed" then
          decodes := decodes ++ [c]
  for c in decodes do
    let ci ← getConstInfo c
    let some val := ci.value?
      | throwError "hreplayed-usage gate: {c} has no proof value"
    lambdaTelescope val fun xs body => do
      let mut sawReplayed := false
      for x in xs do
        let ty ← inferType x
        if (ty.find? (·.isConstOf ``ACL2.evalOpt)).isSome then
          sawReplayed := true
          unless body.containsFVar x.fvarId! do
            throwError "hreplayed-usage gate: {c} takes a replayed \
              hypothesis it never USES — ornamental import (waypoint \
              criterion antipattern 2 / audit evasion B); the native \
              content must be proved FROM the replayed statement, \
              not beside it"
      unless sawReplayed do
        throwError "hreplayed-usage gate: {c} has no evalOpt-shaped \
          hypothesis — a decode must consume a replayed statement"

end ACL2.Imported.Waypoints
