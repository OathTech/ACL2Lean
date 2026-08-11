import ACL2Lean.Imported.Mirrors.Basics
import ACL2Lean.Imported.Mirrors.PermBook
import ACL2Lean.Imported.Mirrors.Tree
import ACL2Lean.Imported.Mirrors.Validation
import ACL2Lean.Imported.Mirrors.ConvertPerm
import ACL2Lean.Imported.Mirrors.OrderedPerms
import ACL2Lean.Imported.Mirrors.Isort
import ACL2Lean.Imported.Mirrors.Qsort
import ACL2Lean.Imported.Mirrors.Msort
import ACL2Lean.Imported.Mirrors.IsChain
import ACL2Lean.Imported.Mirrors.Bsort
-- the extra-natives gate (audit F6) needs the pattern-pin native
import ACL2Lean.Imported.Mirrors.P8ClausifyDetail
-- the provenance gate scans the WHOLE mirror layer — the witness kits'
-- debt entries must be visible here
import ACL2Lean.Imported.EquisortWitness

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The LIFT-COVERAGE GATE (W2(a), validator/lifter arc)

Every GREEN row of the sweep golden must carry an explicit lift DECISION:
a native mirror (whose constant must exist), an explicit PENDING marker
(the blocking work named), or replayed-only (no non-vacuous native fact —
reflexive decodes and type-absorbed statements). A NEW green row without a
catalog entry FAILS this build — "replayed but never lifted" can no longer
accumulate silently (the survey's headline finding, now a ratchet). The
golden is the input, so the catalog can never drift from the sweep.

### THE MIRROR CRITERION (MDD-ratified 2026-07-31)

A mirror must be readable and trusted by a Lean user who does not speak
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
  /-- A proved native mirror: the theorem constant + its SEAM (the
      `driver_replayed%` constant its proof must consume). Axioms must
      be EXACTLY {propext, Classical.choice, Quot.sound} — unconditional
      via replay, no debt (the thin-Lean ruling's REQUIRED win state). -/
  | native (decl : Lean.Name) (seam : Lean.Name)
  /-- A native mirror carrying CLEAR-SORRY debt (thin-Lean ruling
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
  ("simple", "MY-LEN-MY-APP", .nativeSorried ``my_len_my_app_native_driver ``mylenReplayedCond
      "tp:MY-LEN (drv_tp_mylen; unlock: TP-replay discharge)"),
  ("00-direct", "GROUND-ARITH", .native ``ground_arith_native ``groundArithReplayedCond),
  ("00-direct", "SQ-OF-3", .native ``sq_of_3_native ``sqOf3ReplayedCond),
  ("00-direct", "SQ-REWRITES", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("01-multi-theorem", "APP-CONS-CAR", .native ``car_cons_native ``appConsCarReplayedCond),
  ("01-multi-theorem", "APP-NIL", .pending "rule:CONS-CAR-CDR discharger + the true-listp hypothesis decode (the row replays green; audit F7 corrected the stale G5 reason)"),
  ("01-multi-theorem", "LEN2-APP", .pending "len2 world dischargers (entry-1 recipe over the 01 world)"),
  ("02-rev", "APP-ASSOC", .native ``app_assoc_native_driver ``appAssocReplayedCond),
  ("02-rev", "TRUE-LISTP-REV", .pending "the flatten-recipe mirror (the image-of-enc fact, cf TRUE-LISTP-FLATTEN — unconditional, transfers directly)"),
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
  ("10-tree-induction", "TRUE-LISTP-APP", .pending "the flatten-recipe mirror (unconditional — transfers directly)"),
  ("10-tree-induction", "TRUE-LISTP-FLATTEN", .native ``true_listp_flatten_native_driver ``trueListpFlattenReplayed),
  ("12-multi-controller", "LEN-ZIP2", .pending "zip2 correspondence (validator/lifter backlog)"),
  ("13-multi-measured-var", "LEN-INTERLEAVE", .pending "interleave correspondence (backlog)"),
  ("14-accumulator", "LEN-REV-ACC", .pending "accumulator correspondence (backlog)"),
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
    .nativeSorried ``how_many_rm_native_driver ``howManyRmReplayedCond
      "tp:HOW-MANY (dis_how_many_tp; unlock: TP-replay discharge)"),
  ("sorting/convert-perm-to-how-many", "NOT-MEMB-IMPLIES-RM-IS-NO-OP",
    .native ``not_memb_rm_noop_native_driver
      ``notMembRmNoopReplayedCond),
  ("sorting/convert-perm-to-how-many", "NOT-MEMB-IMPLIES-HOW-MANY-IS-0",
    .nativeSorried ``not_memb_how_many_0_native_driver ``notMembHowMany0ReplayedCond
      "tp:HOW-MANY (dis_how_many_tp; unlock: TP-replay discharge)"),
  ("sorting/convert-perm-to-how-many", "HOW-MANY-RM-GENERAL",
    .pending "GREENED in the endgame arc (item I's tau-basis consumer: \
      the *1/3.2 leaf discharges from the recorded slice's \
      NOT-MEMB-IMPLIES-HOW-MANY-IS-0 signature rule, its rule content \
      discharged by that theorem's own replay); the native mirror is a \
      how-many/rm correspondence over the existing rm + how-many sims — \
      wire with the arc's statement-pin wave (item 5), per the \
      unwired-infrastructure ban"),
  ("sorting/convert-perm-to-how-many",
    "PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS",
    .pending "GREENED at the final close-out (the tpthm resurrection + \
      IF-collapse bridge round); the native mirror is the PCE MIRROR \
      BUILD PLAN in TODO (pceExec on the perm_exec_corr template) — \
      wire when the capstone consumer demands it, per the \
      unwired-infrastructure ban"),
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
  -- sorts-equivalent capstones (MSORT/QSORT/BSORT-IS-ISORT): NO entries —
  -- their rows REGRESSED to ASSUMED under the thin-Lean purge
  -- (2026-08-11: the usefi pre-pass lost its forbidden Lean-side
  -- dischargers; the honest offer route carries usefi + fi-self
  -- markers). The catalog tracks GREEN rows only; the entries (and the
  -- retired statement pins) return when the REQUIRED-class admission
  -- coverage + TP-replay discharge re-green the rows.
  ("sorting/convert-perm-to-how-many", "HOW-MANY-TLFIX",
    .replayedOnly "tlfix normalization plumbing (count ignores the final \
      cdr) — no user-facing content"),
  ("sorting/convert-perm-to-how-many", "CONVERT-PERM-TO-HOW-MANY",
    .pending "the book's capstone (perm ↔ counts agree at the witness — \
      the natural native mirror). The PCE exec kit exists (pceExec/\
      pce_exec_corr/dis_pce_total) and the bnext build demonstrates the \
      remaining sim pattern, but the row's conds include rule:PERM-TLFIX \
      and use:PCE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS, whose ONLY \
      criterion-clean dischargers are those theorems' replayed statements \
      — and both rows are RED (the R-lane rung-2 wall; the spine \
      literal-chain frontier). A hand bridge would be the banned \
      ornamental-import pattern. DECLARED at the close-out arc's close \
      (2026-08-05): blocked on those two rows, not on simulation work"),
  ("sorting/isort", "ORDEREDP-ISORT", .nativeSorried ``orderedp_isort_native_driver ``orderedpIsortReplayedCond
      "tp:INSERT (dis_insert_tp; unlock: TP-replay discharge)"),
  ("sorting/isort", "TRUE-LISTP-ISORT", .replayedOnly "subsumed by the isort simulation (corr_isort_enc/isortExec_enc): the program's value on any encoded input IS an encoded List by the sim — no native content beyond it (the type-absorbed true-listp doctrine)"),
  ("sorting/isort", "HOW-MANY-ISORT", .nativeSorried ``how_many_isort_native_driver ``howManyIsortReplayedCond
      "tp:HOW-MANY (dis_how_many_tp; unlock: TP-replay discharge)"),
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
      "total:BNEXT (dis_bnext_total; unlock: with_termination coverage — REQUIRED class) + tp:HOW-MANY (dis_how_many_tp)"),
  ("sorting/bsort", "termination:BSORT",
    .replayedOnly "an internal admission obligation (BSORT's BNEXT-SIZE
      measure decrease, via HOW-MANY-BAD-PAIRS-BNEXT's :linear content),
      not a user-facing theorem — the termination:QSORT doctrine"),
  ("sorting/bsort", "HOW-MANY-BAD-PAIRS-BNEXT",
    .pending "the bubble-pass progress measure (bad-pairs strictly
      decrease unless fixed) — greened by the recursive equal-descent
      protocol (restructure arc); natural native over the bnext sim,
      queued with the bsort cluster's natives"),
  ("sorting/bsort", "ORDEREDP-WHEN-BNEXT-CONSTANT",
    .pending "a bnext fixed point is ordered — GREENED in the endgame
      arc (2e: the expansion detail chain consumed as value equalities,
      the recorded-drop clausify relaxation, the positioned unresolved
      probe); natural native over the bnext sim, queued with the bsort
      cluster's natives"),
  ("sorting/bsort", "ORDEREDP-BSORT",
    .pending "bsort's output is ordered — the interpCount μ-route row
      (restructure arc); native (orderedpL (bsortL l)) over the exec
      kit, queued with the cluster"),
  ("sorting/bsort", "TRUE-LISTP-BSORT",
    .replayedOnly "subsumed by the bsort simulation: the enc image is
      closed under bsortExec (the type-absorbed true-listp doctrine,
      the TRUE-LISTP-RM precedent)"),
  ("sorting/bsort", "HOW-MANY-BSORT",
    .pending "bsort permutes (counts preserved) — the μ-route row
      (restructure arc); native (howManyL (bsortL l) e = howManyL l e),
      queued with the cluster"),
  ("sorting/bsort", "HOW-MANY-SMALLER-BNEXT",
    .pending "count-below invariance across one bubble pass (final
      close-out — greened by the fc-derivations relief + the
      add-literal dedup arm); natural native over the bnext sim
      (howManySmallerL (bnextExec l) e = howManySmallerL l e), queued
      behind the bsort cluster's fork-batch greens"),
  ("sorting/msort", "HOW-MANY-MERGE2", .nativeSorried ``how_many_merge2_native_driver ``howManyMerge2ReplayedCond
      "total:MERGE2 (dis_merge2_total; REQUIRED — with_termination coverage) + tp:HOW-MANY (dis_how_many_tp)"),
  ("sorting/msort", "HOW-MANY-EVENS-AND-ODDS", .nativeSorried ``how_many_evens_and_odds_native_driver ``howManyEvensOddsReplayedCond
      "tp:HOW-MANY (dis_how_many_tp; unlock: TP-replay discharge)"),
  ("sorting/msort", "ORDEREDP-MSORT", .nativeSorried ``orderedp_msort_native_driver ``orderedpMsortReplayedCond
      "total:MERGE2/MSORT (dis_merge2_total, dis_msort_total; REQUIRED) + tp:EVENS (dis_evens_tp)"),
  ("sorting/msort", "HOW-MANY-MSORT", .nativeSorried ``how_many_msort_native_driver ``howManyMsortReplayedCond
      "total:MERGE2/MSORT (REQUIRED) + tp:HOW-MANY (dis_how_many_tp)"),
  ("sorting/qsort", "termination:QSORT", .replayedOnly "an internal admission obligation, not a user-facing theorem: its native content (the filter-count decreases) IS qsortExec own kernel-checked Lean termination proof (filterExec_consCount_le)"),
  ("sorting/qsort", "HOW-MANY-APPEND", .nativeSorried ``how_many_append_native_driver ``howManyAppendReplayedCond
      "tp:HOW-MANY (dis_how_many_tp; unlock: TP-replay discharge)"),
  ("sorting/qsort", "ORDEREDP-APPEND", .nativeSorried ``orderedp_append_native_driver ``orderedpAppendReplayedCond
      "tp:ALL-REL (dis_all_rel_tp) + tp:APPEND (dis_append_tp); unlock: TP-replay discharge"),
  ("sorting/qsort", "HOW-MANY-FILTER-1", .nativeSorried ``how_many_filter_1_native_driver ``howManyFilter1ReplayedCond
      "tp:HOW-MANY (dis_how_many_tp; unlock: TP-replay discharge)"),
  ("sorting/qsort", "HOW-MANY-QSORT", .nativeSorried ``how_many_qsort_native_driver ``howManyQsortReplayedCond
      "total:O< (dis_o_lt_total; REQUIRED) + tp:HOW-MANY/ACL2-COUNT (dis_how_many_tp, dis_acl2_count_tp)"),
  ("sorting/qsort", "PERM-QSORT", .nativeSorried ``perm_qsort_native_driver ``permQsortReplayedCond
      "total:PCE/O< (dis_pce_total, dis_o_lt_total; REQUIRED) + tp:HOW-MANY/ACL2-COUNT + rule:CONVERT-PERM-TO-HOW-MANY (dis_convert_perm; unlock: the R-lane arc)"),
  ("sorting/qsort", "CAR-APPEND", .native ``car_append_native_driver ``carAppendReplayedCond),
  ("sorting/qsort", "ALL-REL-FILTER-1", .nativeSorried ``all_rel_filter_1_native_driver ``allRelFilter1ReplayedCond
      "tp:ALL-REL (dis_all_rel_tp; unlock: TP-replay discharge)"),
  ("sorting/qsort", "ALL-REL-FILTER-2", .nativeSorried ``all_rel_filter_2_native_driver ``allRelFilter2ReplayedCond
      "tp:ALL-REL (dis_all_rel_tp; unlock: TP-replay discharge)"),
  ("sorting/qsort", "ALL-REL-RM-1", .nativeSorried ``all_rel_rm_1_native_driver ``allRelRm1ReplayedCond
      "tp:ALL-REL (dis_all_rel_tp; unlock: TP-replay discharge)"),
  ("sorting/qsort", "ALL-REL-RM-2", .nativeSorried ``all_rel_rm_2_native_driver ``allRelRm2ReplayedCond
      "tp:ALL-REL (dis_all_rel_tp; unlock: TP-replay discharge)"),
  ("sorting/qsort", "PERM-IMPLIES-EQUAL-ALL-REL-2", .native ``perm_implies_equal_all_rel_2_native_driver ``permImpliesAllRel2Replayed),
  ("sorting/qsort", "ORDEREDP-QSORT", .nativeSorried ``orderedp_qsort_native_driver ``orderedpQsortReplayedCond
      "totals (REQUIRED) + tps + rule:CONVERT-PERM-TO-HOW-MANY (dis_convert_perm) + rule:ORDEREDP-APPEND rides the tainted orderedp_append wrapper; unlock: TP-replay + the R-lane"),
  ("sorting/qsort", "TRUE-LISTP-QSORT", .replayedOnly "subsumed by the qsort simulation (qsort_exec_corr/qsortExec_enc) — the type-absorbed true-listp doctrine")]

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
        -- THE SEAM GATE (mirror criterion, antipattern 2): the native
        -- proof must transitively CONSUME its replayed statement.
        -- Deterministic in-Lean used-constants search; only constants
        -- inside this namespace are expanded (the seam is matched by
        -- name, never expanded — its proof object is huge).
        let env ← getEnv
        let mut frontier : List Name := [decl]
        let mut visited : NameSet := {}
        let mut found := false
        while !found && !frontier.isEmpty do
          let c := frontier.head!
          frontier := frontier.tail!
          unless visited.contains c do
            visited := visited.insert c
            if c == seam then
              found := true
            else if (`ACL2.Imported.Mirrors).isPrefixOf c then
              if let some ci := env.find? c then
                if let some v := ci.value? then
                  frontier := v.getUsedConstants.toList ++ frontier
        unless found do
          throwError "lift-coverage gate: {b}/{n}'s native proof does \
            not consume its replayed statement {seam} — the \
            ornamental-import antipattern (mirror criterion 2)"
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
-- into the native layer without failing CI. The `.native` set comes
-- straight from `liftCatalog` (a new entry is gated AUTOMATICALLY — the
-- earlier hand list was one more thing to desync); only the downstream
-- COROLLARIES, which are not catalog rows by design (Mathlib-form
-- restatements of catalog natives), remain enumerated.
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let catalogNatives : List Name := liftCatalog.filterMap fun (_, _, st) =>
    match st with
    | .native decl _ => some decl
    | _ => none
  -- `.nativeSorried` (thin-Lean ruling 2026-08-11): sorryAx REQUIRED
  -- (an entry that loses its debt must be PROMOTED to `.native`, so the
  -- debt registry cannot silently overstate) and nothing else beyond
  -- the classical trio.
  let catalogSorried : List Name := liftCatalog.filterMap fun (_, _, st) =>
    match st with
    | .nativeSorried decl _ _ => some decl
    | _ => none
  let corollaries : List Name :=
    [``ACL2.Imported.Mirrors.perm_cons_native_perm_driver,
     ``ACL2.Imported.Mirrors.isPerm_equivalence_driver,
     ``ACL2.Imported.Mirrors.perm_symm_perm_driver,
     ``ACL2.Imported.Mirrors.perm_trans_perm_driver,
     ``ACL2.Imported.Mirrors.perm_erase_perm_driver,
     ``ACL2.Imported.Mirrors.mem_transport_perm_driver,
     ``ACL2.Imported.Mirrors.ordered_perms_native_perm_driver,
     ``ACL2.Imported.Mirrors.orderedp_rm_isChain_driver,
     ``ACL2.Imported.Mirrors.orderedp_memb_isChain_driver,
     ``ACL2.Imported.Mirrors.p5_dupp_prepend_native_driver]
  -- Mathlib-form corollaries of SORRIED natives inherit the debt
  let sorriedCorollaries : List Name :=
    [``ACL2.Imported.Mirrors.perm_qsort_perm_driver,
     ``ACL2.Imported.Mirrors.orderedp_isort_isChain_driver,
     ``ACL2.Imported.Mirrors.orderedp_msort_isChain_driver,
     ``ACL2.Imported.Mirrors.orderedp_qsort_isChain_driver,
     ``ACL2.Imported.Mirrors.p7_dub_len_native_driver]
  for n in (catalogNatives ++ corollaries) do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "native-entry axiom gate: {n} uses forbidden axioms {bad}"
  for n in (catalogSorried ++ sorriedCorollaries) do
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

-- CRITERION-1 GATE (audit 2026-07-31, outside finding §8): mirror
-- STATEMENT vocabulary, mechanized — every `.native` entry's TYPE must
-- be free of the evaluator layer (evalOpt/EvTrue/World/boolEnc) and of
-- every `*Exec` function. (Value-VIEW helpers like `Logic.toRat`,
-- reached through `lexorderB`'s definition, are acceptable: the ban is
-- the interpreter/exec layer, not pure SExpr arithmetic views — the
-- criterion header wording matches.) In-Lean, deterministic.
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let banned : List Name :=
    [``ACL2.evalOpt, ``ACL2.Replay.EvTrue, ``ACL2.World,
     ``ACL2.Lifting.boolEnc]
  -- The ONE ratified exception: the FLATTEN-RECIPE class (entry 17's
  -- doc) — for a recognizer theorem whose SUBJECT is the imported
  -- program itself, `evalOpt` deliberately remains in the statement
  -- (a fully native restatement would need a simulation that
  -- subsumes, and so bypasses, the replayed theorem).
  let exempt : List Name :=
    [``ACL2.Imported.Mirrors.true_listp_flatten_native_driver]
  for (b, n, st) in liftCatalog do
    let decl? := match st with
      | .native decl _ => some decl
      | .nativeSorried decl _ _ => some decl
      | _ => none
    if let some decl := decl? then
      if exempt.contains decl then continue
      let some ci := (← getEnv).find? decl
        | throwError "criterion-1 gate: {decl} missing"
      for c in ci.type.getUsedConstants do
        if banned.contains c then
          throwError "criterion-1 gate: {b}/{n}'s statement mentions \
            {c} — evaluator vocabulary in a mirror statement \
            (mirror criterion 1)"
        if c.toString.endsWith "Exec" then
          throwError "criterion-1 gate: {b}/{n}'s statement mentions \
            the exec function {c} (mirror criterion 1)"

/-! ## PROVENANCE GATE (thin-Lean ruling 2026-08-11)

Mechanizes the ban that the mirror-provenance audit found unenforced:
no Lean-side content discharger may exist in the mirror layer outside
(a) the D5 GzPrelude (ground-zero rule content — the ratified
carve-out) and (b) the registered FORBIDDEN-DEBT set, every member of
which MUST carry `sorryAx` (a from-scratch re-proof sneaking back in
place of a sorry fails the build — the only legitimate retirement of a
debt entry is deletion in favor of a replay route). A NEW `dis_*`/
`drv_*` constant in the mirror namespaces matching neither list fails.
In-Lean, deterministic (environment scan). -/
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
    [``ACL2.Worlds.Sorting.dis_insert_tp,
     ``ACL2.Worlds.Sorting.dis_how_many_tp,
     ``ACL2.Worlds.Sorting.dis_all_rel_tp,
     ``ACL2.Worlds.Sorting.dis_append_tp,
     ``ACL2.Worlds.Sorting.dis_evens_tp,
     ``ACL2.Worlds.Sorting.dis_acl2_count_tp,
     ``ACL2.Worlds.Sorting.dis_merge2_total,
     ``ACL2.Worlds.Sorting.dis_msort_total,
     ``ACL2.Worlds.Sorting.dis_o_lt_total,
     ``ACL2.Worlds.Sorting.dis_pce_total,
     ``ACL2.Worlds.Sorting.dis_bnext_total,
     ``ACL2.Worlds.Sorting.dis_convert_perm,
     ``ACL2.Lifting.drv_tp_len,
     ``ACL2.Worlds.Simple.drv_tp_mylen,
     ``ACL2.Worlds.Sorting.dis_sortfn1_insert_tp,
     ``ACL2.Worlds.Sorting.dis_sortfn1_tp,
     ``ACL2.Worlds.Sorting.dis_ssortfn1_insert_tp,
     ``ACL2.Worlds.Sorting.dis_ssortfn1_tp]
  for n in debtRegistry do
    let axs ← collectAxioms n
    unless axs.contains ``sorryAx do
      throwError "provenance gate: debt entry {n} carries no sorryAx — \
        a Lean-side proof has replaced the sorry. Forbidden (thin-Lean \
        ruling): retire the entry via a replay route instead"
  let env ← getEnv
  let mirrorNs : List Name :=
    [`ACL2.Worlds, `ACL2.Imported, `ACL2.Lifting]
  let mut offenders : List Name := []
  for (c, _) in env.constants.toList do
    if mirrorNs.any (·.isPrefixOf c) then
      let last := c.componentsRev.headD Name.anonymous
      let s := last.toString
      if s.startsWith "dis_" || s.startsWith "drv_" then
        unless d5Allowed.contains c || decodeAllowed.contains c ||
            debtRegistry.contains c do
          offenders := offenders ++ [c]
  unless offenders.isEmpty do
    throwError "provenance gate: unregistered discharger constant(s) in \
      the mirror layer: {offenders} — Lean-side content dischargers are \
      forbidden (thin-Lean ruling 2026-08-11); register D5 gz content in \
      GzPrelude or route the fact through a replayed statement"

/-! ## EXTRA-NATIVES GATE (audit F6, ruled 2026-08-11)

Natives whose green row lives OUTSIDE the driver-coverage golden
(pattern-pin books run by `Tests/PatternPins.lean`) cannot take a
row-coupled catalog entry — this registry gives them the SAME
axiom-exactness and seam-consumption checks, so no native mirror sits
outside every gate. Each entry: (native, its replayed seam, the pin
site that owns the row). -/
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let extraNatives : List (Name × Name × String) :=
    [(``ACL2.Imported.Mirrors.cons_neq_detail_native_driver,
      ``ACL2.Imported.Mirrors.consNeqDetailReplayed,
      "Tests/PatternPins.lean p8-clausify-detail")]
  for (nat, seam, rowSite) in extraNatives do
    let axs ← collectAxioms nat
    let allowed : List Name :=
      [``propext, ``Classical.choice, ``Quot.sound]
    for a in axs do
      unless allowed.contains a do
        throwError "extra-natives gate: {nat} uses forbidden axiom \
          {a} (row: {rowSite})"
    -- seam: BFS through Mirrors-namespace constants from the native
    -- must reach the replayed seam (same rule as the lift-coverage
    -- seam gate)
    let env ← getEnv
    let mut frontier : List Name := [nat]
    let mut seen : List Name := []
    let mut found := false
    while !frontier.isEmpty && !found do
      let c := frontier.head!
      frontier := frontier.tail!
      unless seen.contains c do
        seen := seen ++ [c]
        if c == seam then
          found := true
        else if (`ACL2.Imported.Mirrors).isPrefixOf c then
          if let some ci := env.find? c then
            if let some v := ci.value? then
              frontier := frontier
                ++ (v.getUsedConstants.toList.filter
                    (fun n => !seen.contains n))
    unless found do
      throwError "extra-natives gate: {nat} does not consume its \
        replayed seam {seam} — the ornamental-import antipattern \
        (row: {rowSite})"

/-! ## DECODE hreplayed-USAGE GATE (ruled 2026-08-11)

Closes the post-purge audit's evasion B: a decode that TAKES a
replayed hypothesis but never uses it would pass every other gate
(the seam gate sees the consumer apply the replayed constant one hop
before the decode) while its native content is proved from scratch —
ornamental import in its purest form. This gate scans every
`*_native_of_replayed` constant (plus the `decodeAllowed` transport)
in the mirror namespaces and requires: (1) at least one hypothesis
whose type mentions `evalOpt` (the replayed-statement shape), and
(2) every such hypothesis actually OCCURRING in the proof term. A
count floor guards the scan predicate itself against rot. KNOWN
LIMIT: a proof that passes the hypothesis to an auxiliary that
ignores it still counts as usage — the residual is an audit item
(per-book-family cadence). -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mirrorNs : List Name :=
    [`ACL2.Worlds, `ACL2.Imported, `ACL2.Lifting]
  let mut decodes : List Name :=
    [``ACL2.Worlds.Sorting.dis_rule_orderedp_append]
  for (c, ci) in env.constants.toList do
    if mirrorNs.any (·.isPrefixOf c) && !c.isInternalDetail then
      if let .thmInfo _ := ci then
        let s := (c.componentsRev.headD Name.anonymous).toString
        -- endsWith (not the narrower `_native_of_replayed`): the
        -- R-instance decodes read `_native_<R>_of_replayed`
        -- (perm_cons_native_perm_of_replayed) — census 2026-08-11
        if s.endsWith "_of_replayed" then
          decodes := decodes ++ [c]
  if decodes.length < 39 then
    throwError "hreplayed-usage gate: only {decodes.length} decode \
      constants found (expected ≥ 39) — the scan predicate rotted or \
      decodes were renamed; fix the scan, never lower the floor blindly"
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
              hypothesis it never USES — ornamental import (mirror \
              criterion antipattern 2 / audit evasion B); the native \
              content must be proved FROM the replayed statement, \
              not beside it"
      unless sawReplayed do
        throwError "hreplayed-usage gate: {c} has no evalOpt-shaped \
          hypothesis — a decode must consume a replayed statement"

/-! ## SHAPE GATE (ruled 2026-08-11)

Every AUTHORED theorem in the mirror content namespaces
(`ACL2.Worlds.*`, `ACL2.Lifting`) must classify into one of the
allowed thin-Lean classes, each with a shape signal:

- DECODE (`*_of_replayed`) — content-checked by the hreplayed-usage
  gate above;
- ISO-corr (`*_exec_corr`) — type must mention `ConvTo`/`evalOpt`;
- ISO-enc (`*_enc`) — type must mention an encoder
  (`enc`/`boolEnc`/`intRep`);
- discharger (`dis_*`/`drv_*`) — allowlisted by the provenance gate;
- WORLD-FACT (`world_has_*`/`world_no_*`) — generated-world lookup
  facts; type must mention `World`;
- registered SUPPORT — the enumerated census below, each line
  reviewed against the 2026-08-11 provenance audits at registration.

Anything unclassifiable FAILS THE BUILD: register it here (with a
justification a reviewer can check) or route its content through a
replayed statement. This converts the formerly-invisible support
bucket into a watched number — the carve-out drift test applied to
the mirror layer. Compiler satellites (`.eq_*`, `._proof_*`,
theorems nested under a constant) are excluded mechanically. -/
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← getEnv
  let nss : List Name := [`ACL2.Worlds, `ACL2.Lifting]
  -- The GENERIC TRANSPORT KIT (ACL2.Lifting): evaluation/transport
  -- machinery, sorting-decoupled by construction — the layer the
  -- ruling says to industrialize. Audited clean as a group
  -- (verification audit 2026-08-11, completeness dimension).
  let supportTransportKit : List Name :=
    [``ACL2.Lifting.toBool_equal, ``ACL2.Lifting.enc_inj,
     ``ACL2.Lifting.conv_unique, ``ACL2.Lifting.conv_plus_int,
     ``ACL2.Lifting.exists_enc_of_trueListp,
     ``ACL2.Lifting.implements_plus, ``ACL2.Lifting.conv_if_false',
     ``ACL2.Lifting.conv_if3, ``ACL2.Lifting.booleanp_cond,
     ``ACL2.Lifting.bool_true_of_cond_truthy,
     ``ACL2.Lifting.implements_len, ``ACL2.Lifting.implements_times,
     ``ACL2.Lifting.replayed_pins_ne_nil,
     ``ACL2.Lifting.implies_t_of_ne_nil,
     ``ACL2.Lifting.conv_and_conds, ``ACL2.Lifting.conv_equalT,
     ``ACL2.Lifting.truthy_of_implies_t,
     ``ACL2.Lifting.equal_truthy_of_eq,
     ``ACL2.Lifting.cond_t_of_true, ``ACL2.Lifting.conv_var_of_get,
     ``ACL2.Lifting.conv_fix, ``ACL2.Lifting.bool_of_cond_eq,
     ``ACL2.Lifting.implements_append,
     ``ACL2.Lifting.replayed_peel_guard,
     ``ACL2.Lifting.int_atom_inj, ``ACL2.Lifting.conv_times_int,
     ``ACL2.Lifting.conv_impliesT, ``ACL2.Lifting.bool_of_iff_truthy,
     ``ACL2.Lifting.native_of_replayed_equal,
     ``ACL2.Lifting.conv_qInt]
  -- PER-BOOK SUPPORT (each line = the audit class that cleared it):
  let supportBook : List (Name × String) :=
    [-- two-valuedness of a single sim — allowed decode support (F5)
     (``ACL2.Worlds.Sorting.allRelExec_t_or_nil, "two-valuedness"),
     (``ACL2.Worlds.Sorting.relExec_t_or_nil, "two-valuedness"),
     (``ACL2.Worlds.Sorting.orderedpExec_t_or_nil, "two-valuedness"),
     (``ACL2.Worlds.Sorting.lexorder_t_or_nil, "two-valuedness"),
     -- P2 definitional-termination measures (boundary note §P2 —
     -- the named, accepted exception)
     (``ACL2.Worlds.Sorting.evensExec_consCount_le, "P2 measure"),
     (``ACL2.Worlds.Sorting.evensExec_consCount_lt, "P2 measure"),
     (``ACL2.Worlds.Sorting.filterExec_consCount_le, "P2 measure"),
     (``ACL2.Worlds.Sorting.consCount_bnext_swap_lt, "P2 measure"),
     (``ACL2.Worlds.Sorting.evensL_length, "P2 measure (native)"),
     -- definitional unfoldings of the relL case table (single-fn)
     (``ACL2.Worlds.Sorting.relL_LT, "relL case unfolding"),
     (``ACL2.Worlds.Sorting.relL_LTE, "relL case unfolding"),
     (``ACL2.Worlds.Sorting.relL_GTE, "relL case unfolding"),
     -- single-fn evaluation bridges / plumbing
     (``ACL2.Worlds.Sorting.chain2Rec_iff_isChain,
       "isChain recursion characterization (iso support)"),
     (``ACL2.Worlds.Sorting.bnext_ns, "symbol plumbing"),
     (``ACL2.Worlds.Sorting.lexorder_eq_boolEnc,
       "builtin evaluation bridge"),
     (``ACL2.Worlds.Sorting.callBuiltin_lexorder_boolEnc,
       "builtin evaluation bridge"),
     (``ACL2.Worlds.Sorting.toBool_relExec,
       "toBool projection of a sim")]
  -- staleness: registered names must exist (mirrors lift-coverage)
  for n in supportTransportKit do
    unless env.contains n do
      throwError "shape gate: stale transport-kit entry {n}"
  for (n, _) in supportBook do
    unless env.contains n do
      throwError "shape gate: stale support entry {n}"
  let mentions (ty : Expr) (targets : List Name) : Bool :=
    (ty.find? (fun e => targets.any e.isConstOf)).isSome
  let mut offenders : List (Name × String) := []
  let mut nCorr := 0
  let mut nEnc := 0
  for (c, ci) in env.constants.toList do
    if nss.any (·.isPrefixOf c) && !c.isInternalDetail
        && !env.contains c.getPrefix then
      if let .thmInfo info := ci then
        let s := (c.componentsRev.headD Name.anonymous).toString
        if s.startsWith "eq_" || s == "eq_def" || s == "sizeOf_spec"
            || s == "induct" || c.components.any (· == `_unary) then
          pure ()
        else if s.endsWith "_of_replayed" then
          pure () -- content-checked by the hreplayed-usage gate
        else if s.startsWith "dis_" || s.startsWith "drv_" then
          pure () -- allowlisted by the provenance gate
        else if s.endsWith "_exec_corr" then
          nCorr := nCorr + 1
          unless mentions info.type
              [``ACL2.Replay.ConvTo, ``ACL2.evalOpt] do
            offenders := offenders ++
              [(c, "corr-named but no ConvTo/evalOpt in the type")]
        else if s.endsWith "_enc" then
          nEnc := nEnc + 1
          unless mentions info.type
              [``ACL2.Lifting.enc, ``ACL2.Lifting.boolEnc,
               ``ACL2.Lifting.intRep] do
            offenders := offenders ++
              [(c, "enc-named but no encoder in the type")]
        else if s.startsWith "world_has_" || s.startsWith "world_no_"
            then
          -- the lookup surfaces as the `World.defs` projection (or a
          -- getElem instance over it) applied to a world constant
          unless mentions info.type
              [``ACL2.World, ``ACL2.World.defs, ``ACL2.Symbol] do
            offenders := offenders ++
              [(c, "world-fact-named but no World lookup in the type")]
        else
          unless supportTransportKit.contains c
              || supportBook.any (·.1 == c) do
            offenders := offenders ++ [(c, "UNCLASSIFIED")]
  if nCorr < 25 || nEnc < 20 then
    throwError "shape gate: class counts collapsed (corr {nCorr}, \
      enc {nEnc}) — the scan predicate rotted; fix the scan, never \
      lower the floors blindly"
  unless offenders.isEmpty do
    throwError "shape gate: mirror-layer theorem(s) outside the \
      thin-Lean classes: {offenders.map (·.1)} — register as SUPPORT \
      with a reviewable justification (if the audits class it clean) \
      or route the content through a replayed statement (thin-Lean \
      ruling 2026-08-11): {offenders}"

end ACL2.Imported.Mirrors
