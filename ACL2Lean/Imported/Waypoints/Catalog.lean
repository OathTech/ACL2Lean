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
import ACL2Lean.Imported.Waypoints.BsortCap
import ACL2Lean.Imported.Waypoints.SortsEquivalent
import ACL2Lean.Imported.Waypoints.RuleApp
import ACL2Lean.Imported.Waypoints.Linear
import ACL2Lean.Imported.Waypoints.NestedInduction
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
   discharge (the ORDEREDP-QSORT/orderedpAppendReplayedCond pairing was
   the live example until P5a retired its hand decode) would pass — the
   gate rules out DETACHMENT, not MIS-PAIRING; seam pairings stay an
   audit item. -/

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
  ("01-multi-theorem", "APP-NIL", .pending "a waypoint entry over the 01 world — the decode itself EXISTS since R1-A (Worlds.Rev.app_nil_native_of_replayed, world-parametric, landed on the 02-rev row below); nothing is blocking, it is unbuilt (the old rule:CONS-CAR-CDR clause was stale — see the R0 note below)"),
  ("01-multi-theorem", "LEN2-APP", .pending "len2 world dischargers (entry-1 recipe over the 01 world)"),
  ("02-rev", "APP-ASSOC", .native ``app_assoc_native_driver ``appAssocReplayedCond),
  ("02-rev", "TRUE-LISTP-REV", .pending "the flatten-recipe waypoint (the image-of-enc fact, cf TRUE-LISTP-FLATTEN — unconditional, transfers directly)"),
  -- PROMOTED to `.native` 2026-08-14 (R1 item A): the APP/REV kit exists
  -- now (`Imported/Rev.lean` — derive_exec%/derive_sim%), and the
  -- `(TRUE-LISTP X)` antecedent is DISCHARGED at the encoded instance by
  -- `Lifting.trueListp_enc` (every enc image is a true list), not assumed.
  ("02-rev", "APP-NIL", .native ``app_nil_native_driver ``appNilReplayedCond),
  -- R0 item 7 (2026-08-13; APP-NIL rows folded in post-flight — same
  -- evidence): the previous blockedOn text ("tp:REV/
  -- rule:CONS-CAR-CDR dischargers") was stale in BOTH halves — tp:REV was
  -- cleared at bcb181d (the BINARY-APPEND→APP→REV cascade; the main-row
  -- cond is gone and the header tally counts both rows unconditional) and
  -- rule:CONS-CAR-CDR has a working discharger (gz_rule_cons_car_cdr,
  -- Provers.lean) — it is a kept condition on NO golden row. Both rows
  -- replay green and UNCONDITIONAL; the only thing missing is decode-layer.
  -- PROMOTED to `.native` 2026-08-14 (R1 item A): the rev exec/iso kit
  -- landed (`Imported/Rev.lean`); REV's ALIGNED reading `Worlds.Rev.revL`
  -- passes the fixed `derive_sim%` template.
  ("02-rev", "REV-APP", .native ``rev_app_native_driver ``revAppReplayedCond),
  ("02-rev", "REV-REV", .native ``rev_rev_native_driver ``revRevReplayedCond),
  -- PROMOTED to `.native` (zero-ruling broadening lane, 2026-08-18). The
  -- "len2 dischargers" reason was STALE in exactly the 02-rev way (R0
  -- item 7): both rows' `cond[…]` labels sit inside `[DISCHARGE: …]`, on
  -- the informational DP probe, and the driver emits both replayed
  -- statements UNCONDITIONAL. What was genuinely missing was an ENDER —
  -- the decode family was EQUAL-only and both rows conclude in a
  -- COMPARISON; `Imported/LiftingRel.lean` supplies `≤`/`<`. No exec kit
  -- was needed: `LEN2`'s emitted body IS `Lifting.lenBody "LEN2"`.
  ("03-linear", "LEN2-NONNEG",
    .native ``len2_nonneg_native_driver ``len2NonnegReplayedCond),
  ("03-linear", "LEN2-CDR-SMALLER",
    .native ``len2_cdr_smaller_native_driver ``len2CdrSmallerReplayedCond),
  ("03-linear", "LINEAR-CHAIN", .pending "#50 DP tactic decode"),
  ("04-multi-case-induction", "EVENLEN-BOOLEANP", .pending "boolean-recognizer decode (near type-absorbed)"),
  -- NEWLY GREEN 2026-08-15 (T1+2 sprint P3b: the `:LHS-TS`/`:RHS-TS`
  -- disjointness cell plus the marker-anchored chain-end IF-collapse).
  ("04-multi-case-induction", "CLASSIFY-POS", .pending "a waypoint entry over the 04 world — the classify decode is unbuilt, not blocked"),
  ("05-hints", "LEN2-APP-HELPER", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-VIA-USE", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-VIA-INDUCT", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-NO-HELPER", .pending "len2 dischargers"),
  ("06-measure", "COUNT-DOWN-ZERO", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  -- (the trio's termination rows went green at P4a, T1+2 sprint
  -- 2026-08-15 — the :ARG-LEAVES/:IF-TEST-FALSE consumption; same
  -- doctrine as termination:QSORT.)
  ("06-measure", "termination:COUNT-DOWN", .replayedOnly "an internal admission obligation, not a user-facing theorem — the termination:QSORT doctrine"),
  ("07-mutual-recursion", "MY-EVENP-3-IS-NIL", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("07-mutual-recursion", "MY-ODDP-3-IS-T", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("07-mutual-recursion", "termination:MY-EVENP", .replayedOnly "an internal admission obligation, not a user-facing theorem — the termination:QSORT doctrine"),
  ("11-custom-measure", "termination:CD2", .replayedOnly "an internal admission obligation, not a user-facing theorem — the termination:QSORT doctrine"),
  -- BOOKKEEPING (T1+2 sprint P5a+P5b collection, 2026-08-16): CD2-BOUND
  -- went FAIL → REPLAYED at P4b but was never given a catalog decision;
  -- BOTH P5 lanes independently surfaced the hole because the gate
  -- reads the golden through an IO read and `invalidate-coverage.sh`
  -- did not invalidate `Catalog.olean` (fixed at this collection).
  -- `.pending`: the value bound `(<= (cd2 n) (nfix n))` needs a cd2
  -- correspondence (exec kit + reading) that is not built — the
  -- validator/lifter backlog class.
  ("11-custom-measure", "CD2-BOUND", .pending "cd2 correspondence (validator/lifter backlog) — the row's value bound (<= (cd2 n) (nfix n)) has no built native reading; green since T1+2 sprint P4b"),
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
  -- PROMOTED to `.native` (zero-ruling broadening lane, 2026-08-18): the
  -- first CONJUNCTIVE row to decode. Its replayed statement is the
  -- macroexpanded `AND` — `(IF (EQUAL …) (EQUAL …) 'NIL)` — which no
  -- ender took until `Lifting.native_of_replayed_and`; the only new
  -- simulation was `DUP`'s (`APP` reused from 02-rev, `LEN` read through
  -- the builtin).
  ("15-nested-induction", "NESTED-INDUCTION",
    .native ``nested_induction_native_driver ``nestedInductionReplayedCond),
  ("16-three-way", "LEN-ZIP3", .pending "zip3 correspondence (backlog)"),
  -- PROMOTED to `.native` (zero-ruling broadening lane, 2026-08-18): the
  -- decode needed nothing new but a `TLP` kit — this book's `APP` is the
  -- SAME symbol with the SAME emitted body as 02-rev's, so
  -- `Worlds.Rev.appExec`/`app_exec_corr`/`appExec_enc` instantiate at this
  -- world directly (world-parametricity paying off across books). The
  -- `(TLP X)` antecedent of BOTH rows is discharged at the encoded
  -- instance by `Worlds.RuleApp.tlpL_true` (this book's OWN recognizer
  -- accepts every enc image — the `Lifting.trueListp_enc` analogue for a
  -- DEFUN recognizer), never assumed.
  ("17-rule-application", "TLP-APP-NIL",
    .native ``tlp_app_nil_native_driver ``tlpAppNilReplayedCond),
  ("17-rule-application", "TLP-APP-NIL-TWICE",
    .native ``tlp_app_nil_twice_native_driver ``tlpAppNilTwiceReplayedCond),
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
  -- SURFACED 2026-08-14 (T1+2 sprint phase 2): this row went GREEN with
  -- the G1-M R-parameterized lane and its catalog decision was never
  -- added — the gap only became visible when the phase-2 edits forced
  -- Catalog to re-elaborate against the current golden (the module reads
  -- the golden, which Lake does not track).
  ("sorting/convert-perm-to-how-many", "PERM-TLFIX",
    .pending "NO DECISION YET. The sibling tlfix-normalization rows \
      (HOW-MANY-TLFIX, RM-TLFIX, MEMB-TLFIX, the two \
      PERM-COUNTER-EXAMPLE-TLFIX rows) are all `.replayedOnly` \
      plumbing and `(PERM (TLFIX X) X)` is plausibly the same class — \
      but classifying a row as plumbing vs content is a MIRROR-side \
      call, deliberately NOT taken by a driver-layer executor. UNLOCK: \
      the next mirror wave decides (`.replayedOnly` with the plumbing \
      justification, or a native)"),
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
  -- entries RETURNED 2026-08-13, parked when the rows regressed to
  -- ASSUMED under the thin-Lean purge and re-greened by the ATOM-leg
  -- increment. Two of the three are `.native` since R4 wave 2g (below);
  -- the third's `.pending` now names a DIFFERENT cause and is not a
  -- queue item.
  -- PROMOTED 2026-08-18 (R4 wave 2g): the book HAS a waypoint module now
  -- (`Waypoints/SortsEquivalent.lean`). The blocker these two entries
  -- named ("queued behind the mirror buildout") was not the whole story
  -- and the correction is on the record: `driver_replayed%` had NO ROUTE
  -- to a `:USE (:FUNCTIONAL-INSTANCE …)` proof at all — the discharge
  -- existed only as a `runBook` parameter the coverage sweep supplies —
  -- so these rows were replayable by the SWEEP and by nothing else. The
  -- macro's `usefi` clause is that route at this layer.
  ("sorting/sorts-equivalent", "MSORT-IS-ISORT",
    .native ``msort_is_isort_native_driver ``msortIsIsortReplayedCond),
  ("sorting/sorts-equivalent", "QSORT-IS-ISORT",
    .native ``qsort_is_isort_native_driver ``qsortIsIsortReplayedCond),
  ("sorting/sorts-equivalent", "BSORT-IS-ISORT",
    .pending "NOT a mirror-buildout queue item, and this entry's own \
      claim is CORRECTED (R4 wave 2g). Its two siblings are `.native` \
      now; this one is not, and the cause is neither the native nor the \
      bsort exec kit (which EXISTS since this wave). The golden's own \
      row says it: `BSORT-IS-ISORT → REPLAYED ✓ [DISCHARGE: \
      Goal:preprocess/tau ◌ assumed cond[total:(BSORT X), \
      ASSUMED:dp-fact]]` — the discharge is ASSUMED, which is a \
      different axis from the KEPT-condition telescope this entry's \
      earlier text tracked, and `driver_replayed%` REFUSES to register a \
      replayed statement carrying ASSUMED:dp-fact (the N1 remediation \
      guard: such a condition states an obligation over \
      independently-quantified opaques that can be FALSE). The row \
      additionally failed EARLIER in the waypoint attempt, on its own \
      dependency (`usefi bridge: consumer discharge of ORDEREDP-BSORT \
      failed: depReplayedProofAt … (frontier)`). The remedy is at the \
      LEAF's EMISSION, not in this layer. Statement pin: \
      Tests/SortingPinsEndgame"),
  ("sorting/convert-perm-to-how-many", "HOW-MANY-TLFIX",
    .replayedOnly "tlfix normalization plumbing (count ignores the final \
      cdr) — no user-facing content"),
  -- PROMOTED 2026-08-18 (R4 wave 2e): the native is BUILT
  -- (`convert_perm_to_how_many_native_of_replayed` +
  -- `convert_perm_to_how_many_native_driver`, stated in the
  -- own-definition `permL`/`pceL` vocabulary per O-6). ONE CORRECTION TO
  -- THIS ROW'S OWN RECORD, stated because it was load-bearing for
  -- whoever built it next: the `.pending` text said "no replay blocker /
  -- the replay side is done", and the row does NOT replay at its own
  -- world with a bare `driver_replayed%` — it hard-fails
  -- `replayCongCollapse: own-position rewrite under PERM at arg 0: 0
  -- step-cited equivfull hypotheses (need exactly 1; cited equivalence
  -- runes [PERM-IS-AN-EQUIVALENCE])`. It replays with `deps [permDev]`,
  -- which offers the PERM book's own equivalence tree. So the claim was
  -- true of the CONDITIONS and false of the invocation; the fix is one
  -- clause, and it is recorded here rather than smoothed over.
  ("sorting/convert-perm-to-how-many", "CONVERT-PERM-TO-HOW-MANY",
    .native ``convert_perm_to_how_many_native_driver
      ``convertPermToHowManyReplayedCond),
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
  -- PROMOTED 2026-08-14 (T1+2 sprint phase 2, the R3 unified
  -- measure/arity table): `total:BNEXT` now arrives BY REPLAY of BNEXT's
  -- emitted `(LEN X)` admission — the measure gate was the last fragment
  -- not carrying the LEN row (audit F6) — so `dis_bnext_total` is GONE
  -- and this row's debt is drained.
  ("sorting/bsort", "HOW-MANY-BNEXT",
    .native ``how_many_bnext_native_driver ``howManyBnextReplayedCond),
  ("sorting/bsort", "termination:BSORT",
    .replayedOnly "an internal admission obligation (BSORT's BNEXT-SIZE
      measure decrease, via HOW-MANY-BAD-PAIRS-BNEXT's :linear content),
      not a user-facing theorem — the termination:QSORT doctrine"),
  -- PROMOTED 2026-08-14 (the R3 measure table's LEN row retired
  -- `total:BNEXT`; `tp:BNEXT-SIZE` had already gone by the replay route,
  -- TP-replay arc increment 3 2026-08-13 — the CALLEE-TP shape).
  ("sorting/bsort", "HOW-MANY-BAD-PAIRS-BNEXT",
    .native ``how_many_bad_pairs_bnext_native_driver
      ``howManyBadPairsBnextReplayedCond),
  -- PROMOTED 2026-08-14 (the R3 measure table's LEN row).
  ("sorting/bsort", "ORDEREDP-WHEN-BNEXT-CONSTANT",
    .native ``orderedp_when_bnext_constant_native_driver
      ``orderedpWhenBnextConstantReplayedCond),
  -- PROMOTED 2026-08-18 (R4 wave 2g): the BSORT EXEC KIT EXISTS, built
  -- by `derive_exec%`'s new `userFn` MEASURE ROW (generic machinery, not
  -- a bsort-specific kit — `Imported/ExecGen.lean`'s header). The
  -- entry's own "remaining frontier" text is superseded and its premise
  -- is corrected on the record: the Lean-side termination artifact is
  -- NOT a P2 hand proof under the measure-absorbed precedent — it is the
  -- REPLAYED decrease itself, at the exec level over arbitrary `SExpr`
  -- (`how_many_bad_pairs_bnext_exec_driver`). The `enc`-image bound that
  -- earlier waves recorded as the blocker is a property of the NATIVE
  -- READING, not of the replay.
  ("sorting/bsort", "ORDEREDP-BSORT",
    .native ``orderedp_bsort_native_driver ``orderedpBsortReplayedCond),
  ("sorting/bsort", "TRUE-LISTP-BSORT",
    .replayedOnly "subsumed by the bsort simulation: the enc image is
      closed under bsortExec (the type-absorbed true-listp doctrine,
      the TRUE-LISTP-RM precedent)"),
  -- PROMOTED 2026-08-18 (R4 wave 2g) — ORDEREDP-BSORT's story exactly.
  ("sorting/bsort", "HOW-MANY-BSORT",
    .native ``how_many_bsort_native_driver ``howManyBsortReplayedCond),
  -- PROMOTED 2026-08-14 (the R3 measure table's LEN row).
  ("sorting/bsort", "HOW-MANY-SMALLER-BNEXT",
    .native ``how_many_smaller_bnext_native_driver
      ``howManySmallerBnextReplayedCond),
  -- PROMOTED 2026-08-14 (the R3 measure table's SUM row: MERGE2's
  -- `(BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y))` measure over BOTH formals
  -- is now assemblable, `dis_merge2_total` is GONE).
  ("sorting/msort", "HOW-MANY-MERGE2", .native ``how_many_merge2_native_driver ``howManyMerge2ReplayedCond),
  ("sorting/msort", "HOW-MANY-EVENS-AND-ODDS", .native ``how_many_evens_and_odds_native_driver ``howManyEvensOddsReplayedCond),
  -- PROMOTED 2026-08-14 (the R3 measure table: MERGE2's sum row plus
  -- MSORT's opaque EVENS/ODDS measured actual, ∃-eliminated onto the
  -- registry decrease; tp:EVENS had gone by the replay route,
  -- TP-replay arc increment 2 2026-08-13).
  ("sorting/msort", "ORDEREDP-MSORT", .native ``orderedp_msort_native_driver ``orderedpMsortReplayedCond),
  -- PROMOTED 2026-08-14 (the R3 measure table, as ORDEREDP-MSORT).
  ("sorting/msort", "HOW-MANY-MSORT", .native ``how_many_msort_native_driver ``howManyMsortReplayedCond),
  ("sorting/qsort", "termination:QSORT", .replayedOnly "an internal admission obligation, not a user-facing theorem: its native content (the filter-count decreases) IS qsortExec own kernel-checked Lean termination proof (filterExec_consCount_le)"),
  ("sorting/qsort", "HOW-MANY-APPEND", .native ``how_many_append_native_driver ``howManyAppendReplayedCond),
  ("sorting/qsort", "ORDEREDP-APPEND", .native ``orderedp_append_native_driver ``orderedpAppendReplayedCond),
  ("sorting/qsort", "HOW-MANY-FILTER-1", .native ``how_many_filter_1_native_driver ``howManyFilter1ReplayedCond),
  -- PROMOTED 2026-08-15 (T1+2 sprint P3b: `total:O<` retired by the
  -- replay route — the ORDINAL registry row (Replay/OrdinalSim), the
  -- `O-FINP` recognizer duality and the world-read EQUAL-alias
  -- normalization of ACL2's recomputed ground-zero rulers — so its LAST
  -- sorried premise went and the entry carries no debt).
  ("sorting/qsort", "HOW-MANY-QSORT", .native ``how_many_qsort_native_driver ``howManyQsortReplayedCond),
  -- (PERM-QSORT promoted at the P3b+P3c collection 2026-08-15: its last
  -- two sorried premises retired in the SAME collection — dis_o_lt_total
  -- by the ordinal registry row (P3b), dis_convert_perm by the WP5
  -- cross-book D1 transfer (P3c); the gate forces the promotion.)
  ("sorting/qsort", "PERM-QSORT", .native ``perm_qsort_native_driver ``permQsortReplayedCond),
  ("sorting/qsort", "CAR-APPEND", .native ``car_append_native_driver ``carAppendReplayedCond),
  ("sorting/qsort", "ALL-REL-FILTER-1", .native ``all_rel_filter_1_native_driver ``allRelFilter1ReplayedCond),
  ("sorting/qsort", "ALL-REL-FILTER-2", .native ``all_rel_filter_2_native_driver ``allRelFilter2ReplayedCond),
  ("sorting/qsort", "ALL-REL-RM-1", .native ``all_rel_rm_1_native_driver ``allRelRm1ReplayedCond),
  ("sorting/qsort", "ALL-REL-RM-2", .native ``all_rel_rm_2_native_driver ``allRelRm2ReplayedCond),
  ("sorting/qsort", "PERM-IMPLIES-EQUAL-ALL-REL-2", .native ``perm_implies_equal_all_rel_2_native_driver ``permImpliesAllRel2Replayed),
  -- (ORDEREDP-QSORT promoted at the same collection — same two premises,
  -- same routes.)
  ("sorting/qsort", "ORDEREDP-QSORT", .native ``orderedp_qsort_native_driver ``orderedpQsortReplayedCond),
  ("sorting/qsort", "TRUE-LISTP-QSORT", .replayedOnly "subsumed by the qsort simulation (qsort_exec_corr/qsortExec_enc) — the type-absorbed true-listp doctrine")]

-- SEAM REACHABILITY (`seamReaches`) lives in `Waypoints/Macro.lean` since
-- R-1b (2026-08-16) — same namespace, so the call sites below are
-- unchanged. It moved UPSTREAM so the mirror-level seam gate
-- (`MirrorProofs/SeamGate.lean`) reuses the one copy rather than cloning
-- it: `MirrorProofs` cannot import this catalog.

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
(a) the D5 ground-zero rule content (the ratified carve-out — the list
is EMPTY since T1+2 sprint P4b: the whole `Imported/GzPrelude.lean`
family moved DOWN to `Replay/GzRules.lean` and is now applied by the
driver's `d5GzRules` registry at each rule's CITED rune, so no
waypoint-layer constant carries gz content any more) and
(b) the registered FORBIDDEN-DEBT set, every member of
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
  -- EMPTY since the P4b re-homing (see the header): kept as the named
  -- slot the carve-out lives in, so a future gz constant has an obvious,
  -- reviewable place to be registered rather than being smuggled into
  -- `decodeAllowed`.
  let d5Allowed : List Name := []
  -- EMPTY since the P5a retirement: `dis_rule_orderedp_append` was the
  -- one DECODE exception (it transported a replayed statement by hand
  -- because `dischargeRuleHyp` could not recompute ACL2's IFF⇒EQUAL
  -- storage normalization); the driver now carries that as a registered
  -- decode class, so the constant was DELETED. Kept as the named slot,
  -- like `d5Allowed`.
  let decodeAllowed : List Name := []
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
    -- (`dis_acl2_count_tp` RETIRED by the replay route, T1+2 sprint
    -- phase 1, 2026-08-14 — the D-A consumer: ACL2's context-refined
    -- leaves + subterm verdicts + the proved ts-algebra)
    -- (`dis_merge2_total`, `dis_msort_total` and `dis_bnext_total`
    -- RETIRED by the replay route, T1+2 sprint phase 2, 2026-08-14 —
    -- the R3 unified measure/arity table: the SUM row (MERGE2's
    -- two-measured-formal `BINARY-+` measure), the LEN row (BNEXT's
    -- `(LEN X)`, already carried by the μ-registry and the decrease
    -- walk but not by the admission gate — audit F6), and MSORT's
    -- opaque EVENS/ODDS measured actual bound by ∃-elimination)
    -- (`dis_o_lt_total` RETIRED by the replay route, T1+2 sprint P3b,
    -- 2026-08-15 — the ORDINAL registry row (`Replay/OrdinalSim`: the
    -- `O-RST`/`O-FIRST-EXPT` sims) plus the `O-FINP` recognizer duality
    -- and the EQUAL-alias reading of the recomputed ground-zero
    -- clauses, which together let the admission prover discharge `O<`
    -- and `O-P` from ACL2's OWN emitted `:TERMINATION-CLAUSES`)
    [-- (`dis_how_many_smaller_tp` RETIRED by the replay route,
     -- TP-replay arc increment 1, 2026-08-12; the MINTED
     -- `dis_bnext_size_tp` — the bsort-measure TP whose emitted leaf
     -- sums a CALLEE's TP — RETIRED by increment 3, 2026-08-13)
     -- (`dis_sortfn1_insert_tp` / `dis_ssortfn1_insert_tp` RETIRED with
     -- the CONS shape, increment 2; `dis_sortfn1_tp` /
     -- `dis_ssortfn1_tp` — the consp-or-nil class — RETIRED with the
     -- CALLEE-TP shape, increment 3)
     -- (`dis_convert_perm` RETIRED by the replay route, T1+2 sprint
     -- P3c 2026-08-15 — the CROSS-BOOK D1 TRANSFER (WP5): the
     -- dependency book's recorded tree replayed at the consumer's
     -- world, world-inclusion gated, and APPLIED as its own D1
     -- constant)
     ]
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
      forbidden (thin-Lean ruling 2026-08-11); D5 gz rule content now \
      lives in Replay/GzRules.lean behind the d5GzRules registry — put it \
      there, or route the fact through a replayed statement"

/-! ## EXTRA-NATIVES SEAM CHECK (audit F6, ruled 2026-08-11; reduced to
the seam half by the gate-cruft review, R3)

Natives whose green row lives OUTSIDE the driver-coverage golden
(pattern-pin books run by `Tests/PatternPins.lean`) cannot take a
row-coupled catalog entry, so nothing pairs them with a seam. This
list does. Their AXIOMS need no entry here — the wide
`_driver` scan in the axiom gate above already covers them.
THREAT MODEL (two-standard rule): a speedbump against forgetting to
consume the replayed statement — not a barrier. DO NOT HARDEN.

GREW 2026-08-16/17 (ruling R-5, off audit A4 #9) from one entry to
three: `p7_dub_len_native_driver` and `p5_dupp_prepend_native_driver`
are natives of pattern-test books, so they are exactly this shape —
they had simply never been paired. -/
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let extraSeams : List (Name × Name × String) :=
    [(``ACL2.Imported.Waypoints.cons_neq_detail_native_driver,
      ``ACL2.Imported.Waypoints.consNeqDetailReplayed,
      "Tests/PatternPins.lean p8-clausify-detail"),
     (``ACL2.Imported.Waypoints.p7_dub_len_native_driver,
      ``ACL2.Imported.Waypoints.p7TargetReplayedCond,
      "Tests/PatternPins.lean p7-cong-collapse"),
     (``ACL2.Imported.Waypoints.p5_dupp_prepend_native_driver,
      ``ACL2.Imported.Waypoints.duppRepReplayed,
      "Tests/PatternPins.lean p5-or-shape-flipped")]
  let env ← getEnv
  for (nat, seam, rowSite) in extraSeams do
    unless seamReaches env nat seam do
      throwError "extra-natives seam check: {nat} does not consume its \
        replayed seam {seam} — the ornamental-import antipattern \
        (row: {rowSite})"

/-! ## ALTERNATE READINGS OF A CATALOGUED ROW (ruling R-5, 2026-08-16/17,
off audit A4 #9)

A4 found 15 declared `_driver` waypoint theorems with no catalog entry
and correctly called them DELIVERABLES, never cruft — a waypoint's
kernel-check is its purpose. Cataloguing them surfaced WHY they were
uncatalogued, which is structural rather than an oversight:
`liftCatalog` is strictly ROW-KEYED (exactly one decision per green
golden row, with a build-failing staleness check in BOTH directions),
and none of these IS a row. They are

  (a) alternative READINGS of a row that already carries its one entry —
      the Mathlib forms over `List.Perm` / `List.IsChain` of a native
      stated over `isPerm` / `orderedpRec`; or
  (b) BUNDLES assembled from several catalogued rows
      (`isPerm_equivalence_driver` = entries 10/15/16); or
  (c) natives of pattern-test books with no golden row at all — those
      went to `extraSeams` above, which is the shape built for them.

Putting (a)/(b) in `liftCatalog` fails the gate either way: a second
entry on an existing key throws "multiple catalog entries", and an
invented key throws "matches no green golden row". So they are
catalogued HERE instead, ANCHORED to the row they read: each entry names
the `(book, row)` whose native it re-reads, and the entry is bound by
(1) the row's existence as a catalogued `.native`, and (2) the SAME
`seamReaches` seam check every native takes — which these pass
TRANSITIVELY, since a reading is proved from the row's native, which
consumes the seam. Their axioms are already bounded by the wide
`_driver` scan in the axiom gate above.

With this list every declared `_driver` theorem is gate-bound, and
`Waypoints/Validation.lean` no longer scans as consumerless.

THREAT MODEL (two-standard rule): a speedbump against a reading drifting
loose from the row it claims to re-read — not a barrier against a
motivated construction, and not a census to keep exhaustive by hand.
DO NOT HARDEN IT. -/
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  -- (reading, anchor book, anchor row, the anchor's seam)
  let readings : List (Name × String × String × Name) :=
    [-- the perm book's idiomatic `List.Perm` forms + the defequiv bundle
     (``ACL2.Imported.Waypoints.perm_cons_native_perm_driver,
      "sorting/perm", "PERM-CONS",
      ``ACL2.Imported.Waypoints.permConsReplayedCond),
     (``ACL2.Imported.Waypoints.perm_symm_perm_driver,
      "sorting/perm", "PERM-SYMMETRIC",
      ``ACL2.Imported.Waypoints.permSymmetricReplayed),
     (``ACL2.Imported.Waypoints.perm_trans_perm_driver,
      "sorting/perm", "PERM-TRANSITIVE",
      ``ACL2.Imported.Waypoints.permTransitiveReplayed),
     (``ACL2.Imported.Waypoints.perm_erase_perm_driver,
      "sorting/perm", "PERM-RM",
      ``ACL2.Imported.Waypoints.permRmReplayed),
     (``ACL2.Imported.Waypoints.mem_transport_perm_driver,
      "sorting/perm", "PERM-MEMB",
      ``ACL2.Imported.Waypoints.permMembReplayed),
     -- the BUNDLE: anchored at the defequiv row it decodes; it also
     -- reaches PERM-SYMMETRIC's and PERM-TRANSITIVE's seams (entries
     -- 10/15/16), so the single anchor is the weaker claim of the three
     (``ACL2.Imported.Waypoints.isPerm_equivalence_driver,
      "sorting/perm", "PERM-IS-AN-EQUIVALENCE",
      ``ACL2.Imported.Waypoints.permEquivReplayed),
     -- the `List.IsChain` sortedness forms
     (``ACL2.Imported.Waypoints.orderedp_isort_isChain_driver,
      "sorting/isort", "ORDEREDP-ISORT",
      ``ACL2.Imported.Waypoints.orderedpIsortReplayedCond),
     (``ACL2.Imported.Waypoints.orderedp_rm_isChain_driver,
      "sorting/ordered-perms", "ORDEREDP-RM",
      ``ACL2.Imported.Waypoints.orderedpRmReplayed),
     (``ACL2.Imported.Waypoints.orderedp_memb_isChain_driver,
      "sorting/ordered-perms", "ORDEREDP-MEMB",
      ``ACL2.Imported.Waypoints.orderedpMembReplayedCond),
     (``ACL2.Imported.Waypoints.ordered_perms_native_perm_driver,
      "sorting/ordered-perms", "ORDERED-PERMS",
      ``ACL2.Imported.Waypoints.orderedPermsCapReplayedCond),
     (``ACL2.Imported.Waypoints.orderedp_msort_isChain_driver,
      "sorting/msort", "ORDEREDP-MSORT",
      ``ACL2.Imported.Waypoints.orderedpMsortReplayedCond),
     (``ACL2.Imported.Waypoints.perm_qsort_perm_driver,
      "sorting/qsort", "PERM-QSORT",
      ``ACL2.Imported.Waypoints.permQsortReplayedCond),
     (``ACL2.Imported.Waypoints.orderedp_qsort_isChain_driver,
      "sorting/qsort", "ORDEREDP-QSORT",
      ``ACL2.Imported.Waypoints.orderedpQsortReplayedCond)]
  let env ← getEnv
  for (reading, book, row, seam) in readings do
    unless env.contains reading do
      throwError "alternate-reading catalog: {reading} does not exist"
    -- (1) the anchor must BE a catalogued native row
    match liftCatalog.filter (fun (cb, cn, _) => cb == book && cn == row) with
    | [(_, _, .native _ _)] => pure ()
    | [(_, _, .nativeSorried _ _ _)] => pure ()
    | [] => throwError "alternate-reading catalog: {reading} anchors on \
        {book}/{row}, which has no catalog entry"
    | _ => throwError "alternate-reading catalog: {reading}'s anchor \
        {book}/{row} is not a catalogued NATIVE row — a reading must \
        re-read a row whose own native exists"
    -- (2) the same seam check every native takes (here TRANSITIVE:
    -- the reading is proved from the anchor's native, which consumes it)
    unless seamReaches env reading seam do
      throwError "alternate-reading catalog: {reading} does not reach \
        the seam {seam} of the row it claims to re-read ({book}/{row}) \
        — the ornamental-import antipattern (waypoint criterion 2)"

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
  -- the hand-written seed is EMPTY since the P5a retirement (see
  -- `decodeAllowed` above); the scan below finds the `_of_replayed`
  -- decodes on its own
  let mut decodes : List Name := []
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
