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
      `driver_replayed%` constant its proof must consume). -/
  | native (decl : Lean.Name) (seam : Lean.Name)
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
    .native ``how_many_rm_native_driver ``howManyRmReplayedCond),
  ("sorting/convert-perm-to-how-many", "NOT-MEMB-IMPLIES-RM-IS-NO-OP",
    .native ``not_memb_rm_noop_native_driver
      ``notMembRmNoopReplayedCond),
  ("sorting/convert-perm-to-how-many", "NOT-MEMB-IMPLIES-HOW-MANY-IS-0",
    .native ``not_memb_how_many_0_native_driver
      ``notMembHowMany0ReplayedCond),
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
    .native ``how_many_bnext_native_driver ``howManyBnextReplayedCond),
  ("sorting/msort", "HOW-MANY-MERGE2", .native ``how_many_merge2_native_driver ``howManyMerge2ReplayedCond),
  ("sorting/msort", "HOW-MANY-EVENS-AND-ODDS", .native ``how_many_evens_and_odds_native_driver ``howManyEvensOddsReplayedCond),
  ("sorting/msort", "ORDEREDP-MSORT", .native ``orderedp_msort_native_driver ``orderedpMsortReplayedCond),
  ("sorting/msort", "HOW-MANY-MSORT", .native ``how_many_msort_native_driver ``howManyMsortReplayedCond),
  ("sorting/qsort", "termination:QSORT", .replayedOnly "an internal admission obligation, not a user-facing theorem: its native content (the filter-count decreases) IS qsortExec own kernel-checked Lean termination proof (filterExec_consCount_le)"),
  ("sorting/qsort", "HOW-MANY-APPEND", .native ``how_many_append_native_driver ``howManyAppendReplayedCond),
  ("sorting/qsort", "ORDEREDP-APPEND", .native ``orderedp_append_native_driver ``orderedpAppendReplayedCond),
  ("sorting/qsort", "HOW-MANY-FILTER-1", .native ``how_many_filter_1_native_driver ``howManyFilter1ReplayedCond),
  ("sorting/qsort", "HOW-MANY-QSORT", .native ``how_many_qsort_native_driver ``howManyQsortReplayedCond),
  ("sorting/qsort", "PERM-QSORT", .native ``perm_qsort_native_driver ``permQsortReplayedCond),
  ("sorting/qsort", "CAR-APPEND", .native ``car_append_native_driver ``carAppendReplayedCond),
  ("sorting/qsort", "ALL-REL-FILTER-1", .native ``all_rel_filter_1_native_driver ``allRelFilter1ReplayedCond),
  ("sorting/qsort", "ALL-REL-FILTER-2", .native ``all_rel_filter_2_native_driver ``allRelFilter2ReplayedCond),
  ("sorting/qsort", "ALL-REL-RM-1", .native ``all_rel_rm_1_native_driver ``allRelRm1ReplayedCond),
  ("sorting/qsort", "ALL-REL-RM-2", .native ``all_rel_rm_2_native_driver ``allRelRm2ReplayedCond),
  ("sorting/qsort", "PERM-IMPLIES-EQUAL-ALL-REL-2", .native ``perm_implies_equal_all_rel_2_native_driver ``permImpliesAllRel2Replayed),
  ("sorting/qsort", "ORDEREDP-QSORT", .native ``orderedp_qsort_native_driver ``orderedpQsortReplayedCond),
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
      if let .native decl seam := st then
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
  let corollaries : List Name :=
    [``ACL2.Imported.Mirrors.perm_cons_native_perm_driver,
     ``ACL2.Imported.Mirrors.isPerm_equivalence_driver,
     ``ACL2.Imported.Mirrors.perm_symm_perm_driver,
     ``ACL2.Imported.Mirrors.perm_trans_perm_driver,
     ``ACL2.Imported.Mirrors.perm_erase_perm_driver,
     ``ACL2.Imported.Mirrors.mem_transport_perm_driver,
     ``ACL2.Imported.Mirrors.ordered_perms_native_perm_driver,
     ``ACL2.Imported.Mirrors.perm_qsort_perm_driver,
     ``ACL2.Imported.Mirrors.orderedp_isort_isChain_driver,
     ``ACL2.Imported.Mirrors.orderedp_rm_isChain_driver,
     ``ACL2.Imported.Mirrors.orderedp_memb_isChain_driver,
     ``ACL2.Imported.Mirrors.orderedp_msort_isChain_driver,
     ``ACL2.Imported.Mirrors.orderedp_qsort_isChain_driver,
     ``ACL2.Imported.Mirrors.p5_dupp_prepend_native_driver,
     ``ACL2.Imported.Mirrors.p7_dub_len_native_driver]
  for n in (catalogNatives ++ corollaries) do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "native-entry axiom gate: {n} uses forbidden axioms {bad}"

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
    if let .native decl _ := st then
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

end ACL2.Imported.Mirrors
