import ACL2Lean.Imported.Waypoints.EquisortParametric

/-! # Parametric-constant STATEMENT pins (pre-merge audit 2026-08-08)

ROLE (two-category ruling, 2026-08-12): REGRESSION CANARIES for the
metric layer, not trust anchors — they detect silent statement-content
drift the golden (status-only) cannot see. See Tests/SortingPins.lean's
header for the full relabeling.

Both audit reviewers (inside I3 / outside O7) flagged that the phase's
headline artifacts — the two equisort capstone parametric constants —
had no statement pin: a driver change could silently alter what they
SAY while `just ci` stays green (the golden pins only the concrete
sweep).  This module pins each constant's STATEMENT structurally:

- the exact ordered binder-name inventory (so a premise can neither
  appear nor vanish unreviewed — the `hrule_*_NN` indices are the
  duplicate-name disambiguation over the book's rule list and change
  only when the rule inventory does, which is exactly a re-review
  moment);
- the conclusion, `EvTrue w env ⟦tformula⟧`, against the HAND-PINNED
  `:TFORMULA` of the capstone `(:DEFTHM …)` events
  (acl2_samples/sorting/equisort.proof-log:13660 and the strong
  analogue) — applied to the bound `w`/`env` in that order;
- for each of the six constraint premises, that its type carries the
  stored rule's lhs/rhs verbatim (the `(:RULES …)` tuples the
  `(:CONSTRAINTS …)` events correspond to);
- the R6 witness rules: NO definition-pinning (`hdef_`) binder, and no
  witness-helper name (`SORTFN1-INSERT`/`SSORTFN1-INSERT`) anywhere in
  the type — the banned-masquerade tripwire.

A failure here means the parametric statement CHANGED: review the new
statement against the log before re-pinning, never blind-update. -/

namespace ACL2.Tests.ParametricPins

open ACL2 ACL2.Replay.Driver Lean Lean.Meta Lean.Elab

/-- Parse one hand-pinned s-expression (hard-fail on anything else). -/
private def pinSExpr (s : String) : SExpr :=
  match ACL2.Parse.parseAll s with
  | .ok [e] => e
  | _ => panic! s!"ParametricPins: unparseable pin {s}"

/-- One constant's structural statement pin. -/
private def checkPin (declName : Name) (binderNames : List String)
    (tformula : String) (rulePins : List (String × String × String))
    (bannedStrs : List String) : Elab.Command.CommandElabM Unit :=
  Elab.Command.liftTermElabM do
    let ci ← getConstInfo declName
    Meta.forallTelescope ci.type fun xs body => do
      -- 1. the exact ordered binder inventory
      let names ← xs.toList.mapM fun x =>
        return (← x.fvarId!.getUserName).toString (escape := false)
      unless names == binderNames do
        throwError "ParametricPins {declName}: binder inventory CHANGED.\n\
          pinned: {binderNames}\ngot:    {names}"
      -- 2. the conclusion: EvTrue w env ⟦tformula⟧ (w, env the bound fvars)
      unless body.isAppOfArity ``ACL2.Replay.EvTrue 3 do
        throwError "ParametricPins {declName}: conclusion is not an \
          EvTrue application: {body}"
      let args := body.getAppArgs
      unless args[0]! == xs[1]! && args[1]! == xs[0]! do
        throwError "ParametricPins {declName}: conclusion is not over the \
          bound w/env"
      let want := reflectSExpr (pinSExpr tformula)
      unless args[2]! == want do
        throwError "ParametricPins {declName}: conclusion formula differs \
          from the pinned :TFORMULA.\nwant {want}\ngot  {args[2]!}"
      -- 3. constraint premises carry the stored rule's lhs/rhs verbatim
      for (binderName, lhs, rhs) in rulePins do
        let some i := names.findIdx? (· == binderName)
          | throwError "ParametricPins {declName}: pinned rule binder \
              {binderName} absent"
        let ty ← inferType xs[i]!
        for (tag, s) in [("lhs", lhs), ("rhs", rhs)] do
          let e := reflectSExpr (pinSExpr s)
          if (ty.find? (· == e)).isNone then
            throwError "ParametricPins {declName}: {binderName} no longer \
              carries its stored-rule {tag} {s}"
      -- 4. the R6 witness rules
      if let some bad := names.find? (·.startsWith "hdef_") then
        throwError "ParametricPins {declName}: definition-pinning binder \
          {bad} appeared — a parametric capstone must pin nothing"
      let strOf : Expr → Option String := fun e =>
        match e with | .lit (.strVal s) => some s | _ => none
      for banned in bannedStrs do
        if (ci.type.find? (fun e => strOf e == some banned)).isSome then
          throwError "ParametricPins {declName}: witness vocabulary \
            {banned} appears in the statement (banned masquerade)"

run_cmd (checkPin ``ACL2.Imported.Waypoints.weakSortfn1IsSortfn2Parametric
        ["env", "w",
         "hnoshadow_CONS", "hnoshadow_CAR", "hnoshadow_CDR", "hnoshadow_CONSP",
         "hnoshadow_ATOM", "hnoshadow_ENDP", "hnoshadow_EQUAL", "hnoshadow_NOT",
         "hnoshadow_BINARY-+", "hnoshadow_BINARY-*", "hnoshadow_UNARY--",
         "hnoshadow_<", "hnoshadow_INTEGERP", "hnoshadow_NATP", "hnoshadow_POSP",
         "hnoshadow_RATIONALP", "hnoshadow_ACL2-NUMBERP", "hnoshadow_ZP",
         "hnoshadow_SYMBOLP", "hnoshadow_BOOLEANP", "hnoshadow_STRINGP",
         "hnoshadow_FIX", "hnoshadow_NFIX", "hnoshadow_IMPLIES", "hnoshadow_IFF",
         "hnoshadow_TRUE-LISTP", "hnoshadow_LEN", "hnoshadow_LEXORDER",
         "hnoshadow_NUMERATOR", "hnoshadow_DENOMINATOR", "hnoshadow_REALPART",
         "hnoshadow_IMAGPART", "hnoshadow_COMPLEX-RATIONALP", "hnoshadow_COERCE",
         "htotal_PERM", "htotal_ORDEREDP", "htotal_HOW-MANY",
         "htotal_PERM-COUNTER-EXAMPLE", "htotal_SORTFN1", "htotal_SORTFN2",
         "htp_HOW-MANY",
         "hrule_CONVERT-PERM-TO-HOW-MANY",
         "hrule_ORDEREDP-SORTFN1_31", "hrule_TRUE-LISTP-SORTFN1_32",
         "hrule_ORDEREDP-SORTFN2_33", "hrule_TRUE-LISTP-SORTFN2_34",
         "hrule_HOW-MANY-SORTFN1_35", "hrule_HOW-MANY-SORTFN2_36",
         "husethm_ORDERED-PERMS"]
        "(IMPLIES (TRUE-LISTP X) (EQUAL (SORTFN1 X) (SORTFN2 X)))"
        [("hrule_ORDEREDP-SORTFN1_31", "(ORDEREDP (SORTFN1 X))", "'T"),
         ("hrule_TRUE-LISTP-SORTFN1_32", "(TRUE-LISTP (SORTFN1 X))", "'T"),
         ("hrule_ORDEREDP-SORTFN2_33", "(ORDEREDP (SORTFN2 X))", "'T"),
         ("hrule_TRUE-LISTP-SORTFN2_34", "(TRUE-LISTP (SORTFN2 X))", "'T"),
         ("hrule_HOW-MANY-SORTFN1_35", "(HOW-MANY E (SORTFN1 X))", "(HOW-MANY E X)"),
         ("hrule_HOW-MANY-SORTFN2_36", "(HOW-MANY E (SORTFN2 X))", "(HOW-MANY E X)")]
        ["SORTFN1-INSERT", "SSORTFN1-INSERT"])

run_cmd (checkPin ``ACL2.Imported.Waypoints.strongSsortfn1IsSsortfn2Parametric
        ["env", "w",
         "hnoshadow_EQUAL", "hnoshadow_NOT", "hnoshadow_IMPLIES",
         "hnoshadow_TRUE-LISTP",
         "htotal_PERM", "htotal_ORDEREDP", "htotal_HOW-MANY",
         "htotal_PERM-COUNTER-EXAMPLE", "htotal_SSORTFN1", "htotal_SSORTFN2",
         "htp_HOW-MANY",
         "hrule_CONVERT-PERM-TO-HOW-MANY",
         "hrule_ORDEREDP-SSORTFN1_44", "hrule_TRUE-LISTP-SSORTFN1_45",
         "hrule_ORDEREDP-SSORTFN2_46", "hrule_TRUE-LISTP-SSORTFN2_47",
         "hrule_HOW-MANY-SSORTFN1_48", "hrule_HOW-MANY-SSORTFN2_49",
         "husethm_ORDERED-PERMS"]
        "(EQUAL (SSORTFN1 X) (SSORTFN2 X))"
        [("hrule_ORDEREDP-SSORTFN1_44", "(ORDEREDP (SSORTFN1 X))", "'T"),
         ("hrule_TRUE-LISTP-SSORTFN1_45", "(TRUE-LISTP (SSORTFN1 X))", "'T"),
         ("hrule_ORDEREDP-SSORTFN2_46", "(ORDEREDP (SSORTFN2 X))", "'T"),
         ("hrule_TRUE-LISTP-SSORTFN2_47", "(TRUE-LISTP (SSORTFN2 X))", "'T"),
         ("hrule_HOW-MANY-SSORTFN1_48", "(HOW-MANY E (SSORTFN1 X))", "(HOW-MANY E X)"),
         ("hrule_HOW-MANY-SSORTFN2_49", "(HOW-MANY E (SSORTFN2 X))", "(HOW-MANY E X)")]
        ["SORTFN1-INSERT", "SSORTFN1-INSERT"])

/-! ## AtCanonical KEPT-inventory pins (final close-out arc increment
0 — close-out audit n1). The two canonical-world instantiations are
PARTIAL non-vacuity witnesses whose entire claim rides on the KEPT
premise inventory being exactly the two named hypotheses; nothing
else gated it (a silent regression from 2 kept premises to more would
have passed `ci`). Pinned: the binder inventory (env + the two KEPT
premises, in order), the conclusion over the CONCRETE
`equisortWaypointsWorld` against the hand-pinned `:TFORMULA`, and the
two premises' CONTENT — the CONVERT-PERM-TO-HOW-MANY stored-rule
lhs/rhs and ORDERED-PERMS's hand-pinned `:TFORMULA`
(acl2_samples/sorting/ordered-perms.proof-log, the `(:DEFTHM …)`
event). A failure means the witnesses' strength CHANGED — review
against the deferral log's D1 close-out entry, never blind-update.
POST-PURGE (2026-08-11, audit fix F1): the AtCanonical witnesses are
additionally SORRY-BACKED — their `totals` dischargers are
FORBIDDEN-DEBT sorries — so the non-vacuity claim is conditional on
that debt; the CATALOG AXIOM GATE
(`ACL2Lean/Imported/Waypoints/Catalog.lean`) gates it — `sorryAx`
REQUIRED there until the debt retires by replay. (That gate replaced
the `#guard_msgs` axiom receipts that used to sit in
`EquisortParametric.lean`; gate-cruft review 2026-08-11 R5. This
module still owns the STATEMENT pins — axioms and statements are
pinned in separate places on purpose.) -/

/-- Structural pin for a CONCRETE-world instantiation constant:
    binder inventory, conclusion `EvTrue <worldConst> env ⟦tformula⟧`,
    and per-premise content (formula strings that must appear verbatim
    in the binder's type). -/
private def checkPinAt (declName : Name) (worldConst : Name)
    (binderNames : List String) (tformula : String)
    (premisePins : List (String × List String)) :
    Elab.Command.CommandElabM Unit :=
  Elab.Command.liftTermElabM do
    let ci ← getConstInfo declName
    Meta.forallTelescope ci.type fun xs body => do
      let names ← xs.toList.mapM fun x =>
        return (← x.fvarId!.getUserName).toString (escape := false)
      unless names == binderNames do
        throwError "ParametricPins {declName}: KEPT inventory CHANGED.\n\
          pinned: {binderNames}\ngot:    {names}"
      unless body.isAppOfArity ``ACL2.Replay.EvTrue 3 do
        throwError "ParametricPins {declName}: conclusion is not an \
          EvTrue application: {body}"
      let args := body.getAppArgs
      unless args[0]! == mkConst worldConst && args[1]! == xs[0]! do
        throwError "ParametricPins {declName}: conclusion is not over \
          {worldConst}/the bound env"
      let want := reflectSExpr (pinSExpr tformula)
      unless args[2]! == want do
        throwError "ParametricPins {declName}: conclusion formula differs \
          from the pinned :TFORMULA.\nwant {want}\ngot  {args[2]!}"
      for (binderName, pins) in premisePins do
        let some i := names.findIdx? (· == binderName)
          | throwError "ParametricPins {declName}: pinned premise binder \
              {binderName} absent"
        let ty ← inferType xs[i]!
        for s in pins do
          let e := reflectSExpr (pinSExpr s)
          if (ty.find? (· == e)).isNone then
            throwError "ParametricPins {declName}: {binderName} no longer \
              carries its pinned content {s}"

run_cmd (checkPinAt ``ACL2.Imported.Waypoints.weakSortfn1IsSortfn2AtCanonical
        ``ACL2.Imported.Waypoints.equisortWaypointsWorld
        ["env", "hrule_CONVERT-PERM-TO-HOW-MANY", "husethm_ORDERED-PERMS"]
        "(IMPLIES (TRUE-LISTP X) (EQUAL (SORTFN1 X) (SORTFN2 X)))"
        [("hrule_CONVERT-PERM-TO-HOW-MANY",
          ["(PERM X Y)",
           "(EQUAL (HOW-MANY (PERM-COUNTER-EXAMPLE X Y) X) \
             (HOW-MANY (PERM-COUNTER-EXAMPLE X Y) Y))"]),
         ("husethm_ORDERED-PERMS",
          ["(IMPLIES (IF (TRUE-LISTP A) (IF (TRUE-LISTP B) \
             (IF (ORDEREDP A) (ORDEREDP B) 'NIL) 'NIL) 'NIL) \
             (EQUAL (EQUAL A B) (PERM A B)))"])])

run_cmd (checkPinAt ``ACL2.Imported.Waypoints.strongSsortfn1IsSsortfn2AtCanonical
        ``ACL2.Imported.Waypoints.equisortWaypointsWorld
        ["env", "hrule_CONVERT-PERM-TO-HOW-MANY", "husethm_ORDERED-PERMS"]
        "(EQUAL (SSORTFN1 X) (SSORTFN2 X))"
        [("hrule_CONVERT-PERM-TO-HOW-MANY",
          ["(PERM X Y)",
           "(EQUAL (HOW-MANY (PERM-COUNTER-EXAMPLE X Y) X) \
             (HOW-MANY (PERM-COUNTER-EXAMPLE X Y) Y))"]),
         ("husethm_ORDERED-PERMS",
          ["(IMPLIES (IF (TRUE-LISTP A) (IF (TRUE-LISTP B) \
             (IF (ORDEREDP A) (ORDEREDP B) 'NIL) 'NIL) 'NIL) \
             (EQUAL (EQUAL A B) (PERM A B)))"])])

end ACL2.Tests.ParametricPins
