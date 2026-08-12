import ACL2Lean.Imported.Mirrors.Macro
import ACL2Lean.Imported.Lifting
import ACL2Lean.DevLoad

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## p8-clausify-detail — the 2e completion criterion's mirror

The pattern book anchoring the expansion detail-chain replay (bsort
*1/4.1.3''s synthetic twin). Per the MDD-ratified completion criterion
(2026-08-01, the PatternPins pin): when the detail-chain replay lands,
this book goes GREEN ROW + NATIVE MIRROR. Landed in the endgame arc
(2026-08-10): the row replays 1/1 UNCONDITIONAL, and the native fact
below is proved FROM the replayed statement (the bridge decode — never
a native re-proof). -/

private def p8Log : String :=
  include_str "../../../acl2_samples/pattern-tests/p8-clausify-detail.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def p8Dev : Development := load_development% p8Log

derive_world p8WorldD from p8Dev

/-- The UNCONDITIONAL driver replayed statement (zero hypotheses). -/
def consNeqDetailReplayed := driver_replayed% p8Dev p8WorldD
  "cons-neq-detail"

private def aS : Symbol := { package := "ACL2", name := "A" }
private def bS : Symbol := { package := "ACL2", name := "B" }
private def dS : Symbol := { package := "ACL2", name := "D" }
private def aT : SExpr := .atom (.symbol { name := "A" })
private def bT : SExpr := .atom (.symbol { name := "B" })
private def dT : SExpr := .atom (.symbol { name := "D" })
private def app1 (n : String) (x : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := n })) (.cons x .nil)
private def app2 (n : String) (x y : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := n })) (.cons x (.cons y .nil))

/-- ENTRY, PROVED — CONS-NEQ-DETAIL natively: distinct heads make the
    swapped two-element cons prefixes distinct. Decoded from the replayed
    statement (modus ponens at the value level over the evaluated
    IMPLIES), never re-proved natively. -/
theorem cons_neq_detail_native_driver (av bv dv : SExpr) (h : av ≠ bv) :
    SExpr.cons av (SExpr.cons bv dv) ≠ SExpr.cons bv (SExpr.cons av dv) := by
  have hrep := consNeqDetailReplayed
  let w := p8WorldD
  let e : Env := ((({} : Env).insert dS dv).insert bS bv).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert dS dv).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
    re_val_var_get w e { name := "B" } bv (by
      show e.get? bS = some bv
      rw [show e = ((({} : Env).insert dS dv).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hd : ∃ N, ∀ f ≥ N, evalOpt f w e dT = some dv :=
    re_val_var_get w e { name := "D" } dv (by
      show e.get? dS = some dv
      rw [show e = ((({} : Env).insert dS dv).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  -- the antecedent: (NOT (EQUAL A B)) ⇒ Logic.not (Logic.equal av bv)
  have hEq1 := conv_builtin2 w e { name := "EQUAL" } aT bT av bv
    (Logic.equal av bv) (by decide) (by decide) ha hb
    (callBuiltin_equal av bv)
  have hNot1 := conv_builtin1 w e { name := "NOT" } (app2 "EQUAL" aT bT)
    (Logic.equal av bv) (Logic.not (Logic.equal av bv)) (by decide)
    (by decide) hEq1 (callBuiltin_not _)
  -- the two swapped conses
  have hCbd := conv_builtin2 w e { name := "CONS" } bT dT bv dv
    (Logic.cons bv dv) (by decide) (by decide) hb hd
    (callBuiltin_cons bv dv)
  have hC1 := conv_builtin2 w e { name := "CONS" } aT (app2 "CONS" bT dT)
    av (Logic.cons bv dv) (Logic.cons av (Logic.cons bv dv)) (by decide)
    (by decide) ha hCbd (callBuiltin_cons _ _)
  have hCad := conv_builtin2 w e { name := "CONS" } aT dT av dv
    (Logic.cons av dv) (by decide) (by decide) ha hd
    (callBuiltin_cons av dv)
  have hC2 := conv_builtin2 w e { name := "CONS" } bT (app2 "CONS" aT dT)
    bv (Logic.cons av dv) (Logic.cons bv (Logic.cons av dv)) (by decide)
    (by decide) hb hCad (callBuiltin_cons _ _)
  -- the consequent: (NOT (EQUAL c1 c2))
  have hEq2 := conv_builtin2 w e { name := "EQUAL" }
    (app2 "CONS" aT (app2 "CONS" bT dT)) (app2 "CONS" bT (app2 "CONS" aT dT))
    (Logic.cons av (Logic.cons bv dv)) (Logic.cons bv (Logic.cons av dv))
    (Logic.equal (Logic.cons av (Logic.cons bv dv))
      (Logic.cons bv (Logic.cons av dv)))
    (by decide) (by decide) hC1 hC2 (callBuiltin_equal _ _)
  have hNot2 := conv_builtin1 w e { name := "NOT" }
    (app2 "EQUAL" (app2 "CONS" aT (app2 "CONS" bT dT))
      (app2 "CONS" bT (app2 "CONS" aT dT)))
    (Logic.equal (Logic.cons av (Logic.cons bv dv))
      (Logic.cons bv (Logic.cons av dv)))
    (Logic.not (Logic.equal (Logic.cons av (Logic.cons bv dv))
      (Logic.cons bv (Logic.cons av dv))))
    (by decide) (by decide) hEq2 (callBuiltin_not _)
  -- the whole formula: IMPLIES of the two
  have hImp := conv_builtin2 w e { name := "IMPLIES" }
    (app1 "NOT" (app2 "EQUAL" aT bT))
    (app1 "NOT" (app2 "EQUAL" (app2 "CONS" aT (app2 "CONS" bT dT))
      (app2 "CONS" bT (app2 "CONS" aT dT))))
    (Logic.not (Logic.equal av bv))
    (Logic.not (Logic.equal (Logic.cons av (Logic.cons bv dv))
      (Logic.cons bv (Logic.cons av dv))))
    (Logic.implies (Logic.not (Logic.equal av bv))
      (Logic.not (Logic.equal (Logic.cons av (Logic.cons bv dv))
        (Logic.cons bv (Logic.cons av dv)))))
    (by decide) (by decide) hNot1 hNot2 (callBuiltin_implies _ _)
  have hne := replayed_pins_ne_nil (hrep e) hImp
  -- modus ponens: av ≠ bv makes the antecedent truthy
  have hA : Logic.not (Logic.equal av bv) ≠ SExpr.nil := by
    have : Logic.equal av bv = SExpr.nil := by
      simp [Logic.equal, beq_eq_false_iff_ne.mpr h]
    rw [this]
    decide +kernel
  have hB := implies_value_mp hne hA
  -- the consequent's truth decodes to the disequality
  intro hcontra
  apply hB
  have : Logic.equal (Logic.cons av (Logic.cons bv dv))
      (Logic.cons bv (Logic.cons av dv)) = SExpr.t := by
    show Logic.equal (SExpr.cons av (SExpr.cons bv dv))
      (SExpr.cons bv (SExpr.cons av dv)) = SExpr.t
    rw [hcontra, Logic.equal_self]
  rw [this]
  rfl

#print axioms cons_neq_detail_native_driver

end ACL2.Imported.Mirrors
