import ACL2Lean.Imported.Lifting

/-! # D5 prelude — ground-zero rule content dischargers.

SCOPE GUARD (thin-Lean ruling 2026-08-11): PREDEFINED (ground-zero)
rules ONLY — gz rule content is axiomatic/bootstrap in ACL2 (no
capturable proof to replay) and expresses trusted-core semantics; a
discharger for a BOOK-proven rule is forbidden, no exceptions. -/

open ACL2 ACL2.Replay ACL2.Lifting

namespace ACL2.Worlds.Sorting

/-! ## Rule variables + the local convergence helpers

Private copies of the term/symbol constants and the two convergence
helpers the five gz dischargers need (they were file-local privates in
`Imported/Sorting.lean` before the 2026-08-11 re-homing). -/

private abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

private def xS : Symbol := { package := "ACL2", name := "X" }
private def yS : Symbol := { package := "ACL2", name := "Y" }
private def zS : Symbol := { package := "ACL2", name := "Z" }
private def aS : Symbol := { package := "ACL2", name := "A" }
private def bS : Symbol := { package := "ACL2", name := "B" }
private def cS : Symbol := { package := "ACL2", name := "C" }
private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def zT : SExpr := .atom (.symbol { name := "Z" })
private def aT : SExpr := .atom (.symbol { name := "A" })
private def bT : SExpr := .atom (.symbol { name := "B" })
private def cT : SExpr := .atom (.symbol { name := "C" })

/-- Any variable converges in any env (unbound reads nil; none of the
    rule variables is `T`). -/
private theorem conv_var (w : World) (env' : Env) (s : Symbol)
    (h : s.isNamed "T" = false) :
    ∃ v, ∃ N, ∀ f ≥ N, evalOpt f w env' (.atom (.symbol s)) = some v :=
  ⟨_, re_val_var w env' s h⟩

private theorem conv_plusT (w : World) (env' : Env) (a b av bv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env' a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env' b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w env' (plusT a b)
      = some (Logic.plus av bv) :=
  conv_builtin2 w env' { name := "BINARY-+" } a b av bv _ (by decide)
    h_no_plus ha hb (callBuiltin_plus _ _)

/-! ## The ground-zero rule dischargers -/

/-- `rule:(+ y x) ≡ (+ x y)` — the arithmetic-3 rune `|(+ y x)|`
    (NOT ground-zero COMMUTATIVITY-OF-+, whose stored orientation is
    the reverse — audit 2026-07-31 inside finding 1). -/
theorem dis_plus_comm (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT yT xT) = evalOpt f w env' (plusT xT yT) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  exact fuel_eq_of_conv (conv_plusT w env' yT xT vy vx h_no_plus hy hx)
    (conv_plusT w env' xT yT vx vy h_no_plus hx hy) (logic_plus_comm vy vx)

/-- `rule:(+ y (+ x z)) ≡ (+ x (+ y z))` — the arithmetic-3 rune
    `|(+ y (+ x z))|`. -/
theorem dis_plus_comm2 (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT yT (plusT xT zT))
        = evalOpt f w env' (plusT xT (plusT yT zT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  obtain ⟨vz, hz⟩ := conv_var w env' zS (by decide)
  exact fuel_eq_of_conv
    (conv_plusT w env' yT (plusT xT zT) vy (Logic.plus vx vz) h_no_plus hy
      (conv_plusT w env' xT zT vx vz h_no_plus hx hz))
    (conv_plusT w env' xT (plusT yT zT) vx (Logic.plus vy vz) h_no_plus hx
      (conv_plusT w env' yT zT vy vz h_no_plus hy hz))
    (logic_plus_comm2 vy vx vz)

/-- `rule:(+ (+ x y) z) ≡ (+ x (+ y z))` — the arithmetic-3 rune
    `|(+ (+ x y) z)|` (no ASSOCIATIVITY-OF-+ is stored in these
    logs). -/
theorem dis_plus_assoc (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT (plusT xT yT) zT)
        = evalOpt f w env' (plusT xT (plusT yT zT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  obtain ⟨vz, hz⟩ := conv_var w env' zS (by decide)
  exact fuel_eq_of_conv
    (conv_plusT w env' (plusT xT yT) zT (Logic.plus vx vy) vz h_no_plus
      (conv_plusT w env' xT yT vx vy h_no_plus hx hy) hz)
    (conv_plusT w env' xT (plusT yT zT) vx (Logic.plus vy vz) h_no_plus hx
      (conv_plusT w env' yT zT vy vz h_no_plus hy hz))
    (logic_plus_assoc vx vy vz)

/-- `rule:(+ x (if a b c)) ≡ (if a (+ x b) (+ x c))` (if-lifting). -/
theorem dis_plus_if_lift (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT xT (ifT aT bT cT))
        = evalOpt f w env' (ifT aT (plusT xT bT) (plusT xT cT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨va, ha⟩ := conv_var w env' aS (by decide)
  obtain ⟨vb, hb⟩ := conv_var w env' bS (by decide)
  obtain ⟨vc, hc⟩ := conv_var w env' cS (by decide)
  cases hta : Logic.toBool va with
  | true =>
    exact fuel_eq_of_conv
      (conv_plusT w env' xT (ifT aT bT cT) vx vb h_no_plus hx
        (conv_if_true w env' aT bT cT va vb ha hta hb))
      (conv_if_true w env' aT (plusT xT bT) (plusT xT cT) va
        (Logic.plus vx vb) ha hta
        (conv_plusT w env' xT bT vx vb h_no_plus hx hb)) rfl
  | false =>
    have han : ∃ N, ∀ f ≥ N, evalOpt f w env' aT = some SExpr.nil :=
      nil_of_toBool_false hta ▸ ha
    exact fuel_eq_of_conv
      (conv_plusT w env' xT (ifT aT bT cT) vx vc h_no_plus hx
        (conv_if_false' w env' aT bT cT vc han hc))
      (conv_if_false' w env' aT (plusT xT bT) (plusT xT cT)
        (Logic.plus vx vc) han
        (conv_plusT w env' xT cT vx vc h_no_plus hx hc)) rfl

/-- `rule:(equal (if a b c) x) ≡ (if a (equal b x) (equal c x))`
    (if-lifting through EQUAL). -/
theorem dis_equal_if_lift (w : World)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (equalT (ifT aT bT cT) xT)
        = evalOpt f w env' (ifT aT (equalT bT xT) (equalT cT xT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨va, ha⟩ := conv_var w env' aS (by decide)
  obtain ⟨vb, hb⟩ := conv_var w env' bS (by decide)
  obtain ⟨vc, hc⟩ := conv_var w env' cS (by decide)
  cases hta : Logic.toBool va with
  | true =>
    exact fuel_eq_of_conv
      (conv_equalT w env' (ifT aT bT cT) xT vb vx h_no_equal
        (conv_if_true w env' aT bT cT va vb ha hta hb) hx)
      (conv_if_true w env' aT (equalT bT xT) (equalT cT xT) va
        (Logic.equal vb vx) ha hta
        (conv_equalT w env' bT xT vb vx h_no_equal hb hx)) rfl
  | false =>
    have han : ∃ N, ∀ f ≥ N, evalOpt f w env' aT = some SExpr.nil :=
      nil_of_toBool_false hta ▸ ha
    exact fuel_eq_of_conv
      (conv_equalT w env' (ifT aT bT cT) xT vc vx h_no_equal
        (conv_if_false' w env' aT bT cT vc han hc) hx)
      (conv_if_false' w env' aT (equalT bT xT) (equalT cT xT)
        (Logic.equal vc vx) han
        (conv_equalT w env' cT xT vc vx h_no_equal hc hx)) rfl

end ACL2.Worlds.Sorting
