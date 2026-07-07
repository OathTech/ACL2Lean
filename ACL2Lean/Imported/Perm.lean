import ACL2Lean.Imported.Lifting

/-! # Imported: the perm book — hand support for the `perm-cons` bridge

World-parametric (invariant L3) support for lifting the driver-replayed
`perm-cons` mirror to the native Lean statement

    `xs.contains a → (xs.isPerm (a :: ys) = (xs.erase a).isPerm ys)`

(with the propositional corollary over `List.Perm` via `List.isPerm_iff`).

Contents:
- HAND HYPOTHESIS DISCHARGERS for the mirror's two conditions — `total:perm`
  (the totality prover's user-fn-if-test frontier) and `tp:memb` (no TP
  prover exists yet). Both are the ratified "demos for industrialization"
  (2026-07-04): each mechanizes exactly the induction a future prover
  extension will generate.
- SIMULATIONS under `enc`: `memb` computes `List.contains`, `rm` computes
  `List.erase`, `perm` computes `List.isPerm` (all `BEq`-based, matching
  ACL2's `equal`).
- THE ASSEMBLY `perm_cons_native_of_mirror`: any proof of the mirror
  statement over a world carrying the three defuns yields the native
  theorem; the driver's mirror plugs in at exactly one seam
  (`Imported/NativeMirrors`). -/

open ACL2 ACL2.Replay ACL2.Lifting

namespace ACL2.Worlds.Perm

/-! ## The defuns, exactly as the log-derived world carries them -/

private def aS : Symbol := ⟨"ACL2", "a"⟩
private def eS : Symbol := ⟨"ACL2", "e"⟩
private def xS : Symbol := ⟨"ACL2", "x"⟩
private def yS : Symbol := ⟨"ACL2", "y"⟩

private def aT : SExpr := .atom (.symbol { name := "a" })
private def eT : SExpr := .atom (.symbol { name := "e" })
private def xT : SExpr := .atom (.symbol { name := "x" })
private def yT : SExpr := .atom (.symbol { name := "y" })

private def qT : SExpr :=
  .cons (.atom (.symbol { name := "quote" })) (.cons SExpr.t .nil)
private def qNil : SExpr :=
  .cons (.atom (.symbol { name := "quote" })) (.cons SExpr.nil .nil)

abbrev membT (a x : SExpr) : SExpr := app2 "memb" a x
abbrev rmT (e x : SExpr) : SExpr := app2 "rm" e x
abbrev permT (x y : SExpr) : SExpr := app2 "perm" x y
private abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil)))

/-- `(defun rm (e x) …)`, macroexpanded. -/
def rmBody : SExpr :=
  ifT (conspT xT)
    (ifT (equalT eT (carT xT)) (cdrT xT) (consT (carT xT) (rmT eT (cdrT xT))))
    qNil

/-- `(defun memb (a x) …)`, macroexpanded. -/
def membBody : SExpr :=
  ifT (conspT xT)
    (ifT (equalT aT (carT xT)) qT (membT aT (cdrT xT)))
    qNil

/-- `(defun perm (x y) …)`, macroexpanded. -/
def permBody : SExpr :=
  ifT (conspT xT)
    (ifT (membT (carT xT) yT) (permT (cdrT xT) (rmT (carT xT) yT)) qNil)
    (ifT (conspT yT) qNil qT)

private def memb_sym : Symbol := ⟨"ACL2", "memb"⟩
private def rm_sym : Symbol := ⟨"ACL2", "rm"⟩
private def perm_sym : Symbol := ⟨"ACL2", "perm"⟩

private theorem memb_ns :
    (memb_sym.isNamed "quote" = false ∧ memb_sym.isNamed "if" = false ∧
     memb_sym.isNamed "let" = false ∧ memb_sym.isNamed "let*" = false) := by decide
private theorem rm_ns :
    (rm_sym.isNamed "quote" = false ∧ rm_sym.isNamed "if" = false ∧
     rm_sym.isNamed "let" = false ∧ rm_sym.isNamed "let*" = false) := by decide
private theorem perm_ns :
    (perm_sym.isNamed "quote" = false ∧ perm_sym.isNamed "if" = false ∧
     perm_sym.isNamed "let" = false ∧ perm_sym.isNamed "let*" = false) := by decide

/-! ## Small kit -/

private theorem nil_of_toBool_false {v : SExpr} (h : Logic.toBool v = false) :
    v = SExpr.nil := by
  cases v <;> simp_all [Logic.toBool]

/-- Fix a per-fuel existential value by fuel monotonicity. -/
private theorem conv_fix {w : World} {e : Env} {t : SExpr}
    (h : ∃ N, ∀ f ≥ N, ∃ u, evalOpt f w e t = some u) :
    ∃ N, ∃ u, ∀ f ≥ N, evalOpt f w e t = some u := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨u, hu⟩ := hN N (le_refl N)
  exact ⟨N, u, fun f hf => evalOpt_ge_fuel N f w e t u hu hf⟩

/-- 2-ary argument STRICTNESS: a converging 2-ary (non-special) application
    has converging arguments. -/
private theorem evalOpt_app2_args (f : Nat) (w : World) (env : Env)
    (s : Symbol) (a1 a2 v : SExpr)
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
    (h : evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) = some v) :
    (∃ u, evalOpt f w env a1 = some u) ∧ (∃ u, evalOpt f w env a2 = some u) := by
  rw [show evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil)))
        = evalOptStep (evalOpt f) w env
            (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) from rfl] at h
  unfold evalOptStep at h
  simp only [Symbol.isNamed, SExpr.toList?] at h
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self,
             ↓reduceIte] at h
  cases hu1 : evalOpt f w env a1 with
  | none => simp [List.mapM, List.mapM.loop, hu1] at h
  | some u1 =>
    cases hu2 : evalOpt f w env a2 with
    | none => simp [List.mapM, List.mapM.loop, hu1, hu2] at h
    | some u2 => exact ⟨⟨u1, rfl⟩, ⟨u2, rfl⟩⟩

private theorem conv_args2_of_conv_app (w : World) (env : Env) (s : Symbol)
    (a1 a2 v : SExpr)
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) = some v) :
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a1 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a2 = some u) := by
  obtain ⟨N, hN⟩ := h
  constructor
  · exact conv_fix ⟨N, fun f hf =>
      (evalOpt_app2_args f w env s a1 a2 v h_ns (hN (f + 1) (by omega))).1⟩
  · exact conv_fix ⟨N, fun f hf =>
      (evalOpt_app2_args f w env s a1 a2 v h_ns (hN (f + 1) (by omega))).2⟩

/-! ## Env plumbing for the `bindArgs`-shaped bodies -/

private theorem bindArgs_ax_a (va vx : SExpr) :
    (bindArgs [aS, xS] [va, vx]).get? aS = some va := by
  show ((({} : Env).insert xS vx).insert aS va).get? aS = some va
  simp
private theorem bindArgs_ax_x (va vx : SExpr) :
    (bindArgs [aS, xS] [va, vx]).get? xS = some vx := by
  show ((({} : Env).insert xS vx).insert aS va).get? xS = some vx
  simp [Env.get?_insert, aS, xS]
private theorem bindArgs_ex_e (ve vx : SExpr) :
    (bindArgs [eS, xS] [ve, vx]).get? eS = some ve := by
  show ((({} : Env).insert xS vx).insert eS ve).get? eS = some ve
  simp
private theorem bindArgs_ex_x (ve vx : SExpr) :
    (bindArgs [eS, xS] [ve, vx]).get? xS = some vx := by
  show ((({} : Env).insert xS vx).insert eS ve).get? xS = some vx
  simp [Env.get?_insert, eS, xS]
private theorem bindArgs_xy_x (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? xS = some vx := by
  show ((({} : Env).insert yS vy).insert xS vx).get? xS = some vx
  simp
private theorem bindArgs_xy_y (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? yS = some vy := by
  show ((({} : Env).insert yS vy).insert xS vx).get? yS = some vy
  simp [Env.get?_insert, xS, yS]

/-! ## `memb`: boolean value, totality, and the TP discharger

ONE strong induction (on the second argument's VALUE count — memb's emitted
measure) yields convergence WITH a boolean-shaped value; totality and the TP
corollary follow. The demo for a future TP prover. -/

private theorem memb_body_bool (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none) :
    ∀ vx va : SExpr, ∃ v, (v = SExpr.t ∨ v = SExpr.nil) ∧
      ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [aS, xS] [va, vx]) membBody = some v := by
  intro vx
  induction vx using acl2Count_strong_induction with
  | step vx ih =>
    intro va
    have ha := re_val_var_get w (bindArgs [aS, xS] [va, vx])
      { name := "a" } va (bindArgs_ax_a va vx)
    have hx := re_val_var_get w (bindArgs [aS, xS] [va, vx])
      { name := "x" } vx (bindArgs_ax_x va vx)
    have hconsp : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [va, vx]) (conspT xT)
        = some (Logic.consp vx) :=
      conv_builtin1 w _ { name := "consp" } xT vx (Logic.consp vx)
        (by decide) h_no_consp hx (callBuiltin_consp _)
    -- the nil path, shared by both non-cons shapes
    have nilCase : Logic.consp vx = SExpr.nil →
        ∃ v, (v = SExpr.t ∨ v = SExpr.nil) ∧
        ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [aS, xS] [va, vx]) membBody = some v := by
      intro hnc
      refine ⟨SExpr.nil, Or.inr rfl, ?_⟩
      have hq := re_val_quote w (bindArgs [aS, xS] [va, vx]) SExpr.nil
      exact fuel_conv_of_eq
        (re_if_false w _ (conspT xT) _ qNil SExpr.nil (hnc ▸ hconsp) hq) hq
    match vx with
    | .nil => exact nilCase rfl
    | .atom _ => exact nilCase rfl
    | .cons hd tl =>
      have hcar : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl]) (carT xT)
          = some hd := by
        have h := conv_builtin1 w _ { name := "car" } xT (.cons hd tl)
          (Logic.car (.cons hd tl)) (by decide) h_no_car hx
          (callBuiltin_car _)
        simpa [Logic.car] using h
      have hcdr : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl]) (cdrT xT)
          = some tl := by
        have h := conv_builtin1 w _ { name := "cdr" } xT (.cons hd tl)
          (Logic.cdr (.cons hd tl)) (by decide) h_no_cdr hx
          (callBuiltin_cdr _)
        simpa [Logic.cdr] using h
      have heq : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl])
            (equalT aT (carT xT)) = some (Logic.equal va hd) :=
        conv_builtin2 w _ { name := "equal" } aT (carT xT) va hd
          (Logic.equal va hd) (by decide) h_no_equal ha hcar
          (callBuiltin_equal _ _)
      obtain ⟨vr, hvr, hr⟩ := ih tl (by simp only [acl2Count_cons]; omega) va
      have hrec : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl])
            (membT aT (cdrT xT)) = some vr :=
        conv_defn_2 w _ memb_sym aT (cdrT xT) va tl aS xS membBody vr
          memb_ns h_memb ha hcdr hr
      have hconsp' : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl]) (conspT xT)
          = some (Logic.consp (.cons hd tl)) := hconsp
      cases hbeq : Logic.toBool (Logic.equal va hd) with
      | true =>
        refine ⟨SExpr.t, Or.inl rfl, ?_⟩
        have hq := re_val_quote w (bindArgs [aS, xS] [va, .cons hd tl]) SExpr.t
        have hInner : ∃ N, ∀ f ≥ N,
            evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl])
              (ifT (equalT aT (carT xT)) qT (membT aT (cdrT xT)))
            = some SExpr.t :=
          fuel_conv_of_eq
            (re_if_true w _ (equalT aT (carT xT)) qT (membT aT (cdrT xT))
              (Logic.equal va hd) SExpr.t heq hbeq hq) hq
        exact fuel_conv_of_eq
          (re_if_true w _ (conspT xT) _ qNil (Logic.consp (.cons hd tl))
            SExpr.t hconsp' rfl hInner) hInner
      | false =>
        refine ⟨vr, hvr, ?_⟩
        have heqNil : ∃ N, ∀ f ≥ N,
            evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl])
              (equalT aT (carT xT)) = some SExpr.nil :=
          nil_of_toBool_false hbeq ▸ heq
        have hInner : ∃ N, ∀ f ≥ N,
            evalOpt f w (bindArgs [aS, xS] [va, .cons hd tl])
              (ifT (equalT aT (carT xT)) qT (membT aT (cdrT xT)))
            = some vr :=
          fuel_conv_of_eq
            (re_if_false w _ (equalT aT (carT xT)) qT (membT aT (cdrT xT))
              vr heqNil hrec) hrec
        exact fuel_conv_of_eq
          (re_if_true w _ (conspT xT) _ qNil (Logic.consp (.cons hd tl))
            vr hconsp' rfl hInner) hInner

/-- `total:memb`, world-parametric — the driver-shape totality statement. -/
theorem dis_memb_total (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (membT a0 a1) = some v := by
  intro env' a0 a1 ⟨N0, v0, h0⟩ ⟨N1, v1, h1⟩
  obtain ⟨v, _, hb⟩ := memb_body_bool w h_memb h_no_consp h_no_equal
    h_no_car h_no_cdr v1 v0
  obtain ⟨N, h⟩ := conv_defn_2 w env' memb_sym a0 a1 v0 v1 aS xS membBody v
    memb_ns h_memb ⟨N0, h0⟩ ⟨N1, h1⟩ hb
  exact ⟨N, v, h⟩

/-- `tp:memb`, world-parametric — the driver-shape TP hypothesis: any value
    `(memb a0 a1)` converges to satisfies memb's emitted boolean TP
    corollary. Argument strictness recovers the argument values; the boolean
    body induction pins the value. -/
theorem dis_memb_tp (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (membT a0 a1) = some v) :
    (bif Logic.toBool (Logic.equal v SExpr.t) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t := by
  obtain ⟨⟨N0, u0, h0⟩, ⟨N1, u1, h1⟩⟩ :=
    conv_args2_of_conv_app w e' { name := "memb" } a0 a1 v (by decide) h
  obtain ⟨u, hu, hb⟩ := memb_body_bool w h_memb h_no_consp h_no_equal
    h_no_car h_no_cdr u1 u0
  have happ := conv_defn_2 w e' memb_sym a0 a1 u0 u1 aS xS membBody u
    memb_ns h_memb ⟨N0, h0⟩ ⟨N1, h1⟩ hb
  have hv : v = u := val_unique h happ
  subst hv
  rcases hu with rfl | rfl
  · simp [Logic.equal, Logic.toBool]
  · rfl

/-! ## `rm`: totality (strong induction on the second value) -/

private theorem rm_body_total (w : World)
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    ∀ vx ve : SExpr, ∃ v, ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [eS, xS] [ve, vx]) rmBody = some v := by
  intro vx
  induction vx using acl2Count_strong_induction with
  | step vx ih =>
    intro ve
    have he := re_val_var_get w (bindArgs [eS, xS] [ve, vx])
      { name := "e" } ve (bindArgs_ex_e ve vx)
    have hx := re_val_var_get w (bindArgs [eS, xS] [ve, vx])
      { name := "x" } vx (bindArgs_ex_x ve vx)
    have hconsp : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [eS, xS] [ve, vx]) (conspT xT)
        = some (Logic.consp vx) :=
      conv_builtin1 w _ { name := "consp" } xT vx (Logic.consp vx)
        (by decide) h_no_consp hx (callBuiltin_consp _)
    have nilCase : Logic.consp vx = SExpr.nil →
        ∃ v, ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [eS, xS] [ve, vx]) rmBody = some v := by
      intro hnc
      have hq := re_val_quote w (bindArgs [eS, xS] [ve, vx]) SExpr.nil
      exact ⟨SExpr.nil, fuel_conv_of_eq
        (re_if_false w _ (conspT xT) _ qNil SExpr.nil (hnc ▸ hconsp) hq) hq⟩
    match vx with
    | .nil => exact nilCase rfl
    | .atom _ => exact nilCase rfl
    | .cons hd tl =>
      have hcar : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl]) (carT xT)
          = some hd := by
        have h := conv_builtin1 w _ { name := "car" } xT (.cons hd tl)
          (Logic.car (.cons hd tl)) (by decide) h_no_car hx
          (callBuiltin_car _)
        simpa [Logic.car] using h
      have hcdr : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl]) (cdrT xT)
          = some tl := by
        have h := conv_builtin1 w _ { name := "cdr" } xT (.cons hd tl)
          (Logic.cdr (.cons hd tl)) (by decide) h_no_cdr hx
          (callBuiltin_cdr _)
        simpa [Logic.cdr] using h
      have heq : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl])
            (equalT eT (carT xT)) = some (Logic.equal ve hd) :=
        conv_builtin2 w _ { name := "equal" } eT (carT xT) ve hd
          (Logic.equal ve hd) (by decide) h_no_equal he hcar
          (callBuiltin_equal _ _)
      obtain ⟨vr, hr⟩ := ih tl (by simp only [acl2Count_cons]; omega) ve
      have hrec : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl])
            (rmT eT (cdrT xT)) = some vr :=
        conv_defn_2 w _ rm_sym eT (cdrT xT) ve tl eS xS rmBody vr
          rm_ns h_rm he hcdr hr
      have hconsp' : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl]) (conspT xT)
          = some (Logic.consp (.cons hd tl)) := hconsp
      cases hbeq : Logic.toBool (Logic.equal ve hd) with
      | true =>
        have hInner : ∃ N, ∀ f ≥ N,
            evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl])
              (ifT (equalT eT (carT xT)) (cdrT xT)
                (consT (carT xT) (rmT eT (cdrT xT))))
            = some tl :=
          fuel_conv_of_eq
            (re_if_true w _ (equalT eT (carT xT)) (cdrT xT)
              (consT (carT xT) (rmT eT (cdrT xT)))
              (Logic.equal ve hd) tl heq hbeq hcdr) hcdr
        exact ⟨tl, fuel_conv_of_eq
          (re_if_true w _ (conspT xT) _ qNil (Logic.consp (.cons hd tl))
            tl hconsp' rfl hInner) hInner⟩
      | false =>
        have heqNil : ∃ N, ∀ f ≥ N,
            evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl])
              (equalT eT (carT xT)) = some SExpr.nil :=
          nil_of_toBool_false hbeq ▸ heq
        have hcons : ∃ N, ∀ f ≥ N,
            evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl])
              (consT (carT xT) (rmT eT (cdrT xT)))
            = some (.cons hd vr) :=
          conv_builtin2 w _ { name := "cons" } (carT xT) (rmT eT (cdrT xT))
            hd vr (.cons hd vr) (by decide) h_no_cons hcar hrec rfl
        have hInner : ∃ N, ∀ f ≥ N,
            evalOpt f w (bindArgs [eS, xS] [ve, .cons hd tl])
              (ifT (equalT eT (carT xT)) (cdrT xT)
                (consT (carT xT) (rmT eT (cdrT xT))))
            = some (.cons hd vr) :=
          fuel_conv_of_eq
            (re_if_false w _ (equalT eT (carT xT)) (cdrT xT)
              (consT (carT xT) (rmT eT (cdrT xT)))
              (.cons hd vr) heqNil hcons) hcons
        exact ⟨.cons hd vr, fuel_conv_of_eq
          (re_if_true w _ (conspT xT) _ qNil (Logic.consp (.cons hd tl))
            (.cons hd vr) hconsp' rfl hInner) hInner⟩

/-- `total:rm`, world-parametric. -/
theorem dis_rm_total (w : World)
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (rmT a0 a1) = some v := by
  intro env' a0 a1 ⟨N0, v0, h0⟩ ⟨N1, v1, h1⟩
  obtain ⟨v, hb⟩ := rm_body_total w h_rm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_cons v1 v0
  obtain ⟨N, h⟩ := conv_defn_2 w env' rm_sym a0 a1 v0 v1 eS xS rmBody v
    rm_ns h_rm ⟨N0, h0⟩ ⟨N1, h1⟩ hb
  exact ⟨N, v, h⟩

/-! ## `perm`: totality (strong induction on the FIRST value; memb/rm
totality in scope — the hand demo for the prover's user-fn-if-test
frontier) -/

private theorem perm_body_total (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    ∀ vx vy : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [xS, yS] [vx, vy]) permBody = some v := by
  intro vx
  induction vx using acl2Count_strong_induction with
  | step vx ih =>
    intro vy
    have hx := re_val_var_get w (bindArgs [xS, yS] [vx, vy])
      { name := "x" } vx (bindArgs_xy_x vx vy)
    have hy := re_val_var_get w (bindArgs [xS, yS] [vx, vy])
      { name := "y" } vy (bindArgs_xy_y vx vy)
    have hconsp : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [vx, vy]) (conspT xT)
        = some (Logic.consp vx) :=
      conv_builtin1 w _ { name := "consp" } xT vx (Logic.consp vx)
        (by decide) h_no_consp hx (callBuiltin_consp _)
    have nilCase : Logic.consp vx = SExpr.nil →
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [vx, vy]) permBody = some v := by
      intro hnc
      have hconspy : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [vx, vy]) (conspT yT)
          = some (Logic.consp vy) :=
        conv_builtin1 w _ { name := "consp" } yT vy (Logic.consp vy)
          (by decide) h_no_consp hy (callBuiltin_consp _)
      have hElse : ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [vx, vy]) (ifT (conspT yT) qNil qT)
          = some v :=
        conv_if_split w _ (conspT yT) qNil qT (Logic.consp vy) hconspy
          (fun _ => ⟨1, SExpr.nil, fun f hf => by
            obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
            exact evalOpt_quote g w _ SExpr.nil⟩)
          (fun _ => ⟨1, SExpr.t, fun f hf => by
            obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
            exact evalOpt_quote g w _ SExpr.t⟩)
      obtain ⟨Ne, v, hv⟩ := hElse
      have hb := fuel_conv_of_eq
        (re_if_false w (bindArgs [xS, yS] [vx, vy]) (conspT xT)
          (ifT (membT (carT xT) yT) (permT (cdrT xT) (rmT (carT xT) yT)) qNil)
          (ifT (conspT yT) qNil qT) v (hnc ▸ hconsp) ⟨Ne, hv⟩) ⟨Ne, hv⟩
      obtain ⟨M, hM⟩ := hb
      exact ⟨M, v, hM⟩
    match vx with
    | .nil => exact nilCase rfl
    | .atom _ => exact nilCase rfl
    | .cons hd tl =>
      have hcar : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [.cons hd tl, vy]) (carT xT)
          = some hd := by
        have h := conv_builtin1 w _ { name := "car" } xT (.cons hd tl)
          (Logic.car (.cons hd tl)) (by decide) h_no_car hx
          (callBuiltin_car _)
        simpa [Logic.car] using h
      have hcdr : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [.cons hd tl, vy]) (cdrT xT)
          = some tl := by
        have h := conv_builtin1 w _ { name := "cdr" } xT (.cons hd tl)
          (Logic.cdr (.cons hd tl)) (by decide) h_no_cdr hx
          (callBuiltin_cdr _)
        simpa [Logic.cdr] using h
      have hy' : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [.cons hd tl, vy]) yT = some vy := hy
      -- (memb (car x) y) converges — memb's totality (already discharged)
      obtain ⟨Nm, vm, hm⟩ :=
        dis_memb_total w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
          (bindArgs [xS, yS] [.cons hd tl, vy]) (carT xT) yT
          (by obtain ⟨Nc, hc⟩ := hcar; exact ⟨Nc, hd, hc⟩)
          (by obtain ⟨Ny, hyy⟩ := hy'; exact ⟨Ny, vy, hyy⟩)
      -- the inner if splits on memb's (unknown) verdict
      have hThen : Logic.toBool vm = true → ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [.cons hd tl, vy])
            (permT (cdrT xT) (rmT (carT xT) yT)) = some v := by
        intro _
        obtain ⟨Nr, vr, hr⟩ :=
          dis_rm_total w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
            (bindArgs [xS, yS] [.cons hd tl, vy]) (carT xT) yT
            (by obtain ⟨Nc, hc⟩ := hcar; exact ⟨Nc, hd, hc⟩)
            (by obtain ⟨Ny, hyy⟩ := hy'; exact ⟨Ny, vy, hyy⟩)
        obtain ⟨Np, vp, hp⟩ := ih tl (by simp only [acl2Count_cons]; omega) vr
        obtain ⟨Na, ha⟩ := conv_defn_2 w _ perm_sym (cdrT xT) (rmT (carT xT) yT)
          tl vr xS yS permBody vp perm_ns h_perm hcdr ⟨Nr, hr⟩ ⟨Np, hp⟩
        exact ⟨Na, vp, ha⟩
      have hElse : Logic.toBool vm = false → ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [.cons hd tl, vy]) qNil = some v :=
        fun _ => by
          obtain ⟨Nq, hq⟩ := re_val_quote w
            (bindArgs [xS, yS] [.cons hd tl, vy]) SExpr.nil
          exact ⟨Nq, SExpr.nil, hq⟩
      obtain ⟨Ni, vi, hi⟩ := conv_if_split w _ (membT (carT xT) yT)
        (permT (cdrT xT) (rmT (carT xT) yT)) qNil vm ⟨Nm, hm⟩ hThen hElse
      have hconsp' : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [.cons hd tl, vy]) (conspT xT)
          = some (Logic.consp (.cons hd tl)) := hconsp
      have hb := fuel_conv_of_eq
        (re_if_true w _ (conspT xT) _ (ifT (conspT yT) qNil qT)
          (Logic.consp (.cons hd tl)) vi hconsp' rfl ⟨Ni, hi⟩) ⟨Ni, hi⟩
      obtain ⟨M, hM⟩ := hb
      exact ⟨M, vi, hM⟩

/-- `total:perm`, world-parametric — the mirror's remaining totality
    hypothesis, discharged by hand (the prover's user-fn-if-test frontier;
    `conv_if_split` over memb's existential verdict is exactly the move a
    future prover extension mechanizes). -/
theorem dis_perm_total (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (permT a0 a1) = some v := by
  intro env' a0 a1 ⟨N0, v0, h0⟩ ⟨N1, v1, h1⟩
  obtain ⟨Nb, v, hb⟩ := perm_body_total w h_perm h_memb h_rm h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_cons v0 v1
  obtain ⟨N, h⟩ := conv_defn_2 w env' perm_sym a0 a1 v0 v1 xS yS permBody v
    perm_ns h_perm ⟨N0, h0⟩ ⟨N1, h1⟩ ⟨Nb, hb⟩
  exact ⟨N, v, h⟩

/-! ## Simulations under `enc` -/

/-- `memb` over an encoded second argument computes `List.contains`. -/
theorem corr_memb_enc (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a x : SExpr) (av : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some av) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' x = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (membT a x)
      = some (bif xs.contains av then SExpr.t else SExpr.nil) := by
  intro xs
  induction xs with
  | nil =>
    intro e' a x av ha hx
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [av, enc []]) membBody
        = some SExpr.nil := by
      have hxv := re_val_var_get w (bindArgs [aS, xS] [av, enc []])
        { name := "x" } (enc []) (bindArgs_ax_x av (enc []))
      have hconsp := conv_builtin1 w _ { name := "consp" } xT (enc [])
        (Logic.consp (enc [])) (by decide) h_no_consp hxv (callBuiltin_consp _)
      have hq := re_val_quote w (bindArgs [aS, xS] [av, enc []]) SExpr.nil
      exact fuel_conv_of_eq
        (re_if_false w _ (conspT xT) _ qNil SExpr.nil hconsp hq) hq
    have hcc : ([] : List SExpr).contains av = false := rfl
    simpa only [hcc, cond_false] using
      conv_defn_2 w e' memb_sym a x av (enc []) aS xS membBody SExpr.nil
        memb_ns h_memb ha hx hbody
  | cons hd tl ihl =>
    intro e' a x av ha hx
    have hav := re_val_var_get w (bindArgs [aS, xS] [av, enc (hd :: tl)])
      { name := "a" } av (bindArgs_ax_a av (enc (hd :: tl)))
    have hxv := re_val_var_get w (bindArgs [aS, xS] [av, enc (hd :: tl)])
      { name := "x" } (enc (hd :: tl)) (bindArgs_ax_x av (enc (hd :: tl)))
    have hencx : enc (hd :: tl) = .cons hd (enc tl) := rfl
    have hconsp : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)]) (conspT xT)
        = some SExpr.t := by
      have h := conv_builtin1 w _ { name := "consp" } xT (enc (hd :: tl))
        (Logic.consp (enc (hd :: tl))) (by decide) h_no_consp hxv
        (callBuiltin_consp _)
      simpa [hencx, Logic.consp] using h
    have hcar : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)]) (carT xT)
        = some hd := by
      have h := conv_builtin1 w _ { name := "car" } xT (enc (hd :: tl))
        (Logic.car (enc (hd :: tl))) (by decide) h_no_car hxv (callBuiltin_car _)
      simpa [hencx, Logic.car] using h
    have hcdr : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)]) (cdrT xT)
        = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "cdr" } xT (enc (hd :: tl))
        (Logic.cdr (enc (hd :: tl))) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
      simpa [hencx, Logic.cdr] using h
    have heq : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)])
          (equalT aT (carT xT)) = some (Logic.equal av hd) :=
      conv_builtin2 w _ { name := "equal" } aT (carT xT) av hd
        (Logic.equal av hd) (by decide) h_no_equal hav hcar
        (callBuiltin_equal _ _)
    have hrec : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)])
          (membT aT (cdrT xT))
        = some (bif tl.contains av then SExpr.t else SExpr.nil) :=
      ihl (bindArgs [aS, xS] [av, enc (hd :: tl)]) aT (cdrT xT) av hav hcdr
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)]) membBody
        = some (bif (hd :: tl).contains av then SExpr.t else SExpr.nil) := by
      have hInner : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)])
            (ifT (equalT aT (carT xT)) qT (membT aT (cdrT xT)))
          = some (bif (hd :: tl).contains av then SExpr.t else SExpr.nil) := by
        cases hbeq : (av == hd) with
        | true =>
          have hq := re_val_quote w
            (bindArgs [aS, xS] [av, enc (hd :: tl)]) SExpr.t
          have htb : Logic.toBool (Logic.equal av hd) = true := by
            simp [Logic.equal, hbeq, Logic.toBool, SExpr.t]
          have h := fuel_conv_of_eq
            (re_if_true w _ (equalT aT (carT xT)) qT (membT aT (cdrT xT))
              (Logic.equal av hd) SExpr.t heq htb hq) hq
          have hcc : (hd :: tl).contains av = true := by
            simp only [List.contains_cons, hbeq, Bool.true_or]
          simpa only [hcc, cond_true] using h
        | false =>
          have heqNil : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [aS, xS] [av, enc (hd :: tl)])
                (equalT aT (carT xT)) = some SExpr.nil := by
            have : Logic.equal av hd = SExpr.nil := by
              simp [Logic.equal, hbeq]
            exact this ▸ heq
          have h := fuel_conv_of_eq
            (re_if_false w _ (equalT aT (carT xT)) qT (membT aT (cdrT xT))
              (bif tl.contains av then SExpr.t else SExpr.nil) heqNil hrec) hrec
          have hcc : (hd :: tl).contains av = tl.contains av := by
            simp only [List.contains_cons, hbeq, Bool.false_or]
          simpa only [hcc] using h
      exact fuel_conv_of_eq
        (re_if_true w _ (conspT xT)
          (ifT (equalT aT (carT xT)) qT (membT aT (cdrT xT)))
          qNil SExpr.t _ hconsp rfl hInner) hInner
    exact conv_defn_2 w e' memb_sym a x av (enc (hd :: tl)) aS xS membBody _
      memb_ns h_memb ha hx hbody

/-- `rm` over an encoded second argument computes `List.erase`. -/
theorem corr_rm_enc (w : World)
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a x : SExpr) (av : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some av) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' x = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (rmT a x) = some (enc (xs.erase av)) := by
  intro xs
  induction xs with
  | nil =>
    intro e' a x av ha hx
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [eS, xS] [av, enc []]) rmBody
        = some SExpr.nil := by
      have hxv := re_val_var_get w (bindArgs [eS, xS] [av, enc []])
        { name := "x" } (enc []) (bindArgs_ex_x av (enc []))
      have hconsp := conv_builtin1 w _ { name := "consp" } xT (enc [])
        (Logic.consp (enc [])) (by decide) h_no_consp hxv (callBuiltin_consp _)
      have hq := re_val_quote w (bindArgs [eS, xS] [av, enc []]) SExpr.nil
      exact fuel_conv_of_eq
        (re_if_false w _ (conspT xT) _ qNil SExpr.nil hconsp hq) hq
    have hee : ([] : List SExpr).erase av = [] := rfl
    simpa only [hee] using
      conv_defn_2 w e' rm_sym a x av (enc []) eS xS rmBody SExpr.nil
        rm_ns h_rm ha hx hbody
  | cons hd tl ihl =>
    intro e' a x av ha hx
    have hav := re_val_var_get w (bindArgs [eS, xS] [av, enc (hd :: tl)])
      { name := "e" } av (bindArgs_ex_e av (enc (hd :: tl)))
    have hxv := re_val_var_get w (bindArgs [eS, xS] [av, enc (hd :: tl)])
      { name := "x" } (enc (hd :: tl)) (bindArgs_ex_x av (enc (hd :: tl)))
    have hencx : enc (hd :: tl) = .cons hd (enc tl) := rfl
    have hconsp : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)]) (conspT xT)
        = some SExpr.t := by
      have h := conv_builtin1 w _ { name := "consp" } xT (enc (hd :: tl))
        (Logic.consp (enc (hd :: tl))) (by decide) h_no_consp hxv
        (callBuiltin_consp _)
      simpa [hencx, Logic.consp] using h
    have hcar : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)]) (carT xT)
        = some hd := by
      have h := conv_builtin1 w _ { name := "car" } xT (enc (hd :: tl))
        (Logic.car (enc (hd :: tl))) (by decide) h_no_car hxv (callBuiltin_car _)
      simpa [hencx, Logic.car] using h
    have hcdr : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)]) (cdrT xT)
        = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "cdr" } xT (enc (hd :: tl))
        (Logic.cdr (enc (hd :: tl))) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
      simpa [hencx, Logic.cdr] using h
    have heq : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)])
          (equalT eT (carT xT)) = some (Logic.equal av hd) :=
      conv_builtin2 w _ { name := "equal" } eT (carT xT) av hd
        (Logic.equal av hd) (by decide) h_no_equal hav hcar
        (callBuiltin_equal _ _)
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)]) rmBody
        = some (enc ((hd :: tl).erase av)) := by
      have hInner : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)])
            (ifT (equalT eT (carT xT)) (cdrT xT)
              (consT (carT xT) (rmT eT (cdrT xT))))
          = some (enc ((hd :: tl).erase av)) := by
        cases hbeq : (hd == av) with
        | true =>
          have htb : Logic.toBool (Logic.equal av hd) = true := by
            have : (av == hd) = true := by
              exact beq_iff_eq.mpr (beq_iff_eq.mp hbeq).symm
            simp [Logic.equal, this, Logic.toBool, SExpr.t]
          have h := fuel_conv_of_eq
            (re_if_true w _ (equalT eT (carT xT)) (cdrT xT)
              (consT (carT xT) (rmT eT (cdrT xT)))
              (Logic.equal av hd) (enc tl) heq htb hcdr) hcdr
          have hee : (hd :: tl).erase av = tl := by
            rw [List.erase_cons, if_pos hbeq]
          simpa only [hee] using h
        | false =>
          have heqNil : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)])
                (equalT eT (carT xT)) = some SExpr.nil := by
            have hne : (av == hd) = false := by
              cases hav2 : (av == hd) with
              | false => rfl
              | true => exact absurd (beq_iff_eq.mpr (beq_iff_eq.mp hav2).symm) (by simp [hbeq])
            have : Logic.equal av hd = SExpr.nil := by simp [Logic.equal, hne]
            exact this ▸ heq
          have hrec : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)])
                (rmT eT (cdrT xT)) = some (enc (tl.erase av)) :=
            ihl (bindArgs [eS, xS] [av, enc (hd :: tl)]) eT (cdrT xT) av hav hcdr
          have hcons : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [eS, xS] [av, enc (hd :: tl)])
                (consT (carT xT) (rmT eT (cdrT xT)))
              = some (.cons hd (enc (tl.erase av))) :=
            conv_builtin2 w _ { name := "cons" } (carT xT) (rmT eT (cdrT xT))
              hd (enc (tl.erase av)) (.cons hd (enc (tl.erase av)))
              (by decide) h_no_cons hcar hrec rfl
          have h := fuel_conv_of_eq
            (re_if_false w _ (equalT eT (carT xT)) (cdrT xT)
              (consT (carT xT) (rmT eT (cdrT xT)))
              (.cons hd (enc (tl.erase av))) heqNil hcons) hcons
          have hee : (hd :: tl).erase av = hd :: tl.erase av := by
            rw [List.erase_cons, if_neg (by simp [hbeq])]
          simpa only [hee,
            show enc (hd :: tl.erase av) = .cons hd (enc (tl.erase av)) from rfl]
            using h
      exact fuel_conv_of_eq
        (re_if_true w _ (conspT xT)
          (ifT (equalT eT (carT xT)) (cdrT xT)
            (consT (carT xT) (rmT eT (cdrT xT))))
          qNil SExpr.t _ hconsp rfl hInner) hInner
    exact conv_defn_2 w e' rm_sym a x av (enc (hd :: tl)) eS xS rmBody _
      rm_ns h_rm ha hx hbody

/-- `perm` over encoded arguments computes `List.isPerm`. -/
theorem corr_perm_enc (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    ∀ (xs ys : List SExpr) (e' : Env) (x y : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' x = some (enc xs)) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' y = some (enc ys)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (permT x y)
      = some (bif xs.isPerm ys then SExpr.t else SExpr.nil) := by
  intro xs
  induction xs with
  | nil =>
    intro ys e' x y hx hy
    have hxv := re_val_var_get w (bindArgs [xS, yS] [enc [], enc ys])
      { name := "x" } (enc []) (bindArgs_xy_x (enc []) (enc ys))
    have hyv := re_val_var_get w (bindArgs [xS, yS] [enc [], enc ys])
      { name := "y" } (enc ys) (bindArgs_xy_y (enc []) (enc ys))
    have hconspx := conv_builtin1 w _ { name := "consp" } xT (enc [])
      (Logic.consp (enc [])) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hconspy := conv_builtin1 w _ { name := "consp" } yT (enc ys)
      (Logic.consp (enc ys)) (by decide) h_no_consp hyv (callBuiltin_consp _)
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc [], enc ys]) permBody
        = some (bif ([] : List SExpr).isPerm ys then SExpr.t else SExpr.nil) := by
      have hElse : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [enc [], enc ys])
            (ifT (conspT yT) qNil qT)
          = some (bif ([] : List SExpr).isPerm ys then SExpr.t else SExpr.nil) := by
        cases ys with
        | nil =>
          have hq := re_val_quote w (bindArgs [xS, yS] [enc [], enc []]) SExpr.t
          have h := fuel_conv_of_eq
            (re_if_false w _ (conspT yT) qNil qT SExpr.t
              (by simpa [enc, Logic.consp] using hconspy) hq) hq
          simpa only [List.isPerm,
            show ([] : List SExpr).isEmpty = true from rfl, cond_true] using h
        | cons h2 t2 =>
          have hq := re_val_quote w
            (bindArgs [xS, yS] [enc [], enc (h2 :: t2)]) SExpr.nil
          have h := fuel_conv_of_eq
            (re_if_true w _ (conspT yT) qNil qT SExpr.t SExpr.nil
              (by simpa [enc, Logic.consp] using hconspy) rfl hq) hq
          simpa only [List.isPerm,
            show (h2 :: t2).isEmpty = false from rfl, cond_false] using h
      exact fuel_conv_of_eq
        (re_if_false w _ (conspT xT) _ (ifT (conspT yT) qNil qT)
          _ (by simpa [enc, Logic.consp] using hconspx) hElse) hElse
    exact conv_defn_2 w e' perm_sym x y (enc []) (enc ys) xS yS permBody _
      perm_ns h_perm hx hy hbody
  | cons hd tl ihl =>
    intro ys e' x y hx hy
    have hxv := re_val_var_get w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
      { name := "x" } (enc (hd :: tl)) (bindArgs_xy_x (enc (hd :: tl)) (enc ys))
    have hyv := re_val_var_get w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
      { name := "y" } (enc ys) (bindArgs_xy_y (enc (hd :: tl)) (enc ys))
    have hencx : enc (hd :: tl) = .cons hd (enc tl) := rfl
    have hconspx : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (conspT xT)
        = some SExpr.t := by
      have h := conv_builtin1 w _ { name := "consp" } xT (enc (hd :: tl))
        (Logic.consp (enc (hd :: tl))) (by decide) h_no_consp hxv
        (callBuiltin_consp _)
      simpa [hencx, Logic.consp] using h
    have hcar : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (carT xT)
        = some hd := by
      have h := conv_builtin1 w _ { name := "car" } xT (enc (hd :: tl))
        (Logic.car (enc (hd :: tl))) (by decide) h_no_car hxv (callBuiltin_car _)
      simpa [hencx, Logic.car] using h
    have hcdr : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (cdrT xT)
        = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "cdr" } xT (enc (hd :: tl))
        (Logic.cdr (enc (hd :: tl))) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
      simpa [hencx, Logic.cdr] using h
    have hmemb : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
          (membT (carT xT) yT)
        = some (bif ys.contains hd then SExpr.t else SExpr.nil) :=
      corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr ys
        _ (carT xT) yT hd hcar hyv
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) permBody
        = some (bif (hd :: tl).isPerm ys then SExpr.t else SExpr.nil) := by
      have hInner : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
            (ifT (membT (carT xT) yT)
              (permT (cdrT xT) (rmT (carT xT) yT)) qNil)
          = some (bif (hd :: tl).isPerm ys then SExpr.t else SExpr.nil) := by
        cases hc : ys.contains hd with
        | true =>
          have hmemb' : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
                (membT (carT xT) yT) = some SExpr.t := by
            simpa only [hc, cond_true] using hmemb
          have hrm : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
                (rmT (carT xT) yT) = some (enc (ys.erase hd)) :=
            corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
              h_no_cons ys _ (carT xT) yT hd hcar hyv
          have hrec : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
                (permT (cdrT xT) (rmT (carT xT) yT))
              = some (bif tl.isPerm (ys.erase hd) then SExpr.t else SExpr.nil) :=
            ihl (ys.erase hd) _ (cdrT xT) (rmT (carT xT) yT) hcdr hrm
          have h := fuel_conv_of_eq
            (re_if_true w _ (membT (carT xT) yT) _ qNil SExpr.t
              _ hmemb' rfl hrec) hrec
          simpa only [List.isPerm, hc, Bool.true_and] using h
        | false =>
          have hmembNil : ∃ N, ∀ f ≥ N,
              evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
                (membT (carT xT) yT) = some SExpr.nil := by
            simpa only [hc, cond_false] using hmemb
          have hq := re_val_quote w
            (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) SExpr.nil
          have h := fuel_conv_of_eq
            (re_if_false w _ (membT (carT xT) yT)
              (permT (cdrT xT) (rmT (carT xT) yT)) qNil SExpr.nil
              hmembNil hq) hq
          simpa only [List.isPerm, hc, Bool.false_and, cond_false] using h
      exact fuel_conv_of_eq
        (re_if_true w _ (conspT xT)
          (ifT (membT (carT xT) yT) (permT (cdrT xT) (rmT (carT xT) yT)) qNil)
          (ifT (conspT yT) qNil qT)
          SExpr.t _ hconspx rfl hInner) hInner
    exact conv_defn_2 w e' perm_sym x y (enc (hd :: tl)) (enc ys) xS yS
      permBody _ perm_ns h_perm hx hy hbody

/-! ## The assembly -/

/-- The perm-cons mirror formula, exactly as the log emits it. -/
def perm_consFormula : SExpr :=
  impliesT (membT aT xT)
    (equalT (permT xT (consT aT yT)) (permT (rmT aT xT) yT))

/-- The native theorem FROM the mirror: any proof of the (truthiness) mirror
    statement over a world carrying the three defuns yields
    `xs.contains a → (xs.isPerm (a :: ys) = (xs.erase a).isPerm ys)`. The
    mirror is consumed at exactly one seam. -/
theorem perm_cons_native_of_mirror (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (hmirror : ∀ env : Env,
      ∃ N, ∀ f, f ≥ N → ∃ v,
        evalOpt f w env perm_consFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr) (hmem : xs.contains av = true) :
    xs.isPerm (av :: ys) = (xs.erase av).isPerm ys := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "a" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  -- the antecedent: (memb a x) computes contains = t
  have hP : ∃ N, ∀ f ≥ N, evalOpt f w e (membT aT xT) = some SExpr.t := by
    have h := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
      xs e aT xT av ha hx
    simpa only [hmem, cond_true] using h
  -- (cons a y) encodes (av :: ys)
  have hcons : ∃ N, ∀ f ≥ N,
      evalOpt f w e (consT aT yT) = some (enc (av :: ys)) :=
    conv_builtin2 w e { name := "cons" } aT yT av (enc ys)
      (enc (av :: ys)) (by decide) h_no_cons ha hy rfl
  -- LHS: (perm x (cons a y)) computes isPerm xs (av :: ys)
  have hL : ∃ N, ∀ f ≥ N, evalOpt f w e (permT xT (consT aT yT))
      = some (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil) :=
    corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons xs (av :: ys) e xT (consT aT yT) hx hcons
  -- RHS: (perm (rm a x) y) computes isPerm (xs.erase av) ys
  have hrm : ∃ N, ∀ f ≥ N,
      evalOpt f w e (rmT aT xT) = some (enc (xs.erase av)) :=
    corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e aT xT av ha hx
  have hR : ∃ N, ∀ f ≥ N, evalOpt f w e (permT (rmT aT xT) yT)
      = some (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil) :=
    corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons (xs.erase av) ys e (rmT aT xT) yT hrm hy
  -- the mirror at e: implies-truthy; antecedent truthy → equal truthy
  have hEq : ∃ N, ∀ f ≥ N, evalOpt f w e
      (equalT (permT xT (consT aT yT)) (permT (rmT aT xT) yT))
      = some (Logic.equal
          (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
          (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil)) :=
    conv_builtin2 w e { name := "equal" } _ _ _ _ _ (by decide) h_no_equal
      hL hR (callBuiltin_equal _ _)
  have hImp : ∃ N, ∀ f ≥ N, evalOpt f w e perm_consFormula
      = some (Logic.implies SExpr.t
          (Logic.equal
            (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
            (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil))) :=
    conv_builtin2 w e { name := "implies" } _ _ _ _ _ (by decide)
      h_no_implies hP hEq (callBuiltin_implies _ _)
  -- decode: the mirror's truthiness pins implies ≠ nil → = t → equal truthy
  obtain ⟨Nm, hm⟩ := hmirror e
  have hne : Logic.implies SExpr.t
      (Logic.equal
        (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
        (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil))
      ≠ SExpr.nil := by
    obtain ⟨NI, hI⟩ := hImp
    obtain ⟨v, hv, hvne⟩ := hm (max Nm NI) (by omega)
    have : v = Logic.implies SExpr.t _ :=
      Option.some.inj ((hI (max Nm NI) (by omega)) ▸ hv.symm.trans rfl)
    exact this ▸ hvne
  have hIt := implies_t_of_ne_nil hne
  have hQt : Logic.toBool (Logic.equal
      (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
      (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil)) = true :=
    truthy_of_implies_t hIt rfl
  -- Bool-cond injectivity: t ≠ nil discriminates
  exact bool_of_cond_eq (eq_of_equal_truthy hQt)

/-! ## The remaining perm-book native entries (lifter sprint 2026-07-06)

Each consumes its theorem's UNCONDITIONAL driver mirror at exactly one seam
(`hmirror`) and decodes through the `corr_*` simulation layer with the
Lifting decode kit (`mirror_pins_ne_nil` / `bool_of_cond_eq` /
`conv_and_conds` / `mirror_peel_guard`). -/

private def bS : Symbol := ⟨"ACL2", "b"⟩
private def bT : SExpr := .atom (.symbol { name := "b" })
private def zS : Symbol := ⟨"ACL2", "z"⟩
private def zT : SExpr := .atom (.symbol { name := "z" })

def perm_symmetricFormula : SExpr := impliesT (permT xT yT) (permT yT xT)

/-- perm-symmetric, natively: `isPerm` is symmetric. -/
theorem perm_symmetric_native_of_mirror (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (hmirror : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_symmetricFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys : List SExpr) (hp : xs.isPerm ys = true) :
    ys.isPerm xs = true := by
  let e : Env := (({} : Env).insert yS (enc ys)).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert yS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = (({} : Env).insert yS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hA := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs ys e xT yT hx hy
  have hC := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons ys xs e yT xT hy hx
  have hImp := conv_builtin2 w e { name := "implies" } _ _ _ _ _ (by decide)
    h_no_implies hA hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (mirror_pins_ne_nil (hmirror e) hImp)
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hp]; rfl))

def memb_rmFormula : SExpr := impliesT (membT aT (rmT bT xT)) (membT aT xT)

/-- memb-rm, natively: membership survives erasing another element. -/
theorem memb_rm_native_of_mirror (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (hmirror : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env memb_rmFormula = some v ∧ v ≠ SExpr.nil)
    (av bv : SExpr) (xs : List SExpr)
    (hmem : (xs.erase bv).contains av = true) :
    xs.contains av = true := by
  let e : Env := ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "a" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
    re_val_var_get w e { name := "b" } bv (by
      show e.get? bS = some bv
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hrm := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons xs e bT xT bv hb hx
  have hA := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
    (xs.erase bv) e aT (rmT bT xT) av ha hrm
  have hC := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
    xs e aT xT av ha hx
  have hImp := conv_builtin2 w e { name := "implies" } _ _ _ _ _ (by decide)
    h_no_implies hA hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (mirror_pins_ne_nil (hmirror e) hImp)
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hmem]; rfl))

def comm_rmFormula : SExpr := equalT (rmT aT (rmT bT xT)) (rmT bT (rmT aT xT))

/-- comm-rm, natively: erasures commute (a LIST equality, decoded via `enc`
    injectivity). -/
theorem comm_rm_native_of_mirror (w : World)
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (hmirror : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env comm_rmFormula = some v ∧ v ≠ SExpr.nil)
    (av bv : SExpr) (xs : List SExpr) :
    (xs.erase bv).erase av = (xs.erase av).erase bv := by
  let e : Env := ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "a" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
    re_val_var_get w e { name := "b" } bv (by
      show e.get? bS = some bv
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hL := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons (xs.erase bv) e aT (rmT bT xT) av ha
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e bT xT bv hb hx)
  have hR := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons (xs.erase av) e bT (rmT aT xT) bv hb
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e aT xT av ha hx)
  have hEq := conv_builtin2 w e { name := "equal" } _ _ _ _ _ (by decide)
    h_no_equal hL hR (callBuiltin_equal _ _)
  exact enc_inj (eq_of_equal_truthy (toBool_true_of_ne_nil
    (mirror_pins_ne_nil (hmirror e) hEq)))

def perm_membFormula : SExpr :=
  impliesT (ifT (permT xT yT) (membT aT xT) qNil) (membT aT yT)

/-- perm-memb, natively: membership transports across `isPerm`. -/
theorem perm_memb_native_of_mirror (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (hmirror : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_membFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) (hmem : xs.contains av = true) :
    ys.contains av = true := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "a" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hAnd := conv_and_conds w e (permT xT yT) (membT aT xT)
    (xs.isPerm ys) (xs.contains av)
    (corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons xs ys e xT yT hx hy)
    (corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
      xs e aT xT av ha hx)
  have hC := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
    ys e aT yT av ha hy
  have hImp := conv_builtin2 w e { name := "implies" } _ _ _ _ _ (by decide)
    h_no_implies hAnd hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (mirror_pins_ne_nil (hmirror e) hImp)
  have hb : (xs.isPerm ys && xs.contains av) = true := by rw [hp, hmem]; rfl
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hb]; rfl))

def perm_rmFormula : SExpr :=
  impliesT (permT xT yT) (permT (rmT aT xT) (rmT aT yT))

/-- perm-rm, natively: `isPerm` is preserved by erasing the same element. -/
theorem perm_rm_native_of_mirror (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (hmirror : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_rmFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr) (hp : xs.isPerm ys = true) :
    (xs.erase av).isPerm (ys.erase av) = true := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "a" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hA := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs ys e xT yT hx hy
  have hC := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons (xs.erase av) (ys.erase av) e
    (rmT aT xT) (rmT aT yT)
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e aT xT av ha hx)
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      ys e aT yT av ha hy)
  have hImp := conv_builtin2 w e { name := "implies" } _ _ _ _ _ (by decide)
    h_no_implies hA hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (mirror_pins_ne_nil (hmirror e) hImp)
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hp]; rfl))

def perm_transitiveFormula : SExpr :=
  impliesT (ifT (permT xT yT) (permT yT zT) qNil) (permT xT zT)

/-- perm-transitive, natively: `isPerm` is transitive. -/
theorem perm_transitive_native_of_mirror (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (hmirror : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_transitiveFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys zs : List SExpr)
    (hxy : xs.isPerm ys = true) (hyz : ys.isPerm zs = true) :
    xs.isPerm zs = true := by
  let e : Env := ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hz : ∃ N, ∀ f ≥ N, evalOpt f w e zT = some (enc zs) :=
    re_val_var_get w e { name := "z" } (enc zs) (by
      show e.get? zS = some (enc zs)
      rw [show e = ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hAnd := conv_and_conds w e (permT xT yT) (permT yT zT)
    (xs.isPerm ys) (ys.isPerm zs)
    (corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons xs ys e xT yT hx hy)
    (corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons ys zs e yT zT hy hz)
  have hC := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs zs e xT zT hx hz
  have hImp := conv_builtin2 w e { name := "implies" } _ _ _ _ _ (by decide)
    h_no_implies hAnd hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (mirror_pins_ne_nil (hmirror e) hImp)
  have hb : (xs.isPerm ys && ys.isPerm zs) = true := by rw [hxy, hyz]; rfl
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hb]; rfl))

private abbrev booleanpT (x : SExpr) : SExpr := app1 "booleanp" x

/-- The `defequiv`-generated obligation, macroexpanded exactly as ACL2's
    Goal input clause states it (audit #3 verified this byte-for-byte
    against the log's :INPUTCLAUSE). -/
def perm_equivFormula : SExpr :=
  ifT (booleanpT (permT xT yT))
    (ifT (permT xT xT)
      (ifT (impliesT (permT xT yT) (permT yT xT))
        (impliesT (ifT (permT xT yT) (permT yT zT) qNil) (permT xT zT))
        qNil)
      qNil)
    qNil

/-- perm-is-an-equivalence, natively — the genuinely NEW conjunct is
    REFLEXIVITY (the symmetric/transitive conjuncts have their own
    theorems): peel the `booleanp` guard (type-absorbed), then the `(perm
    x x)` guard IS the native fact. -/
theorem perm_refl_native_of_mirror (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_booleanp : w.defs.get? ({ name := "booleanp" } : Symbol) = none)
    (hmirror : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_equivFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) : xs.isPerm xs = true := by
  let e : Env := ((({} : Env).insert zS (enc [])).insert yS (enc [])).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "x" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert zS (enc [])).insert yS (enc [])).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc []) :=
    re_val_var_get w e { name := "y" } (enc []) (by
      show e.get? yS = some (enc [])
      rw [show e = ((({} : Env).insert zS (enc [])).insert yS (enc [])).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- guard 1: (booleanp (perm x y)) computes to t = bif true (type-absorbed)
  have hpxy := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs [] e xT yT hx hy
  have hG1 : ∃ N, ∀ f ≥ N, evalOpt f w e (booleanpT (permT xT yT))
      = some (bif true then SExpr.t else SExpr.nil) := by
    have h := conv_builtin1 w e { name := "booleanp" } (permT xT yT)
      (bif xs.isPerm [] then SExpr.t else SExpr.nil)
      (Logic.booleanp (bif xs.isPerm [] then SExpr.t else SExpr.nil))
      (by decide) h_no_booleanp hpxy (callBuiltin_booleanp _)
    rw [booleanp_cond] at h
    exact h
  obtain ⟨_, hrest⟩ := mirror_peel_guard (hmirror e) hG1
  -- guard 2: (perm x x) — its Bool IS the reflexivity fact
  have hG2 := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs xs e xT xT hx hx
  exact (mirror_peel_guard hrest hG2).1

/-- The idiomatic corollary over `List.Perm`: a member can be moved across —
    `a ∈ xs → (xs ~ a :: ys ↔ xs.erase a ~ ys)`. -/
theorem perm_cons_native_perm_of_mirror (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (hmirror : ∀ env : Env,
      ∃ N, ∀ f, f ≥ N → ∃ v,
        evalOpt f w env perm_consFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr) (hmem : av ∈ xs) :
    xs.Perm (av :: ys) ↔ (xs.erase av).Perm ys := by
  have h := perm_cons_native_of_mirror w h_perm h_memb h_rm h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_cons h_no_implies hmirror av xs ys
    (by simpa [List.contains_iff_mem] using hmem)
  constructor
  · intro hp
    exact List.isPerm_iff.mp (h ▸ List.isPerm_iff.mpr hp)
  · intro hp
    exact List.isPerm_iff.mp (h ▸ List.isPerm_iff.mpr hp)

end ACL2.Worlds.Perm

