import ACL2Lean.EvalOpt
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Count
import ACL2Lean.Imported.Lifting

open ACL2 ACL2.Replay

/-! # Generality probe: append-associativity replay

A second, structurally-different theorem replayed with the SAME schematic
machinery built for `my-len-my-app` (`Imported/SimpleWorld.lean`):

  `app-assoc`  (acl2_samples/recon-tests/02-rev):
  `(equal (app (app a b) c) (app a (app b c)))`,  induction on `a`.

Differences that make this a real generality test:
- cons-reassociation, not arithmetic — no `binary-+`, no `fix`, no
  `type-prescription`, so NO `fix`-gap and the base case is fully schematic;
- the IH solidify is PURE (the IH applies directly, no commutativity reorder);
- needs `car-cons` (`re_car_cons`) and the 2-formal compound unfold
  (`evalOpt_unfold2_conv`) — both added for this probe;
- the calls use args (`a`,`b`,`c`,`(cdr a)`) that are NOT the function's formals
  (`x`,`y`), so the variable-unfold shortcut `re_unfold2_var` does not apply and
  every unfold uses the general `evalOpt_unfold2_conv`.

Consumes only `h_app_total` (my-app admission ⇒ totality) + def/no-shadow facts. -/

namespace ACL2.Worlds.AppAssoc

private def sym (name : String) : Symbol := { package := "ACL2", name := name }

def appBody : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "IF" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CONSP" })) (SExpr.cons (SExpr.atom (.symbol { name := "X" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CONS" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CAR" })) (SExpr.cons (SExpr.atom (.symbol { name := "X" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "APP" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CDR" })) (SExpr.cons (SExpr.atom (.symbol { name := "X" })) SExpr.nil)) (SExpr.cons (SExpr.atom (.symbol { name := "Y" })) SExpr.nil))) SExpr.nil))) (SExpr.cons (SExpr.atom (.symbol { name := "Y" })) SExpr.nil))))

def world : World where
  defs := ({} : DefMap)
    |>.insert (sym "APP") ([sym "X", sym "Y"], appBody)

private def x_sym : Symbol := sym "X"
private def y_sym : Symbol := sym "Y"
private def a_sym : Symbol := sym "A"
private def b_sym : Symbol := sym "B"
private def c_sym : Symbol := sym "C"
private def app_sym : Symbol := sym "APP"

private def aT : SExpr := .atom (.symbol { name := "A" })
private def bT : SExpr := .atom (.symbol { name := "B" })
private def cT : SExpr := .atom (.symbol { name := "C" })
private def appOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "APP" })) (.cons a (.cons b .nil))
private def equalOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil))
private def carOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CAR" })) (.cons t .nil)
private def cdrOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CDR" })) (.cons t .nil)
private def consOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))
private def conspOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CONSP" })) (.cons t .nil)
/-- The then-branch of `app`'s body after substituting args: `(cons (car a)(app (cdr a) b))`. -/
private def appThen (a b : SExpr) : SExpr := consOf (carOf a) (appOf (cdrOf a) b)

def app_assocFormula : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "EQUAL" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "APP" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "APP" })) (SExpr.cons (SExpr.atom (.symbol { name := "A" })) (SExpr.cons (SExpr.atom (.symbol { name := "B" })) SExpr.nil))) (SExpr.cons (SExpr.atom (.symbol { name := "C" })) SExpr.nil))) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "APP" })) (SExpr.cons (SExpr.atom (.symbol { name := "A" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "APP" })) (SExpr.cons (SExpr.atom (.symbol { name := "B" })) (SExpr.cons (SExpr.atom (.symbol { name := "C" })) SExpr.nil))) SExpr.nil))) SExpr.nil)))

private theorem formula_decomp :
    app_assocFormula = equalOf (appOf (appOf aT bT) cT) (appOf aT (appOf bT cT)) := rfl

private theorem app_not_special :
    app_sym.isNamed "QUOTE" = false ∧ app_sym.isNamed "IF" = false ∧
    app_sym.isNamed "LET" = false ∧ app_sym.isNamed "LET*" = false := by decide
private theorem consp_not_special :
    ({ name := "CONSP" } : Symbol).isNamed "QUOTE" = false ∧
    ({ name := "CONSP" } : Symbol).isNamed "IF" = false ∧
    ({ name := "CONSP" } : Symbol).isNamed "LET" = false ∧
    ({ name := "CONSP" } : Symbol).isNamed "LET*" = false := by decide
private theorem equal_not_special :
    ({ name := "EQUAL" } : Symbol).isNamed "QUOTE" = false ∧
    ({ name := "EQUAL" } : Symbol).isNamed "IF" = false ∧
    ({ name := "EQUAL" } : Symbol).isNamed "LET" = false ∧
    ({ name := "EQUAL" } : Symbol).isNamed "LET*" = false := by decide

private theorem car_not_special :
    ({ name := "CAR" } : Symbol).isNamed "QUOTE" = false ∧
    ({ name := "CAR" } : Symbol).isNamed "IF" = false ∧
    ({ name := "CAR" } : Symbol).isNamed "LET" = false ∧
    ({ name := "CAR" } : Symbol).isNamed "LET*" = false := by decide
private theorem cdr_not_special :
    ({ name := "CDR" } : Symbol).isNamed "QUOTE" = false ∧
    ({ name := "CDR" } : Symbol).isNamed "IF" = false ∧
    ({ name := "CDR" } : Symbol).isNamed "LET" = false ∧
    ({ name := "CDR" } : Symbol).isNamed "LET*" = false := by decide
private theorem cons_not_special :
    ({ name := "CONS" } : Symbol).isNamed "QUOTE" = false ∧
    ({ name := "CONS" } : Symbol).isNamed "IF" = false ∧
    ({ name := "CONS" } : Symbol).isNamed "LET" = false ∧
    ({ name := "CONS" } : Symbol).isNamed "LET*" = false := by decide

private theorem appBody_nolet : WellScoped appBody = true := by decide
private theorem appBody_fv : ∀ s ∈ freeVars appBody, s ∈ [x_sym, y_sym] := by decide

/-- Append associativity, replayed schematically. Consumes my-app totality +
    def/no-shadow facts only. -/
theorem app_assoc_generic
    (w : World) (env : Env)
    (h_app : w.defs[app_sym]? = some ([x_sym, y_sym], appBody))
    (h_no_equal : w.defs[({ name := "EQUAL" } : Symbol)]? = none)
    (h_no_consp : w.defs[({ name := "CONSP" } : Symbol)]? = none)
    (h_no_cdr   : w.defs[({ name := "CDR" } : Symbol)]? = none)
    (h_no_car   : w.defs[({ name := "CAR" } : Symbol)]? = none)
    (h_no_cons  : w.defs[({ name := "CONS" } : Symbol)]? = none)
    (h_app_total : ∀ (e' : Env) (a b : SExpr),
      (∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' a = some av) →
      (∃ M, ∀ f ≥ M, ∃ bv, evalOpt f w e' b = some bv) →
      ∃ M, ∃ rv, ∀ f ≥ M, evalOpt f w e' (appOf a b) = some rv)
    :
    ∃ N, ∀ f, f ≥ N → evalOpt f w env app_assocFormula = some SExpr.t := by
  suffices H : ∀ av : SExpr, ∀ e : Env,
      (∀ f, evalOpt (f + 1) w e (.atom (.symbol a_sym)) = some av) →
      ∃ N, ∀ f, f ≥ N → evalOpt f w e app_assocFormula = some SExpr.t by
    obtain ⟨av, h_av⟩ : ∃ av, ∀ f, evalOpt (f + 1) w env (.atom (.symbol a_sym)) = some av := by
      match ha : env.get? a_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w env a_sym v ha⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w env a_sym ha (by decide)⟩
    exact H av env h_av
  refine acl2_induction_consp (fun av => ∀ e : Env,
      (∀ f, evalOpt (f + 1) w e (.atom (.symbol a_sym)) = some av) →
      ∃ N, ∀ f, f ≥ N → evalOpt f w e app_assocFormula = some SExpr.t) ?base ?step

  -- ════════════════ Subgoal *1/2 (base): consp av = nil ════════════════
  case base =>
    intro av h_consp e h_ae
    obtain ⟨bv, h_be⟩ : ∃ bv, ∀ f, evalOpt (f + 1) w e bT = some bv := by
      match hb : e.get? b_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w e b_sym v hb⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w e b_sym hb (by decide)⟩
    obtain ⟨cv, h_ce⟩ : ∃ cv, ∀ f, evalOpt (f + 1) w e cT = some cv := by
      match hc : e.get? c_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w e c_sym v hc⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w e c_sym hc (by decide)⟩
    have hac : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ae g⟩
    have hbc : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_be g⟩
    have hcc : ∃ N, ∀ f ≥ N, evalOpt f w e cT = some cv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ce g⟩
    have hconsp_a : ∃ N, ∀ f ≥ N, evalOpt f w e (conspOf aT) = some .nil := by
      have h := conv_builtin1 w e { name := "CONSP" } aT av (Logic.consp av)
        consp_not_special h_no_consp hac (callBuiltin_consp av)
      rwa [h_consp] at h
    obtain ⟨Nbc, vbc, hbc'⟩ := h_app_total e bT cT
      ⟨1, fun f hf => ⟨bv, by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_be g⟩⟩
      ⟨1, fun f hf => ⟨cv, by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ce g⟩⟩
    have hvbc : ∃ N, ∀ f ≥ N, evalOpt f w e (appOf bT cT) = some vbc := ⟨Nbc, hbc'⟩
    -- nodeB1: (app a b) ⇒ b   [:DEFINITION compound unfold ; if-FALSE]
    have nodeB1 : ∃ N, ∀ f ≥ N, evalOpt f w e (appOf aT bT) = evalOpt f w e bT := by
      obtain ⟨Nab, vab, hab⟩ := h_app_total e aT bT
        ⟨1, fun f hf => ⟨av, by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ae g⟩⟩
        ⟨1, fun f hf => ⟨bv, by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_be g⟩⟩
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym, y_sym] [av, bv]) appBody = some vab := by
        refine ⟨Nab + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_2 (g + 1) w e app_sym aT bT av bv x_sym y_sym appBody
              app_not_special h_app (h_ae g) (h_be g)]
        exact hab (g + 2) (by omega)
      exact fuel_chain_eq
        (evalOpt_unfold2_conv w e app_sym x_sym y_sym appBody aT bT av bv vab
          app_not_special h_app appBody_fv appBody_nolet hac hbc hbody)
        (re_if_false w e (conspOf aT) (appThen aT bT) bT bv hconsp_a hbc)
    -- nodeB2: (app a (app b c)) ⇒ (app b c)   [:DEFINITION compound unfold ; if-FALSE]
    have nodeB2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf aT (appOf bT cT)) = evalOpt f w e (appOf bT cT) := by
      obtain ⟨Nr, vr, hr⟩ := h_app_total e aT (appOf bT cT)
        ⟨1, fun f hf => ⟨av, by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ae g⟩⟩
        ⟨Nbc, fun f hf => ⟨vbc, hbc' f hf⟩⟩
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym, y_sym] [av, vbc]) appBody = some vr := by
        refine ⟨max Nr Nbc + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_2 (g + 1) w e app_sym aT (appOf bT cT) av vbc x_sym y_sym appBody
              app_not_special h_app (h_ae g) (hbc' (g + 1) (by omega))]
        exact hr (g + 2) (by omega)
      exact fuel_chain_eq
        (evalOpt_unfold2_conv w e app_sym x_sym y_sym appBody aT (appOf bT cT) av vbc vr
          app_not_special h_app appBody_fv appBody_nolet hac hvbc hbody)
        (re_if_false w e (conspOf aT) (appThen aT (appOf bT cT)) (appOf bT cT) vbc hconsp_a hvbc)
    -- equal-self on (app b c)
    have hself : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (appOf bT cT) (appOf bT cT)) = some SExpr.t := by
      obtain ⟨Na, ha⟩ := hvbc
      refine ⟨Na + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_equal_self g w e (appOf bT cT) vbc (ha g (by omega)) h_no_equal
    -- Assemble: equal A B  →[nodeB1 under (app · c), equal-left]  equal (app b c) B
    --                      →[nodeB2 under equal-right]            equal (app b c)(app b c)
    --                      →[equal-self]                          t
    have c1 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (appOf (appOf aT bT) cT) (appOf aT (appOf bT cT)))
        = evalOpt f w e (equalOf (appOf bT cT) (appOf aT (appOf bT cT))) :=
      evalOpt_congr_binary_left w e { name := "EQUAL" }
        (appOf (appOf aT bT) cT) (appOf bT cT) (appOf aT (appOf bT cT)) equal_not_special
        (evalOpt_congr_binary_left w e { name := "APP" }
          (appOf aT bT) bT cT app_not_special nodeB1)
    have c2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (appOf bT cT) (appOf aT (appOf bT cT)))
        = evalOpt f w e (equalOf (appOf bT cT) (appOf bT cT)) :=
      evalOpt_congr_binary_right w e { name := "EQUAL" }
        (appOf bT cT) (appOf aT (appOf bT cT)) (appOf bT cT) equal_not_special nodeB2
    rw [formula_decomp]
    exact fuel_chain_eq (fuel_chain_eq c1 c2) hself

  -- ════════════════ Subgoal *1/1 (step): consp av ≠ nil ════════════════
  case step =>
    intro av h_consp ih e h_ae
    obtain ⟨bv, h_be⟩ : ∃ bv, ∀ f, evalOpt (f + 1) w e bT = some bv := by
      match hb : e.get? b_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w e b_sym v hb⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w e b_sym hb (by decide)⟩
    obtain ⟨cv, h_ce⟩ : ∃ cv, ∀ f, evalOpt (f + 1) w e cT = some cv := by
      match hc : e.get? c_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w e c_sym v hc⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w e c_sym hc (by decide)⟩
    have hac : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ae g⟩
    have hbc : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_be g⟩
    have hcc : ∃ N, ∀ f ≥ N, evalOpt f w e cT = some cv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ce g⟩
    have hct : Logic.consp av = SExpr.t := by
      match av with
      | .cons _ _ => rfl
      | .nil => exact absurd rfl h_consp
      | .atom _ => exact absurd rfl h_consp
    have hconsp_t : ∃ N, ∀ f ≥ N, evalOpt f w e (conspOf aT) = some (Logic.consp av) :=
      conv_builtin1 w e { name := "CONSP" } aT av (Logic.consp av) consp_not_special h_no_consp hac
        (callBuiltin_consp av)
    have hcar : ∃ N, ∀ f ≥ N, evalOpt f w e (carOf aT) = some (Logic.car av) :=
      conv_builtin1 w e { name := "CAR" } aT av (Logic.car av) car_not_special h_no_car hac
        (callBuiltin_car av)
    have hcdr : ∃ N, ∀ f ≥ N, evalOpt f w e (cdrOf aT) = some (Logic.cdr av) :=
      conv_builtin1 w e { name := "CDR" } aT av (Logic.cdr av) cdr_not_special h_no_cdr hac
        (callBuiltin_cdr av)
    -- (app (cdr a) b) ⇒ vcab ; (app b c) ⇒ vbc   (totality)
    obtain ⟨Ncab, vcab, hcab⟩ := h_app_total e (cdrOf aT) bT
      (by obtain ⟨N, h⟩ := hcdr; exact ⟨N, fun f hf => ⟨Logic.cdr av, h f hf⟩⟩)
      (by obtain ⟨N, h⟩ := hbc; exact ⟨N, fun f hf => ⟨bv, h f hf⟩⟩)
    have hvcab : ∃ N, ∀ f ≥ N, evalOpt f w e (appOf (cdrOf aT) bT) = some vcab := ⟨Ncab, hcab⟩
    obtain ⟨Nbc, vbc, hbc'⟩ := h_app_total e bT cT
      (by obtain ⟨N, h⟩ := hbc; exact ⟨N, fun f hf => ⟨bv, h f hf⟩⟩)
      (by obtain ⟨N, h⟩ := hcc; exact ⟨N, fun f hf => ⟨cv, h f hf⟩⟩)
    have hvbc : ∃ N, ∀ f ≥ N, evalOpt f w e (appOf bT cT) = some vbc := ⟨Nbc, hbc'⟩
    -- T2 = (cons (car a) (app (cdr a) b)) ⇒ cons(car av, vcab)
    have hT2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appThen aT bT) = some (.cons (Logic.car av) vcab) :=
      conv_builtin2 w e { name := "CONS" } (carOf aT) (appOf (cdrOf aT) bT)
        (Logic.car av) vcab (.cons (Logic.car av) vcab) cons_not_special h_no_cons hcar hvcab rfl
    -- stepN1: (app a b) ⇒ (cons (car a) (app (cdr a) b))   [unfold ; if-TRUE]
    have stepN1 : ∃ N, ∀ f ≥ N, evalOpt f w e (appOf aT bT) = evalOpt f w e (appThen aT bT) := by
      obtain ⟨Nab, vab, hab⟩ := h_app_total e aT bT
        (by obtain ⟨N, h⟩ := hac; exact ⟨N, fun f hf => ⟨av, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hbc; exact ⟨N, fun f hf => ⟨bv, h f hf⟩⟩)
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym, y_sym] [av, bv]) appBody = some vab := by
        refine ⟨Nab + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_2 (g + 1) w e app_sym aT bT av bv x_sym y_sym appBody
              app_not_special h_app (h_ae g) (h_be g)]
        exact hab (g + 2) (by omega)
      exact fuel_chain_eq
        (evalOpt_unfold2_conv w e app_sym x_sym y_sym appBody aT bT av bv vab
          app_not_special h_app appBody_fv appBody_nolet hac hbc hbody)
        (re_if_true w e (conspOf aT) (appThen aT bT) bT (Logic.consp av)
          (.cons (Logic.car av) vcab) hconsp_t (by rw [hct]; decide) hT2)
    -- stepN2: (app T2 c) ⇒ (cons (car a) (app (app (cdr a) b) c))  [unfold ; if-T ; car-cons ; cdr-cons]
    have stepN2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf (appThen aT bT) cT)
        = evalOpt f w e (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT)) := by
      -- convergences for the then-branch (cons (car T2) (app (cdr T2) c))
      have hcarT2 : ∃ N, ∀ f ≥ N, evalOpt f w e (carOf (appThen aT bT)) = some (Logic.car av) := by
        have h := conv_builtin1 w e { name := "CAR" } (appThen aT bT) (.cons (Logic.car av) vcab)
          (Logic.car (.cons (Logic.car av) vcab)) car_not_special h_no_car hT2
          (callBuiltin_car (.cons (Logic.car av) vcab))
        simpa [Logic.car] using h
      have hcdrT2 : ∃ N, ∀ f ≥ N, evalOpt f w e (cdrOf (appThen aT bT)) = some vcab := by
        have h := conv_builtin1 w e { name := "CDR" } (appThen aT bT) (.cons (Logic.car av) vcab)
          (Logic.cdr (.cons (Logic.car av) vcab)) cdr_not_special h_no_cdr hT2
          (callBuiltin_cdr (.cons (Logic.car av) vcab))
        simpa [Logic.cdr] using h
      obtain ⟨Nac, vac, hacc⟩ := h_app_total e (cdrOf (appThen aT bT)) cT
        (by obtain ⟨N, h⟩ := hcdrT2; exact ⟨N, fun f hf => ⟨vcab, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hcc; exact ⟨N, fun f hf => ⟨cv, h f hf⟩⟩)
      have hthen : ∃ N, ∀ f ≥ N,
          evalOpt f w e (consOf (carOf (appThen aT bT)) (appOf (cdrOf (appThen aT bT)) cT))
          = some (.cons (Logic.car av) vac) :=
        conv_builtin2 w e { name := "CONS" } (carOf (appThen aT bT)) (appOf (cdrOf (appThen aT bT)) cT)
          (Logic.car av) vac (.cons (Logic.car av) vac) cons_not_special h_no_cons hcarT2 ⟨Nac, hacc⟩ rfl
      -- (app T2 c) totality, for the unfold body value
      obtain ⟨NappT2c, vT2c, hT2c⟩ := h_app_total e (appThen aT bT) cT
        (by obtain ⟨N, h⟩ := hT2; exact ⟨N, fun f hf => ⟨_, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hcc; exact ⟨N, fun f hf => ⟨cv, h f hf⟩⟩)
      have hbody2 : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym, y_sym] [.cons (Logic.car av) vcab, cv]) appBody = some vT2c := by
        obtain ⟨NT2, hT2spec⟩ := hT2
        refine ⟨max NappT2c NT2 + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_2 (g + 1) w e app_sym (appThen aT bT) cT (.cons (Logic.car av) vcab) cv
              x_sym y_sym appBody app_not_special h_app (hT2spec (g + 1) (by omega)) (h_ce g)]
        exact hT2c (g + 2) (by omega)
      exact fuel_chain_eq (fuel_chain_eq (fuel_chain_eq
        (evalOpt_unfold2_conv w e app_sym x_sym y_sym appBody (appThen aT bT) cT
          (.cons (Logic.car av) vcab) cv vT2c app_not_special h_app appBody_fv appBody_nolet hT2 hcc hbody2)
        (re_if_true w e (conspOf (appThen aT bT))
          (consOf (carOf (appThen aT bT)) (appOf (cdrOf (appThen aT bT)) cT)) cT
          (Logic.consp (.cons (Logic.car av) vcab)) (.cons (Logic.car av) vac)
          (conv_builtin1 w e { name := "CONSP" } (appThen aT bT) (.cons (Logic.car av) vcab)
            (Logic.consp (.cons (Logic.car av) vcab)) consp_not_special h_no_consp hT2
            (callBuiltin_consp (.cons (Logic.car av) vcab))) rfl hthen))
        -- car-cons lifted under cons-left
        (evalOpt_congr_binary_left w e { name := "CONS" }
          (carOf (appThen aT bT)) (carOf aT) (appOf (cdrOf (appThen aT bT)) cT) cons_not_special
          (re_car_cons w e (carOf aT) (appOf (cdrOf aT) bT) (Logic.car av) vcab
            h_no_car h_no_cons hcar hvcab)))
        -- cdr-cons lifted under (app · c) then cons-right
        (evalOpt_congr_binary_right w e { name := "CONS" } (carOf aT)
          (appOf (cdrOf (appThen aT bT)) cT) (appOf (appOf (cdrOf aT) bT) cT) cons_not_special
          (evalOpt_congr_binary_left w e { name := "APP" }
            (cdrOf (appThen aT bT)) (appOf (cdrOf aT) bT) cT app_not_special
            (re_cdr_cons w e (carOf aT) (appOf (cdrOf aT) bT) (Logic.car av) vcab
              h_no_cdr h_no_cons hcar hvcab)))
    -- stepN3: (app a (app b c)) ⇒ (cons (car a) (app (cdr a) (app b c)))  [unfold ; if-TRUE]
    have stepN3 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf aT (appOf bT cT)) = evalOpt f w e (appThen aT (appOf bT cT)) := by
      obtain ⟨Nr, vr, hr⟩ := h_app_total e aT (appOf bT cT)
        (by obtain ⟨N, h⟩ := hac; exact ⟨N, fun f hf => ⟨av, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hvbc; exact ⟨N, fun f hf => ⟨vbc, h f hf⟩⟩)
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym, y_sym] [av, vbc]) appBody = some vr := by
        refine ⟨max Nr Nbc + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_2 (g + 1) w e app_sym aT (appOf bT cT) av vbc x_sym y_sym appBody
              app_not_special h_app (h_ae g) (hbc' (g + 1) (by omega))]
        exact hr (g + 2) (by omega)
      -- then-branch (cons (car a) (app (cdr a) (app b c))) converges
      obtain ⟨Ncdrbc, vcdrbc, hcdrbc⟩ := h_app_total e (cdrOf aT) (appOf bT cT)
        (by obtain ⟨N, h⟩ := hcdr; exact ⟨N, fun f hf => ⟨Logic.cdr av, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hvbc; exact ⟨N, fun f hf => ⟨vbc, h f hf⟩⟩)
      have hthen : ∃ N, ∀ f ≥ N,
          evalOpt f w e (appThen aT (appOf bT cT)) = some (.cons (Logic.car av) vcdrbc) :=
        conv_builtin2 w e { name := "CONS" } (carOf aT) (appOf (cdrOf aT) (appOf bT cT))
          (Logic.car av) vcdrbc (.cons (Logic.car av) vcdrbc) cons_not_special h_no_cons hcar
          ⟨Ncdrbc, hcdrbc⟩ rfl
      exact fuel_chain_eq
        (evalOpt_unfold2_conv w e app_sym x_sym y_sym appBody aT (appOf bT cT) av vbc vr
          app_not_special h_app appBody_fv appBody_nolet hac hvbc hbody)
        (re_if_true w e (conspOf aT) (appThen aT (appOf bT cT)) (appOf bT cT) (Logic.consp av)
          (.cons (Logic.car av) vcdrbc) hconsp_t (by rw [hct]; decide) hthen)
    -- solidify: (app (cdr a) (app b c)) ⇒ (app (app (cdr a) b) c)   [IH, PURE]
    have hsolid : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf (cdrOf aT) (appOf bT cT))
        = evalOpt f w e (appOf (appOf (cdrOf aT) bT) cT) := by
      -- IH instantiated in e' = e.insert a (cdr av)
      have h_ae' : ∀ f, evalOpt (f + 1) w (e.insert a_sym (Logic.cdr av))
          (.atom (.symbol a_sym)) = some (Logic.cdr av) := fun f =>
        evalOpt_var f w _ a_sym (Logic.cdr av) (by simp)
      obtain ⟨Nih, hih⟩ := ih (e.insert a_sym (Logic.cdr av)) h_ae'
      obtain ⟨Nbr, hbr⟩ := evalOpt_substTerm_subst1 w e a_sym (cdrOf aT) (Logic.cdr av)
        app_assocFormula (by decide) hcdr
      have hsubst : substTerm [a_sym] [cdrOf aT] app_assocFormula
          = equalOf (appOf (appOf (cdrOf aT) bT) cT) (appOf (cdrOf aT) (appOf bT cT)) := rfl
      have hEQt : ∃ N, ∀ f ≥ N, evalOpt f w e
          (equalOf (appOf (appOf (cdrOf aT) bT) cT) (appOf (cdrOf aT) (appOf bT cT)))
          = some SExpr.t :=
        ⟨max Nbr Nih, fun f hf => by
          rw [← hsubst]; exact (hbr f (by omega)).trans (hih f (by omega))⟩
      -- A' = (app (app (cdr a) b) c) ⇒ vA' ; B' = (app (cdr a) (app b c)) ⇒ vB'  (totality)
      obtain ⟨NA, vA, hA⟩ := h_app_total e (appOf (cdrOf aT) bT) cT
        (by obtain ⟨N, h⟩ := hvcab; exact ⟨N, fun f hf => ⟨vcab, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hcc; exact ⟨N, fun f hf => ⟨cv, h f hf⟩⟩)
      obtain ⟨NB, vB, hB⟩ := h_app_total e (cdrOf aT) (appOf bT cT)
        (by obtain ⟨N, h⟩ := hcdr; exact ⟨N, fun f hf => ⟨Logic.cdr av, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hvbc; exact ⟨N, fun f hf => ⟨vbc, h f hf⟩⟩)
      obtain ⟨NEQ, hEQ⟩ := hEQt
      obtain ⟨NIH, hIH⟩ : ∃ N, ∀ f ≥ N,
          evalOpt f w e (appOf (appOf (cdrOf aT) bT) cT)
          = evalOpt f w e (appOf (cdrOf aT) (appOf bT cT)) := by
        refine ⟨max NA (max NB NEQ), fun f hf => ?_⟩
        have hV := eval_equal_t_implies_eq f w e
          (appOf (appOf (cdrOf aT) bT) cT) (appOf (cdrOf aT) (appOf bT cT)) vA vB
          (hA f (by omega)) (hB f (by omega)) h_no_equal (hEQ (f + 1) (by omega))
        rw [hA f (by omega), hB f (by omega), hV]
      exact ⟨NIH, fun f hf => (hIH f hf).symm⟩
    -- Assemble. SELF = (cons (car a) (app (app (cdr a) b) c)).
    -- A-side: (app (app a b) c) ⇒ (app T2 c) ⇒ SELF.
    have hAside : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf (appOf aT bT) cT)
        = evalOpt f w e (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT)) :=
      fuel_chain_eq
        (evalOpt_congr_binary_left w e { name := "APP" }
          (appOf aT bT) (appThen aT bT) cT app_not_special stepN1)
        stepN2
    -- B-side: (app a (app b c)) ⇒ (cons (car a)(app (cdr a)(app b c))) ⇒ SELF.
    have hBside : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf aT (appOf bT cT))
        = evalOpt f w e (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT)) :=
      fuel_chain_eq stepN3
        (evalOpt_congr_binary_right w e { name := "CONS" } (carOf aT)
          (appOf (cdrOf aT) (appOf bT cT)) (appOf (appOf (cdrOf aT) bT) cT) cons_not_special hsolid)
    -- equal-self on SELF
    have hself : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT))
                               (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT))) = some SExpr.t := by
      obtain ⟨NA, vA, hA⟩ := h_app_total e (appOf (cdrOf aT) bT) cT
        (by obtain ⟨N, h⟩ := hvcab; exact ⟨N, fun f hf => ⟨vcab, h f hf⟩⟩)
        (by obtain ⟨N, h⟩ := hcc; exact ⟨N, fun f hf => ⟨cv, h f hf⟩⟩)
      have hSELF : ∃ N, ∀ f ≥ N,
          evalOpt f w e (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT))
          = some (.cons (Logic.car av) vA) :=
        conv_builtin2 w e { name := "CONS" } (carOf aT) (appOf (appOf (cdrOf aT) bT) cT)
          (Logic.car av) vA (.cons (Logic.car av) vA) cons_not_special h_no_cons hcar ⟨NA, hA⟩ rfl
      obtain ⟨Ns, hs⟩ := hSELF
      refine ⟨Ns + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_equal_self g w e (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT))
        (.cons (Logic.car av) vA) (hs g (by omega)) h_no_equal
    rw [formula_decomp]
    exact fuel_chain_eq (fuel_chain_eq
      (evalOpt_congr_binary_left w e { name := "EQUAL" }
        (appOf (appOf aT bT) cT) (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT))
        (appOf aT (appOf bT cT)) equal_not_special hAside)
      (evalOpt_congr_binary_right w e { name := "EQUAL" }
        (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT)) (appOf aT (appOf bT cT))
        (consOf (carOf aT) (appOf (appOf (cdrOf aT) bT) cT)) equal_not_special hBside))
      hself

/-! ## Native-theorem bridge (append associativity → `List.append_assoc`)

Same recipe as SimpleWorld: TYPE morphism `enc : List SExpr → SExpr` + a
SIMULATION (`corr_app_enc`: evalOpt's `app` simulates `++` under `enc`). The
twist: the result is a LIST, so descending the SExpr equality to the `List`
equality needs `enc` INJECTIVITY. -/

private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })

-- Reduction-friendly `DefMap`: every concrete world lookup is `by decide`.
theorem world_has_app : world.defs[app_sym]? = some ([x_sym, y_sym], appBody) := by decide
theorem world_no_equal : world.defs[({ name := "EQUAL" } : Symbol)]? = none := by decide
theorem world_no_consp : world.defs[({ name := "CONSP" } : Symbol)]? = none := by decide
theorem world_no_cdr : world.defs[({ name := "CDR" } : Symbol)]? = none := by decide
theorem world_no_car : world.defs[({ name := "CAR" } : Symbol)]? = none := by decide
theorem world_no_cons : world.defs[({ name := "CONS" } : Symbol)]? = none := by decide

private theorem bindArgs_xy_x (vx vy : SExpr) :
    (bindArgs [x_sym, y_sym] [vx, vy]).get? x_sym = some vx := by
  show ((({} : Env).insert y_sym vy).insert x_sym vx).get? x_sym = some vx
  simp
private theorem bindArgs_xy_y (vx vy : SExpr) :
    (bindArgs [x_sym, y_sym] [vx, vy]).get? y_sym = some vy := by
  show ((({} : Env).insert y_sym vy).insert x_sym vx).get? y_sym = some vy
  simp only [Env.get?_insert]
  simp only [x_sym, y_sym, sym, beq_iff_eq]
  rw [if_neg (by decide)]; simp

private theorem conv_fix {w : World} {e : Env} {t : SExpr}
    (h : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e t = some av) :
    ∃ av, ∃ M, ∀ f ≥ M, evalOpt f w e t = some av := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨av, hav⟩ := hM M (Nat.le_refl M)
  exact ⟨av, M, fun f hf => evalOpt_ge_fuel M f w e t av hav hf⟩

/-- `app a b` converges (induction on the first argument's VALUE). Discharges
    `h_app_total`. -/
private theorem dis_app_total_val (w : World)
    (h_app : w.defs.get? app_sym = some ([x_sym, y_sym], appBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (av1 : SExpr) (e' : Env) (a b av2 : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some av1) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' b = some av2) →
    ∃ rv, ∃ N, ∀ f ≥ N, evalOpt f w e' (appOf a b) = some rv := by
  refine acl2_induction_consp (fun av1 => ∀ (e' : Env) (a b av2 : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some av1) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' b = some av2) →
    ∃ rv, ∃ N, ∀ f ≥ N, evalOpt f w e' (appOf a b) = some rv) ?base ?step
  · intro av1 hconsp e' a b av2 ha hb
    refine ⟨av2, ?_⟩
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [av1, av2]) xT = some av1 :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ x_sym av1 (bindArgs_xy_x av1 av2)⟩
    have hy_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [av1, av2]) yT = some av2 :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ y_sym av2 (bindArgs_xy_y av1 av2)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [av1, av2]) (conspOf xT) = some .nil := by
      have h := conv_builtin1 w _ { name := "CONSP" } xT av1 (Logic.consp av1)
        consp_not_special h_no_consp hx_ba (callBuiltin_consp av1)
      rwa [hconsp] at h
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [av1, av2]) appBody = some av2 := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [x_sym, y_sym] [av1, av2]) (conspOf xT)
        (consOf (carOf xT) (appOf (cdrOf xT) yT)) yT av2 hconspx_ba hy_ba
      obtain ⟨Ny, hy⟩ := hy_ba
      exact ⟨max Ni Ny, fun f hf => (hi f (by omega)).trans (hy f (by omega))⟩
    exact conv_defn_2 w e' app_sym a b av1 av2 x_sym y_sym appBody av2
      app_not_special h_app ha hb hbody
  · intro av1 hconsp ih e' a b av2 ha hb
    obtain ⟨hd, tl, rfl⟩ : ∃ hd tl, av1 = .cons hd tl := by
      match av1 with
      | .cons p q => exact ⟨p, q, rfl⟩
      | .nil => exact absurd rfl hconsp
      | .atom _ => exact absurd rfl hconsp
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) xT = some (.cons hd tl) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ x_sym _ (bindArgs_xy_x _ _)⟩
    have hy_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) yT = some av2 :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ y_sym _ (bindArgs_xy_y _ _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (conspOf xT)
        = some (Logic.consp (.cons hd tl)) :=
      conv_builtin1 w _ { name := "CONSP" } xT (.cons hd tl) (Logic.consp (.cons hd tl))
        consp_not_special h_no_consp hx_ba (callBuiltin_consp _)
    have hcarx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (carOf xT) = some hd := by
      have h := conv_builtin1 w _ { name := "CAR" } xT (.cons hd tl) (Logic.car (.cons hd tl))
        car_not_special h_no_car hx_ba (callBuiltin_car _)
      simpa [Logic.car] using h
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (cdrOf xT) = some tl := by
      have h := conv_builtin1 w _ { name := "CDR" } xT (.cons hd tl) (Logic.cdr (.cons hd tl))
        cdr_not_special h_no_cdr hx_ba (callBuiltin_cdr _)
      simpa [Logic.cdr] using h
    obtain ⟨rv', hrec⟩ := ih (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (cdrOf xT) yT av2
      hcdrx_ba hy_ba
    refine ⟨.cons hd rv', ?_⟩
    have hthen : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2])
          (consOf (carOf xT) (appOf (cdrOf xT) yT)) = some (.cons hd rv') :=
      conv_builtin2 w _ { name := "CONS" } (carOf xT) (appOf (cdrOf xT) yT)
        hd rv' (.cons hd rv') cons_not_special h_no_cons hcarx_ba hrec rfl
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) appBody
        = some (.cons hd rv') := by
      obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (conspOf xT)
        (consOf (carOf xT) (appOf (cdrOf xT) yT)) yT (Logic.consp (.cons hd tl))
        (.cons hd rv') hconspx_ba rfl hthen
      obtain ⟨Nt, ht⟩ := hthen
      exact ⟨max Ni Nt, fun f hf => (hi f (by omega)).trans (ht f (by omega))⟩
    exact conv_defn_2 w e' app_sym a b (.cons hd tl) av2 x_sym y_sym appBody
      (.cons hd rv') app_not_special h_app ha hb hbody

private theorem dis_app_total (w : World)
    (h_app : w.defs.get? app_sym = some ([x_sym, y_sym], appBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (e' : Env) (a b : SExpr)
    (ha : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' a = some av)
    (hb : ∃ M, ∀ f ≥ M, ∃ bv, evalOpt f w e' b = some bv) :
    ∃ M, ∃ rv, ∀ f ≥ M, evalOpt f w e' (appOf a b) = some rv := by
  obtain ⟨av, hav⟩ := conv_fix ha; obtain ⟨bv, hbv⟩ := conv_fix hb
  obtain ⟨rv, N, h⟩ := dis_app_total_val w h_app h_no_consp h_no_cdr h_no_car h_no_cons
    av e' a b bv hav hbv
  exact ⟨N, rv, h⟩


/-- Driver-shape totality for `app` (v-FIXED hypothesis forms, any world with
    the `app` definition and unshadowed builtins) — discharges the driver
    mirror's `total:app` hypothesis in `Imported/NativeMirrors`. -/
theorem drv_total_app (w : World)
    (h_app : w.defs.get? app_sym = some ([x_sym, y_sym], appBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (e' : Env) (a0 a1 : SExpr)
    (h0 : ∃ N v, ∀ f ≥ N, evalOpt f w e' a0 = some v)
    (h1 : ∃ N v, ∀ f ≥ N, evalOpt f w e' a1 = some v) :
    ∃ N v, ∀ f ≥ N, evalOpt f w e' (appOf a0 a1) = some v := by
  obtain ⟨N0, v0, hv0⟩ := h0; obtain ⟨N1, v1, hv1⟩ := h1
  exact dis_app_total w h_app h_no_consp h_no_cdr h_no_car h_no_cons e' a0 a1
    ⟨N0, fun f hf => ⟨v0, hv0 f hf⟩⟩ ⟨N1, fun f hf => ⟨v1, hv1 f hf⟩⟩

/-- The replayed statement for `world`, UNCONDITIONAL (my-app totality discharged). -/
theorem app_assoc_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → evalOpt f world env app_assocFormula = some SExpr.t :=
  app_assoc_generic world env world_has_app world_no_equal world_no_consp
    world_no_cdr world_no_car world_no_cons
    (dis_app_total world world_has_app world_no_consp world_no_cdr
      world_no_car world_no_cons)

-- TYPE morphism + injectivity: the shared library's (`Imported/Lifting`).
open ACL2.Lifting (enc enc_inj)

/-- SIMULATION: `app` over encoded lists computes `++` under `enc` — ONE
    instantiation of the library's name-generic `corr_append_enc`. -/
private theorem corr_app_enc (w : World)
    (h_app : w.defs.get? app_sym = some ([x_sym, y_sym], appBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a b : SExpr) (ys : List SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' b = some (enc ys)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (appOf a b) = some (enc (xs ++ ys)) :=
  ACL2.Lifting.corr_append_enc w "APP" (by decide) h_app
    h_no_consp h_no_cdr h_no_car h_no_cons

/-- The native assembly, PARAMETERIZED by the world and the mirror: any proof
    of the replayed statement over a world carrying the `app` definition (hand or
    log-derived, hand-proved or driver-replayed) yields the native theorem.
    The replayed statement is consumed at exactly ONE point — the seam the catalog
    (`Imported/NativeMirrors`) plugs the driver's mirror into. -/
theorem app_assoc_native_of_replayed (w : World)
    (h_app : w.defs.get? app_sym = some ([x_sym, y_sym], appBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hreplayed : ∀ env : Env,
      ∃ N, ∀ f, f ≥ N → ∃ v,
        evalOpt f w env app_assocFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys zs : List SExpr) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  let e : Env := ((({} : Env).insert c_sym (enc zs)).insert b_sym (enc ys)).insert a_sym (enc xs)
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some (enc xs) :=
    ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w e a_sym (enc xs) (by
        show e.get? a_sym = some (enc xs); simp [e])⟩
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some (enc ys) :=
    ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w e b_sym (enc ys) (by
        show e.get? b_sym = some (enc ys)
        simp only [e, Env.get?_insert, a_sym, b_sym, sym, beq_iff_eq]
        rw [if_neg (by decide)]; simp)⟩
  have hc : ∃ N, ∀ f ≥ N, evalOpt f w e cT = some (enc zs) :=
    ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w e c_sym (enc zs) (by
        show e.get? c_sym = some (enc zs)
        simp only [e, Env.get?_insert, a_sym, b_sym, c_sym, sym, beq_iff_eq]
        rw [if_neg (by decide), if_neg (by decide)]; simp)⟩
  obtain ⟨NL, hL⟩ := corr_app_enc w h_app h_no_consp h_no_cdr h_no_car h_no_cons (xs ++ ys) e (appOf aT bT) cT zs
    (corr_app_enc w h_app h_no_consp h_no_cdr h_no_car h_no_cons xs e aT bT ys ha hb) hc
  obtain ⟨NR, hR⟩ := corr_app_enc w h_app h_no_consp h_no_cdr h_no_car h_no_cons xs e aT (appOf bT cT) (ys ++ zs) ha
    (corr_app_enc w h_app h_no_consp h_no_cdr h_no_car h_no_cons ys e bT cT zs hb hc)
  -- the spine ender: the replayed statement's equal ⇒ t + listRep decode both sides
  exact ACL2.Lifting.native_of_replayed_equal w e ACL2.Lifting.listRep
    (appOf (appOf aT bT) cT) (appOf aT (appOf bT cT))
    ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs)) h_no_equal ⟨NL, hL⟩ ⟨NR, hR⟩ (hreplayed e)


/-- **The native theorem**, idiomatic Lean (`List.append_assoc`), proven via
    the ACL2 oracle — here instantiated with the HAND replayed statement. -/
theorem app_assoc_native (xs ys zs : List SExpr) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  app_assoc_native_of_replayed world world_has_app world_no_consp world_no_cdr
    world_no_car world_no_cons world_no_equal
    -- the HAND replayed statement pins exact t; inject into the truthiness form (G2)
    (fun env => evtrue_of_eq_t (app_assoc_uncond env)) xs ys zs

end ACL2.Worlds.AppAssoc
