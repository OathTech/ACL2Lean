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


end ACL2.Worlds.AppAssoc
