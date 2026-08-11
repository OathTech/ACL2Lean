import ACL2Lean.EvalOpt
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Count
import ACL2Lean.Imported.Lifting

open ACL2 ACL2.Replay

namespace ACL2.Worlds.Simple

def sym (name : String) : Symbol := { package := "ACL2", name := name }

-- Body uses macro-expanded form (matching ACL2's DEFUN emission):
-- (IF (CONSP X) (BINARY-+ (QUOTE 1) (MY-LEN (CDR X))) (QUOTE 0))
def my_lenBody : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons (.atom (.symbol { name := "X" })) .nil))
      (.cons (.cons (.atom (.symbol { name := "BINARY-+" }))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons (.atom (.number (.int 1))) .nil))
                (.cons (.cons (.atom (.symbol { name := "MY-LEN" }))
                        (.cons (.cons (.atom (.symbol { name := "CDR" })) (.cons (.atom (.symbol { name := "X" })) .nil)) .nil))
                  .nil)))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons (.atom (.number (.int 0))) .nil))
          .nil)))

def my_appBody : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "IF" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CONSP" })) (SExpr.cons (SExpr.atom (.symbol { name := "X" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CONS" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CAR" })) (SExpr.cons (SExpr.atom (.symbol { name := "X" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "MY-APP" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "CDR" })) (SExpr.cons (SExpr.atom (.symbol { name := "X" })) SExpr.nil)) (SExpr.cons (SExpr.atom (.symbol { name := "Y" })) SExpr.nil))) SExpr.nil))) (SExpr.cons (SExpr.atom (.symbol { name := "Y" })) SExpr.nil))))

-- ACL2's ground-zero `fix`: (defun fix (x) (if (acl2-numberp x) x 0)). Modeling it as a
-- defined function (task #24) lets the base case replay `definition:fix` schematically
-- (def-unfold + acl2-numberp recognizer + if-simplification) instead of value-matching.
-- evalOpt computes the same value either way (def-unfold vs the `fix` builtin), so this is
-- additive; the base-case rework consumes it.
def fixBody : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "ACL2-NUMBERP" })) (.cons (.atom (.symbol { name := "X" })) .nil))
      (.cons (.atom (.symbol { name := "X" }))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons (.atom (.number (.int 0))) .nil)) .nil)))

def world : World where
  defs := ({} : DefMap)
    |>.insert (sym "MY-LEN") ([sym "X"], my_lenBody)
    |>.insert (sym "MY-APP") ([sym "X", sym "Y"], my_appBody)
    |>.insert (sym "FIX") ([sym "X"], fixBody)

private def x_sym : Symbol := sym "X"
private def y_sym : Symbol := sym "Y"
private def my_len_sym : Symbol := sym "MY-LEN"
private def my_app_sym : Symbol := sym "MY-APP"
private def fix_sym : Symbol := sym "FIX"

/-! ## Body-environment lookups (the env after definition expansion) -/

private theorem bindArgs_xy_x (vx vy : SExpr) :
    (bindArgs [x_sym, y_sym] [vx, vy]).get? x_sym = some vx := by
  show ((({} : Env).insert y_sym vy).insert x_sym vx).get? x_sym = some vx
  simp

private theorem bindArgs_xy_y (vx vy : SExpr) :
    (bindArgs [x_sym, y_sym] [vx, vy]).get? y_sym = some vy := by
  show ((({} : Env).insert y_sym vy).insert x_sym vx).get? y_sym = some vy
  simp only [Env.get?_insert, x_sym, y_sym, sym, beq_iff_eq]
  rw [if_neg (by decide)]; simp

private theorem bindArgs_x_x (vx : SExpr) :
    (bindArgs [x_sym] [vx]).get? x_sym = some vx := by
  show (({} : Env).insert x_sym vx).get? x_sym = some vx
  simp

-- Formula uses macro-expanded form:
-- (EQUAL (MY-LEN (MY-APP X Y)) (BINARY-+ (MY-LEN X) (MY-LEN Y)))
def my_len_my_appFormula : SExpr :=
  .cons (.atom (.symbol { name := "EQUAL" }))
    (.cons (.cons (.atom (.symbol { name := "MY-LEN" }))
            (.cons (.cons (.atom (.symbol { name := "MY-APP" }))
                    (.cons (.atom (.symbol { name := "X" })) (.cons (.atom (.symbol { name := "Y" })) .nil)))
              .nil))
      (.cons (.cons (.atom (.symbol { name := "BINARY-+" }))
              (.cons (.cons (.atom (.symbol { name := "MY-LEN" }))
                      (.cons (.atom (.symbol { name := "X" })) .nil))
                (.cons (.cons (.atom (.symbol { name := "MY-LEN" }))
                        (.cons (.atom (.symbol { name := "Y" })) .nil))
                  .nil)))
        .nil))

/-! ## Term decomposition (so the formula and its subterms line up with the
    arity-specific congruence lemmas, by `rfl`). -/

private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def lenOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "MY-LEN" })) (.cons t .nil)
private def appOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "MY-APP" })) (.cons a (.cons b .nil))
private def plusOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons b .nil))
private def equalOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil))
private def fixOf (z : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "FIX" })) (.cons z .nil)
private def q0 : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons (.atom (.number (.int 0))) .nil)
private def q1 : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons (.atom (.number (.int 1))) .nil)
private def carOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CAR" })) (.cons t .nil)
private def cdrOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CDR" })) (.cons t .nil)
private def consOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))
private def conspOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CONSP" })) (.cons t .nil)

/-- The replayed-statement formula, decomposed. By `rfl`. -/
private theorem formula_decomp :
    my_len_my_appFormula = equalOf (lenOf (appOf xT yT)) (plusOf (lenOf xT) (lenOf yT)) := rfl

/-! ## Proof rules: isNamed facts (by decide) -/

private theorem my_app_not_special :
    my_app_sym.isNamed "QUOTE" = false ∧ my_app_sym.isNamed "IF" = false ∧
    my_app_sym.isNamed "LET" = false ∧ my_app_sym.isNamed "LET*" = false := by decide

private theorem my_len_not_special :
    my_len_sym.isNamed "QUOTE" = false ∧ my_len_sym.isNamed "IF" = false ∧
    my_len_sym.isNamed "LET" = false ∧ my_len_sym.isNamed "LET*" = false := by decide

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

private theorem plus_not_special :
    ({ name := "BINARY-+" } : Symbol).isNamed "QUOTE" = false ∧
    ({ name := "BINARY-+" } : Symbol).isNamed "IF" = false ∧
    ({ name := "BINARY-+" } : Symbol).isNamed "LET" = false ∧
    ({ name := "BINARY-+" } : Symbol).isNamed "LET*" = false := by decide

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

/-! ## Body structure facts (LET-free; free vars ⊆ formals) for the unfold transfer -/

private theorem my_appBody_nolet : WellScoped my_appBody = true := by decide
private theorem my_lenBody_nolet : WellScoped my_lenBody = true := by decide
private theorem my_appBody_fv : ∀ s ∈ freeVars my_appBody, s = x_sym ∨ s = y_sym := by decide
private theorem my_lenBody_fv : ∀ s ∈ freeVars my_lenBody, s = x_sym := by decide

private theorem fix_not_special :
    fix_sym.isNamed "QUOTE" = false ∧ fix_sym.isNamed "IF" = false ∧
    fix_sym.isNamed "LET" = false ∧ fix_sym.isNamed "LET*" = false := by decide
private theorem acl2numberp_not_special :
    ({ name := "ACL2-NUMBERP" } : Symbol).isNamed "QUOTE" = false ∧
    ({ name := "ACL2-NUMBERP" } : Symbol).isNamed "IF" = false ∧
    ({ name := "ACL2-NUMBERP" } : Symbol).isNamed "LET" = false ∧
    ({ name := "ACL2-NUMBERP" } : Symbol).isNamed "LET*" = false := by decide
private theorem fixBody_nolet : WellScoped fixBody = true := by decide
private theorem fixBody_fv : ∀ s ∈ freeVars fixBody, s ∈ [x_sym] := by decide
/-- `substTerm [x] [z] fixBody = (if (acl2-numberp z) z '0)` — the fix body with `x:=z`. -/
private theorem fixBody_subst (z : SExpr) :
    substTerm [x_sym] [z] fixBody
      = .cons (.atom (.symbol { name := "IF" }))
          (.cons (.cons (.atom (.symbol { name := "ACL2-NUMBERP" })) (.cons z .nil))
            (.cons z (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                              (.cons (.atom (.number (.int 0))) .nil)) .nil))) := rfl

/-! ## The concrete instantiation (definition verification branch) -/

/-- Prove the definition hypotheses for the concrete world.
    This is the "verify definitions" branch of the proof tree —
    it establishes that the HashMap contains what we expect. -/
-- Definition verification branch: prove HashMap lookup facts.
-- Pattern: rw [getElem?_insert] peels off one insert, simp resolves key comparison.

-- Definition verification: prove HashMap lookup facts.
-- Pattern: unfold world, rw [getElem?_insert], simp to resolve key comparisons.

-- With the reduction-friendly `DefMap`, every concrete world lookup is `by decide`
-- (the lookup REDUCES) — no `unfold`/`getElem?_insert`/`simp` needed. This is exactly
-- the property that lets the driver derive these facts on the fly (P3).
theorem world_has_my_app :
    world.defs[my_app_sym]? = some ([x_sym, y_sym], my_appBody) := by decide

theorem world_has_my_len :
    world.defs[my_len_sym]? = some ([x_sym], my_lenBody) := by decide

theorem world_no_equal :
    world.defs[({ name := "EQUAL" } : Symbol)]? = none := by decide

theorem world_no_consp :
    world.defs[({ name := "CONSP" } : Symbol)]? = none := by decide

theorem world_no_plus :
    world.defs[({ name := "BINARY-+" } : Symbol)]? = none := by decide

theorem world_no_cdr :
    world.defs[({ name := "CDR" } : Symbol)]? = none := by decide

theorem world_no_car :
    world.defs[({ name := "CAR" } : Symbol)]? = none := by decide

theorem world_no_cons :
    world.defs[({ name := "CONS" } : Symbol)]? = none := by decide
theorem world_no_acl2numberp :
    world.defs[({ name := "ACL2-NUMBERP" } : Symbol)]? = none := by decide
theorem world_has_fix :
    world.defs[fix_sym]? = some ([x_sym], fixBody) := by decide

/-! ## Native-theorem bridge

We lift the ACL2 replayed statement to an IDIOMATIC Lean theorem (the MIRROR) about `List`:
`(xs ++ ys).length = xs.length + ys.length`. The recipe (per
`docs/comms/2026-03-22_acl2-lean-bridge.md`): a TYPE morphism `enc : List SExpr
→ SExpr` plus a SIMULATION over the function structure (correspondence lemmas:
`evalOpt`'s `my-app`/`my-len` simulate `++`/`length` under `enc`). This lifts the
ACL2 theorem without redoing the property proof.

The hand-replay chain and its Lean-side dischargers that used to sit here
(`my_len_my_app_generic`/`my_len_my_app`/`my_len_my_app_uncond`/
`my_len_my_app_native`, the `dis_*` value dischargers, the `drv_total_*`
totality dischargers) were PURGED under the thin-Lean ruling
(2026-08-11): the content they established is content ACL2 derives, and
the driver-based natives in `Imported/Mirrors/Basics` carry it now. -/

/-- Convergence to SOME value (value possibly per-fuel) ⇒ to a FIXED value. -/
private theorem conv_fix {w : World} {e : Env} {t : SExpr}
    (h : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e t = some av) :
    ∃ av, ∃ M, ∀ f ≥ M, evalOpt f w e t = some av := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨av, hav⟩ := hM M (Nat.le_refl M)
  exact ⟨av, M, fun f hf => evalOpt_ge_fuel M f w e t av hav hf⟩

/-! ### Driver-form dischargers (consumed by `Imported/NativeMirrors`)

The DRIVER's conditional replayed statement states its hypotheses in v-FIXED form
(`∃ N v, ∀ f ≥ N, … = some v`) and its type-prescription hypothesis with the
function-application convergence as antecedent. These restate the hand
dischargers above in exactly those shapes (over `world`; the catalog transfers
them to the log-derived world by `evalOpt_defs_ext`). -/

/-- `fix`'s body converges in `bindArgs` for an ARBITRARY argument value
    (`acl2-numberp` decides the branch; both branches converge). -/
private theorem fixBody_conv (w : World)
    (h_no_acl2numberp : w.defs.get? ({ name := "ACL2-NUMBERP" } : Symbol) = none)
    (av : SExpr) :
    ∃ bv, ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [x_sym] [av]) fixBody = some bv := by
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [x_sym] [av]) xT = some av :=
    ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w _ x_sym _ (bindArgs_x_x _)⟩
  have hcond : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [x_sym] [av])
      (.cons (.atom (.symbol { name := "ACL2-NUMBERP" })) (.cons xT .nil))
      = some (Logic.acl2Numberp av) :=
    conv_builtin1 w _ { name := "ACL2-NUMBERP" } xT av (Logic.acl2Numberp av)
      acl2numberp_not_special h_no_acl2numberp hx (callBuiltin_acl2_numberp av)
  by_cases hb : Logic.toBool (Logic.acl2Numberp av) = true
  · -- truthy test: the then-branch is `x` itself
    exact ⟨av, conv_if_true w _ _ xT q0 (Logic.acl2Numberp av) av hcond hb hx⟩
  · -- nil test: the else-branch is `'0`
    have hnil : Logic.acl2Numberp av = SExpr.nil := by
      revert hb; generalize Logic.acl2Numberp av = c
      intro hb; cases c <;> simp_all
    obtain ⟨Nc, hc⟩ := hcond
    refine ⟨.atom (.number (.int 0)), Nc + 2, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show evalOpt (g + 1) w (bindArgs [x_sym] [av])
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons (.cons (.atom (.symbol { name := "ACL2-NUMBERP" })) (.cons xT .nil))
          (.cons xT (.cons q0 .nil)))) = some (.atom (.number (.int 0)))
    rw [evalOpt_if_false g w _ _ xT q0 (by rw [hc g (by omega), hnil])]
    obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
    exact evalOpt_quote g2 w _ _

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes the
    driver-shape type prescription for `my-len` (any value `(my-len a0)`
    converges to satisfies the emitted TP corollary) Lean-side — content
    ACL2 derives. Statement kept as the named premise; proof retired to
    `sorry`. UNLOCK: TP-replay discharge. -/
theorem drv_tp_mylen (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (lenOf a0) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
        Logic.not (Logic.lt v (.atom (.number (.int 0))))
      else SExpr.nil) = SExpr.t := by
  sorry

/-! ### The type morphism + simulation -/

-- The TYPE morphism: the shared library's (`Imported/Lifting`).
open ACL2.Lifting (enc)

/-- SIMULATION: `my-app` over encoded lists computes `++` under `enc` — ONE
    instantiation of the library's name-generic `corr_append_enc`. -/
private theorem corr_app_enc (w : World)
    (h_myapp : w.defs.get? my_app_sym = some ([x_sym, y_sym], my_appBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a b : SExpr) (ys : List SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' b = some (enc ys)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (appOf a b) = some (enc (xs ++ ys)) :=
  ACL2.Lifting.corr_append_enc w "MY-APP" (by decide) h_myapp
    h_no_consp h_no_cdr h_no_car h_no_cons

/-- SIMULATION: `my-len` over encoded lists computes `List.length` under
    `enc` — ONE instantiation of the library's name-generic `corr_len_enc`. -/
private theorem corr_len_enc (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (lenOf a)
      = some (.atom (.number (.int xs.length))) :=
  ACL2.Lifting.corr_len_enc w "MY-LEN" (by decide) h_mylen
    h_no_consp h_no_plus h_no_cdr

/-- The native assembly, PARAMETERIZED by the mirror: any proof of the mirror
    statement over `w` (hand-built or driver-replayed) yields the native
    theorem. The replayed statement is consumed at exactly ONE point — this is the seam the
    catalog (`Imported/NativeMirrors`) plugs the driver's mirror into. -/
theorem my_len_my_app_native_of_replayed (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_myapp : w.defs.get? my_app_sym = some ([x_sym, y_sym], my_appBody))
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (hreplayed : ∀ env : Env,
      ∃ N, ∀ f, f ≥ N → ∃ v,
        evalOpt f w env my_len_my_appFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys : List SExpr) :
    (xs ++ ys).length = xs.length + ys.length := by
  -- env binding x ↦ enc xs, y ↦ enc ys
  let e : Env := (({} : Env).insert y_sym (enc ys)).insert x_sym (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w e x_sym (enc xs) (by
        show e.get? x_sym = some (enc xs); simp [e])⟩
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w e y_sym (enc ys) (by
        show e.get? y_sym = some (enc ys)
        simp only [e, Env.get?_insert, x_sym, y_sym, sym, beq_iff_eq]
        rw [if_neg (by decide)]; simp)⟩
  -- LHS value: my-len (my-app x y) ⇒ int ↑(xs ++ ys).length   (simulation)
  obtain ⟨NL, hL⟩ := corr_len_enc w h_mylen h_no_consp h_no_plus h_no_cdr (xs ++ ys) e (appOf xT yT) (corr_app_enc w h_myapp h_no_consp h_no_cdr h_no_car h_no_cons xs e xT yT ys hx hy)
  -- RHS value: (+ (my-len x) (my-len y)) ⇒ int (↑xs.length + ↑ys.length)
  obtain ⟨NLx, hLx⟩ := corr_len_enc w h_mylen h_no_consp h_no_plus h_no_cdr xs e xT hx
  obtain ⟨NLy, hLy⟩ := corr_len_enc w h_mylen h_no_consp h_no_plus h_no_cdr ys e yT hy
  obtain ⟨NR, hR⟩ : ∃ N, ∀ f ≥ N, evalOpt f w e (plusOf (lenOf xT) (lenOf yT))
      = some (.atom (.number (.int ((xs.length : Int) + (ys.length : Int))))) := by
    have h := conv_builtin2 w e { name := "BINARY-+" } (lenOf xT) (lenOf yT)
      (.atom (.number (.int (xs.length : Int)))) (.atom (.number (.int (ys.length : Int))))
      (Logic.plus (.atom (.number (.int (xs.length : Int)))) (.atom (.number (.int (ys.length : Int)))))
      plus_not_special h_no_plus ⟨NLx, hLx⟩ ⟨NLy, hLy⟩ (callBuiltin_plus _ _)
    rwa [logic_plus_int] at h
  -- replayed statement: formula ⇒ t ; eval_equal_t splits the equality, the two values coincide
  -- the spine ender: the replayed statement's equal ⇒ t + intRep decode, then the Nat cast
  have hint : ((xs ++ ys).length : Int) = (xs.length : Int) + (ys.length : Int) :=
    ACL2.Lifting.native_of_replayed_equal w e ACL2.Lifting.intRep
      (lenOf (appOf xT yT)) (plusOf (lenOf xT) (lenOf yT))
      ((xs ++ ys).length : Int) ((xs.length : Int) + (ys.length : Int))
      h_no_equal ⟨NL, hL⟩ ⟨NR, hR⟩ (hreplayed e)
  omega

end ACL2.Worlds.Simple
