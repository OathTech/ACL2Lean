import ACL2Lean.Imported.Sorting.Iso

/-! # The sorting books — LAYER 2 (cont.): THE ADMISSION SUBSTRATE

The same two-stage correspondence as `Iso.lean`, for the functions
that exist only because ACL2's ADMISSION machinery uses them: the
ordinal kit (`O-FINP`, `O-FIRST-EXPT`, `O-FIRST-COEFF`, `O-RST`, `O<`)
and the size kit (`INTEGER-ABS`, `LENGTH`, `ACL2-COUNT`). Quicksort's
termination argument is stated in exactly this vocabulary, so replaying
its admission needs these correspondences.

A separate module only because of the 1500-line module norm; it is
layer 2 in every other respect.
-/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm ACL2.ExecGen

namespace ACL2.Worlds.Sorting

private theorem o_finp_ns :
    (o_finp_sym.isNamed "QUOTE" = false ∧ o_finp_sym.isNamed "IF" = false ∧
     o_finp_sym.isNamed "LET" = false ∧
     o_finp_sym.isNamed "LET*" = false) := by decide

private theorem o_fe_ns :
    (o_fe_sym.isNamed "QUOTE" = false ∧ o_fe_sym.isNamed "IF" = false ∧
     o_fe_sym.isNamed "LET" = false ∧
     o_fe_sym.isNamed "LET*" = false) := by decide

private theorem o_fc_ns :
    (o_fc_sym.isNamed "QUOTE" = false ∧ o_fc_sym.isNamed "IF" = false ∧
     o_fc_sym.isNamed "LET" = false ∧
     o_fc_sym.isNamed "LET*" = false) := by decide

private theorem o_rst_ns :
    (o_rst_sym.isNamed "QUOTE" = false ∧ o_rst_sym.isNamed "IF" = false ∧
     o_rst_sym.isNamed "LET" = false ∧
     o_rst_sym.isNamed "LET*" = false) := by decide

private theorem o_lt_ns :
    (o_lt_sym.isNamed "QUOTE" = false ∧ o_lt_sym.isNamed "IF" = false ∧
     o_lt_sym.isNamed "LET" = false ∧
     o_lt_sym.isNamed "LET*" = false) := by decide

def oFinpExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then SExpr.nil else SExpr.t

def oFirstExptExec (x : SExpr) : SExpr :=
  if Logic.toBool (oFinpExec x) = true then .atom (.number (.int 0))
  else Logic.car (Logic.car x)

def oFirstCoeffExec (x : SExpr) : SExpr :=
  if Logic.toBool (oFinpExec x) = true then x
  else Logic.cdr (Logic.car x)

/-- `oFinpExec x` is false exactly on conses. -/
private theorem oFinpExec_false_consp {x : SExpr}
    (h : Logic.toBool (oFinpExec x) = false) :
    Logic.toBool (Logic.consp x) = true := by
  unfold oFinpExec at h
  by_cases hc : Logic.toBool (Logic.consp x) = true
  · exact hc
  · rw [if_neg hc] at h; exact absurd h (by decide)

private theorem oFirstExptExec_consCount_lt {x : SExpr}
    (h : Logic.toBool (oFinpExec x) = false) :
    (oFirstExptExec x).consCount < x.consCount := by
  rw [oFirstExptExec, if_neg (by rw [h]; decide)]
  exact lt_of_le_of_lt (consCount_car_le _)
    (consCount_car_lt_of_consp (oFinpExec_false_consp h))

def oLtExec (x y : SExpr) : SExpr :=
  if _h1 : Logic.toBool (oFinpExec x) = true then
    (if Logic.toBool (oFinpExec y) = true then Logic.lt x y else SExpr.t)
  else if Logic.toBool (oFinpExec y) = true then SExpr.nil
  else if Logic.toBool (Logic.equal (oFirstExptExec x) (oFirstExptExec y))
      = true then
    (if Logic.toBool (Logic.equal (oFirstCoeffExec x) (oFirstCoeffExec y))
        = true then
      oLtExec (Logic.cdr x) (Logic.cdr y)
     else Logic.lt (oFirstCoeffExec x) (oFirstCoeffExec y))
  else oLtExec (oFirstExptExec x) (oFirstExptExec y)
termination_by x.consCount
decreasing_by
  · exact consCount_cdr_lt_of_consp (oFinpExec_false_consp
      (Bool.not_eq_true _ ▸ eq_false_of_ne_true _h1))
  · exact oFirstExptExec_consCount_lt
      (Bool.not_eq_true _ ▸ eq_false_of_ne_true _h1)

/-- Stage 1 for the small ordinal fns (non-recursive walks). -/
theorem o_finp_exec_corr (w : World)
    (h_fn : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (oFinpT x) (oFinpExec xv) := by
  intro env x xv hx
  refine conv_defn_1 w env o_finp_sym x xv xS oFinpBody _
    o_finp_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
    (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT) qNil qT'
    (Logic.consp xv) SExpr.nil SExpr.t hconsp
    (fun _ => re_val_quote w _ SExpr.nil)
    (fun _ => re_val_quote w _ SExpr.t)
  rw [oFinpExec]
  exact h

theorem o_fe_exec_corr (w : World)
    (h_fn : w.defs.get? o_fe_sym = some ([xS], oFirstExptBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (oFirstExptT x) (oFirstExptExec xv)
    := by
  intro env x xv hx
  refine conv_defn_1 w env o_fe_sym x xv xS oFirstExptBody _
    o_fe_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hfinp := o_finp_exec_corr w h_finp h_no_consp _ xT xv hxv
  have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
    (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
  have hcarcar := conv_builtin1 w _ { name := "CAR" } (carT xT)
    (Logic.car xv) (Logic.car (Logic.car xv)) (by decide) h_no_car hcar
    (callBuiltin_car _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (oFinpT xT) q0
    (carT (carT xT)) (oFinpExec xv) (.atom (.number (.int 0)))
    (Logic.car (Logic.car xv)) hfinp
    (fun _ => re_val_quote w _ (.atom (.number (.int 0))))
    (fun _ => hcarcar)
  rw [oFirstExptExec]
  exact h

theorem o_fc_exec_corr (w : World)
    (h_fn : w.defs.get? o_fc_sym = some ([xS], oFirstCoeffBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv →
      ConvTo w env (oFirstCoeffT x) (oFirstCoeffExec xv) := by
  intro env x xv hx
  refine conv_defn_1 w env o_fc_sym x xv xS oFirstCoeffBody _
    o_fc_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hfinp := o_finp_exec_corr w h_finp h_no_consp _ xT xv hxv
  have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
    (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
  have hcdrcar := conv_builtin1 w _ { name := "CDR" } (carT xT)
    (Logic.car xv) (Logic.cdr (Logic.car xv)) (by decide) h_no_cdr hcar
    (callBuiltin_cdr _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (oFinpT xT) xT
    (cdrT (carT xT)) (oFinpExec xv) xv (Logic.cdr (Logic.car xv)) hfinp
    (fun _ => hxv)
    (fun _ => hcdrcar)
  rw [oFirstCoeffExec]
  exact h

private theorem callBuiltin_lt (a b : SExpr) :
    callBuiltin "<" [a, b] = some (Logic.lt a b) := rfl

/-- Stage 1: an `O<` call converges to `oLtExec` (strong induction on
    the FIRST argument's count — both recursion sites descend into
    `x`). -/
theorem o_lt_exec_corr (w : World)
    (h_lt : w.defs.get? o_lt_sym = some ([xS, yS], oLtBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_fe : w.defs.get? o_fe_sym = some ([xS], oFirstExptBody))
    (h_fc : w.defs.get? o_fc_sym = some ([xS], oFirstCoeffBody))
    (h_rst : w.defs.get? o_rst_sym = some ([xS], oRstBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none) :
    ∀ (env : Env) (a b av bv : SExpr),
      ConvTo w env a av → ConvTo w env b bv →
      ConvTo w env (oLtT a b) (oLtExec av bv) := by
  have hbody : ∀ (n : Nat) (xv yv : SExpr), xv.consCount = n →
      ConvTo w (bindArgs [xS, yS] [xv, yv]) oLtBody (oLtExec xv yv) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro xv yv hn
      have hxv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
        { name := "X" } xv (bindArgs_xy_x' xv yv)
      have hyv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
        { name := "Y" } yv (bindArgs_xy_y' xv yv)
      have hfx := o_finp_exec_corr w h_finp h_no_consp _ xT xv hxv
      have hfy := o_finp_exec_corr w h_finp h_no_consp _ yT yv hyv
      have hfex := o_fe_exec_corr w h_fe h_finp h_no_consp h_no_car _
        xT xv hxv
      have hfey := o_fe_exec_corr w h_fe h_finp h_no_consp h_no_car _
        yT yv hyv
      have hfcx := o_fc_exec_corr w h_fc h_finp h_no_consp h_no_car
        h_no_cdr _ xT xv hxv
      have hfcy := o_fc_exec_corr w h_fc h_finp h_no_consp h_no_car
        h_no_cdr _ yT yv hyv
      have heqFe := conv_builtin2 w _ { name := "EQUAL" } (oFirstExptT xT)
        (oFirstExptT yT) (oFirstExptExec xv) (oFirstExptExec yv) _
        (by decide) h_no_equal hfex hfey (callBuiltin_equal _ _)
      have heqFc := conv_builtin2 w _ { name := "EQUAL" } (oFirstCoeffT xT)
        (oFirstCoeffT yT) (oFirstCoeffExec xv) (oFirstCoeffExec yv) _
        (by decide) h_no_equal hfcx hfcy (callBuiltin_equal _ _)
      have hltxy := conv_builtin2 w _ { name := "<" } xT yT xv yv _
        (by decide) h_no_ltb hxv hyv (callBuiltin_lt _ _)
      have hltFc := conv_builtin2 w _ { name := "<" } (oFirstCoeffT xT)
        (oFirstCoeffT yT) (oFirstCoeffExec xv) (oFirstCoeffExec yv) _
        (by decide) h_no_ltb hfcx hfcy (callBuiltin_lt _ _)
      -- (o-rst x/y) values
      have hcdrx := conv_builtin1 w _ { name := "CDR" } xT xv
        (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
      have hcdry := conv_builtin1 w _ { name := "CDR" } yT yv
        (Logic.cdr yv) (by decide) h_no_cdr hyv (callBuiltin_cdr _)
      have hrstx : ConvTo w (bindArgs [xS, yS] [xv, yv]) (oRstT xT)
          (Logic.cdr xv) := by
        refine conv_defn_1 w _ o_rst_sym xT xv xS oRstBody _
          o_rst_ns h_rst hxv ?_
        have hxv' := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" }
          xv (bindArgs_single_get_self xS xv)
        exact conv_builtin1 w _ { name := "CDR" } xT xv (Logic.cdr xv)
          (by decide) h_no_cdr hxv' (callBuiltin_cdr _)
      have hrsty : ConvTo w (bindArgs [xS, yS] [xv, yv]) (oRstT yT)
          (Logic.cdr yv) := by
        refine conv_defn_1 w _ o_rst_sym yT yv xS oRstBody _
          o_rst_ns h_rst hyv ?_
        have hyv' := re_val_var_get w (bindArgs [xS] [yv]) { name := "X" }
          yv (bindArgs_single_get_self xS yv)
        exact conv_builtin1 w _ { name := "CDR" } xT yv (Logic.cdr yv)
          (by decide) h_no_cdr hyv' (callBuiltin_cdr _)
      have houter := conv_if_lift w (bindArgs [xS, yS] [xv, yv])
        (oFinpT xT)
        (ifT (oFinpT yT) (ltT xT yT) qT')
        (ifT (oFinpT yT) qNil
          (ifT (equalT (oFirstExptT xT) (oFirstExptT yT))
            (ifT (equalT (oFirstCoeffT xT) (oFirstCoeffT yT))
              (oLtT (oRstT xT) (oRstT yT))
              (ltT (oFirstCoeffT xT) (oFirstCoeffT yT)))
            (oLtT (oFirstExptT xT) (oFirstExptT yT))))
        (oFinpExec xv)
        (if Logic.toBool (oFinpExec yv) = true then Logic.lt xv yv
         else SExpr.t)
        (if Logic.toBool (oFinpExec yv) = true then SExpr.nil
         else if Logic.toBool (Logic.equal (oFirstExptExec xv)
             (oFirstExptExec yv)) = true then
           (if Logic.toBool (Logic.equal (oFirstCoeffExec xv)
               (oFirstCoeffExec yv)) = true then
             oLtExec (Logic.cdr xv) (Logic.cdr yv)
            else Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
         else oLtExec (oFirstExptExec xv) (oFirstExptExec yv))
        hfx
        (fun _ =>
          conv_if_lift w _ (oFinpT yT) (ltT xT yT) qT' (oFinpExec yv)
            (Logic.lt xv yv) SExpr.t hfy
            (fun _ => hltxy)
            (fun _ => re_val_quote w _ SExpr.t))
        (fun hb1 =>
          conv_if_lift w _ (oFinpT yT) qNil _ (oFinpExec yv) SExpr.nil
            (if Logic.toBool (Logic.equal (oFirstExptExec xv)
                (oFirstExptExec yv)) = true then
              (if Logic.toBool (Logic.equal (oFirstCoeffExec xv)
                  (oFirstCoeffExec yv)) = true then
                oLtExec (Logic.cdr xv) (Logic.cdr yv)
               else Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
             else oLtExec (oFirstExptExec xv) (oFirstExptExec yv))
            hfy
            (fun _ => re_val_quote w _ SExpr.nil)
            (fun _ =>
              conv_if_lift w _
                (equalT (oFirstExptT xT) (oFirstExptT yT)) _
                (oLtT (oFirstExptT xT) (oFirstExptT yT))
                (Logic.equal (oFirstExptExec xv) (oFirstExptExec yv))
                (if Logic.toBool (Logic.equal (oFirstCoeffExec xv)
                    (oFirstCoeffExec yv)) = true then
                  oLtExec (Logic.cdr xv) (Logic.cdr yv)
                 else Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
                (oLtExec (oFirstExptExec xv) (oFirstExptExec yv))
                heqFe
                (fun _ =>
                  conv_if_lift w _
                    (equalT (oFirstCoeffT xT) (oFirstCoeffT yT))
                    (oLtT (oRstT xT) (oRstT yT))
                    (ltT (oFirstCoeffT xT) (oFirstCoeffT yT))
                    (Logic.equal (oFirstCoeffExec xv) (oFirstCoeffExec yv))
                    (oLtExec (Logic.cdr xv) (Logic.cdr yv))
                    (Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
                    heqFc
                    (fun _ =>
                      conv_defn_2 w _ o_lt_sym (oRstT xT) (oRstT yT)
                        (Logic.cdr xv) (Logic.cdr yv) xS yS oLtBody _
                        o_lt_ns h_lt hrstx hrsty
                        (ih (Logic.cdr xv).consCount
                          (hn ▸ consCount_cdr_lt_of_consp
                            (oFinpExec_false_consp hb1))
                          (Logic.cdr xv) (Logic.cdr yv) rfl))
                    (fun _ => hltFc))
                (fun _ =>
                  conv_defn_2 w _ o_lt_sym (oFirstExptT xT)
                    (oFirstExptT yT) (oFirstExptExec xv)
                    (oFirstExptExec yv) xS yS oLtBody _
                    o_lt_ns h_lt hfex hfey
                    (ih (oFirstExptExec xv).consCount
                      (hn ▸ oFirstExptExec_consCount_lt hb1)
                      (oFirstExptExec xv) (oFirstExptExec yv) rfl))))
      rw [oLtExec.eq_def]
      simp only [dite_eq_ite]
      exact houter
  intro env a b av bv ha hb
  exact conv_defn_2 w env o_lt_sym a b av bv xS yS oLtBody _
    o_lt_ns h_lt ha hb (hbody av.consCount av bv rfl)

private theorem integer_abs_ns :
    (integer_abs_sym.isNamed "QUOTE" = false ∧
     integer_abs_sym.isNamed "IF" = false ∧
     integer_abs_sym.isNamed "LET" = false ∧
     integer_abs_sym.isNamed "LET*" = false) := by decide

private theorem length_ns :
    (length_sym.isNamed "QUOTE" = false ∧
     length_sym.isNamed "IF" = false ∧
     length_sym.isNamed "LET" = false ∧
     length_sym.isNamed "LET*" = false) := by decide

private theorem acl2_count_ns :
    (acl2_count_sym.isNamed "QUOTE" = false ∧
     acl2_count_sym.isNamed "IF" = false ∧
     acl2_count_sym.isNamed "LET" = false ∧
     acl2_count_sym.isNamed "LET*" = false) := by decide

private theorem callBuiltin_integerp (a : SExpr) :
    callBuiltin "INTEGERP" [a] = some (Logic.integerp a) := rfl

private theorem callBuiltin_neg (a : SExpr) :
    callBuiltin "UNARY--" [a] = some (Logic.neg a) := rfl

private theorem callBuiltin_stringp (a : SExpr) :
    callBuiltin "STRINGP" [a] = some (Logic.stringp a) := rfl

private theorem callBuiltin_len (a : SExpr) :
    callBuiltin "LEN" [a] = some (Logic.len a) := rfl

private theorem callBuiltin_coerce (a b : SExpr) :
    callBuiltin "COERCE" [a, b] = some (Logic.coerce a b) := rfl

private theorem callBuiltin_rationalp (a : SExpr) :
    callBuiltin "RATIONALP" [a]
      = some (match a with
              | .atom (.number _) => SExpr.t
              | _ => SExpr.nil) := rfl

private theorem callBuiltin_numerator (a : SExpr) :
    callBuiltin "NUMERATOR" [a] = some (Logic.numerator a) := rfl

private theorem callBuiltin_denominator (a : SExpr) :
    callBuiltin "DENOMINATOR" [a] = some (Logic.denominator a) := rfl

private theorem callBuiltin_complexRationalp (a : SExpr) :
    callBuiltin "COMPLEX-RATIONALP" [a]
      = some (Logic.complexRationalp a) := rfl

private theorem callBuiltin_realpart (a : SExpr) :
    callBuiltin "REALPART" [a] = some (Logic.realpart a) := rfl

private theorem callBuiltin_imagpart (a : SExpr) :
    callBuiltin "IMAGPART" [a] = some (Logic.imagpart a) := rfl

/-- `rationalp`'s value as the callBuiltin match (the Logic twin). -/
private abbrev rationalpV (a : SExpr) : SExpr :=
  match a with
  | .atom (.number _) => SExpr.t
  | _ => SExpr.nil

def integerAbsExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.integerp x) = true then
    (if Logic.toBool (Logic.lt x (.atom (.number (.int 0)))) = true then
      Logic.neg x
     else x)
  else .atom (.number (.int 0))

def lengthExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.stringp x) = true then
    Logic.len (Logic.coerce x (symV "LIST"))
  else Logic.len x

def acl2CountExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    Logic.plus int1 (Logic.plus (acl2CountExec (Logic.car x))
      (acl2CountExec (Logic.cdr x)))
  else if Logic.toBool (rationalpV x) = true then
    (if Logic.toBool (Logic.integerp x) = true then integerAbsExec x
     else Logic.plus (integerAbsExec (Logic.numerator x))
       (Logic.denominator x))
  else if _hc : Logic.toBool (Logic.complexRationalp x) = true then
    Logic.plus int1 (Logic.plus (acl2CountExec (Logic.realpart x))
      (acl2CountExec (Logic.imagpart x)))
  else if Logic.toBool (Logic.stringp x) = true then lengthExec x
  else .atom (.number (.int 0))
termination_by x.consCount
decreasing_by
  · exact consCount_car_lt_of_consp (by assumption)
  · exact consCount_cdr_lt_of_consp (by assumption)
  · exact absurd _hc (by simp [Logic.complexRationalp, Logic.toBool])
  · exact absurd _hc (by simp [Logic.complexRationalp, Logic.toBool])

/-- Stage 1 for `integer-abs` (non-recursive). -/
theorem integer_abs_exec_corr (w : World)
    (h_fn : w.defs.get? integer_abs_sym = some ([xS], integerAbsBody))
    (h_no_integerp : w.defs.get? ({ name := "INTEGERP" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_neg : w.defs.get? ({ name := "UNARY--" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (integerAbsT x) (integerAbsExec xv)
    := by
  intro env x xv hx
  refine conv_defn_1 w env integer_abs_sym x xv xS integerAbsBody _
    integer_abs_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hip := conv_builtin1 w _ { name := "INTEGERP" } xT xv
    (Logic.integerp xv) (by decide) h_no_integerp hxv
    (callBuiltin_integerp _)
  have hq0 : ConvTo w (bindArgs [xS] [xv]) q0 (.atom (.number (.int 0))) :=
    re_val_quote w _ (.atom (.number (.int 0)))
  have hlt := conv_builtin2 w _ { name := "<" } xT q0 xv
    (.atom (.number (.int 0))) _ (by decide) h_no_ltb hxv hq0
    (callBuiltin_lt _ _)
  have hneg := conv_builtin1 w _ { name := "UNARY--" } xT xv
    (Logic.neg xv) (by decide) h_no_neg hxv (callBuiltin_neg _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (app1 "INTEGERP" xT)
    (ifT (ltT xT q0) (app1 "UNARY--" xT) xT) q0 (Logic.integerp xv)
    (if Logic.toBool (Logic.lt xv (.atom (.number (.int 0)))) = true then
      Logic.neg xv
     else xv)
    (.atom (.number (.int 0))) hip
    (fun _ => conv_if_lift w _ (ltT xT q0) (app1 "UNARY--" xT) xT
      (Logic.lt xv (.atom (.number (.int 0)))) (Logic.neg xv) xv hlt
      (fun _ => hneg) (fun _ => hxv))
    (fun _ => hq0)
  rw [integerAbsExec]
  exact h

/-- Stage 1 for `length` (non-recursive). -/
theorem length_exec_corr (w : World)
    (h_fn : w.defs.get? length_sym = some ([xS], lengthBody))
    (h_no_stringp : w.defs.get? ({ name := "STRINGP" } : Symbol) = none)
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_coerce : w.defs.get? ({ name := "COERCE" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (lengthT x) (lengthExec xv) := by
  intro env x xv hx
  refine conv_defn_1 w env length_sym x xv xS lengthBody _
    length_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hsp := conv_builtin1 w _ { name := "STRINGP" } xT xv
    (Logic.stringp xv) (by decide) h_no_stringp hxv (callBuiltin_stringp _)
  have hco := conv_builtin2 w _ { name := "COERCE" } xT (qSym "LIST") xv
    (symV "LIST") _ (by decide) h_no_coerce hxv
    (re_val_quote w _ (symV "LIST")) (callBuiltin_coerce _ _)
  have hlen1 := conv_builtin1 w _ { name := "LEN" }
    (app2 "COERCE" xT (qSym "LIST")) (Logic.coerce xv (symV "LIST"))
    (Logic.len (Logic.coerce xv (symV "LIST"))) (by decide) h_no_len hco
    (callBuiltin_len _)
  have hlen2 := conv_builtin1 w _ { name := "LEN" } xT xv
    (Logic.len xv) (by decide) h_no_len hxv (callBuiltin_len _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (app1 "STRINGP" xT)
    (app1 "LEN" (app2 "COERCE" xT (qSym "LIST"))) (app1 "LEN" xT)
    (Logic.stringp xv) (Logic.len (Logic.coerce xv (symV "LIST")))
    (Logic.len xv) hsp
    (fun _ => hlen1) (fun _ => hlen2)
  rw [lengthExec]
  exact h

/-- Stage 1: an `acl2-count` call converges to `acl2CountExec`. -/
theorem acl2_count_exec_corr (w : World)
    (h_ac : w.defs.get? acl2_count_sym = some ([xS], acl2CountBody))
    (h_ia : w.defs.get? integer_abs_sym = some ([xS], integerAbsBody))
    (h_len : w.defs.get? length_sym = some ([xS], lengthBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_rationalp : w.defs.get? ({ name := "RATIONALP" } : Symbol) = none)
    (h_no_integerp : w.defs.get? ({ name := "INTEGERP" } : Symbol) = none)
    (h_no_num : w.defs.get? ({ name := "NUMERATOR" } : Symbol) = none)
    (h_no_den : w.defs.get? ({ name := "DENOMINATOR" } : Symbol) = none)
    (h_no_crp : w.defs.get?
      ({ name := "COMPLEX-RATIONALP" } : Symbol) = none)
    (h_no_stringp : w.defs.get? ({ name := "STRINGP" } : Symbol) = none)
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_coerce : w.defs.get? ({ name := "COERCE" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_neg : w.defs.get? ({ name := "UNARY--" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (acl2CountT x) (acl2CountExec xv)
    := by
  have hbody : ∀ xv : SExpr,
      ConvTo w (bindArgs [xS] [xv]) acl2CountBody (acl2CountExec xv) := by
    refine consCount_strong_induction
      (fun xv => ConvTo w (bindArgs [xS] [xv]) acl2CountBody
        (acl2CountExec xv)) ?_
    intro xv ih
    have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
      (bindArgs_single_get_self xS xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hrp := conv_builtin1 w _ { name := "RATIONALP" } xT xv
      (rationalpV xv) (by decide) h_no_rationalp hxv
      (callBuiltin_rationalp _)
    have hip := conv_builtin1 w _ { name := "INTEGERP" } xT xv
      (Logic.integerp xv) (by decide) h_no_integerp hxv
      (callBuiltin_integerp _)
    have hcrp := conv_builtin1 w _ { name := "COMPLEX-RATIONALP" } xT xv
      (Logic.complexRationalp xv) (by decide) h_no_crp hxv
      (callBuiltin_complexRationalp _)
    have hsp := conv_builtin1 w _ { name := "STRINGP" } xT xv
      (Logic.stringp xv) (by decide) h_no_stringp hxv
      (callBuiltin_stringp _)
    have hnum := conv_builtin1 w _ { name := "NUMERATOR" } xT xv
      (Logic.numerator xv) (by decide) h_no_num hxv
      (callBuiltin_numerator _)
    have hden := conv_builtin1 w _ { name := "DENOMINATOR" } xT xv
      (Logic.denominator xv) (by decide) h_no_den hxv
      (callBuiltin_denominator _)
    -- the cons branch: 1 + (count car + count cdr)
    have hconsBranch : Logic.toBool (Logic.consp xv) = true →
        ConvTo w (bindArgs [xS] [xv])
          (plusT q1 (plusT (acl2CountT (carT xT)) (acl2CountT (cdrT xT))))
          (Logic.plus int1 (Logic.plus (acl2CountExec (Logic.car xv))
            (acl2CountExec (Logic.cdr xv)))) := by
      intro hb
      have hrec1 := conv_defn_1 w _ acl2_count_sym (carT xT)
        (Logic.car xv) xS acl2CountBody _ acl2_count_ns h_ac hcar
        (ih (Logic.car xv) (consCount_car_lt_of_consp hb))
      have hrec2 := conv_defn_1 w _ acl2_count_sym (cdrT xT)
        (Logic.cdr xv) xS acl2CountBody _ acl2_count_ns h_ac hcdr
        (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb))
      have hinner := conv_builtin2 w _ { name := "BINARY-+" }
        (acl2CountT (carT xT)) (acl2CountT (cdrT xT)) _ _ _ (by decide)
        h_no_plus hrec1 hrec2 (callBuiltin_plus _ _)
      exact conv_builtin2 w _ { name := "BINARY-+" } q1 _ int1 _ _
        (by decide) h_no_plus (re_val_quote w _ int1) hinner
        (callBuiltin_plus _ _)
    -- the rational branch
    have hIA := integer_abs_exec_corr w h_ia h_no_integerp h_no_ltb
      h_no_neg _ xT xv hxv
    have hIAnum := integer_abs_exec_corr w h_ia h_no_integerp h_no_ltb
      h_no_neg _ (app1 "NUMERATOR" xT) (Logic.numerator xv) hnum
    have hratBranch : ConvTo w (bindArgs [xS] [xv])
        (ifT (app1 "INTEGERP" xT)
          (integerAbsT xT)
          (plusT (integerAbsT (app1 "NUMERATOR" xT))
            (app1 "DENOMINATOR" xT)))
        (if Logic.toBool (Logic.integerp xv) = true then integerAbsExec xv
         else Logic.plus (integerAbsExec (Logic.numerator xv))
           (Logic.denominator xv)) :=
      conv_if_lift w _ (app1 "INTEGERP" xT) _ _ (Logic.integerp xv)
        (integerAbsExec xv)
        (Logic.plus (integerAbsExec (Logic.numerator xv))
          (Logic.denominator xv)) hip
        (fun _ => hIA)
        (fun _ =>
          conv_builtin2 w _ { name := "BINARY-+" }
            (integerAbsT (app1 "NUMERATOR" xT)) (app1 "DENOMINATOR" xT)
            _ _ _ (by decide) h_no_plus hIAnum hden
            (callBuiltin_plus _ _))
    -- the string branch
    have hLen := length_exec_corr w h_len h_no_stringp h_no_len
      h_no_coerce _ xT xv hxv
    have houter := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT)
      (plusT q1 (plusT (acl2CountT (carT xT)) (acl2CountT (cdrT xT))))
      (ifT (app1 "RATIONALP" xT)
        (ifT (app1 "INTEGERP" xT)
          (integerAbsT xT)
          (plusT (integerAbsT (app1 "NUMERATOR" xT))
            (app1 "DENOMINATOR" xT)))
        (ifT (app1 "COMPLEX-RATIONALP" xT)
          (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
            (acl2CountT (app1 "IMAGPART" xT))))
          (ifT (app1 "STRINGP" xT) (lengthT xT) q0)))
      (Logic.consp xv)
      (Logic.plus int1 (Logic.plus (acl2CountExec (Logic.car xv))
        (acl2CountExec (Logic.cdr xv))))
      (if Logic.toBool (rationalpV xv) = true then
        (if Logic.toBool (Logic.integerp xv) = true then integerAbsExec xv
         else Logic.plus (integerAbsExec (Logic.numerator xv))
           (Logic.denominator xv))
       else if Logic.toBool (Logic.stringp xv) = true then lengthExec xv
       else .atom (.number (.int 0)))
      hconsp hconsBranch
      (fun _ =>
        conv_if_lift w _ (app1 "RATIONALP" xT) _ _ (rationalpV xv)
          (if Logic.toBool (Logic.integerp xv) = true then
            integerAbsExec xv
           else Logic.plus (integerAbsExec (Logic.numerator xv))
             (Logic.denominator xv))
          (if Logic.toBool (Logic.stringp xv) = true then lengthExec xv
           else .atom (.number (.int 0)))
          hrp
          (fun _ => hratBranch)
          (fun _ =>
            have hcomplex : ConvTo w (bindArgs [xS] [xv])
                (ifT (app1 "COMPLEX-RATIONALP" xT)
                  (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
                    (acl2CountT (app1 "IMAGPART" xT))))
                  (ifT (app1 "STRINGP" xT) (lengthT xT) q0))
                (if Logic.toBool (Logic.stringp xv) = true then
                  lengthExec xv
                 else .atom (.number (.int 0))) := by
              have := conv_if_lift w (bindArgs [xS] [xv])
                (app1 "COMPLEX-RATIONALP" xT)
                (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
                  (acl2CountT (app1 "IMAGPART" xT))))
                (ifT (app1 "STRINGP" xT) (lengthT xT) q0)
                (Logic.complexRationalp xv)
                (if Logic.toBool (Logic.stringp xv) = true then
                  lengthExec xv
                 else .atom (.number (.int 0)))
                (if Logic.toBool (Logic.stringp xv) = true then
                  lengthExec xv
                 else .atom (.number (.int 0)))
                hcrp
                (fun hb =>
                  absurd hb (by
                    simp [Logic.complexRationalp, Logic.toBool]))
                (fun _ =>
                  conv_if_lift w _ (app1 "STRINGP" xT) (lengthT xT) q0
                    (Logic.stringp xv) (lengthExec xv)
                    (.atom (.number (.int 0))) hsp
                    (fun _ => hLen)
                    (fun _ => re_val_quote w _ (.atom (.number (.int 0)))))
              simpa [ite_self] using this
            hcomplex))
    rw [acl2CountExec.eq_def]
    simp only [dite_eq_ite]
    exact houter
  intro env x xv hx
  exact conv_defn_1 w env acl2_count_sym x xv xS acl2CountBody _
    acl2_count_ns h_ac hx (hbody xv)

end ACL2.Worlds.Sorting
