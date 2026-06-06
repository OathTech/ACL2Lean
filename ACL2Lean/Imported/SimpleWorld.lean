import ACL2Lean.EvalOpt
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Count

open ACL2 ACL2.Replay

namespace ACL2.Worlds.Simple

private def sym (name : String) : Symbol := ⟨"ACL2", name⟩

-- Body uses macro-expanded form (matching ACL2's DEFUN emission):
-- (IF (CONSP X) (BINARY-+ (QUOTE 1) (MY-LEN (CDR X))) (QUOTE 0))
def my_lenBody : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
    (.cons (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.cons (.atom (.symbol { name := "binary-+" }))
              (.cons (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 1))) .nil))
                (.cons (.cons (.atom (.symbol { name := "my-len" }))
                        (.cons (.cons (.atom (.symbol { name := "cdr" })) (.cons (.atom (.symbol { name := "x" })) .nil)) .nil))
                  .nil)))
        (.cons (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 0))) .nil))
          .nil)))

def my_appBody : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "if" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "consp" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "cons" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "car" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-app" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "cdr" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil))) SExpr.nil))) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil))))

def world : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert (sym "my-len") ([sym "x"], my_lenBody)
    |>.insert (sym "my-app") ([sym "x", sym "y"], my_appBody)

private def x_sym : Symbol := sym "x"
private def y_sym : Symbol := sym "y"
private def my_len_sym : Symbol := sym "my-len"
private def my_app_sym : Symbol := sym "my-app"

-- Formula uses macro-expanded form:
-- (EQUAL (MY-LEN (MY-APP X Y)) (BINARY-+ (MY-LEN X) (MY-LEN Y)))
/-! ## Totality + type-prescription for my-len -/

/-- Applied to any value, the my-len body converges to a (non-negative)
    integer. By induction on acl2Count via `acl2_induction_consp`; the
    recursive call `(my-len (cdr x))` is discharged by the IH on `(cdr val)`.
    This combines ACL2's termination (totality) and its type-prescription
    (`integerp (my-len x)`) into the one fact the replay needs. -/
theorem my_len_total (w : World)
    (h_my_len : w.defs[my_len_sym]? = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs[({ name := "consp" } : Symbol)]? = none)
    (h_no_cdr : w.defs[({ name := "cdr" } : Symbol)]? = none)
    (h_no_plus : w.defs[({ name := "binary-+" } : Symbol)]? = none) :
    ∀ val : SExpr, ∃ k : Int, ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [x_sym] [val]) my_lenBody
        = some (.atom (.number (.int k))) := by
  apply acl2_induction_consp
  · -- BASE: consp val = nil → body takes else-branch → 0
    intro val hconsp
    have hxlook : (bindArgs [x_sym] [val]).get? { name := "x" } = some val := by
      simp [bindArgs, x_sym, sym]
    refine ⟨0, 4, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
    have hc : evalOpt (g + 3) w (bindArgs [x_sym] [val])
        (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
        = some .nil := by
      rw [evalOpt_builtin_1 (g + 2) w (bindArgs [x_sym] [val]) { name := "consp" }
            (.atom (.symbol { name := "x" })) val (by decide) h_no_consp
            (evalOpt_var (g + 1) w (bindArgs [x_sym] [val]) { name := "x" } val hxlook)]
      rw [callBuiltin_consp, hconsp]
    unfold my_lenBody
    rw [evalOpt_if_false (g + 3) w (bindArgs [x_sym] [val]) _ _ _ hc]
    exact evalOpt_quote (g + 2) w _ (.atom (.number (.int 0)))
  · -- STEP: consp val ≠ nil, IH gives convergence of (my-len (cdr val))
    intro val hconsp ih
    obtain ⟨k', N', hrec⟩ := ih
    have hxlook : (bindArgs [x_sym] [val]).get? { name := "x" } = some val := by
      simp [bindArgs, x_sym, sym]
    have htrue : Logic.toBool (Logic.consp val) = true := by
      cases val with
      | cons a d => rfl
      | nil => exact absurd rfl hconsp
      | atom a => exact absurd rfl hconsp
    refine ⟨1 + k', N' + 5, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
    -- (consp x) → consp val (truthy)
    have hc : evalOpt (g + 4) w (bindArgs [x_sym] [val])
        (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
        = some (Logic.consp val) := by
      rw [evalOpt_builtin_1 (g + 3) w (bindArgs [x_sym] [val]) { name := "consp" }
            (.atom (.symbol { name := "x" })) val (by decide) h_no_consp
            (evalOpt_var (g + 2) w (bindArgs [x_sym] [val]) { name := "x" } val hxlook)]
      rw [callBuiltin_consp]
    -- (cdr x) → cdr val
    have hcdr : evalOpt (g + 2) w (bindArgs [x_sym] [val])
        (.cons (.atom (.symbol { name := "cdr" })) (.cons (.atom (.symbol { name := "x" })) .nil))
        = some (Logic.cdr val) := by
      rw [evalOpt_builtin_1 (g + 1) w (bindArgs [x_sym] [val]) { name := "cdr" }
            (.atom (.symbol { name := "x" })) val (by decide) h_no_cdr
            (evalOpt_var g w (bindArgs [x_sym] [val]) { name := "x" } val hxlook)]
      rw [callBuiltin_cdr]
    -- (my-len (cdr x)) → int k' (via IH)
    have hmylen : evalOpt (g + 3) w (bindArgs [x_sym] [val])
        (.cons (.atom (.symbol { name := "my-len" }))
          (.cons (.cons (.atom (.symbol { name := "cdr" }))
                   (.cons (.atom (.symbol { name := "x" })) .nil)) .nil))
        = some (.atom (.number (.int k'))) := by
      rw [evalOpt_defn_1 (g + 2) w (bindArgs [x_sym] [val]) { name := "my-len" }
            (.cons (.atom (.symbol { name := "cdr" }))
              (.cons (.atom (.symbol { name := "x" })) .nil))
            (Logic.cdr val) x_sym my_lenBody (by decide) h_my_len hcdr]
      exact hrec (g + 2) (by omega)
    -- '1 → int 1
    have hone : evalOpt (g + 3) w (bindArgs [x_sym] [val])
        (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 1))) .nil))
        = some (.atom (.number (.int 1))) :=
      evalOpt_quote (g + 2) w _ (.atom (.number (.int 1)))
    unfold my_lenBody
    rw [evalOpt_if_true (g + 4) w (bindArgs [x_sym] [val]) _ _ _ (Logic.consp val) hc htrue]
    rw [evalOpt_builtin_2 (g + 3) w (bindArgs [x_sym] [val]) { name := "binary-+" }
          _ _ (.atom (.number (.int 1))) (.atom (.number (.int k'))) (by decide) h_no_plus
          hone hmylen]
    rw [callBuiltin_plus, logic_plus_int]

/-- Totality for my-app: applied to any (xval, yval), the my-app body
    converges to a value. Induction on acl2Count of xval (yval fixed); the
    recursive (my-app (cdr x) y) is discharged by the IH on (cdr xval). -/
theorem my_app_total (w : World)
    (h_my_app : w.defs[my_app_sym]? = some ([x_sym, y_sym], my_appBody))
    (h_no_consp : w.defs[({ name := "consp" } : Symbol)]? = none)
    (h_no_cdr : w.defs[({ name := "cdr" } : Symbol)]? = none)
    (h_no_car : w.defs[({ name := "car" } : Symbol)]? = none)
    (h_no_cons : w.defs[({ name := "cons" } : Symbol)]? = none) :
    ∀ yval xval : SExpr, ∃ v : SExpr, ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [x_sym, y_sym] [xval, yval]) my_appBody = some v := by
  intro yval
  apply acl2_induction_consp
  · -- BASE: consp xval = nil → else-branch → y → yval
    intro xval hconsp
    have hxlook : (bindArgs [x_sym, y_sym] [xval, yval]).get? { name := "x" } = some xval := by
      show (bindArgs [x_sym, y_sym] [xval, yval])[({ name := "x" } : Symbol)]? = some xval
      simp only [bindArgs, x_sym, y_sym, sym, Std.HashMap.getElem?_insert]
      rw [if_pos (by decide)]
    have hylook : (bindArgs [x_sym, y_sym] [xval, yval]).get? { name := "y" } = some yval := by
      show (bindArgs [x_sym, y_sym] [xval, yval])[({ name := "y" } : Symbol)]? = some yval
      simp only [bindArgs, x_sym, y_sym, sym, Std.HashMap.getElem?_insert]
      rw [if_neg (by decide), if_pos (by decide)]
    refine ⟨yval, 4, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
    have hc : evalOpt (g + 3) w (bindArgs [x_sym, y_sym] [xval, yval])
        (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
        = some .nil := by
      rw [evalOpt_builtin_1 (g + 2) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "consp" }
            (.atom (.symbol { name := "x" })) xval (by decide) h_no_consp
            (evalOpt_var (g + 1) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "x" } xval hxlook)]
      rw [callBuiltin_consp, hconsp]
    unfold my_appBody
    rw [evalOpt_if_false (g + 3) w (bindArgs [x_sym, y_sym] [xval, yval]) _ _ _ hc]
    exact evalOpt_var (g + 2) w _ { name := "y" } yval hylook
  · -- STEP: consp xval ≠ nil → CONS (CAR x) (MY-APP (CDR x) y)
    intro xval hconsp ih
    obtain ⟨v', N', hrec⟩ := ih
    have hxlook : (bindArgs [x_sym, y_sym] [xval, yval]).get? { name := "x" } = some xval := by
      show (bindArgs [x_sym, y_sym] [xval, yval])[({ name := "x" } : Symbol)]? = some xval
      simp only [bindArgs, x_sym, y_sym, sym, Std.HashMap.getElem?_insert]
      rw [if_pos (by decide)]
    have hylook : (bindArgs [x_sym, y_sym] [xval, yval]).get? { name := "y" } = some yval := by
      show (bindArgs [x_sym, y_sym] [xval, yval])[({ name := "y" } : Symbol)]? = some yval
      simp only [bindArgs, x_sym, y_sym, sym, Std.HashMap.getElem?_insert]
      rw [if_neg (by decide), if_pos (by decide)]
    have htrue : Logic.toBool (Logic.consp xval) = true := by
      cases xval with
      | cons a d => rfl
      | nil => exact absurd rfl hconsp
      | atom a => exact absurd rfl hconsp
    refine ⟨.cons (Logic.car xval) v', N' + 5, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
    -- (consp x) → consp xval (truthy)
    have hc : evalOpt (g + 4) w (bindArgs [x_sym, y_sym] [xval, yval])
        (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
        = some (Logic.consp xval) := by
      rw [evalOpt_builtin_1 (g + 3) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "consp" }
            (.atom (.symbol { name := "x" })) xval (by decide) h_no_consp
            (evalOpt_var (g + 2) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "x" } xval hxlook)]
      rw [callBuiltin_consp]
    -- (car x) → car xval
    have hcar : evalOpt (g + 3) w (bindArgs [x_sym, y_sym] [xval, yval])
        (.cons (.atom (.symbol { name := "car" })) (.cons (.atom (.symbol { name := "x" })) .nil))
        = some (Logic.car xval) := by
      rw [evalOpt_builtin_1 (g + 2) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "car" }
            (.atom (.symbol { name := "x" })) xval (by decide) h_no_car
            (evalOpt_var (g + 1) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "x" } xval hxlook)]
      rw [callBuiltin_car]
    -- (cdr x) → cdr xval
    have hcdr : evalOpt (g + 2) w (bindArgs [x_sym, y_sym] [xval, yval])
        (.cons (.atom (.symbol { name := "cdr" })) (.cons (.atom (.symbol { name := "x" })) .nil))
        = some (Logic.cdr xval) := by
      rw [evalOpt_builtin_1 (g + 1) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "cdr" }
            (.atom (.symbol { name := "x" })) xval (by decide) h_no_cdr
            (evalOpt_var g w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "x" } xval hxlook)]
      rw [callBuiltin_cdr]
    -- (MY-APP (cdr x) y) → v' via IH
    have happ : evalOpt (g + 3) w (bindArgs [x_sym, y_sym] [xval, yval])
        (.cons (.atom (.symbol { name := "my-app" }))
          (.cons (.cons (.atom (.symbol { name := "cdr" }))
                   (.cons (.atom (.symbol { name := "x" })) .nil))
            (.cons (.atom (.symbol { name := "y" })) .nil)))
        = some v' := by
      rw [evalOpt_defn_2 (g + 2) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "my-app" }
            (.cons (.atom (.symbol { name := "cdr" })) (.cons (.atom (.symbol { name := "x" })) .nil))
            (.atom (.symbol { name := "y" })) (Logic.cdr xval) yval x_sym y_sym my_appBody
            (by decide) h_my_app hcdr
            (evalOpt_var (g + 1) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "y" } yval hylook)]
      exact hrec (g + 2) (by omega)
    unfold my_appBody
    rw [evalOpt_if_true (g + 4) w (bindArgs [x_sym, y_sym] [xval, yval]) _ _ _
          (Logic.consp xval) hc htrue]
    rw [evalOpt_builtin_2 (g + 3) w (bindArgs [x_sym, y_sym] [xval, yval]) { name := "cons" }
          _ _ (Logic.car xval) v' (by decide) h_no_cons hcar happ]
    rfl


end ACL2.Worlds.Simple
