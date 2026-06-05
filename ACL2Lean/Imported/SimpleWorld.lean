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
def my_len_my_appFormula : SExpr :=
  .cons (.atom (.symbol { name := "equal" }))
    (.cons (.cons (.atom (.symbol { name := "my-len" }))
            (.cons (.cons (.atom (.symbol { name := "my-app" }))
                    (.cons (.atom (.symbol { name := "x" })) (.cons (.atom (.symbol { name := "y" })) .nil)))
              .nil))
      (.cons (.cons (.atom (.symbol { name := "binary-+" }))
              (.cons (.cons (.atom (.symbol { name := "my-len" }))
                      (.cons (.atom (.symbol { name := "x" })) .nil))
                (.cons (.cons (.atom (.symbol { name := "my-len" }))
                        (.cons (.atom (.symbol { name := "y" })) .nil))
                  .nil)))
        .nil))

/-! ## Proof rules: isNamed facts (by decide) -/

private theorem my_app_not_special :
    my_app_sym.isNamed "quote" = false ∧ my_app_sym.isNamed "if" = false ∧
    my_app_sym.isNamed "let" = false ∧ my_app_sym.isNamed "let*" = false := by decide

private theorem my_len_not_special :
    my_len_sym.isNamed "quote" = false ∧ my_len_sym.isNamed "if" = false ∧
    my_len_sym.isNamed "let" = false ∧ my_len_sym.isNamed "let*" = false := by decide

private theorem consp_not_special :
    ({ name := "consp" } : Symbol).isNamed "quote" = false ∧
    ({ name := "consp" } : Symbol).isNamed "if" = false ∧
    ({ name := "consp" } : Symbol).isNamed "let" = false ∧
    ({ name := "consp" } : Symbol).isNamed "let*" = false := by decide

/-! ## The generic proof (parameterized by world + definition hypotheses) -/

/-- The main theorem, parameterized by a world and proofs that the
    relevant definitions are present and builtins are not shadowed.
    This is the "use definitions" branch of the proof tree. -/
theorem my_len_my_app_generic
    (w : World) (env : Env)
    -- Definition hypotheses (from the "verify definitions" branch)
    (h_my_app : w.defs[my_app_sym]? = some ([x_sym, y_sym], my_appBody))
    (h_my_len : w.defs[my_len_sym]? = some ([x_sym], my_lenBody))
    -- Builtin non-shadowing (builtins used in proof must not be in w.defs)
    (h_no_equal : w.defs[({ name := "equal" } : Symbol)]? = none)
    (h_no_consp : w.defs[({ name := "consp" } : Symbol)]? = none)
    (h_no_plus  : w.defs[({ name := "binary-+" } : Symbol)]? = none)
    (h_no_cdr   : w.defs[({ name := "cdr" } : Symbol)]? = none)
    (h_no_car   : w.defs[({ name := "car" } : Symbol)]? = none)
    (h_no_cons  : w.defs[({ name := "cons" } : Symbol)]? = none) :
    ∃ N, ∀ f, f ≥ N → evalOpt f w env my_len_my_appFormula = some SExpr.t := by
  -- The proof follows the ACL2 proof tree: induction on acl2Count of env(x),
  -- then for each case, a chain of rewrites ending in equal-self.
  --
  -- Each rewrite establishes eval(lhs) = some v and eval(rhs) = some v
  -- (both sides evaluate to the same value). Then T1 lifts this to the
  -- enclosing formula, and T16 chains the steps.

  -- First: what does env map x and y to?
  -- We case-split on whether x is bound and extract its value.
  -- If x is unbound, evalOpt returns nil for it, so consp(nil)=nil → base case.
  have h_x : ∃ xv, ∀ f, evalOpt (f + 1) w env (.atom (.symbol x_sym)) = some xv := by
    match hx : env.get? x_sym with
    | some v => exact ⟨v, fun f => evalOpt_var f w env x_sym v hx⟩
    | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w env x_sym hx (by decide)⟩
  obtain ⟨xv, h_xv⟩ := h_x

  have h_y : ∃ yv, ∀ f, evalOpt (f + 1) w env (.atom (.symbol y_sym)) = some yv := by
    match hy : env.get? y_sym with
    | some v => exact ⟨v, fun f => evalOpt_var f w env y_sym v hy⟩
    | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w env y_sym hy (by decide)⟩
  obtain ⟨yv, h_yv⟩ := h_y

  -- Induction on xv using T10 (acl2_induction_consp).
  -- P(xv) = the formula evaluates to T when env maps x to xv (and y to yv).
  suffices h_ind : ∀ xv,
      (∀ f, evalOpt (f + 1) w env (.atom (.symbol x_sym)) = some xv) →
      ∃ N, ∀ f, f ≥ N → evalOpt f w env my_len_my_appFormula = some SExpr.t from
    h_ind xv h_xv
  -- Apply T10: induction on consp/cdr structure of xv
  apply acl2_induction_consp (fun xv =>
    (∀ f, evalOpt (f + 1) w env (.atom (.symbol x_sym)) = some xv) →
    ∃ N, ∀ f, f ≥ N → evalOpt f w env my_len_my_appFormula = some SExpr.t)

  -- Base case: consp(xv) = nil
  · intro xv h_consp h_xv'
    -- Abbreviations for the SExpr subterms referenced by the proof tree
    let my_app_xy := SExpr.cons (.atom (.symbol my_app_sym))
          (.cons (.atom (.symbol x_sym)) (.cons (.atom (.symbol y_sym)) .nil))
    let y_var := SExpr.atom (.symbol y_sym)
    let my_len_x := SExpr.cons (.atom (.symbol my_len_sym))
          (.cons (.atom (.symbol x_sym)) .nil)
    let quote_0 := SExpr.cons (.atom (.symbol { name := "quote" }))
          (.cons (.atom (.number (.int 0))) .nil)
    let my_len_y := SExpr.cons (.atom (.symbol my_len_sym))
          (.cons y_var .nil)
    let plus_0_len_y := SExpr.cons (.atom (.symbol { name := "binary-+" }))
          (.cons quote_0 (.cons my_len_y .nil))
    let rhs_term := SExpr.cons (.atom (.symbol { name := "binary-+" }))
          (.cons my_len_x (.cons my_len_y .nil))

    -- NODE 1 (definition:my-app): eval(MY-APP x y) = eval(y) in env
    -- Both sides evaluate to yv. Proof: T4 unfolds my-app, T5 resolves
    -- IF (consp=nil → else), T7 looks up y in bodyEnv → yv.
    -- NODE 1 (definition:my-app): eval(MY-APP x y) = eval(y)
    -- Proof: T4 + T5 + T6 + T7 composed. Both sides = some yv.
    -- The composition is correct but fighting Lean's tactic mode on
    -- fuel arithmetic and symbol name matching. These issues would not
    -- exist in a proof-producing checker (which generates Expr directly).
    have h_node1 : ∃ N, ∀ f ≥ N,
        evalOpt f w env my_app_xy = evalOpt f w env y_var := by
      refine ⟨5, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      have hxlook : (bindArgs [x_sym, y_sym] [xv, yv]).get? { name := "x" } = some xv := by
        simp [bindArgs, x_sym, y_sym, sym]
      have hylook : (bindArgs [x_sym, y_sym] [xv, yv]).get? { name := "y" } = some yv := by
        show (bindArgs [x_sym, y_sym] [xv, yv])[({ name := "y" } : Symbol)]? = some yv
        simp only [bindArgs, x_sym, y_sym, sym, Std.HashMap.getElem?_insert]
        rw [if_neg (by decide), if_pos (by decide)]
      -- test (consp x) → nil in body env (x ↦ xv)
      have hc : evalOpt (g + 3) w (bindArgs [x_sym, y_sym] [xv, yv])
          (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
          = some .nil := by
        rw [evalOpt_builtin_1 (g + 2) w (bindArgs [x_sym, y_sym] [xv, yv]) { name := "consp" }
              (.atom (.symbol { name := "x" })) xv (by decide) h_no_consp
              (evalOpt_var (g + 1) w (bindArgs [x_sym, y_sym] [xv, yv]) { name := "x" } xv hxlook)]
        rw [callBuiltin_consp, h_consp]
      -- LHS: (MY-APP x y) unfolds, takes else-branch → y → yv
      have hlhs : evalOpt (g + 5) w env my_app_xy = some yv := by
        show evalOpt (g + 5) w env (.cons (.atom (.symbol my_app_sym))
          (.cons (.atom (.symbol x_sym)) (.cons (.atom (.symbol y_sym)) .nil))) = _
        rw [evalOpt_defn_2 (g + 4) w env my_app_sym (.atom (.symbol x_sym))
              (.atom (.symbol y_sym)) xv yv x_sym y_sym my_appBody (by decide) h_my_app
              (h_xv' (g + 3)) (h_yv (g + 3))]
        unfold my_appBody
        rw [evalOpt_if_false (g + 3) w (bindArgs [x_sym, y_sym] [xv, yv]) _ _ _ hc]
        exact evalOpt_var (g + 2) w _ { name := "y" } yv hylook
      have hrhs : evalOpt (g + 5) w env y_var = some yv := h_yv (g + 4)
      rw [hlhs, hrhs]

    -- NODE 2 (definition:my-len): eval(MY-LEN x) = eval(QUOTE 0) in env
    -- MY-LEN with consp(xv)=nil → body takes else-branch → 0
    have h_node2 : ∃ N, ∀ f ≥ N,
        evalOpt f w env my_len_x = evalOpt f w env quote_0 := by
      refine ⟨5, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      -- variable x looks up to xv in the body env (formal x_sym ↦ xv)
      have hxlook : (bindArgs [x_sym] [xv]).get? { name := "x" } = some xv := by
        simp [bindArgs, x_sym, sym]
      -- the test (consp x) evaluates to nil in the body env (x ↦ xv)
      have hc : evalOpt (g + 3) w (bindArgs [x_sym] [xv])
          (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
          = some .nil := by
        rw [evalOpt_builtin_1 (g + 2) w (bindArgs [x_sym] [xv]) { name := "consp" }
              (.atom (.symbol { name := "x" })) xv (by decide) h_no_consp
              (evalOpt_var (g + 1) w (bindArgs [x_sym] [xv]) { name := "x" } xv hxlook)]
        rw [callBuiltin_consp, h_consp]
      -- LHS: (MY-LEN x) unfolds, takes else-branch → (QUOTE 0) → 0
      have hlhs : evalOpt (g + 5) w env my_len_x = some (.atom (.number (.int 0))) := by
        show evalOpt (g + 5) w env (.cons (.atom (.symbol my_len_sym))
          (.cons (.atom (.symbol x_sym)) .nil)) = _
        rw [evalOpt_defn_1 (g + 4) w env my_len_sym (.atom (.symbol x_sym)) xv x_sym
              my_lenBody (by decide) h_my_len (h_xv' (g + 3))]
        unfold my_lenBody
        rw [evalOpt_if_false (g + 3) w (bindArgs [x_sym] [xv]) _ _ _ hc]
        exact evalOpt_quote (g + 2) w _ (.atom (.number (.int 0)))
      have hrhs : evalOpt (g + 5) w env quote_0 = some (.atom (.number (.int 0))) :=
        evalOpt_quote (g + 4) w env (.atom (.number (.int 0)))
      rw [hlhs, hrhs]

    -- NODE 3 (rewrite:unicity-of-0): eval(BINARY-+ '0 (MY-LEN y)) = eval(MY-LEN y)
    -- Uses unicity-of-0 axiom + fix elimination via type-prescription
    have h_node3 : ∃ N, ∀ f ≥ N,
        evalOpt f w env plus_0_len_y = evalOpt f w env my_len_y := by
      exact ⟨5, fun f hf => by sorry⟩

    -- NODE 4 (equal-self): (MY-LEN y) converges, so (EQUAL (MY-LEN y)(MY-LEN y)) = T.
    have h_conv : ∃ v N, ∀ f ≥ N, evalOpt f w env my_len_y = some v := by
      sorry -- totality of my-len applied to y (Phase 1: induction on acl2Count)

    -- Lift each node fact through its evaluation context via one-step
    -- argument congruence, then chain with fuel_chain_eq. No replaceSubterm,
    -- no pcEq — the context is built explicitly here.
    -- LHS: (MY-LEN (MY-APP x y)) ~ (MY-LEN y)
    have hLHS := evalOpt_cong_unary w env { name := "my-len" } my_app_xy y_var
      (by decide) (by decide) (by decide) (by decide) h_node1
    -- RHS: (BINARY-+ (MY-LEN x)(MY-LEN y)) ~ (BINARY-+ '0 (MY-LEN y)) ~ (MY-LEN y)
    have hII := evalOpt_cong_bin1 w env { name := "binary-+" } my_len_x quote_0 my_len_y
      (by decide) (by decide) (by decide) (by decide) h_node2
    have hRHS := fuel_chain_eq hII h_node3
    -- Formula congruence in each EQUAL argument.
    have hIII := evalOpt_cong_bin1 w env { name := "equal" }
      (SExpr.cons (.atom (.symbol my_len_sym)) (.cons my_app_xy .nil)) my_len_y rhs_term
      (by decide) (by decide) (by decide) (by decide) hLHS
    have hIV := evalOpt_cong_bin2 w env { name := "equal" } my_len_y rhs_term my_len_y
      (by decide) (by decide) (by decide) (by decide) hRHS
    -- equal-self finish (needs (MY-LEN y) to converge).
    have hV : ∃ N, ∀ f ≥ N,
        evalOpt f w env (SExpr.cons (.atom (.symbol { name := "equal" }))
          (.cons my_len_y (.cons my_len_y .nil))) = some SExpr.t := by
      obtain ⟨v, Nc, hc⟩ := h_conv
      refine ⟨Nc + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_equal_self g w env my_len_y v (hc g (by omega)) h_no_equal
    -- CHAIN: formula ~ (EQUAL (MY-LEN y) rhs) ~ (EQUAL (MY-LEN y)(MY-LEN y)) ~ some T
    exact fuel_chain_eq (fuel_chain_eq hIII hIV) hV

  -- Step case: consp(xv) ≠ nil, IH available
  · intro xv h_consp ih h_xv'
    -- Same structure: 5 nodes + equal-self, chained by T1 + T16.
    -- The IH connects via T15 (env substitution).
    sorry

/-! ## The concrete instantiation (definition verification branch) -/

/-- Prove the definition hypotheses for the concrete world.
    This is the "verify definitions" branch of the proof tree —
    it establishes that the HashMap contains what we expect. -/
-- Definition verification branch: prove HashMap lookup facts.
-- Pattern: rw [getElem?_insert] peels off one insert, simp resolves key comparison.

-- Definition verification: prove HashMap lookup facts.
-- Pattern: unfold world, rw [getElem?_insert], simp to resolve key comparisons.

theorem world_has_my_app :
    world.defs[my_app_sym]? = some ([x_sym, y_sym], my_appBody) := by
  unfold world
  rw [Std.HashMap.getElem?_insert]
  simp [my_app_sym, x_sym, y_sym, sym]

theorem world_has_my_len :
    world.defs[my_len_sym]? = some ([x_sym], my_lenBody) := by
  unfold world
  rw [Std.HashMap.getElem?_insert]; simp [my_len_sym, sym]
  simp [x_sym, sym]

theorem world_no_equal :
    world.defs[({ name := "equal" } : Symbol)]? = none := by
  unfold world
  rw [Std.HashMap.getElem?_insert]; simp [sym]

theorem world_no_consp :
    world.defs[({ name := "consp" } : Symbol)]? = none := by
  unfold world; rw [Std.HashMap.getElem?_insert]; simp [sym]

theorem world_no_plus :
    world.defs[({ name := "binary-+" } : Symbol)]? = none := by
  unfold world; rw [Std.HashMap.getElem?_insert]; simp [sym]

theorem world_no_cdr :
    world.defs[({ name := "cdr" } : Symbol)]? = none := by
  unfold world; rw [Std.HashMap.getElem?_insert]; simp [sym]

theorem world_no_car :
    world.defs[({ name := "car" } : Symbol)]? = none := by
  unfold world; rw [Std.HashMap.getElem?_insert]; simp [sym]

theorem world_no_cons :
    world.defs[({ name := "cons" } : Symbol)]? = none := by
  unfold world; rw [Std.HashMap.getElem?_insert]; simp [sym]

/-- The final theorem: combines the definition verification branch
    (sorry-free HashMap lookups) with the proof replay branch.
    NOTE: still transitively depends on sorries in `my_len_my_app_generic`
    (base case: h_node3/h_conv; the step case). Not yet a complete proof. -/
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f, f ≥ N → evalOpt f world env my_len_my_appFormula = some SExpr.t :=
  my_len_my_app_generic world env
    world_has_my_app world_has_my_len world_no_equal world_no_consp
    world_no_plus world_no_cdr world_no_car world_no_cons

end ACL2.Worlds.Simple
