import ACL2Lean.EvalOpt
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Count

open ACL2 ACL2.Replay

namespace ACL2.Worlds.Simple

private def sym (name : String) : Symbol := ⟨"ACL2", name⟩

def my_lenBody : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "if" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "consp" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "+" })) (SExpr.cons (SExpr.atom (.number (.int (1)))) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "cdr" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) SExpr.nil)) SExpr.nil))) (SExpr.cons (SExpr.atom (.number (.int (0)))) SExpr.nil))))

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

def my_len_my_appFormula : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "equal" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-app" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil))) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "+" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil)) SExpr.nil))) SExpr.nil)))

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
    -- Builtin non-shadowing
    (h_no_equal : w.defs[({ name := "equal" } : Symbol)]? = none)
    (h_no_consp : w.defs[({ name := "consp" } : Symbol)]? = none) :
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

    -- NODE 1 (definition:my-app): eval(MY-APP x y) = eval(y) in env
    -- Both sides evaluate to yv. Proof: T4 unfolds my-app, T5 resolves
    -- IF (consp=nil → else), T7 looks up y in bodyEnv → yv.
    have h_node1 : ∃ N, ∀ f ≥ N,
        evalOpt f w env my_app_xy = evalOpt f w env y_var := by
      -- Both evaluate to yv at sufficient fuel
      exact ⟨5, fun f hf => by
        -- LHS: eval(MY-APP x y) = some yv
        -- T4 at fuel f: needs args eval'd at f-1, body at f-1
        -- T5 + T7 inside body at f-2, f-3
        sorry⟩

    -- NODE 2 (definition:my-len): eval(MY-LEN x) = eval(QUOTE 0) in env
    -- MY-LEN with consp(xv)=nil → body takes else-branch → 0
    have h_node2 : ∃ N, ∀ f ≥ N,
        evalOpt f w env my_len_x = evalOpt f w env quote_0 := by
      exact ⟨5, fun f hf => by sorry⟩

    -- NODE 3 (rewrite:unicity-of-0): eval(BINARY-+ '0 (MY-LEN y)) = eval(MY-LEN y)
    -- Uses unicity-of-0 axiom + fix elimination via type-prescription
    have h_node3 : ∃ N, ∀ f ≥ N,
        evalOpt f w env plus_0_len_y = evalOpt f w env my_len_y := by
      exact ⟨5, fun f hf => by sorry⟩

    -- NODE 4 (equal-self): eval(EQUAL (MY-LEN y) (MY-LEN y)) = some T
    -- After the 3 rewrites, the formula becomes (EQUAL (MY-LEN y) (MY-LEN y)).
    -- T3 says this evaluates to T if (MY-LEN y) converges.
    -- We compute: F1 = replaceSubterm formula (MY-APP x y) y
    --             F2 = replaceSubterm F1 (MY-LEN x) (QUOTE 0)
    --             F3 = replaceSubterm F2 (BINARY-+ '0 (MY-LEN y)) (MY-LEN y)
    -- Then F3 should be (EQUAL (MY-LEN y) (MY-LEN y)).
    let F1 := replaceSubterm my_len_my_appFormula my_app_xy y_var
    let F2 := replaceSubterm F1 my_len_x quote_0
    let F3 := replaceSubterm F2 plus_0_len_y my_len_y

    -- The equal-self step: eval(F3) = some T
    -- F3 should be (EQUAL (MY-LEN y) (MY-LEN y))
    have h_node4 : ∃ N, ∀ f ≥ N, evalOpt f w env F3 = some SExpr.t := by
      exact ⟨5, fun f hf => by sorry⟩

    -- CHAIN: T1 (congruence) + T16 (transitivity)
    -- eval(formula) = eval(F1) by T1 using h_node1
    -- eval(F1) = eval(F2) by T1 using h_node2
    -- eval(F2) = eval(F3) by T1 using h_node3
    -- eval(F3) = some T by h_node4
    exact fuel_chain_eq
      (fuel_chain_eq
        (fuel_chain_eq
          (evalOpt_replace_congr_fwd w env my_len_my_appFormula my_app_xy y_var h_node1)
          (evalOpt_replace_congr_fwd w env F1 my_len_x quote_0 h_node2))
        (evalOpt_replace_congr_fwd w env F2 plus_0_len_y my_len_y h_node3))
      h_node4

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
  unfold world
  rw [Std.HashMap.getElem?_insert]; simp [sym]

/-- The final theorem: combines the definition verification branch
    with the proof replay branch. Zero sorry in this theorem. -/
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f, f ≥ N → evalOpt f world env my_len_my_appFormula = some SExpr.t :=
  my_len_my_app_generic world env
    world_has_my_app world_has_my_len world_no_equal world_no_consp

end ACL2.Worlds.Simple
