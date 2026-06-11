import ACL2Lean.EvalOpt
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Count
import ACL2Lean.Imported.Lifting

open ACL2 ACL2.Replay

namespace ACL2.Worlds.Simple

def sym (name : String) : Symbol := ⟨"ACL2", name⟩

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

-- ACL2's ground-zero `fix`: (defun fix (x) (if (acl2-numberp x) x 0)). Modeling it as a
-- defined function (task #24) lets the base case replay `definition:fix` schematically
-- (def-unfold + acl2-numberp recognizer + if-simplification) instead of value-matching.
-- evalOpt computes the same value either way (def-unfold vs the `fix` builtin), so this is
-- additive; the base-case rework consumes it.
def fixBody : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
    (.cons (.cons (.atom (.symbol { name := "acl2-numberp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.atom (.symbol { name := "x" }))
        (.cons (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 0))) .nil)) .nil)))

def world : World where
  defs := ({} : DefMap)
    |>.insert (sym "my-len") ([sym "x"], my_lenBody)
    |>.insert (sym "my-app") ([sym "x", sym "y"], my_appBody)
    |>.insert (sym "fix") ([sym "x"], fixBody)

private def x_sym : Symbol := sym "x"
private def y_sym : Symbol := sym "y"
private def my_len_sym : Symbol := sym "my-len"
private def my_app_sym : Symbol := sym "my-app"
private def fix_sym : Symbol := sym "fix"

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

/-! ## Term decomposition (so the formula and its subterms line up with the
    arity-specific congruence lemmas, by `rfl`). -/

private def xT : SExpr := .atom (.symbol { name := "x" })
private def yT : SExpr := .atom (.symbol { name := "y" })
private def lenOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "my-len" })) (.cons t .nil)
private def appOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "my-app" })) (.cons a (.cons b .nil))
private def plusOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "binary-+" })) (.cons a (.cons b .nil))
private def equalOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "equal" })) (.cons a (.cons b .nil))
private def fixOf (z : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "fix" })) (.cons z .nil)
private def q0 : SExpr :=
  .cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 0))) .nil)
private def q1 : SExpr :=
  .cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 1))) .nil)
private def carOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "car" })) (.cons t .nil)
private def cdrOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "cdr" })) (.cons t .nil)
private def consOf (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil))
private def conspOf (t : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "consp" })) (.cons t .nil)

/-- The mirror-theorem formula, decomposed. By `rfl`. -/
private theorem formula_decomp :
    my_len_my_appFormula = equalOf (lenOf (appOf xT yT)) (plusOf (lenOf xT) (lenOf yT)) := rfl

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

private theorem equal_not_special :
    ({ name := "equal" } : Symbol).isNamed "quote" = false ∧
    ({ name := "equal" } : Symbol).isNamed "if" = false ∧
    ({ name := "equal" } : Symbol).isNamed "let" = false ∧
    ({ name := "equal" } : Symbol).isNamed "let*" = false := by decide

private theorem plus_not_special :
    ({ name := "binary-+" } : Symbol).isNamed "quote" = false ∧
    ({ name := "binary-+" } : Symbol).isNamed "if" = false ∧
    ({ name := "binary-+" } : Symbol).isNamed "let" = false ∧
    ({ name := "binary-+" } : Symbol).isNamed "let*" = false := by decide

private theorem car_not_special :
    ({ name := "car" } : Symbol).isNamed "quote" = false ∧
    ({ name := "car" } : Symbol).isNamed "if" = false ∧
    ({ name := "car" } : Symbol).isNamed "let" = false ∧
    ({ name := "car" } : Symbol).isNamed "let*" = false := by decide

private theorem cdr_not_special :
    ({ name := "cdr" } : Symbol).isNamed "quote" = false ∧
    ({ name := "cdr" } : Symbol).isNamed "if" = false ∧
    ({ name := "cdr" } : Symbol).isNamed "let" = false ∧
    ({ name := "cdr" } : Symbol).isNamed "let*" = false := by decide

private theorem cons_not_special :
    ({ name := "cons" } : Symbol).isNamed "quote" = false ∧
    ({ name := "cons" } : Symbol).isNamed "if" = false ∧
    ({ name := "cons" } : Symbol).isNamed "let" = false ∧
    ({ name := "cons" } : Symbol).isNamed "let*" = false := by decide

/-! ## Body structure facts (LET-free; free vars ⊆ formals) for the unfold transfer -/

private theorem my_appBody_nolet : NoLet my_appBody = true := by decide
private theorem my_lenBody_nolet : NoLet my_lenBody = true := by decide
private theorem my_appBody_fv : ∀ s ∈ freeVars my_appBody, s = x_sym ∨ s = y_sym := by decide
private theorem my_lenBody_fv : ∀ s ∈ freeVars my_lenBody, s = x_sym := by decide

private theorem fix_not_special :
    fix_sym.isNamed "quote" = false ∧ fix_sym.isNamed "if" = false ∧
    fix_sym.isNamed "let" = false ∧ fix_sym.isNamed "let*" = false := by decide
private theorem acl2numberp_not_special :
    ({ name := "acl2-numberp" } : Symbol).isNamed "quote" = false ∧
    ({ name := "acl2-numberp" } : Symbol).isNamed "if" = false ∧
    ({ name := "acl2-numberp" } : Symbol).isNamed "let" = false ∧
    ({ name := "acl2-numberp" } : Symbol).isNamed "let*" = false := by decide
private theorem fixBody_nolet : NoLet fixBody = true := by decide
private theorem fixBody_fv : ∀ s ∈ freeVars fixBody, s ∈ [x_sym] := by decide
/-- `substTerm [x] [z] fixBody = (if (acl2-numberp z) z '0)` — the fix body with `x:=z`. -/
private theorem fixBody_subst (z : SExpr) :
    substTerm [x_sym] [z] fixBody
      = .cons (.atom (.symbol { name := "if" }))
          (.cons (.cons (.atom (.symbol { name := "acl2-numberp" })) (.cons z .nil))
            (.cons z (.cons (.cons (.atom (.symbol { name := "quote" }))
                              (.cons (.atom (.number (.int 0))) .nil)) .nil))) := rfl

/-! ## The generic proof (parameterized by world + definition hypotheses) -/

/-- The mirror theorem for `my-len-my-app`, proved by replaying the real ACL2
    proof tree node-for-node — **both subgoals, sorry-free** (axioms:
    `{propext, Classical.choice, Quot.sound}`), modulo the consumed ACL2 facts
    `h_mylen_int` (type-prescription:my-len, used only by the base case),
    `h_mylen_total` / `h_myapp_total` (my-len/my-app admission ⇒ totality), which
    are still hypotheses. No functionality facts: the step case is fully schematic
    and totality-based, faithful to *1/1's runes (which cite no type-prescription).

    Base case `*1/2`: NODE 1–4 (def:my-app⇒y, def:my-len⇒0, unicity-of-0,
    equal-self). Step case `*1/1`: NODE 1 (def:my-app⇒cons), NODE 2 (def:my-len
    recursive + `cdr-cons` exposed via the compound-arg unfold), NODE 3
    (def:my-len⇒(+1 (my-len(cdr x)))), NODE 4 (commutativity-of-+,
    commutativity-2-of-+, the rewriting-equivalence solidify justified by the
    IH), NODE 5 (equal-self). Each node's subterm-rewrite fact is lifted through
    its exact tree context path by the proven arity-specific congruence lemmas —
    NOT the generic sorried `replaceSubterm` path — and chained by transitivity.

    Induction predicate generalizes over the environment `e` and the value `xv`
    bound to `x`, so the step-case IH (about `x ↦ cdr xv`) is usable — we
    instantiate it at `e.insert x (cdr xv)`. (The previous scaffold fixed one
    `env` and merely *hypothesized* `env(x)=xv`, making the IH vacuous.)

    Parameterized by a world and proofs that the relevant definitions are present
    and builtins are not shadowed (the "use definitions" branch of the tree). -/
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
    (h_no_cons  : w.defs[({ name := "cons" } : Symbol)]? = none)
    (h_no_acl2numberp : w.defs[({ name := "acl2-numberp" } : Symbol)]? = none)
    -- `fix` as a defined function (ACL2 ground-zero): the base case's NODE 3 replays
    -- `definition:fix` by unfolding this, NOT by collapsing `(+ 0 z)` to a value.
    (h_fix : w.defs[fix_sym]? = some ([x_sym], fixBody))
    -- Consumed ACL2 fact: `type-prescription:my-len` (my-len returns an integer)
    -- + my-len's admission (termination ⇒ convergence). The tree cites
    -- `type-prescription:my-len` at the base NODE 3 fix-elimination and throughout.
    -- Discharged concretely for `world` by replaying that corollary (a my-len
    -- structural induction) — see the instantiation below.
    (h_mylen_int : ∀ (e' : Env) (arg : SExpr),
      (∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' arg = some av) →
      ∃ M, ∃ k : Int, ∀ f ≥ M, evalOpt f w e' (lenOf arg) = some (.atom (.number (.int k))))
    -- Consumed ACL2 fact: my-len's ADMISSION ⇒ TOTALITY (my-len converges to SOME
    -- value whenever its argument does). This is the global world-fact the step
    -- subgoal *1/1 needs to discharge the evalOpt fuel side-conditions of its
    -- :DEFINITION unfolds — crucially NOT `type-prescription`, which the real *1/1
    -- does NOT cite in its runes (only the base *1/2 cites type-prescription:my-len,
    -- for the fix / unicity-of-0 / acl2-numberp reasoning).
    (h_mylen_total : ∀ (e' : Env) (arg : SExpr),
      (∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' arg = some av) →
      ∃ M, ∃ av, ∀ f ≥ M, evalOpt f w e' (lenOf arg) = some av)
    -- my-app's ADMISSION ⇒ TOTALITY (converges to SOME value when both args do).
    -- Used by the step case for the my-app :DEFINITION unfold and the IH solidify —
    -- a global world-fact, replacing the `h_myapp_fn` functionality crutch.
    (h_myapp_total : ∀ (e' : Env) (a b : SExpr),
      (∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' a = some av) →
      (∃ M, ∀ f ≥ M, ∃ bv, evalOpt f w e' b = some bv) →
      ∃ M, ∃ rv, ∀ f ≥ M, evalOpt f w e' (appOf a b) = some rv)
    :
    ∃ N, ∀ f, f ≥ N → evalOpt f w env my_len_my_appFormula = some SExpr.t := by
  -- Generalize over the environment and the value of x, then do the same
  -- consp/cdr induction ACL2's `INDUCTION on (my-app x y)` scheme prescribes.
  suffices H : ∀ xv : SExpr, ∀ e : Env,
      (∀ f, evalOpt (f + 1) w e (.atom (.symbol x_sym)) = some xv) →
      ∃ N, ∀ f, f ≥ N → evalOpt f w e my_len_my_appFormula = some SExpr.t by
    obtain ⟨xv, h_xv⟩ : ∃ xv, ∀ f, evalOpt (f + 1) w env (.atom (.symbol x_sym)) = some xv := by
      match hx : env.get? x_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w env x_sym v hx⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w env x_sym hx (by decide)⟩
    exact H xv env h_xv
  refine acl2_induction_consp (fun xv => ∀ e : Env,
      (∀ f, evalOpt (f + 1) w e (.atom (.symbol x_sym)) = some xv) →
      ∃ N, ∀ f, f ≥ N → evalOpt f w e my_len_my_appFormula = some SExpr.t) ?base ?step

  -- ── Subgoal *1/2 (base): consp xv = nil ─────────────────────────────────
  case base =>
    intro xv h_consp e h_xe
    -- SCHEMATIC replay of *1/2 (task #29), in the same per-rune combinator style as the
    -- step case — each node applies its rune's rule + congruence, values existential from
    -- totality (h_mylen_total / h_myapp_total), NOT computed-both-sides-and-matched:
    --   node1 (def:my-app)     : re_unfold2_var ; (consp⇒nil) recognizer ; re_if_false
    --   node2 (def:my-len)     : re_unfold1_var ; (consp⇒nil) recognizer ; re_if_false
    --   node3 (unicity-of-0)   : (+ 0 z) ⇒ (fix z) ; then definition:fix replayed via the
    --                            `fix` defun unfold (task #24) ; acl2-numberp recognizer
    --                            (type-prescription:my-len ⇒ z is an int) ; re_if_true
    --   node4 (equal-self)     : evalOpt_equal_self
    -- value of y in e
    obtain ⟨yv, h_ye⟩ : ∃ yv, ∀ f, evalOpt (f + 1) w e (.atom (.symbol y_sym)) = some yv := by
      match hy : e.get? y_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w e y_sym v hy⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w e y_sym hy (by decide)⟩

    -- (my-len y) converges to a specific integer k (consumed type-prescription
    -- + termination fact for my-len). Used by NODE 3 and NODE 4.
    have h_y_conv : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e yT = some av :=
      ⟨1, fun f hf => by
        obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
        exact ⟨yv, h_ye m⟩⟩
    obtain ⟨Nlen, k, hlen⟩ := h_mylen_int e yT h_y_conv

    -- The four tree nodes as subterm-rewrite facts (eval lhs = eval rhs).
    -- Shared convergence facts for the base-case nodes (existential, totality-sourced —
    -- the same style as the step case, NOT computed-and-matched).
    have hxc : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some xv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_xe g⟩
    have hyc : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some yv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ye g⟩
    have hxc' : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e xT = some av := hxc.imp fun _ h f hf => ⟨xv, h f hf⟩
    have hyc' : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e yT = some av := hyc.imp fun _ h f hf => ⟨yv, h f hf⟩
    -- (consp x) ⇒ nil  (recognizer/false: consp xv = nil from the case hypothesis).
    have hconspx : ∃ N, ∀ f ≥ N, evalOpt f w e
        (.cons (.atom (.symbol { name := "consp" })) (.cons xT .nil)) = some .nil := by
      have h := conv_builtin1 w e { name := "consp" } xT xv (Logic.consp xv)
        consp_not_special h_no_consp hxc (callBuiltin_consp xv)
      rwa [h_consp] at h
    -- NODE 1  definition:my-app (base): (my-app x y) ⇒ y
    --   [def:my-app unfold ; (consp x) ⇒ nil recognizer/false ; if-simplification ⇒ else=y].
    have node1 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf xT yT) = evalOpt f w e yT := by
      obtain ⟨Nr0, rv0, hr0⟩ := h_myapp_total e xT yT hxc' hyc'
      have hbody1 : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym, y_sym] [xv, yv]) my_appBody = some rv0 := by
        refine ⟨Nr0 + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_2 (g + 1) w e my_app_sym xT yT xv yv x_sym y_sym my_appBody
              my_app_not_special h_my_app (h_xe g) (h_ye g)]
        exact hr0 (g + 2) (by omega)
      exact fuel_chain_eq
        (re_unfold2_var w e my_app_sym x_sym y_sym xv yv my_appBody rv0 (by decide)
          my_app_not_special h_my_app my_appBody_fv my_appBody_nolet h_xe h_ye hbody1)
        (re_if_false w e (.cons (.atom (.symbol { name := "consp" })) (.cons xT .nil))
          (consOf (carOf xT) (appOf (cdrOf xT) yT)) yT yv hconspx hyc)
    -- NODE 2  definition:my-len (base): (my-len x) ⇒ '0
    --   [def:my-len unfold ; (consp x) ⇒ nil recognizer/false ; if-simplification ⇒ else='0].
    have node2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (lenOf xT) = evalOpt f w e q0 := by
      obtain ⟨Nr0, rv0, hr0⟩ := h_mylen_total e xT hxc'
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym] [xv]) my_lenBody = some rv0 := by
        refine ⟨Nr0 + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_1 (g + 1) w e my_len_sym xT xv x_sym my_lenBody
              my_len_not_special h_my_len (h_xe g)]
        exact hr0 (g + 2) (by omega)
      have hq0' : ∃ N, ∀ f ≥ N, evalOpt f w e q0 = some (.atom (.number (.int 0))) :=
        ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact evalOpt_quote g w e _⟩
      exact fuel_chain_eq
        (re_unfold1_var w e my_len_sym x_sym xv my_lenBody rv0
          my_len_not_special h_my_len my_lenBody_fv my_lenBody_nolet h_xe hbody)
        (re_if_false w e (.cons (.atom (.symbol { name := "consp" })) (.cons xT .nil))
          (plusOf q1 (lenOf (cdrOf xT))) q0 (.atom (.number (.int 0))) hconspx hq0')
    -- NODE 3  rewrite:unicity-of-0  (binary-+ '0 (my-len y)) ⇒ (my-len y)
    --   SCHEMATIC replay of ACL2's two sub-rewrites, with the REAL intermediate `(fix z)`
    --   (z := (my-len y), an integer by type-prescription:my-len):
    --     (A) rewrite:unicity-of-0  (binary-+ '0 z) ⇒ (fix z)
    --     (B) definition:fix        (fix z) ⇒ z   [unfold ; acl2-numberp recognizer ; if-true]
    --   NOT the collapsed `(+ 0 z) ⇒ z` value-match — `definition:fix` is replayed via the
    --   `fix` defun unfold, the recognizer combinator, and if-simplification, exactly the
    --   node chain the driver will emit.
    have hz : ∃ N, ∀ f ≥ N, evalOpt f w e (lenOf yT) = some (.atom (.number (.int k))) := ⟨Nlen, hlen⟩
    have hq0 : ∃ N, ∀ f ≥ N, evalOpt f w e q0 = some (.atom (.number (.int 0))) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact evalOpt_quote g w e _⟩
    -- (B) (fix z) ⇒ z.
    have node3B : ∃ N, ∀ f ≥ N, evalOpt f w e (fixOf (lenOf yT)) = evalOpt f w e (lenOf yT) := by
      -- fixBody at x ↦ int k converges to int k (acl2-numberp ⇒ t ; if-then ⇒ x).
      have hxk : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym] [.atom (.number (.int k))]) xT = some (.atom (.number (.int k))) :=
        ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                           exact evalOpt_var g w _ x_sym _ (bindArgs_x_x _)⟩
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym] [.atom (.number (.int k))]) fixBody = some (.atom (.number (.int k))) := by
        have hrec := re_acl2_numberp_int w (bindArgs [x_sym] [.atom (.number (.int k))]) xT k h_no_acl2numberp hxk
        have hif := re_if_true w (bindArgs [x_sym] [.atom (.number (.int k))])
          (.cons (.atom (.symbol { name := "acl2-numberp" })) (.cons xT .nil)) xT q0
          SExpr.t (.atom (.number (.int k))) hrec (by decide) hxk
        obtain ⟨Nif, hif'⟩ := hif; obtain ⟨Nx, hx'⟩ := hxk
        exact ⟨max Nif Nx, fun f hf => (hif' f (by omega)).trans (hx' f (by omega))⟩
      have unfold := evalOpt_unfold1_conv w e fix_sym x_sym fixBody (lenOf yT)
        (.atom (.number (.int k))) (.atom (.number (.int k))) fix_not_special h_fix fixBody_fv fixBody_nolet hz hbody
      have hif2 : ∃ N, ∀ f ≥ N,
          evalOpt f w e (substTerm [x_sym] [lenOf yT] fixBody) = evalOpt f w e (lenOf yT) := by
        rw [fixBody_subst]
        exact re_if_true w e (.cons (.atom (.symbol { name := "acl2-numberp" })) (.cons (lenOf yT) .nil))
          (lenOf yT) q0 SExpr.t (.atom (.number (.int k)))
          (re_acl2_numberp_int w e (lenOf yT) k h_no_acl2numberp hz) (by decide) hz
      exact fuel_chain_eq unfold hif2
    -- (A) (binary-+ '0 z) ⇒ (fix z): both converge to int k.
    have node3A : ∃ N, ∀ f ≥ N,
        evalOpt f w e (plusOf q0 (lenOf yT)) = evalOpt f w e (fixOf (lenOf yT)) := by
      have hplus : ∃ N, ∀ f ≥ N,
          evalOpt f w e (plusOf q0 (lenOf yT)) = some (.atom (.number (.int k))) :=
        conv_builtin2 w e { name := "binary-+" } q0 (lenOf yT)
          (.atom (.number (.int 0))) (.atom (.number (.int k))) (.atom (.number (.int k)))
          plus_not_special h_no_plus hq0 hz (by simp only [callBuiltin_plus, logic_plus_zero_int])
      obtain ⟨Npl, hpl⟩ := hplus; obtain ⟨Nb, hb⟩ := node3B; obtain ⟨Nz, hz'⟩ := hz
      refine ⟨max Npl (max Nb Nz), fun f hf => ?_⟩
      rw [hpl f (by omega), hb f (by omega), hz' f (by omega)]
    have node3 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (plusOf q0 (lenOf yT)) = evalOpt f w e (lenOf yT) :=
      fuel_chain_eq node3A node3B
    -- NODE 4  equal-self  (equal (my-len y) (my-len y)) ⇒ t  [my-len y converges]
    have node4 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (lenOf yT) (lenOf yT)) = some SExpr.t := by
      refine ⟨Nlen + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + Nlen + 1 := ⟨f - Nlen - 1, by omega⟩
      have hl : evalOpt (g + Nlen) w e (lenOf yT) = some (.atom (.number (.int k))) :=
        hlen (g + Nlen) (by omega)
      show evalOpt (g + Nlen + 1) w e
          (.cons (.atom (.symbol { name := "equal" })) (.cons (lenOf yT) (.cons (lenOf yT) .nil)))
          = some SExpr.t
      exact evalOpt_equal_self (g + Nlen) w e (lenOf yT) (.atom (.number (.int k))) hl h_no_equal

    -- Lift each node through the surrounding context by arity-specific
    -- congruence (the faithful replay of ACL2's congruence-through-context),
    -- then chain by transitivity.
    have c1 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (lenOf (appOf xT yT)) (plusOf (lenOf xT) (lenOf yT)))
        = evalOpt f w e (equalOf (lenOf yT) (plusOf (lenOf xT) (lenOf yT))) :=
      evalOpt_congr_binary_left w e { name := "equal" }
        (lenOf (appOf xT yT)) (lenOf yT) (plusOf (lenOf xT) (lenOf yT)) equal_not_special
        (evalOpt_congr_unary w e { name := "my-len" } (appOf xT yT) yT my_len_not_special node1)
    have c2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (lenOf yT) (plusOf (lenOf xT) (lenOf yT)))
        = evalOpt f w e (equalOf (lenOf yT) (plusOf q0 (lenOf yT))) :=
      evalOpt_congr_binary_right w e { name := "equal" }
        (lenOf yT) (plusOf (lenOf xT) (lenOf yT)) (plusOf q0 (lenOf yT)) equal_not_special
        (evalOpt_congr_binary_left w e { name := "binary-+" } (lenOf xT) q0 (lenOf yT) plus_not_special node2)
    have c3 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (lenOf yT) (plusOf q0 (lenOf yT)))
        = evalOpt f w e (equalOf (lenOf yT) (lenOf yT)) :=
      evalOpt_congr_binary_right w e { name := "equal" }
        (lenOf yT) (plusOf q0 (lenOf yT)) (lenOf yT) equal_not_special node3

    rw [formula_decomp]
    exact fuel_chain_eq (fuel_chain_eq (fuel_chain_eq c1 c2) c3) node4

  -- ── Subgoal *1/1 (step): consp xv ≠ nil, IH at cdr xv ───────────────────
  case step =>
    intro xv h_consp ih e h_xe
    -- ════════════════════════════════════════════════════════════════════════
    -- SCHEMATIC replay of *1/1. Each node applies its rune's combinator; values
    -- stay existential, sourced from TOTALITY (h_mylen_total / h_myapp_total) —
    -- NOT type-prescription, which *1/1 does not cite (only the base *1/2 does):
    --   node1 (def:my-app)   : re_unfold2_var ; re_if_true
    --   node2  (def:my-len)  : node2a (evalOpt_unfold1_conv ; re_if_true)
    --                          ; node2b (re_cdr_cons, lifted by congruence)
    --   node3 (def:my-len)   : re_unfold1_var ; re_if_true
    --   node4a (comm-of-+)   : re_plus_comm           (operands existential)
    --   node4b (comm-2-of-+) : re_plus_comm2          (UNCONDITIONAL, no int)
    --   node4c (IH solidify) : evalOpt_substTerm_subst1 + eval_equal_t_implies_eq
    --                          ; re_plus_comm  — the IH as a Γ fact, no arithmetic
    --   node5 (equal-self)   : A' converges (totality) + evalOpt_equal_self
    -- ════════════════════════════════════════════════════════════════════════
    -- value of y in e
    obtain ⟨yv, h_ye⟩ : ∃ yv, ∀ f, evalOpt (f + 1) w e (.atom (.symbol y_sym)) = some yv := by
      match hy : e.get? y_sym with
      | some v => exact ⟨v, fun f => evalOpt_var f w e y_sym v hy⟩
      | none => exact ⟨.nil, fun f => evalOpt_var_unbound f w e y_sym hy (by decide)⟩

    -- Shared convergence facts (driven by h_xe/h_ye + the consumed type fact).
    have hxc : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some xv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_xe g⟩
    have hyc : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some yv :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_ye g⟩
    -- (cdr x) ⇒ cdr xv
    have hcdrx : ∃ N, ∀ f ≥ N, evalOpt f w e (cdrOf xT) = some (Logic.cdr xv) :=
      conv_builtin1 w e { name := "cdr" } xT xv (Logic.cdr xv) cdr_not_special h_no_cdr hxc
        (callBuiltin_cdr xv)
    obtain ⟨Ncdr, hcdr⟩ := hcdrx
    obtain ⟨Ny0, hy0⟩ := hyc
    -- (my-len (cdr x)) ⇒ SOME V1 ;  (my-len y) ⇒ SOME V2   (TOTALITY — the step
    -- subgoal *1/1 cites no type-prescription; these runes need only convergence).
    obtain ⟨M1, V1, hk1⟩ := h_mylen_total e (cdrOf xT)
      ⟨Ncdr, fun f hf => ⟨Logic.cdr xv, hcdr f hf⟩⟩
    obtain ⟨M2, V2, hk2⟩ := h_mylen_total e yT
      ⟨Ny0, fun f hf => ⟨yv, hy0 f hf⟩⟩
    -- '1 ⇒ int 1
    have hq1 : ∃ N, ∀ f ≥ N, evalOpt f w e q1 = some (.atom (.number (.int 1))) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w e _⟩
    -- (binary-+ '1 (my-len (cdr x))) ⇒ plus (int 1) V1
    have hA : ∃ N, ∀ f ≥ N, evalOpt f w e (plusOf q1 (lenOf (cdrOf xT)))
        = some (Logic.plus (.atom (.number (.int 1))) V1) :=
      conv_builtin2 w e { name := "binary-+" } q1 (lenOf (cdrOf xT))
        (.atom (.number (.int 1))) V1
        (Logic.plus (.atom (.number (.int 1))) V1)
        plus_not_special h_no_plus hq1 ⟨M1, hk1⟩ (callBuiltin_plus _ _)

    -- consp xv = t  (step case: xv is a cons)
    have hct : Logic.consp xv = SExpr.t := by
      match xv with
      | .cons _ _ => rfl
      | .nil => exact absurd rfl h_consp
      | .atom _ => exact absurd rfl h_consp
    -- consp test convergence (truthy), in env e
    have hconspx : ∃ N, ∀ f ≥ N, evalOpt f w e
        (.cons (.atom (.symbol { name := "consp" })) (.cons xT .nil)) = some (Logic.consp xv) :=
      conv_builtin1 w e { name := "consp" } xT xv (Logic.consp xv) consp_not_special h_no_consp hxc
        (callBuiltin_consp xv)
    -- (car x) ⇒ car xv
    have hcarx : ∃ N, ∀ f ≥ N, evalOpt f w e (carOf xT) = some (Logic.car xv) :=
      conv_builtin1 w e { name := "car" } xT xv (Logic.car xv) car_not_special h_no_car hxc
        (callBuiltin_car xv)
    -- (my-app (cdr x) y) ⇒ SOME rv   (my-app TOTALITY, not functionality)
    obtain ⟨Nrv, rv, hrv'⟩ := h_myapp_total e (cdrOf xT) yT
      ⟨Ncdr, fun f hf => ⟨Logic.cdr xv, hcdr f hf⟩⟩ ⟨Ny0, fun f hf => ⟨yv, hy0 f hf⟩⟩
    have hrv : ∃ N, ∀ f ≥ N, evalOpt f w e (appOf (cdrOf xT) yT) = some rv := ⟨Nrv, hrv'⟩
    -- (my-len (my-app (cdr x) y)) ⇒ SOME k_rv   (my-len TOTALITY; used by node5)
    obtain ⟨Nkrv, k_rv, hkrv'⟩ := h_mylen_total e (appOf (cdrOf xT) yT)
      ⟨Nrv, fun f hf => ⟨rv, hrv' f hf⟩⟩
    have hk_rv : ∃ N, ∀ f ≥ N,
        evalOpt f w e (lenOf (appOf (cdrOf xT) yT)) = some k_rv := ⟨Nkrv, hkrv'⟩


    -- NODE 1  definition:my-app (recursive case) (my-app x y) ⇒ (cons (car x) (my-app (cdr x) y))
    --   [consp x ⇒ t, if-then]
    -- (cons (car x) (my-app (cdr x) y)) ⇒ cons(car xv, rv), reused for LHS-body and RHS.
    have hcons : ∃ N, ∀ f ≥ N,
        evalOpt f w e (consOf (carOf xT) (appOf (cdrOf xT) yT))
        = some (.cons (Logic.car xv) rv) :=
      conv_builtin2 w e { name := "cons" } (carOf xT) (appOf (cdrOf xT) yT)
        (Logic.car xv) rv (.cons (Logic.car xv) rv) cons_not_special h_no_cons hcarx hrv rfl
    -- NODE 1 = :DEFINITION my-app unfold (my-app x y ⇒ body) ; if-simplification.
    have node1 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (appOf xT yT)
        = evalOpt f w e (consOf (carOf xT) (appOf (cdrOf xT) yT)) := by
      -- body's value in bindArgs is existential — from my-app totality via the
      -- definition-unfold relation, not computed.
      obtain ⟨Nr0, rv0, hr0⟩ := h_myapp_total e xT yT
        (hxc.imp fun N h f hf => ⟨xv, h f hf⟩) ⟨Ny0, fun f hf => ⟨yv, hy0 f hf⟩⟩
      have hrv0 : ∃ N, ∀ f ≥ N, evalOpt f w e (appOf xT yT) = some rv0 := ⟨Nr0, hr0⟩
      have hbody1 : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym, y_sym] [xv, yv]) my_appBody = some rv0 := by
        obtain ⟨Nr, hr⟩ := hrv0
        refine ⟨Nr + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_2 (g + 1) w e my_app_sym xT yT xv yv x_sym y_sym my_appBody
              my_app_not_special h_my_app (h_xe g) (h_ye g)]
        exact hr (g + 2) (by omega)
      exact fuel_chain_eq
        (re_unfold2_var w e my_app_sym x_sym y_sym xv yv my_appBody rv0 (by decide)
          my_app_not_special h_my_app my_appBody_fv my_appBody_nolet h_xe h_ye hbody1)
        (re_if_true w e (.cons (.atom (.symbol { name := "consp" })) (.cons xT .nil))
          (consOf (carOf xT) (appOf (cdrOf xT) yT)) yT (Logic.consp xv)
          (.cons (Logic.car xv) rv) hconspx (by rw [hct]; decide) hcons)
    -- NODE 2  definition:my-len (recursive) (my-len (cons (car x) (my-app (cdr x) y)))
    --   ⇒ (binary-+ '1 (my-len (my-app (cdr x) y)))   [consp⇒t, if-then, cdr-cons]
    -- node2 = node2a (my-len T unfold: consp T ⇒ t, if-then) ; node2b (cdr-cons exposed).
    -- T = (cons (car x) (my-app (cdr x) y)), Tval = cons(car xv, rv) (hcons).
    have node2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (lenOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))
        = evalOpt f w e (plusOf q1 (lenOf (appOf (cdrOf xT) yT))) := by
      -- (cdr T) ⇒ rv  (in e), reused for node2a's then-branch and node2b cdr-cons
      have hcdrT : ∃ N, ∀ f ≥ N,
          evalOpt f w e (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT))) = some rv :=
        conv_builtin1 w e { name := "cdr" } (consOf (carOf xT) (appOf (cdrOf xT) yT))
          (.cons (Logic.car xv) rv) rv cdr_not_special h_no_cdr hcons rfl
      -- my-len T converges to SOME value vkk (TOTALITY, not type-prescription —
      -- *1/1 doesn't cite type-prescription); the unfolded body value is existential.
      obtain ⟨Ncons, hconsspec⟩ := hcons
      obtain ⟨Nkk, vkk, hkk⟩ := h_mylen_total e (consOf (carOf xT) (appOf (cdrOf xT) yT))
        ⟨Ncons, fun f hf => ⟨.cons (Logic.car xv) rv, hconsspec f hf⟩⟩
      have hbodyT : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym] [.cons (Logic.car xv) rv]) my_lenBody = some vkk := by
        refine ⟨max Nkk Ncons + 1, fun f hf => ?_⟩
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [← evalOpt_defn_1 (g + 1) w e my_len_sym
              (consOf (carOf xT) (appOf (cdrOf xT) yT)) (.cons (Logic.car xv) rv)
              x_sym my_lenBody my_len_not_special h_my_len (hconsspec (g + 1) (by omega))]
        exact hkk (g + 2) (by omega)
      -- my-len (cdr T) converges to SOME value vcdr (TOTALITY)
      obtain ⟨Ncdr', hcdrTspec⟩ := hcdrT
      obtain ⟨Nkcdr, vcdr, hkcdr⟩ := h_mylen_total e
        (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))
        ⟨Ncdr', fun f hf => ⟨rv, hcdrTspec f hf⟩⟩
      -- node2a: :DEFINITION my-len unfold on compound arg T (the eventual substTerm
      -- unfold lemma) ; if-simplification (consp T ⇒ t).  Values existential, sourced
      -- from TOTALITY — no type-prescription (faithful to *1/1's runes).
      have node2a : ∃ N, ∀ f ≥ N,
          evalOpt f w e (lenOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))
          = evalOpt f w e (plusOf q1 (lenOf (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT))))) :=
        fuel_chain_eq
          (evalOpt_unfold1_conv w e my_len_sym x_sym my_lenBody
            (consOf (carOf xT) (appOf (cdrOf xT) yT)) (.cons (Logic.car xv) rv)
            vkk my_len_not_special h_my_len
            (fun s hs => by simpa using my_lenBody_fv s hs) my_lenBody_nolet
            ⟨Ncons, hconsspec⟩ hbodyT)
          (re_if_true w e
            (.cons (.atom (.symbol { name := "consp" }))
              (.cons (consOf (carOf xT) (appOf (cdrOf xT) yT)) .nil))
            (plusOf q1 (lenOf (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT))))) q0
            (Logic.consp (.cons (Logic.car xv) rv))
            (Logic.plus (.atom (.number (.int 1))) vcdr)
            (conv_builtin1 w e { name := "consp" } (consOf (carOf xT) (appOf (cdrOf xT) yT))
              (.cons (Logic.car xv) rv) (Logic.consp (.cons (Logic.car xv) rv))
              consp_not_special h_no_consp ⟨Ncons, hconsspec⟩ (callBuiltin_consp _))
            rfl
            (conv_builtin2 w e { name := "binary-+" } q1
              (lenOf (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT))))
              (.atom (.number (.int 1))) vcdr
              (Logic.plus (.atom (.number (.int 1))) vcdr)
              plus_not_special h_no_plus hq1 ⟨Nkcdr, hkcdr⟩ (callBuiltin_plus _ _)))
      -- node2b: cdr-cons rune (cdr (cons (car x) (my-app (cdr x) y)) ⇒ (my-app (cdr x) y))
      -- via `re_cdr_cons` (the `logic_cdr_cons` dispatch entry, operands existential),
      -- lifted through (+ 1 (my-len ·)) by congruence. Operand convergences
      -- `hcarx`/`hrv` are sourced from totality (my-app totality for `hrv`).
      have node2b : ∃ N, ∀ f ≥ N,
          evalOpt f w e (plusOf q1 (lenOf (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))))
          = evalOpt f w e (plusOf q1 (lenOf (appOf (cdrOf xT) yT))) :=
        evalOpt_congr_binary_right w e { name := "binary-+" } q1
          (lenOf (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))) (lenOf (appOf (cdrOf xT) yT))
          plus_not_special
          (evalOpt_congr_unary w e { name := "my-len" }
            (cdrOf (consOf (carOf xT) (appOf (cdrOf xT) yT))) (appOf (cdrOf xT) yT)
            my_len_not_special
            (re_cdr_cons w e (carOf xT) (appOf (cdrOf xT) yT) (Logic.car xv) rv
              h_no_cdr h_no_cons hcarx hrv))
      exact fuel_chain_eq node2a node2b
    -- NODE 3  definition:my-len  (my-len x) ⇒ (binary-+ '1 (my-len (cdr x)))
    --   = :DEFINITION unfold (my-len x ⇒ body) ; if-simplification (consp x ⇒ t).
    have node3 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (lenOf xT) = evalOpt f w e (plusOf q1 (lenOf (cdrOf xT))) := by
      -- the body's value in bindArgs is existential — from my-len TOTALITY via the
      -- definition-unfold relation, NOT type-prescription (absent in *1/1).
      obtain ⟨Nk, vk, hk⟩ := h_mylen_total e xT
        ⟨1, fun f hf => ⟨xv, by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact h_xe g⟩⟩
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [x_sym] [xv]) my_lenBody = some vk :=
        ⟨max Nk 1, fun f hf => by
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
          rw [← evalOpt_defn_1 (g + 1) w e my_len_sym xT xv x_sym my_lenBody
                my_len_not_special h_my_len (h_xe g)]
          exact hk (g + 2) (by omega)⟩
      exact fuel_chain_eq
        (re_unfold1_var w e my_len_sym x_sym xv my_lenBody vk
          my_len_not_special h_my_len my_lenBody_fv my_lenBody_nolet h_xe hbody)
        (re_if_true w e (.cons (.atom (.symbol { name := "consp" })) (.cons xT .nil))
          (plusOf q1 (lenOf (cdrOf xT))) q0 (Logic.consp xv)
          (Logic.plus (.atom (.number (.int 1))) V1)
          hconspx (by rw [hct]; decide) hA)
    -- NODE 4a  commutativity-of-+  ⇒ apply the `commutativity-of-+` combinator.
    have node4a : ∃ N, ∀ f ≥ N,
        evalOpt f w e (plusOf (plusOf q1 (lenOf (cdrOf xT))) (lenOf yT))
        = evalOpt f w e (plusOf (lenOf yT) (plusOf q1 (lenOf (cdrOf xT)))) :=
      re_plus_comm w e (plusOf q1 (lenOf (cdrOf xT))) (lenOf yT)
        (Logic.plus (.atom (.number (.int 1))) V1) V2 h_no_plus hA ⟨M2, hk2⟩
    -- NODE 4b  commutativity-2-of-+  (+ (my-len y) (+ '1 (my-len (cdr x))))
    --   ⇒ (+ '1 (+ (my-len y) (my-len (cdr x))))
    have node4b : ∃ N, ∀ f ≥ N,
        evalOpt f w e (plusOf (lenOf yT) (plusOf q1 (lenOf (cdrOf xT))))
        = evalOpt f w e (plusOf q1 (plusOf (lenOf yT) (lenOf (cdrOf xT)))) :=
      re_plus_comm2 w e (lenOf yT) q1 (lenOf (cdrOf xT))
        V2 (.atom (.number (.int 1))) V1 h_no_plus
        ⟨M2, hk2⟩ hq1 ⟨M1, hk1⟩
    -- NODE 4c  rewriting-equivalence (solidify), justified by the INDUCTION HYPOTHESIS:
    --   (+ (my-len y) (my-len (cdr x))) ⇒ (my-len (my-app (cdr x) y))
    have node4c : ∃ N, ∀ f ≥ N,
        evalOpt f w e (plusOf (lenOf yT) (lenOf (cdrOf xT)))
        = evalOpt f w e (lenOf (appOf (cdrOf xT) yT)) := by
      -- SCHEMATIC solidify (rewriting-equivalence justified by the IH). The IH `ih`
      -- (P at cdr xv), instantiated in e' = e.insert x (cdr xv) ( = envUpdate e [x]
      -- [cdr xv] ), is converted to the goal-env terms by the substTerm SUBSTITUTION
      -- LEMMA (`evalOpt_substTerm_subst1`, arg (cdr x) ⇒ cdr xv): bridging the whole
      -- formula gives `eval_e (equal (my-len (my-app (cdr x) y)) (+ (my-len (cdr x))
      -- (my-len y))) = t`. `eval_equal_t_implies_eq` turns that into the IH as an
      -- eval-equality; `commutativity-of-+` (the rune that commutes the IH literal)
      -- reorders. NO functionality, NO integer arithmetic — the solidify fact IS the
      -- IH. All convergences come from TOTALITY (h_mylen_total / h_myapp_total).
      -- x ⇒ cdr xv in e'.
      have hx_e' : ∀ f, evalOpt (f + 1) w (e.insert x_sym (Logic.cdr xv))
          (.atom (.symbol x_sym)) = some (Logic.cdr xv) := fun f =>
        evalOpt_var f w _ x_sym (Logic.cdr xv) (by simp)
      obtain ⟨Nih, hih⟩ := ih (e.insert x_sym (Logic.cdr xv)) hx_e'
      -- Substitution lemma: substTerm [x] [cdr x] formula evaluated in e = formula in
      -- e' (= envUpdate e [x] [cdr xv], defeq to e.insert x (cdr xv)).
      obtain ⟨Nbr, hbr⟩ := evalOpt_substTerm_subst1 w e x_sym (cdrOf xT) (Logic.cdr xv)
        my_len_my_appFormula (by decide) ⟨Ncdr, hcdr⟩
      -- substTerm [x] [cdr x] formula = (equal (my-len (my-app (cdr x) y))
      --                                        (+ (my-len (cdr x)) (my-len y))).
      have hsubst : substTerm [x_sym] [cdrOf xT] my_len_my_appFormula
          = equalOf (lenOf (appOf (cdrOf xT) yT))
                    (plusOf (lenOf (cdrOf xT)) (lenOf yT)) := rfl
      -- eval_e (equal A_e B_e) = t.
      have hEQt : ∃ N, ∀ f ≥ N, evalOpt f w e
          (equalOf (lenOf (appOf (cdrOf xT) yT)) (plusOf (lenOf (cdrOf xT)) (lenOf yT)))
          = some SExpr.t :=
        ⟨max Nbr Nih, fun f hf => by
          rw [← hsubst]; exact (hbr f (by omega)).trans (hih f (by omega))⟩
      -- Convergences in e via TOTALITY (no functionality).
      obtain ⟨Napp, vrv, happ⟩ := h_myapp_total e (cdrOf xT) yT
        ⟨Ncdr, fun f hf => ⟨Logic.cdr xv, hcdr f hf⟩⟩ ⟨Ny0, fun f hf => ⟨yv, hy0 f hf⟩⟩
      obtain ⟨NA, V1, hA1⟩ := h_mylen_total e (appOf (cdrOf xT) yT)
        ⟨Napp, fun f hf => ⟨vrv, happ f hf⟩⟩
      obtain ⟨Nlc, Vc, hlc⟩ := h_mylen_total e (cdrOf xT)
        ⟨Ncdr, fun f hf => ⟨Logic.cdr xv, hcdr f hf⟩⟩
      obtain ⟨Nly, Vy, hly⟩ := h_mylen_total e yT ⟨Ny0, fun f hf => ⟨yv, hy0 f hf⟩⟩
      obtain ⟨NB, hB1⟩ : ∃ N, ∀ f ≥ N, evalOpt f w e (plusOf (lenOf (cdrOf xT)) (lenOf yT))
          = some (Logic.plus Vc Vy) :=
        conv_builtin2 w e { name := "binary-+" } (lenOf (cdrOf xT)) (lenOf yT) Vc Vy
          (Logic.plus Vc Vy) plus_not_special h_no_plus ⟨Nlc, hlc⟩ ⟨Nly, hly⟩ (callBuiltin_plus _ _)
      obtain ⟨NEQ, hEQ⟩ := hEQt
      -- IH as an eval-equality in e (eval_equal_t on the bridged formula).
      obtain ⟨NIH, hIH⟩ : ∃ N, ∀ f ≥ N, evalOpt f w e (lenOf (appOf (cdrOf xT) yT))
          = evalOpt f w e (plusOf (lenOf (cdrOf xT)) (lenOf yT)) := by
        refine ⟨max NA (max NB NEQ), fun f hf => ?_⟩
        have hV := eval_equal_t_implies_eq f w e
          (lenOf (appOf (cdrOf xT) yT)) (plusOf (lenOf (cdrOf xT)) (lenOf yT))
          V1 (Logic.plus Vc Vy) (hA1 f (by omega)) (hB1 f (by omega)) h_no_equal
          (hEQ (f + 1) (by omega))
        rw [hA1 f (by omega), hB1 f (by omega), hV]
      -- node4c = commutativity-of-+ (reorder the IH literal) ; IH (reversed).
      exact fuel_chain_eq
        (re_plus_comm w e (lenOf yT) (lenOf (cdrOf xT)) Vy Vc h_no_plus ⟨Nly, hly⟩ ⟨Nlc, hlc⟩)
        ⟨NIH, fun f hf => (hIH f hf).symm⟩
    -- NODE 5  equal-self  (equal A' A') ⇒ t
    -- A' = (binary-+ '1 (my-len (my-app (cdr x) y)))
    have hAprime : ∃ N, ∀ f ≥ N,
        evalOpt f w e (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
        = some (Logic.plus (.atom (.number (.int 1))) k_rv) :=
      conv_builtin2 w e { name := "binary-+" } q1 (lenOf (appOf (cdrOf xT) yT))
        (.atom (.number (.int 1))) k_rv
        (Logic.plus (.atom (.number (.int 1))) k_rv)
        plus_not_special h_no_plus hq1 hk_rv (callBuiltin_plus _ _)
    have node5 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                               (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))) = some SExpr.t := by
      obtain ⟨Na, ha⟩ := hAprime
      refine ⟨Na + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_equal_self g w e (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
        (Logic.plus (.atom (.number (.int 1))) k_rv) (ha g (by omega)) h_no_equal

    -- Lift each node through its context path and chain (tree order):
    -- A-side:   F0 →(node1) F1 →(node2) F2 ;  B-side: F2 →(node3) F3 →(4a) F4 →(4b) F5 →(4c) F6 ; equal-self.
    have c1 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (lenOf (appOf xT yT)) (plusOf (lenOf xT) (lenOf yT)))
        = evalOpt f w e (equalOf (lenOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))
                                 (plusOf (lenOf xT) (lenOf yT))) :=
      evalOpt_congr_binary_left w e { name := "equal" }
        (lenOf (appOf xT yT)) (lenOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))
        (plusOf (lenOf xT) (lenOf yT)) equal_not_special
        (evalOpt_congr_unary w e { name := "my-len" }
          (appOf xT yT) (consOf (carOf xT) (appOf (cdrOf xT) yT)) my_len_not_special node1)
    have c2 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (lenOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))
                               (plusOf (lenOf xT) (lenOf yT)))
        = evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                                 (plusOf (lenOf xT) (lenOf yT))) :=
      evalOpt_congr_binary_left w e { name := "equal" }
        (lenOf (consOf (carOf xT) (appOf (cdrOf xT) yT)))
        (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
        (plusOf (lenOf xT) (lenOf yT)) equal_not_special node2
    have c3 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                               (plusOf (lenOf xT) (lenOf yT)))
        = evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                                 (plusOf (plusOf q1 (lenOf (cdrOf xT))) (lenOf yT))) :=
      evalOpt_congr_binary_right w e { name := "equal" }
        (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
        (plusOf (lenOf xT) (lenOf yT))
        (plusOf (plusOf q1 (lenOf (cdrOf xT))) (lenOf yT)) equal_not_special
        (evalOpt_congr_binary_left w e { name := "binary-+" }
          (lenOf xT) (plusOf q1 (lenOf (cdrOf xT))) (lenOf yT) plus_not_special node3)
    have c4 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                               (plusOf (plusOf q1 (lenOf (cdrOf xT))) (lenOf yT)))
        = evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                                 (plusOf (lenOf yT) (plusOf q1 (lenOf (cdrOf xT))))) :=
      evalOpt_congr_binary_right w e { name := "equal" }
        (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
        (plusOf (plusOf q1 (lenOf (cdrOf xT))) (lenOf yT))
        (plusOf (lenOf yT) (plusOf q1 (lenOf (cdrOf xT)))) equal_not_special node4a
    have c5 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                               (plusOf (lenOf yT) (plusOf q1 (lenOf (cdrOf xT)))))
        = evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                                 (plusOf q1 (plusOf (lenOf yT) (lenOf (cdrOf xT))))) :=
      evalOpt_congr_binary_right w e { name := "equal" }
        (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
        (plusOf (lenOf yT) (plusOf q1 (lenOf (cdrOf xT))))
        (plusOf q1 (plusOf (lenOf yT) (lenOf (cdrOf xT)))) equal_not_special node4b
    have c6 : ∃ N, ∀ f ≥ N,
        evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                               (plusOf q1 (plusOf (lenOf yT) (lenOf (cdrOf xT)))))
        = evalOpt f w e (equalOf (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
                                 (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))) :=
      evalOpt_congr_binary_right w e { name := "equal" }
        (plusOf q1 (lenOf (appOf (cdrOf xT) yT)))
        (plusOf q1 (plusOf (lenOf yT) (lenOf (cdrOf xT))))
        (plusOf q1 (lenOf (appOf (cdrOf xT) yT))) equal_not_special
        (evalOpt_congr_binary_right w e { name := "binary-+" }
          q1 (plusOf (lenOf yT) (lenOf (cdrOf xT))) (lenOf (appOf (cdrOf xT) yT)) plus_not_special node4c)

    rw [formula_decomp]
    exact fuel_chain_eq (fuel_chain_eq (fuel_chain_eq (fuel_chain_eq
      (fuel_chain_eq (fuel_chain_eq c1 c2) c3) c4) c5) c6) node5

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
    world.defs[({ name := "equal" } : Symbol)]? = none := by decide

theorem world_no_consp :
    world.defs[({ name := "consp" } : Symbol)]? = none := by decide

theorem world_no_plus :
    world.defs[({ name := "binary-+" } : Symbol)]? = none := by decide

theorem world_no_cdr :
    world.defs[({ name := "cdr" } : Symbol)]? = none := by decide

theorem world_no_car :
    world.defs[({ name := "car" } : Symbol)]? = none := by decide

theorem world_no_cons :
    world.defs[({ name := "cons" } : Symbol)]? = none := by decide
theorem world_no_acl2numberp :
    world.defs[({ name := "acl2-numberp" } : Symbol)]? = none := by decide
theorem world_has_fix :
    world.defs[fix_sym]? = some ([x_sym], fixBody) := by decide

/-- The mirror theorem for the concrete `world`, sorry-free (axioms:
    `{propext, Classical.choice, Quot.sound}`) — both subgoals of the ACL2 proof
    tree are replayed. It still TAKES the consumed ACL2 facts `h_mylen_int`
    (type-prescription:my-len, base case only) and `h_mylen_total` / `h_myapp_total`
    (my-len/my-app admission ⇒ totality) as hypotheses; discharging them concretely
    for `world` (by replaying the type-prescription corollary + the admissions) is
    the remaining work, tracked separately. So this is a proof "modulo those ACL2
    facts" — not yet an unconditional import. -/
theorem my_len_my_app (env : Env)
    (h_mylen_int : ∀ (e' : Env) (arg : SExpr),
      (∃ M, ∀ f ≥ M, ∃ av, evalOpt f world e' arg = some av) →
      ∃ M, ∃ k : Int, ∀ f ≥ M, evalOpt f world e' (lenOf arg) = some (.atom (.number (.int k))))
    (h_mylen_total : ∀ (e' : Env) (arg : SExpr),
      (∃ M, ∀ f ≥ M, ∃ av, evalOpt f world e' arg = some av) →
      ∃ M, ∃ av, ∀ f ≥ M, evalOpt f world e' (lenOf arg) = some av)
    (h_myapp_total : ∀ (e' : Env) (a b : SExpr),
      (∃ M, ∀ f ≥ M, ∃ av, evalOpt f world e' a = some av) →
      (∃ M, ∀ f ≥ M, ∃ bv, evalOpt f world e' b = some bv) →
      ∃ M, ∃ rv, ∀ f ≥ M, evalOpt f world e' (appOf a b) = some rv) :
    ∃ N, ∀ f, f ≥ N → evalOpt f world env my_len_my_appFormula = some SExpr.t :=
  my_len_my_app_generic world env
    world_has_my_app world_has_my_len world_no_equal world_no_consp
    world_no_plus world_no_cdr world_no_car world_no_cons
    world_no_acl2numberp world_has_fix
    h_mylen_int h_mylen_total h_myapp_total

/-! ## Native-theorem bridge

We lift the ACL2 mirror to an IDIOMATIC Lean theorem about `List`:
`(xs ++ ys).length = xs.length + ys.length`. The recipe (per
`docs/comms/2026-03-22_acl2-lean-bridge.md`): a TYPE morphism `enc : List SExpr
→ SExpr` plus a SIMULATION over the function structure (correspondence lemmas:
`evalOpt`'s `my-app`/`my-len` simulate `++`/`length` under `enc`). This lifts the
ACL2 theorem without redoing the property proof.

First, DISCHARGERS for the consumed facts (so the mirror for `world` is
UNCONDITIONAL): ACL2 functions are total over all objects, so these are
existential inductions over arbitrary `SExpr` — proofs, not s-expr algorithms. -/

/-- Convergence to SOME value (value possibly per-fuel) ⇒ to a FIXED value. -/
private theorem conv_fix {w : World} {e : Env} {t : SExpr}
    (h : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e t = some av) :
    ∃ av, ∃ M, ∀ f ≥ M, evalOpt f w e t = some av := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨av, hav⟩ := hM M (Nat.le_refl M)
  exact ⟨av, M, fun f hf => evalOpt_ge_fuel M f w e t av hav hf⟩

/-- `my-len arg` returns an integer (induction on the argument VALUE). -/
private theorem dis_mylen_int_val (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none) :
    ∀ (av : SExpr) (e' : Env) (arg : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' arg = some av) →
    ∃ N, ∃ k : Int, 0 ≤ k ∧
      ∀ f ≥ N, evalOpt f w e' (lenOf arg) = some (.atom (.number (.int k))) := by
  refine acl2_induction_consp (fun av => ∀ (e' : Env) (arg : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' arg = some av) →
    ∃ N, ∃ k : Int, 0 ≤ k ∧ ∀ f ≥ N, evalOpt f w e' (lenOf arg)
      = some (.atom (.number (.int k)))) ?base ?step
  · intro av hconsp e' arg harg
    have hx_ba : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [x_sym] [av]) xT = some av :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ x_sym av (bindArgs_x_x av)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [av]) (conspOf xT) = some .nil := by
      have h := conv_builtin1 w _ { name := "consp" } xT av (Logic.consp av)
        consp_not_special h_no_consp hx_ba (callBuiltin_consp av)
      rwa [hconsp] at h
    have hq0_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [av]) q0 = some (.atom (.number (.int 0))) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [av]) my_lenBody = some (.atom (.number (.int 0))) := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [x_sym] [av]) (conspOf xT)
        (plusOf q1 (lenOf (cdrOf xT))) q0 (.atom (.number (.int 0))) hconspx_ba hq0_ba
      obtain ⟨Nq, hq⟩ := hq0_ba
      exact ⟨max Ni Nq, fun f hf => (hi f (by omega)).trans (hq f (by omega))⟩
    obtain ⟨N, h⟩ := conv_defn_1 w e' my_len_sym arg av x_sym my_lenBody
      (.atom (.number (.int 0))) my_len_not_special h_mylen harg hbody
    exact ⟨N, 0, by omega, h⟩
  · intro av hconsp ih e' arg harg
    obtain ⟨hd, tl, rfl⟩ : ∃ hd tl, av = .cons hd tl := by
      match av with
      | .cons a d => exact ⟨a, d, rfl⟩
      | .nil => exact absurd rfl hconsp
      | .atom _ => exact absurd rfl hconsp
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [.cons hd tl]) xT = some (.cons hd tl) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ x_sym _ (bindArgs_x_x _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [.cons hd tl]) (conspOf xT)
        = some (Logic.consp (.cons hd tl)) :=
      conv_builtin1 w _ { name := "consp" } xT (.cons hd tl) (Logic.consp (.cons hd tl))
        consp_not_special h_no_consp hx_ba (callBuiltin_consp _)
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [.cons hd tl]) (cdrOf xT) = some tl := by
      have h := conv_builtin1 w _ { name := "cdr" } xT (.cons hd tl) (Logic.cdr (.cons hd tl))
        cdr_not_special h_no_cdr hx_ba (callBuiltin_cdr _)
      simpa [Logic.cdr] using h
    have hq1_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [.cons hd tl]) q1 = some (.atom (.number (.int 1))) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    obtain ⟨Nk, k, hknn, hk⟩ := ih (bindArgs [x_sym] [.cons hd tl]) (cdrOf xT) hcdrx_ba
    have hsum : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [.cons hd tl]) (plusOf q1 (lenOf (cdrOf xT)))
        = some (.atom (.number (.int (1 + k)))) := by
      have h := conv_builtin2 w _ { name := "binary-+" } q1 (lenOf (cdrOf xT))
        (.atom (.number (.int 1))) (.atom (.number (.int k)))
        (Logic.plus (.atom (.number (.int 1))) (.atom (.number (.int k))))
        plus_not_special h_no_plus hq1_ba ⟨Nk, hk⟩ (callBuiltin_plus _ _)
      rwa [logic_plus_int] at h
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym] [.cons hd tl]) my_lenBody
        = some (.atom (.number (.int (1 + k)))) := by
      obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [x_sym] [.cons hd tl]) (conspOf xT)
        (plusOf q1 (lenOf (cdrOf xT))) q0 (Logic.consp (.cons hd tl))
        (.atom (.number (.int (1 + k)))) hconspx_ba rfl hsum
      obtain ⟨Ns, hs⟩ := hsum
      exact ⟨max Ni Ns, fun f hf => (hi f (by omega)).trans (hs f (by omega))⟩
    obtain ⟨N, h⟩ := conv_defn_1 w e' my_len_sym arg (.cons hd tl) x_sym my_lenBody
      (.atom (.number (.int (1 + k)))) my_len_not_special h_mylen harg hbody
    exact ⟨N, 1 + k, by omega, h⟩

/-- `my-app a b` converges (induction on the first argument's VALUE). -/
private theorem dis_myapp_total_val (w : World)
    (h_myapp : w.defs.get? my_app_sym = some ([x_sym, y_sym], my_appBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
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
      have h := conv_builtin1 w _ { name := "consp" } xT av1 (Logic.consp av1)
        consp_not_special h_no_consp hx_ba (callBuiltin_consp av1)
      rwa [hconsp] at h
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [av1, av2]) my_appBody = some av2 := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [x_sym, y_sym] [av1, av2]) (conspOf xT)
        (consOf (carOf xT) (appOf (cdrOf xT) yT)) yT av2 hconspx_ba hy_ba
      obtain ⟨Ny, hy⟩ := hy_ba
      exact ⟨max Ni Ny, fun f hf => (hi f (by omega)).trans (hy f (by omega))⟩
    exact conv_defn_2 w e' my_app_sym a b av1 av2 x_sym y_sym my_appBody av2
      my_app_not_special h_myapp ha hb hbody
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
      conv_builtin1 w _ { name := "consp" } xT (.cons hd tl) (Logic.consp (.cons hd tl))
        consp_not_special h_no_consp hx_ba (callBuiltin_consp _)
    have hcarx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (carOf xT) = some hd := by
      have h := conv_builtin1 w _ { name := "car" } xT (.cons hd tl) (Logic.car (.cons hd tl))
        car_not_special h_no_car hx_ba (callBuiltin_car _)
      simpa [Logic.car] using h
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (cdrOf xT) = some tl := by
      have h := conv_builtin1 w _ { name := "cdr" } xT (.cons hd tl) (Logic.cdr (.cons hd tl))
        cdr_not_special h_no_cdr hx_ba (callBuiltin_cdr _)
      simpa [Logic.cdr] using h
    obtain ⟨rv', hrec⟩ := ih (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (cdrOf xT) yT av2
      hcdrx_ba hy_ba
    refine ⟨.cons hd rv', ?_⟩
    have hthen : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2])
          (consOf (carOf xT) (appOf (cdrOf xT) yT)) = some (.cons hd rv') :=
      conv_builtin2 w _ { name := "cons" } (carOf xT) (appOf (cdrOf xT) yT)
        hd rv' (.cons hd rv') cons_not_special h_no_cons hcarx_ba hrec rfl
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) my_appBody
        = some (.cons hd rv') := by
      obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [x_sym, y_sym] [.cons hd tl, av2]) (conspOf xT)
        (consOf (carOf xT) (appOf (cdrOf xT) yT)) yT (Logic.consp (.cons hd tl))
        (.cons hd rv') hconspx_ba rfl hthen
      obtain ⟨Nt, ht⟩ := hthen
      exact ⟨max Ni Nt, fun f hf => (hi f (by omega)).trans (ht f (by omega))⟩
    exact conv_defn_2 w e' my_app_sym a b (.cons hd tl) av2 x_sym y_sym my_appBody
      (.cons hd rv') my_app_not_special h_myapp ha hb hbody

private theorem dis_mylen_int (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (e' : Env) (arg : SExpr)
    (h : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' arg = some av) :
    ∃ M, ∃ k : Int, ∀ f ≥ M, evalOpt f w e' (lenOf arg)
      = some (.atom (.number (.int k))) := by
  obtain ⟨av, hav⟩ := conv_fix h
  obtain ⟨N, k, _, hk⟩ := dis_mylen_int_val w h_mylen h_no_consp h_no_plus h_no_cdr av e' arg hav
  exact ⟨N, k, hk⟩

/-- The NONNEGATIVE-integer discharge for `my-len` — the full content of its
    emitted type-prescription corollary (integerp AND ≥ 0), consumed by the
    native-bridge validation of the DRIVER's conditional mirror. -/
theorem dis_mylen_int_nonneg (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (e' : Env) (arg : SExpr)
    (h : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' arg = some av) :
    ∃ M, ∃ k : Int, 0 ≤ k ∧
      ∀ f ≥ M, evalOpt f w e' (lenOf arg) = some (.atom (.number (.int k))) := by
  obtain ⟨av, hav⟩ := conv_fix h
  exact dis_mylen_int_val w h_mylen h_no_consp h_no_plus h_no_cdr av e' arg hav

private theorem dis_mylen_total (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (e' : Env) (arg : SExpr)
    (h : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' arg = some av) :
    ∃ M, ∃ av, ∀ f ≥ M, evalOpt f w e' (lenOf arg) = some av := by
  obtain ⟨M, k, hk⟩ := dis_mylen_int w h_mylen h_no_consp h_no_plus h_no_cdr e' arg h
  exact ⟨M, .atom (.number (.int k)), hk⟩

private theorem dis_myapp_total (w : World)
    (h_myapp : w.defs.get? my_app_sym = some ([x_sym, y_sym], my_appBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (e' : Env) (a b : SExpr)
    (ha : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e' a = some av)
    (hb : ∃ M, ∀ f ≥ M, ∃ bv, evalOpt f w e' b = some bv) :
    ∃ M, ∃ rv, ∀ f ≥ M, evalOpt f w e' (appOf a b) = some rv := by
  obtain ⟨av, hav⟩ := conv_fix ha; obtain ⟨bv, hbv⟩ := conv_fix hb
  obtain ⟨rv, N, h⟩ := dis_myapp_total_val w h_myapp h_no_consp h_no_cdr h_no_car h_no_cons av e' a b bv hav hbv
  exact ⟨N, rv, h⟩

/-- The mirror for `world`, UNCONDITIONAL (consumed facts discharged — closes #23). -/
theorem my_len_my_app_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → evalOpt f world env my_len_my_appFormula = some SExpr.t :=
  my_len_my_app env
    (dis_mylen_int world world_has_my_len world_no_consp world_no_plus world_no_cdr)
    (dis_mylen_total world world_has_my_len world_no_consp world_no_plus world_no_cdr)
    (dis_myapp_total world world_has_my_app world_no_consp world_no_cdr
      world_no_car world_no_cons)

/-! ### Driver-form dischargers (consumed by `Imported/NativeMirrors`)

The DRIVER's conditional mirror states its hypotheses in v-FIXED form
(`∃ N v, ∀ f ≥ N, … = some v`) and its type-prescription hypothesis with the
function-application convergence as antecedent. These restate the hand
dischargers above in exactly those shapes (over `world`; the catalog transfers
them to the log-derived world by `evalOpt_defs_ext`). -/

/-- `fix`'s body converges in `bindArgs` for an ARBITRARY argument value
    (`acl2-numberp` decides the branch; both branches converge). -/
private theorem fixBody_conv (w : World)
    (h_no_acl2numberp : w.defs.get? ({ name := "acl2-numberp" } : Symbol) = none)
    (av : SExpr) :
    ∃ bv, ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [x_sym] [av]) fixBody = some bv := by
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [x_sym] [av]) xT = some av :=
    ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w _ x_sym _ (bindArgs_x_x _)⟩
  have hcond : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [x_sym] [av])
      (.cons (.atom (.symbol { name := "acl2-numberp" })) (.cons xT .nil))
      = some (Logic.acl2Numberp av) :=
    conv_builtin1 w _ { name := "acl2-numberp" } xT av (Logic.acl2Numberp av)
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
      (.cons (.atom (.symbol { name := "if" }))
        (.cons (.cons (.atom (.symbol { name := "acl2-numberp" })) (.cons xT .nil))
          (.cons xT (.cons q0 .nil)))) = some (.atom (.number (.int 0)))
    rw [evalOpt_if_false g w _ _ xT q0 (by rw [hc g (by omega), hnil])]
    obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
    exact evalOpt_quote g2 w _ _

/-- Driver-shape totality for `my-len`. -/
theorem drv_total_mylen (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (e' : Env) (a0 : SExpr)
    (h : ∃ N v, ∀ f ≥ N, evalOpt f w e' a0 = some v) :
    ∃ N v, ∀ f ≥ N, evalOpt f w e' (lenOf a0) = some v := by
  obtain ⟨N, v, hv⟩ := h
  exact dis_mylen_total w h_mylen h_no_consp h_no_plus h_no_cdr e' a0 ⟨N, fun f hf => ⟨v, hv f hf⟩⟩

/-- Driver-shape totality for `my-app`. -/
theorem drv_total_myapp (w : World)
    (h_myapp : w.defs.get? my_app_sym = some ([x_sym, y_sym], my_appBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (e' : Env) (a0 a1 : SExpr)
    (h0 : ∃ N v, ∀ f ≥ N, evalOpt f w e' a0 = some v)
    (h1 : ∃ N v, ∀ f ≥ N, evalOpt f w e' a1 = some v) :
    ∃ N v, ∀ f ≥ N, evalOpt f w e' (appOf a0 a1) = some v := by
  obtain ⟨N0, v0, hv0⟩ := h0; obtain ⟨N1, v1, hv1⟩ := h1
  exact dis_myapp_total w h_myapp h_no_consp h_no_cdr h_no_car h_no_cons e' a0 a1 ⟨N0, fun f hf => ⟨v0, hv0 f hf⟩⟩
    ⟨N1, fun f hf => ⟨v1, hv1 f hf⟩⟩

/-- Driver-shape totality for `fix` (non-recursive: definition unfold + the
    body's convergence on the argument's value). -/
theorem drv_total_fix (w : World)
    (h_fix : w.defs.get? fix_sym = some ([x_sym], fixBody))
    (h_no_acl2numberp : w.defs.get? ({ name := "acl2-numberp" } : Symbol) = none)
    (e' : Env) (a0 : SExpr)
    (h : ∃ N v, ∀ f ≥ N, evalOpt f w e' a0 = some v) :
    ∃ N v, ∀ f ≥ N, evalOpt f w e' (fixOf a0) = some v := by
  obtain ⟨N, av, hav⟩ := h
  obtain ⟨bv, hbody⟩ := fixBody_conv w h_no_acl2numberp av
  obtain ⟨Nf, hNf⟩ := conv_defn_1 w e' fix_sym a0 av x_sym fixBody bv
    fix_not_special h_fix ⟨N, hav⟩ hbody
  exact ⟨Nf, bv, hNf⟩

/-- Driver-shape type prescription for `my-len`: any value `(my-len a0)`
    converges to satisfies the emitted TP corollary (an integer, not below 0).
    The antecedent asserts only the APPLICATION's convergence; argument
    strictness (`conv_arg1_of_conv_app`) recovers `a0`'s, and the nonnegative
    discharge pins the value. -/
theorem drv_tp_mylen (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (lenOf a0) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
        Logic.not (Logic.lt v (.atom (.number (.int 0))))
      else SExpr.nil) = SExpr.t := by
  have harg : ∃ N, ∀ f ≥ N, ∃ u, evalOpt f w e' a0 = some u :=
    conv_arg1_of_conv_app w e' { name := "my-len" } a0 v (by decide) h
  obtain ⟨M, k, hk0, hk⟩ := dis_mylen_int_nonneg w h_mylen h_no_consp h_no_plus h_no_cdr e' a0 harg
  have hv : v = .atom (.number (.int k)) := val_unique h ⟨M, hk⟩
  subst hv
  simp only [Logic.integerp, Logic.toBool, Logic.lt_int, Logic.not, cond_true]
  rw [if_neg (by omega : ¬ k < 0)]
  rfl

/-! ### The type morphism + simulation -/

-- The TYPE morphism: the shared library's (`Imported/Lifting`).
open ACL2.Lifting (enc)

/-- SIMULATION: `my-app` over encoded lists computes `++` under `enc` — ONE
    instantiation of the library's name-generic `corr_append_enc`. -/
private theorem corr_app_enc (w : World)
    (h_myapp : w.defs.get? my_app_sym = some ([x_sym, y_sym], my_appBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a b : SExpr) (ys : List SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' b = some (enc ys)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (appOf a b) = some (enc (xs ++ ys)) :=
  ACL2.Lifting.corr_append_enc w "my-app" (by decide) h_myapp
    h_no_consp h_no_cdr h_no_car h_no_cons

/-- SIMULATION: `my-len` over encoded lists computes `List.length` under
    `enc` — ONE instantiation of the library's name-generic `corr_len_enc`. -/
private theorem corr_len_enc (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (lenOf a)
      = some (.atom (.number (.int xs.length))) :=
  ACL2.Lifting.corr_len_enc w "my-len" (by decide) h_mylen
    h_no_consp h_no_plus h_no_cdr

/-- The native assembly, PARAMETERIZED by the mirror: any proof of the mirror
    statement over `w` (hand-built or driver-replayed) yields the native
    theorem. The mirror is consumed at exactly ONE point — this is the seam the
    catalog (`Imported/NativeMirrors`) plugs the driver's mirror into. -/
theorem my_len_my_app_native_of_mirror (w : World)
    (h_mylen : w.defs.get? my_len_sym = some ([x_sym], my_lenBody))
    (h_myapp : w.defs.get? my_app_sym = some ([x_sym, y_sym], my_appBody))
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (hmirror : ∀ env : Env,
      ∃ N, ∀ f, f ≥ N → evalOpt f w env my_len_my_appFormula = some SExpr.t)
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
    have h := conv_builtin2 w e { name := "binary-+" } (lenOf xT) (lenOf yT)
      (.atom (.number (.int (xs.length : Int)))) (.atom (.number (.int (ys.length : Int))))
      (Logic.plus (.atom (.number (.int (xs.length : Int)))) (.atom (.number (.int (ys.length : Int)))))
      plus_not_special h_no_plus ⟨NLx, hLx⟩ ⟨NLy, hLy⟩ (callBuiltin_plus _ _)
    rwa [logic_plus_int] at h
  -- mirror: formula ⇒ t ; eval_equal_t splits the equality, the two values coincide
  -- the spine ender: the mirror's equal ⇒ t + intRep decode, then the Nat cast
  have hint : ((xs ++ ys).length : Int) = (xs.length : Int) + (ys.length : Int) :=
    ACL2.Lifting.native_of_mirror_equal w e ACL2.Lifting.intRep
      (lenOf (appOf xT yT)) (plusOf (lenOf xT) (lenOf yT))
      ((xs ++ ys).length : Int) ((xs.length : Int) + (ys.length : Int))
      h_no_equal ⟨NL, hL⟩ ⟨NR, hR⟩ (hmirror e)
  omega

/-- **The native theorem we want**, in idiomatic Lean — `List.length_append`,
    proved via the ACL2 oracle (NOT by the native list induction), here
    instantiated with the HAND mirror. A bug anywhere in stages 1–7 of the
    pipeline makes this fail to typecheck. -/
theorem my_len_my_app_native (xs ys : List SExpr) :
    (xs ++ ys).length = xs.length + ys.length :=
  my_len_my_app_native_of_mirror world world_has_my_len world_has_my_app
    world_no_equal world_no_consp world_no_plus world_no_cdr world_no_car
    world_no_cons my_len_my_app_uncond xs ys

end ACL2.Worlds.Simple
