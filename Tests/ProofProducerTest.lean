/-
  Tests for the proof-producing checker (`ACL2Lean/Replay/ProofProducer.lean`).

  Two groups:
  - Term-mode hand proofs (Test 1–5): exactly the shapes the producer emits,
    written by hand against the EvalLemmas, as a readable specification.
  - MetaM tests (`section MetaMTests`): build proofs via
    `proveNode`/`proveLiteralChain`/`liftCongr`/`synthTotality1` and
    kernel-check them with `check`.

  Importing this module from `Tests.lean` is also what pulls `ProofProducer`
  into the `just ci` build graph (the production module is not imported by the
  `ACL2Lean` root library).
-/
import ACL2Lean.Replay.ProofProducer

namespace ACL2.Replay.ProofProducer

open ACL2 ACL2.Replay Lean Elab Meta

-- ============================================================
-- Validation: term-mode proofs using our lemmas directly.
-- These demonstrate what the proof-producing checker emits.
-- ============================================================

-- Test 1: equal-self on ground terms
-- The checker would emit exactly this term.
example : evalOpt 2 World.empty {}
    (.cons (.atom (.symbol { name := "equal" }))
      (.cons (.atom (.number (.int 1)))
        (.cons (.atom (.number (.int 1))) .nil)))
    = some SExpr.t :=
  evalOpt_equal_self 1 World.empty {}
    (.atom (.number (.int 1)))
    (.atom (.number (.int 1)))
    (by simp [evalOpt, evalOptStep])
    (by show World.empty.defs[({ name := "equal" } : Symbol)]? = none; simp [World.empty])

-- Test 2: IF with nil test takes else branch
-- Simpler than consp — just IF with a constant test.
example : evalOpt 2 World.empty {}
    (.cons (.atom (.symbol { name := "if" }))
      (.cons .nil
        (.cons (.atom (.number (.int 42)))
          (.cons (.atom (.number (.int 0))) .nil))))
    = some (.atom (.number (.int 0))) :=
  evalOpt_if_false 1 World.empty {}
    .nil (.atom (.number (.int 42))) (.atom (.number (.int 0)))
    (by simp [evalOpt, evalOptStep])

-- Test 3: definition expansion of a 1-arg function
-- World with identity function: (defun id (x) x)
private def idWorld : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert { name := "id" } ([{ name := "x" }], .atom (.symbol { name := "x" }))

-- eval(id 42) = eval(42) = some 42
example : evalOpt 3 idWorld {}
    (.cons (.atom (.symbol { name := "id" }))
      (.cons (.atom (.number (.int 42))) .nil))
    = some (.atom (.number (.int 42))) :=
  evalOpt_defn_1 2 idWorld {}
    { name := "id" }
    (.atom (.number (.int 42)))
    (.atom (.number (.int 42)))
    { name := "x" }
    (.atom (.symbol { name := "x" }))
    (by decide) -- not special
    (by show idWorld.defs[({ name := "id" } : Symbol)]? = _
        simp [idWorld])
    (by simp [evalOpt, evalOptStep]) -- arg 42 evals to 42
  |>.trans (by -- body x in {x→42} evals to 42
    simp [evalOpt, evalOptStep, bindArgs])

-- Test 4: Chaining two steps — definition expansion followed by equal-self.
-- World: (defun id (x) x)
-- Theorem: (EQUAL (id 42) 42) = T
example : evalOpt 4 idWorld {}
    (.cons (.atom (.symbol { name := "equal" }))
      (.cons (.cons (.atom (.symbol { name := "id" }))
              (.cons (.atom (.number (.int 42))) .nil))
        (.cons (.atom (.number (.int 42))) .nil)))
    = some SExpr.t := by
  rw [evalOpt_builtin_2 3 idWorld {} { name := "equal" }
      (.cons (.atom (.symbol { name := "id" })) (.cons (.atom (.number (.int 42))) .nil))
      (.atom (.number (.int 42)))
      (.atom (.number (.int 42)))  -- v_lhs: id 42 evaluates to 42
      (.atom (.number (.int 42)))  -- v_rhs: 42 evaluates to 42
      (by decide)  -- "equal" not special
      (by show idWorld.defs[({ name := "equal" } : Symbol)]? = none; simp [idWorld])
      -- LHS arg: (id 42) evaluates to 42
      (by rw [evalOpt_defn_1 2 idWorld {} { name := "id" }
              (.atom (.number (.int 42))) (.atom (.number (.int 42)))
              { name := "x" } (.atom (.symbol { name := "x" }))
              (by decide)
              (by show idWorld.defs[({ name := "id" } : Symbol)]? = _; simp [idWorld])
              (by simp [evalOpt, evalOptStep])]
          simp [evalOpt, evalOptStep, bindArgs])
      -- RHS arg: 42 evaluates to 42
      (by simp [evalOpt, evalOptStep])]
  -- Now goal: some (callBuiltin "equal" [42, 42]) = some T
  simp [callBuiltin_equal]

-- Test 5: Definition expansion with IF resolution.
-- World with: (defun f (x) (if (consp x) (quote 1) (quote 0)))
-- Prove: eval(f NIL) = some 0  (consp nil = nil → else branch → 0)
-- This chains: defn expand → IF-false → quote.
private def testWorld5 : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert { name := "f" } ([{ name := "x" }],
      .cons (.atom (.symbol { name := "if" }))
        (.cons (.cons (.atom (.symbol { name := "consp" }))
                (.cons (.atom (.symbol { name := "x" })) .nil))
          (.cons (.cons (.atom (.symbol { name := "quote" }))
                  (.cons (.atom (.number (.int 1))) .nil))
            (.cons (.cons (.atom (.symbol { name := "quote" }))
                    (.cons (.atom (.number (.int 0))) .nil))
              .nil))))

-- The body term, written out explicitly
private def testBody5 : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
    (.cons (.cons (.atom (.symbol { name := "consp" }))
            (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.cons (.atom (.symbol { name := "quote" }))
              (.cons (.atom (.number (.int 1))) .nil))
        (.cons (.cons (.atom (.symbol { name := "quote" }))
                (.cons (.atom (.number (.int 0))) .nil))
          .nil)))

example : evalOpt 5 testWorld5 {}
    (.cons (.atom (.symbol { name := "f" }))
      (.cons .nil .nil))
    = some (.atom (.number (.int 0))) := by
  -- Step 1: T4 (defn expand): eval(f nil) = eval(body) in {x→nil}
  have h_defn : testWorld5.defs.get? { name := "f" } = some ([{ name := "x" }], testBody5) := by
    show testWorld5.defs[({ name := "f" } : Symbol)]? = _; simp [testWorld5, testBody5]
  rw [evalOpt_defn_1 4 testWorld5 {} { name := "f" }
      .nil .nil { name := "x" } testBody5
      (by decide) h_defn
      (by simp [evalOpt, evalOptStep])]
  -- Goal: evalOpt 4 testWorld5 (bindArgs [x] [nil]) testBody5 = some 0
  -- Body is (IF (CONSP x) (QUOTE 1) (QUOTE 0)) in env {x→nil}
  -- Step 2: T5 (if-false) — consp nil = nil, take else branch
  -- But to apply T5, we need to unfold testBody5 first
  unfold testBody5
  -- Now apply T5 with consp nil = nil as the test
  rw [evalOpt_if_false 3 testWorld5 (bindArgs [{ name := "x" }] [.nil])
      (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 1))) .nil))
      (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 0))) .nil))
      (by -- eval consp(x) in {x→nil} = some nil
          rw [evalOpt_builtin_1 2 testWorld5 _ { name := "consp" }
              (.atom (.symbol { name := "x" })) .nil
              (by decide)
              (by show testWorld5.defs[({ name := "consp" } : Symbol)]? = none
                  simp [testWorld5])
              (evalOpt_var 1 testWorld5 _ { name := "x" } .nil
                (by show (bindArgs [{ name := "x" }] [.nil]).get? { name := "x" } = some .nil
                    simp [bindArgs]))]
          simp [callBuiltin_consp, Logic.consp])]
  -- Goal: evalOpt 3 testWorld5 {x→nil} (QUOTE 0) = some 0
  exact evalOpt_quote 2 testWorld5 _ (.atom (.number (.int 0)))

-- ============================================================
-- MetaM proof construction tests.
-- These verify the proof producers emit correct symbolic proofs.
-- ============================================================

section MetaMTests

-- Test: proveNode for equal-self with a VARIABLE (not ground!)
-- Proof tree node: (EQUAL X X) → (QUOTE T) where X is a free variable
elab "#test_symbolic_equal_self" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let x : SExpr := .atom (.symbol { name := "x" })
    let equal_x_x : SExpr := .cons (.atom (.symbol { name := "equal" }))
      (.cons x (.cons x .nil))
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    let node : ProofNode := .node ("equal-self", "NIL") equal_x_x quote_t []
    let proof ← proveNode ctx node
    let _ ← check proof
    logInfo m!"symbolic equal-self OK: {← inferType proof}"

#test_symbolic_equal_self

-- Test: proveLiteralChain with equal-self on a variable
elab "#test_symbolic_chain" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let x : SExpr := .atom (.symbol { name := "x" })
    let equal_x_x : SExpr := .cons (.atom (.symbol { name := "equal" }))
      (.cons x (.cons x .nil))
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    let node : ProofNode := .node ("equal-self", "NIL") equal_x_x quote_t []
    let proof ← proveLiteralChain ctx equal_x_x [node]
    let _ ← check proof
    logInfo m!"symbolic chain OK: {← inferType proof}"

#test_symbolic_chain

-- Test: end-to-end theorem production
-- Produces a named Lean theorem from a proof tree, kernel-checked.
elab "#test_add_theorem" : command => do
  Elab.Command.liftTermElabM do
    let x : SExpr := .atom (.symbol { name := "x" })
    let formula : SExpr := .cons (.atom (.symbol { name := "equal" }))
      (.cons x (.cons x .nil))
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    let nodes : List ProofNode := [
      .node ("equal-self", "NIL") formula quote_t []
    ]
    addTheoremFromChain (Lean.mkConst ``World.empty) World.empty
      #[``World.empty] formula nodes `ACL2.Replay.ProofProducer.equal_x_x_auto

#test_add_theorem

-- Verify: the auto-generated theorem is usable in downstream proofs
example (env : Env) : ∃ N, ∀ f ≥ N, evalOpt f World.empty env
    (.cons (.atom (.symbol { name := "equal" }))
      (.cons (.atom (.symbol { name := "x" }))
        (.cons (.atom (.symbol { name := "x" })) .nil)))
    = some SExpr.t :=
  equal_x_x_auto env

-- B0 test: liftCongr lifts a node proof at a SUBTERM position.
-- equal-self rewrites (EQUAL X X) → (QUOTE T) inside (CONSP (EQUAL X X));
-- liftCongr must produce eval(CONSP (EQUAL X X)) = eval(CONSP (QUOTE T)).
elab "#test_lift_congr_subterm" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let x : SExpr := .atom (.symbol { name := "x" })
    let equal_x_x : SExpr := .cons (.atom (.symbol { name := "equal" }))
      (.cons x (.cons x .nil))
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    -- the node proof: eval(EQUAL X X) = eval(QUOTE T)
    let node : ProofNode := .node ("equal-self", "NIL") equal_x_x quote_t []
    let nodeProof ← proveNode ctx node
    -- the enclosing term: (CONSP (EQUAL X X))
    let consp_eq : SExpr := .cons (.atom (.symbol { name := "consp" }))
      (.cons equal_x_x .nil)
    let (newTerm, stepProof) ← liftCongr ctx consp_eq equal_x_x quote_t nodeProof
    let _ ← check stepProof
    logInfo m!"liftCongr OK: rewrote to {repr newTerm}\n  {← inferType stepProof}"

#test_lift_congr_subterm

-- Recognizer (structural): (CONSP (CONS X Y)) → 'T, no context facts.
-- The handler discharges the call via the general consp-of-cons fact.
elab "#test_recognizer_structural" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let x : SExpr := .atom (.symbol { name := "x" })
    let y : SExpr := .atom (.symbol { name := "y" })
    let cons_x_y : SExpr := .cons (.atom (.symbol { name := "cons" }))
      (.cons x (.cons y .nil))
    let consp_cons_xy : SExpr := .cons (.atom (.symbol { name := "consp" }))
      (.cons cons_x_y .nil)
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    let node : ProofNode :=
      .node ("fake-rune-for-anonymous-enabled-rule", "NIL") consp_cons_xy quote_t []
    let proof ← proveNode ctx node
    let _ ← check proof
    logInfo m!"recognizer structural OK: {← inferType proof}"

#test_recognizer_structural

-- Recognizer (context fact): (CONSP X) → 'NIL where X is a variable.
-- ctx carries the shared value of X (= nil, via evalOpt_var_unbound) and a
-- fact proof `Logic.consp nil = nil`. The handler matches the fact (defeq to
-- the callBuiltin-level equation) to discharge the call.
elab "#test_recognizer_context_fact" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let xSym : Symbol := { name := "x" }
    -- Shared value of X: nil. Convergence proof: ∀ f, evalOpt (f+1) ... = some nil.
    let convProof ← Term.elabTerm
      (← `(fun (f : Nat) => evalOpt_var_unbound f World.empty {} { name := "x" }
            (by simp) (by decide))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let convProof ← instantiateMVars convProof
    let nilVal := reflectSExpr SExpr.nil
    -- Fact: Logic.consp nil = nil (defeq to callBuiltin "consp" [nil] = nil).
    let factProof ← Term.elabTerm
      (← `((by decide : Logic.consp SExpr.nil = SExpr.nil))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let factProof ← instantiateMVars factProof
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
      vars := [(xSym, nilVal, convProof)]
      facts := [factProof]
    }
    let x : SExpr := .atom (.symbol { name := "x" })
    let consp_x : SExpr := .cons (.atom (.symbol { name := "consp" }))
      (.cons x .nil)
    let quote_nil : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.nil .nil)
    let node : ProofNode :=
      .node ("fake-rune-for-anonymous-enabled-rule", "NIL") consp_x quote_nil []
    let proof ← proveNode ctx node
    let _ ← check proof
    logInfo m!"recognizer context-fact OK: {← inferType proof}"

#test_recognizer_context_fact

-- definition node (base-case shape), reproducing the hand proof `h_node2`:
-- world has `my-len` with body (IF (CONSP X) (BINARY-+ '1 (MY-LEN (CDR X))) (QUOTE 0));
-- node (MY-LEN X) → (QUOTE 0); ctx binds X to nil with a `consp nil = nil` fact.
-- The IF takes the else (constant) branch, so the recursive then-branch is
-- never entered. Handler must produce ∃N∀f≥N, eval (MY-LEN X) = eval (QUOTE 0).
private def defnTestBody : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
    (.cons (.cons (.atom (.symbol { name := "consp" }))
            (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.cons (.atom (.symbol { name := "binary-+" }))
              (.cons (.cons (.atom (.symbol { name := "quote" }))
                       (.cons (.atom (.number (.int 1))) .nil))
                (.cons (.cons (.atom (.symbol { name := "my-len" }))
                         (.cons (.cons (.atom (.symbol { name := "cdr" }))
                                  (.cons (.atom (.symbol { name := "x" })) .nil)) .nil))
                  .nil)))
        (.cons (.cons (.atom (.symbol { name := "quote" }))
                (.cons (.atom (.number (.int 0))) .nil))
          .nil)))

private def defnTestWorld : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert { name := "my-len" } ([{ name := "x" }], defnTestBody)

elab "#test_definition_node" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let xSym : Symbol := { name := "x" }
    -- Shared value of X: nil. Convergence proof ∀ f, eval (f+1) ... X = some nil.
    let convProof ← Term.elabTerm
      (← `(fun (f : Nat) => evalOpt_var_unbound f defnTestWorld {} { name := "x" }
            (by simp) (by decide))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let convProof ← instantiateMVars convProof
    let nilVal := reflectSExpr SExpr.nil
    -- Fact: Logic.consp nil = nil (defeq to callBuiltin "consp" [nil] = nil).
    let factProof ← Term.elabTerm
      (← `((by decide : Logic.consp SExpr.nil = SExpr.nil))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let factProof ← instantiateMVars factProof
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``defnTestWorld
      world := defnTestWorld
      envExpr := emptyEnv
      worldUnfoldNames := #[``defnTestWorld, ``defnTestBody]
      vars := [(xSym, nilVal, convProof)]
      facts := [factProof]
    }
    let x : SExpr := .atom (.symbol { name := "x" })
    let my_len_x : SExpr := .cons (.atom (.symbol { name := "my-len" }))
      (.cons x .nil)
    let quote_0 : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons (.atom (.number (.int 0))) .nil)
    -- if-simplification child: rhs is the chosen (else) branch (QUOTE 0).
    let ifChild : ProofNode :=
      .node ("if-simplification", "NIL") defnTestBody quote_0 []
    let node : ProofNode :=
      .node ("definition", "my-len") my_len_x quote_0 [ifChild]
    let proof ← proveNode ctx node
    let _ ← check proof
    logInfo m!"definition node OK: {← inferType proof}"

#test_definition_node

-- synthTotality1: synthesize the totality / type-prescription theorem for a
-- 1-arg structurally recursive function and kernel-check it. Uses a small
-- test world holding `my-len` (same body as SimpleWorld's), demonstrating the
-- SAME routine reproduces what `my_len_total` proves by hand — no hardcoded
-- function/formal names; detection-driven from the body shape.
private def totalityTestBody : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
    (.cons (.cons (.atom (.symbol { name := "consp" }))
            (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.cons (.atom (.symbol { name := "binary-+" }))
              (.cons (.cons (.atom (.symbol { name := "quote" }))
                       (.cons (.atom (.number (.int 1))) .nil))
                (.cons (.cons (.atom (.symbol { name := "my-len" }))
                         (.cons (.cons (.atom (.symbol { name := "cdr" }))
                                  (.cons (.atom (.symbol { name := "x" })) .nil)) .nil))
                  .nil)))
        (.cons (.cons (.atom (.symbol { name := "quote" }))
                (.cons (.atom (.number (.int 0))) .nil)) .nil)))

private def totalityTestWorld : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert { name := "my-len" } ([{ name := "x" }], totalityTestBody)

elab "#test_synth_totality1" : command => do
  Elab.Command.liftTermElabM do
    let proof ← synthTotality1 totalityTestWorld (Lean.mkConst ``totalityTestWorld)
      #[``totalityTestWorld, ``totalityTestBody] { name := "my-len" }
    let _ ← check proof
    let ty ← inferType proof
    logInfo m!"synthTotality1 OK: {ty}"
    -- Confirm the produced type matches the `my_len_total`-shaped statement:
    -- ∀ val, ∃ k, ∃ N, ∀ f ≥ N,
    --   evalOpt f w (bindArgs [x] [val]) totalityTestBody = some (int k).
    let expected ← Term.elabTerm
      (← `(∀ val : SExpr, ∃ k : Int, ∃ N, ∀ f ≥ N,
            evalOpt f totalityTestWorld (bindArgs [({ name := "x" } : Symbol)] [val])
              totalityTestBody = some (.atom (.number (.int k))))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    unless ← Meta.isDefEq ty expected do
      throwError "synthTotality1: produced type does not match expected statement:\n\
        produced: {ty}\n  expected: {expected}"
    logInfo m!"synthTotality1: produced type matches the my_len_total statement shape."

#test_synth_totality1

-- Frontier hard-fail check: a non-structural / wrong-shape function must be
-- rejected (no sorry, no hardcoding). Here `id` is not of the IF/CONSP shape.
private def idTestWorld : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert { name := "id" } ([{ name := "x" }], .atom (.symbol { name := "x" }))

elab "#test_synth_totality1_frontier" : command => do
  Elab.Command.liftTermElabM do
    let ok ← (do
      let _ ← synthTotality1 idTestWorld (Lean.mkConst ``idTestWorld)
        #[``idTestWorld] { name := "id" }
      pure true) <|> pure false
    if ok then
      throwError "synthTotality1 should have hard-failed on non-recursive `id`"
    logInfo m!"synthTotality1 correctly hard-failed at the frontier (non-IF body)."

#test_synth_totality1_frontier

-- proveConvergesExist on a recursive CALL `(MY-LEN X)`: the converger drives off
-- `synthTotality1` to learn `MY-LEN` is total/integer-valued, and produces a
-- kernel-checked convergence-to-integer proof for the call. Exercised end-to-end
-- through `proveNode` on an `equal-self` node `(EQUAL (MY-LEN X) (MY-LEN X)) → 'T`
-- whose LHS argument is the recursive call (previously unsupported by
-- `proveConverges`, since `(MY-LEN X)` is a CALL). No hardcoded names.
elab "#test_equal_self_on_recursive_call" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``totalityTestWorld
      world := totalityTestWorld
      envExpr := emptyEnv
      worldUnfoldNames := #[``totalityTestWorld, ``totalityTestBody]
    }
    let x : SExpr := .atom (.symbol { name := "x" })
    let my_len_x : SExpr := .cons (.atom (.symbol { name := "my-len" }))
      (.cons x .nil)
    let equal_mlx_mlx : SExpr := .cons (.atom (.symbol { name := "equal" }))
      (.cons my_len_x (.cons my_len_x .nil))
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    let node : ProofNode :=
      .node ("equal-self", "NIL") equal_mlx_mlx quote_t []
    let proof ← proveNode ctx node
    let _ ← check proof
    logInfo m!"equal-self on (MY-LEN X) OK: {← inferType proof}"

#test_equal_self_on_recursive_call

end MetaMTests

end ACL2.Replay.ProofProducer
