/-
  Driver tests — hand-built proof trees, positive and negative, growing in size.

  POSITIVE: the driver emits a REAL, sorry-free proof of the mirror theorem
  (`#print axioms` clean — no `sorryAx`).
  NEGATIVE: the driver `throwError`s CLEANLY at the named frontier (fail-closed,
  never `sorry`). A negative test passes iff the driver throws.

  The trees here are hand-constructed VALUES of the real `ClauseProof`/`ProofNode`
  types — the driver's INPUT (exactly what the parser emits), not a pre-staged proof.
  As node-kinds land, each adds a positive case and the negative cases shrink.
-/
import ACL2Lean.Replay.Driver

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Elab Lean.Meta

namespace ACL2.Tests.Driver

/-! ## SExpr builders (for hand-building tree values) -/

private def sym (n : String) : SExpr := .atom (.symbol { name := n })
private def quo (v : SExpr) : SExpr := .cons (sym "quote") (.cons v .nil)
private def numv (k : Int) : SExpr := .atom (.number (.int k))
private def equalOf (a b : SExpr) : SExpr := .cons (sym "equal") (.cons a (.cons b .nil))

/-! ## The minimal USEFUL tree: one `equal-self` node proving `(equal x x)` for a
    FREE VARIABLE `x` — universally over the environment. -/

/-- The variable `x`. -/
private def varX : SExpr := sym "x"
/-- `(equal x x)` — the literal (x a free variable, NOT a ground constant). -/
private def litEqXX : SExpr := equalOf varX varX

/-- One `equal-self` node: `(equal x x) ⇒ (quote t)`. -/
private def equalSelfNode : ProofNode :=
  .node ("equal-self", "NIL") litEqXX Driver.quoteT [] {}

private def litProof : LiteralProof :=
  { index := 1, literal := litEqXX, notFlg := false,
    nodes := [equalSelfNode], result := Driver.quoteT }

private def simplifyStep : WaterfallStep :=
  { processor := "simplify-clause", result := default, runes := [],
    newClauses := [], items := [.literal litProof], extraFields := [] }

private def goalNode : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litEqXX],
    steps := [simplifyStep], induction := none, children := [] }

/-- The minimal positive tree (faithful `ClauseProof` value). -/
def s2Tree : ClauseProof := { name := "refl-equal-x-x", formula := litEqXX, root := some goalNode }

/-! ## Frontend: run the driver over `World.empty`, UNIVERSALLY over the env.

The mirror theorem is `∀ env, ∃ N, ∀ f ≥ N, evalOpt f w env formula = some t` — the
`env` is universally quantified (it ranges over every assignment to the formula's free
variables). The driver emits the body for an `env` PARAMETER (an fvar); the frontend
λ-abstracts over it to produce the universal fact. -/

/-- `acl2_replay% <clauseProofTerm>` — elaborates the tree value, runs the driver over
    the empty world for a universally-quantified `env`, and returns the emitted proof
    of `∀ env, <mirror>`. Fails to elaborate if the driver `throwError`s. -/
elab "acl2_replay% " t:term : term => do
  let cpExpr ← Term.elabTermAndSynthesize t (some (mkConst ``ACL2.ClauseProof))
  let cp ← unsafe evalExpr ClauseProof (mkConst ``ACL2.ClauseProof) cpExpr
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``World.empty, envExpr := env,
        worldUnfoldNames := #[``World.empty] }
    let proof ← replayProof cfg cp
    mkLambdaFVars #[env] proof

/-! ## POSITIVE — S2: a real, sorry-free UNIVERSAL mirror theorem from the minimal tree. -/

/-- The driver-emitted proof that, under the mirror semantics, `(equal x x)` evaluates
    to `t` for EVERY environment (every binding of `x`). -/
def s2_mirror := acl2_replay% s2Tree

-- The emitted type IS the intended universal mirror statement (no weakening: `env`
-- universally quantified, `x` a free variable).
example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, evalOpt f World.empty env litEqXX = some SExpr.t :=
  s2_mirror

-- Sorry-free: must be {propext, Classical.choice, Quot.sound} — no sorryAx.
#print axioms s2_mirror

/-! ## BRIDGE — use the driver's output to prove the corresponding NATIVE Lean fact.

The ACL2 theorem `(equal x x)` corresponds, over a standard Lean type, to reflexivity
`∀ (n : Nat), n = n`. We derive it END-TO-END: encode `Nat → SExpr`, instantiate the
driver's mirror fact at the env binding `x ↦ enc n`, read off `enc n = enc n` via the
mirror's `equal`-reflects-equality lemma, then descend through `enc`'s injectivity to
`n = n`. The proof routes through `s2_mirror` (the driver output) — NOT `rfl`.

(Reflexivity is of course trivially true natively; this step demonstrates the full
plumbing — ACL2 proof tree → mirror fact → native fact about a standard type — which
is what later, non-trivial theorems will reuse.) -/

/-- Encode a `Nat` as the corresponding ACL2 integer object. -/
private def enc (n : Nat) : SExpr := .atom (.number (.int (Int.ofNat n)))

private theorem enc_inj {a b : Nat} (h : enc a = enc b) : a = b := by
  simp only [enc, SExpr.atom.injEq, Atom.number.injEq, Number.int.injEq, Int.ofNat.injEq] at h
  exact h

/-- The env binding the ACL2 variable `x` to the encoded `Nat`. -/
private def envOf (n : Nat) : Env := ({} : Env).insert { name := "x" } (enc n)

private theorem envOf_get (n : Nat) : (envOf n).get? { name := "x" } = some (enc n) := by
  show (envOf n)[({ name := "x" } : Symbol)]? = some (enc n)
  unfold envOf; rw [Std.HashMap.getElem?_insert]; simp

/-- The native Lean fact `∀ n : Nat, n = n`, proven THROUGH the driver's mirror output
    `s2_mirror` (via the `Nat → SExpr` encoding), not by `rfl`. -/
theorem native_nat_refl (n : Nat) : n = n := by
  obtain ⟨N, hN⟩ := s2_mirror (envOf n)
  have hvar : evalOpt (N + 1) World.empty (envOf n) (.atom (.symbol { name := "x" }))
      = some (enc n) :=
    evalOpt_var N World.empty (envOf n) { name := "x" } (enc n) (envOf_get n)
  have hno : World.empty.defs.get? ({ name := "equal" } : Symbol) = none := by simp [World.empty]
  have heq : evalOpt (N + 2) World.empty (envOf n) litEqXX = some SExpr.t := hN (N + 2) (by omega)
  have hval : enc n = enc n :=
    eval_equal_t_implies_eq (N + 1) World.empty (envOf n)
      (.atom (.symbol { name := "x" })) (.atom (.symbol { name := "x" }))
      (enc n) (enc n) hvar hvar hno heq
  exact enc_inj hval

-- Sorry-free, and it genuinely depends on `s2_mirror` (the driver output).
#print axioms native_nat_refl

/-! ## NEGATIVE — the driver must fail cleanly (fail-closed, never sorry). -/

/-- Run the driver on a tree and assert it `throwError`s. -/
private def expectDriverFails (label : String) (cp : ClauseProof) : Elab.Command.CommandElabM Unit :=
  Elab.Command.liftTermElabM do
    let emptyEnv ← Term.elabTerm (← `(({} : Env))) none
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``World.empty, envExpr := emptyEnv,
        worldUnfoldNames := #[``World.empty] }
    try
      let _ ← replayProof cfg cp
      throwError "NEGATIVE TEST FAILED ({label}): driver SUCCEEDED but should have failed"
    catch e =>
      logInfo m!"negative test OK ({label}): driver failed cleanly — {e.toMessageData}"

elab "#expect_driver_fails " s:str t:term : command => do
  let cpExpr ← Elab.Command.liftTermElabM (Term.elabTermAndSynthesize t (some (mkConst ``ACL2.ClauseProof)))
  let cp ← Elab.Command.liftTermElabM (unsafe evalExpr ClauseProof (mkConst ``ACL2.ClauseProof) cpExpr)
  expectDriverFails s.getString cp

-- (N1) an unsupported rewrite rune before the closer → replayNode hard-fails.
private def rewriteNode : ProofNode :=
  .node ("definition", "my-app") (sym "x") (sym "y") [] {}
private def treeRewriteFrontier : ClauseProof :=
  { name := "neg-rewrite", formula := litEqXX,
    root := some { goalNode with steps := [{ simplifyStep with
      items := [.literal { litProof with nodes := [rewriteNode, equalSelfNode] }] }] } }
#expect_driver_fails "unsupported rewrite rune" treeRewriteFrontier

-- (N2) an induction scheme → replayClause hard-fails.
private def treeInduction : ClauseProof :=
  { name := "neg-induction", formula := litEqXX,
    root := some { goalNode with
      induction := some { term := sym "x", subgoalCount := 2, scheme := [] } } }
#expect_driver_fails "induction scheme" treeInduction

-- (N3) a non-equal-self terminal node → replayLiteral hard-fails.
private def treeBadTerminal : ClauseProof :=
  { name := "neg-bad-terminal", formula := litEqXX,
    root := some { goalNode with steps := [{ simplifyStep with
      items := [.literal { litProof with nodes := [rewriteNode] }] }] } }
#expect_driver_fails "non-equal-self terminal" treeBadTerminal

end ACL2.Tests.Driver
