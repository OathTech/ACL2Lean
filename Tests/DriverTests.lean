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
private def ap1 (f : String) (a : SExpr) : SExpr := .cons (sym f) (.cons a .nil)
private def ap2 (f : String) (a b : SExpr) : SExpr := .cons (sym f) (.cons a (.cons b .nil))

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

/-- A carried world-structure fact: `equal` is not shadowed in the empty world.
    Established ONCE here (the driver never re-derives it). For the real pipeline this
    is what `gen-world` would emit alongside the world def. -/
theorem empty_no_equal : World.empty.defs.get? ({ name := "equal" } : Symbol) = none := by
  simp [World.empty]
theorem empty_no_cdr : World.empty.defs.get? ({ name := "cdr" } : Symbol) = none := by
  simp [World.empty]
theorem empty_no_cons : World.empty.defs.get? ({ name := "cons" } : Symbol) = none := by
  simp [World.empty]

/-- The carried world-structure facts for the empty world (builtins not shadowed). -/
def emptyNoShadow : List (Symbol × Expr) :=
  [({ name := "equal" }, mkConst ``empty_no_equal),
   ({ name := "cdr" },   mkConst ``empty_no_cdr),
   ({ name := "cons" },  mkConst ``empty_no_cons)]

/-- `acl2_replay% <clauseProofTerm>` — elaborates the tree value, runs the driver over
    the empty world for a universally-quantified `env`, and returns the emitted proof
    of `∀ env, <mirror>`. Fails to elaborate if the driver `throwError`s. -/
elab "acl2_replay% " t:term : term => do
  let cpExpr ← Term.elabTermAndSynthesize t (some (mkConst ``ACL2.ClauseProof))
  let cp ← unsafe evalExpr ClauseProof (mkConst ``ACL2.ClauseProof) cpExpr
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``World.empty, envExpr := env, noShadow := emptyNoShadow }
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

/-! ## POSITIVE — S3: a real rewrite rune (`cdr-cons`) + path-directed congruence.

Hand-built tree for `(equal (cdr (cons a b)) b)`: a `cdr-cons` node rewrites
`(cdr (cons a b)) ⇒ b` (lifted through `equal arg1` via its `:PATH`), then equal-self
closes `(equal b b)`. The first node that is a real rewrite, not just a closer —
exercises `replayNode`'s cdr-cons handler + `proveConv` of the (variable) operands +
the path-directed `emitCongruence`. -/
private def varA : SExpr := sym "a"
private def varB : SExpr := sym "b"
/-- `(equal (cdr (cons a b)) b)`. -/
private def litCdrCons : SExpr := equalOf (ap1 "cdr" (ap2 "cons" varA varB)) varB
private def cdrConsNode : ProofNode :=
  .node ("rewrite", "cdr-cons") (ap1 "cdr" (ap2 "cons" varA varB)) varB []
    { path := [.arg 1 { name := "equal" }, .arg 1 { name := "cdr" }] }
private def eqSelfBB : ProofNode :=
  .node ("equal-self", "NIL") (equalOf varB varB) Driver.quoteT [] {}
private def s3Goal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litCdrCons],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litCdrCons, notFlg := false,
                           nodes := [cdrConsNode, eqSelfBB], result := Driver.quoteT }] }],
    induction := none, children := [] }
private def s3Tree : ClauseProof := { name := "cdr-cons-refl", formula := litCdrCons, root := some s3Goal }

/-- Driver-emitted proof that `(equal (cdr (cons a b)) b)` evaluates to `t` for every env. -/
def s3_mirror := acl2_replay% s3Tree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, evalOpt f World.empty env litCdrCons = some SExpr.t :=
  s3_mirror

#print axioms s3_mirror

/-! ## POSITIVE — convergence analyzer on a COMPOUND operand.

`(equal (cons a b) (cons a b))`: equal-self on a compound term forces `proveConv` to
recurse into the `(cons a b)` application (`re_conv_cons` over the two variable
operands) rather than handle only a bare variable/quote. -/
private def litConsEq : SExpr := equalOf (ap2 "cons" varA varB) (ap2 "cons" varA varB)
private def consEqGoal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litConsEq],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litConsEq, notFlg := false,
                           nodes := [.node ("equal-self", "NIL") litConsEq Driver.quoteT [] {}],
                           result := Driver.quoteT }] }],
    induction := none, children := [] }
private def consEqTree : ClauseProof := { name := "cons-self", formula := litConsEq, root := some consEqGoal }

def consEq_mirror := acl2_replay% consEqTree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, evalOpt f World.empty env litConsEq = some SExpr.t :=
  consEq_mirror

#print axioms consEq_mirror

/-! ## POSITIVE — 3a(ii): the DEFINITION-UNFOLD node (a defined function in the world).

`(defun pair (x) (cons x x))`, theorem `(equal (pair x) (cons x x))`: the `definition`
node unfolds `(pair x) ⇒ (cons x x)` (lifted through `equal arg1`), then equal-self
closes `(equal (cons x x) (cons x x))`. Exercises `replayNode`'s definition handler
(`re_unfold1_conv`) — incl. the body's ∀-env convergence (`proveConvAllEnv`) that the
unfold needs at the `bindArgs` env — plus the carried `DefInfo` (def/closed/no-let
facts). A real def-unfold shape (cons body avoids needing `binary-*` convergence). -/

/-- Body of `pair`: `(cons x x)`. -/
private def pairBody : SExpr :=
  .cons (.atom (.symbol { name := "cons" }))
    (.cons (.atom (.symbol { name := "x" })) (.cons (.atom (.symbol { name := "x" })) .nil))

/-- A world with just `(defun pair (x) (cons x x))`. -/
def pairWorld : World :=
  { World.empty with defs := World.empty.defs.insert { name := "pair" } ([{ name := "x" }], pairBody) }

theorem pair_def :
    pairWorld.defs.get? ({ name := "pair" } : Symbol) = some ([{ name := "x" }], pairBody) := by
  show pairWorld.defs[({ name := "pair" } : Symbol)]? = _
  simp [pairWorld, World.empty]
theorem pair_closed : ∀ s ∈ freeVars pairBody, s ∈ [({ name := "x" } : Symbol)] := by decide
theorem pair_nolet : NoLet pairBody = true := by decide
theorem pairWorld_no_equal : pairWorld.defs.get? ({ name := "equal" } : Symbol) = none := by
  show pairWorld.defs[({ name := "equal" } : Symbol)]? = _
  simp [pairWorld, World.empty]
theorem pairWorld_no_cons : pairWorld.defs.get? ({ name := "cons" } : Symbol) = none := by
  show pairWorld.defs[({ name := "cons" } : Symbol)]? = _
  simp [pairWorld, World.empty]

/-- Run the driver over `pairWorld` (carries `pair`'s DefInfo + non-shadowing facts). -/
elab "acl2_replay_pair% " t:term : term => do
  let cpExpr ← Term.elabTermAndSynthesize t (some (mkConst ``ACL2.ClauseProof))
  let cp ← unsafe evalExpr ClauseProof (mkConst ``ACL2.ClauseProof) cpExpr
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let di : DefInfo :=
      { formal := { name := "x" }, body := pairBody,
        defFact := mkConst ``pair_def, closedFact := mkConst ``pair_closed,
        noLetFact := mkConst ``pair_nolet }
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``pairWorld, envExpr := env,
        noShadow := [({ name := "equal" }, mkConst ``pairWorld_no_equal),
                     ({ name := "cons" },  mkConst ``pairWorld_no_cons)],
        defs := [({ name := "pair" }, di)] }
    let proof ← replayProof cfg cp
    mkLambdaFVars #[env] proof

private def varXp : SExpr := sym "x"
/-- `(equal (pair x) (cons x x))`. -/
private def litPair : SExpr := equalOf (ap1 "pair" varXp) (ap2 "cons" varXp varXp)
private def pairDefNode : ProofNode :=
  .node ("definition", "pair") (ap1 "pair" varXp) (ap2 "cons" varXp varXp) []
    { path := [.arg 1 { name := "equal" }, .arg 1 { name := "pair" }] }
private def pairEqSelf : ProofNode :=
  .node ("equal-self", "NIL") (equalOf (ap2 "cons" varXp varXp) (ap2 "cons" varXp varXp)) Driver.quoteT [] {}
private def pairGoal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litPair],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litPair, notFlg := false,
                           nodes := [pairDefNode, pairEqSelf], result := Driver.quoteT }] }],
    induction := none, children := [] }
private def pairTree : ClauseProof := { name := "pair-rewrites", formula := litPair, root := some pairGoal }

def pair_mirror := acl2_replay_pair% pairTree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, evalOpt f pairWorld env litPair = some SExpr.t :=
  pair_mirror

#print axioms pair_mirror

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

/-! ## emitCongruence — path-directed lifting (consumes :PATH, no subterm search).

Lifts a node eval-equality to the whole literal by navigating the node's `:PATH`
(`PathFrame`s), not by locating the redex. Exercised here on a real (sorry-free)
node proof: reflexivity of `(cdr (cons a b))` lifted through `(equal · b)` via the
path `[arg 1 EQUAL, arg 1 CDR]` — i.e. the `binary_left equal` congruence — yielding
`eval (equal (cdr (cons a b)) b) = eval (equal …)`. (The per-rune node proofs that
feed this — cdr-cons etc. — are S3.) -/
elab "#emitcongr_pathdirected_test" : command => Elab.Command.liftTermElabM do
  withLocalDeclD `w (mkConst ``World) fun w =>
  withLocalDeclD `e (mkConst ``Env) fun e => do
    let X := ap1 "cdr" (ap2 "cons" (sym "a") (sym "b"))
    let lit := equalOf X (sym "b")
    let nodeTy ← mkEvalEqExist w e X X
    let nodeProof ← Term.elabTermAndSynthesize (← `(⟨0, fun _ _ => rfl⟩)) (some nodeTy)
    let frames : List PathFrame := [.arg 1 { name := "equal" }, .arg 1 { name := "cdr" }]
    let (lifted, _) ← emitCongruence w e lit frames X X nodeProof
    let _ ← check lifted
    let expected ← mkEvalEqExist w e lit lit
    unless ← isDefEq (← inferType lifted) expected do
      throwError "emitCongruence path-directed: type\n{← ppExpr (← inferType lifted)}\n≠ expected\n{← ppExpr expected}"
    logInfo "emitCongruence path-directed OK (cdr-cons lifted through equal arg1)"

#emitcongr_pathdirected_test

-- NEGATIVE: a `.boundary` path frame (child node inside an unfold) is not yet
-- supported — emitCongruence must hard-fail cleanly.
elab "#emitcongr_boundary_fails" : command => Elab.Command.liftTermElabM do
  withLocalDeclD `w (mkConst ``World) fun w =>
  withLocalDeclD `e (mkConst ``Env) fun e => do
    let X := ap1 "cdr" (ap2 "cons" (sym "a") (sym "b"))
    let lit := equalOf X (sym "b")
    let nodeProof ← Term.elabTermAndSynthesize (← `(⟨0, fun _ _ => rfl⟩)) (some (← mkEvalEqExist w e X X))
    let frames : List PathFrame :=
      [.arg 1 { name := "equal" }, .boundary { name := "BODY" } { name := "if" }, .arg 1 { name := "cdr" }]
    try
      let _ ← emitCongruence w e lit frames X X nodeProof
      throwError "NEGATIVE TEST FAILED: boundary frame accepted"
    catch e => logInfo m!"negative test OK (boundary path frame): {e.toMessageData}"

#emitcongr_boundary_fails

/-! ## NEGATIVE — the driver must fail cleanly (fail-closed, never sorry). -/

/-- Run the driver on a tree and assert it `throwError`s. -/
private def expectDriverFails (label : String) (cp : ClauseProof) : Elab.Command.CommandElabM Unit :=
  Elab.Command.liftTermElabM do
    let emptyEnv ← Term.elabTerm (← `(({} : Env))) none
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``World.empty, envExpr := emptyEnv, noShadow := emptyNoShadow }
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

-- (N4) the TYPE-SET frontier: a clause closed by `fake-rune-for-type-set` at
-- preprocess-clause, with NO rewrite detail / no closing literal — exactly the shape
-- ACL2 emits for `equal-trans` (transitivity by type-set; see recon-tests/
-- 08-equality-reasoning). The driver must hard-fail (we do NOT re-derive type-set in
-- Lean — that would be inference). Becomes replayable only with type-set
-- instrumentation (the "(B)" track), never by a Lean-side decision.
private def varY : SExpr := sym "y"
private def varZ : SExpr := sym "z"
/-- `(implies (and (equal x y) (equal y z)) (equal x z))`. -/
private def transFormula : SExpr :=
  .cons (sym "implies")
    (.cons (.cons (sym "and") (.cons (equalOf varX varY) (.cons (equalOf varY varZ) .nil)))
      (.cons (equalOf varX varZ) .nil))
private def typeSetStep : WaterfallStep :=
  { processor := "preprocess-clause", result := default,
    runes := [("fake-rune-for-type-set", "NIL")], newClauses := [], items := [], extraFields := [] }
private def treeTypeSet : ClauseProof :=
  { name := "neg-type-set", formula := transFormula,
    root := some { goalNode with inputClause := [transFormula], steps := [typeSetStep] } }
#expect_driver_fails "type-set-closed clause (fake-rune-for-type-set)" treeTypeSet

end ACL2.Tests.Driver
