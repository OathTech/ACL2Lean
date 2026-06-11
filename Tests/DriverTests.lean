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

-- NO hand-marshalled world facts: the driver DERIVES every `defs.get? … = none` /
-- `= some (…)` / freeVars⊆formals / NoLet by kernel decision from `cfg.worldVal`
-- (`World.defs` is a reduction-friendly `DefMap`). The config carries only the world
-- (as `Expr` + value) and env.

/-- `acl2_replay% <clauseProofTerm>` — elaborates the tree value, runs the driver over
    the empty world for a universally-quantified `env`, and returns the emitted proof
    of `∀ env, <mirror>`. Fails to elaborate if the driver `throwError`s. -/
elab "acl2_replay% " t:term : term => do
  let cpExpr ← Term.elabTermAndSynthesize t (some (mkConst ``ACL2.ClauseProof))
  let cp ← unsafe evalExpr ClauseProof (mkConst ``ACL2.ClauseProof) cpExpr
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``World.empty, envExpr := env, worldVal := World.empty }
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

/-! ## POSITIVE — convergence analyzer on car/cdr/consp/binary-+ builtins.

`(equal T T)` with `T = (binary-+ (consp (cons a b)) (car (cdr (cons a b))))`: equal-self
forces `proveConv` through every new builtin convergence case at once — `re_conv_plus`
over `re_conv_consp`/`re_conv_car` over `re_conv_cdr`/`re_conv_cons` over the variables.
These are the decoupled (non-case-dependent) convergence builtins; recognizer/
if-simplification need the case context (`ReplayCtx`) and land with the induction scaffold. -/
private def litBuiltinsEq : SExpr :=
  let t := ap2 "binary-+" (ap1 "consp" (ap2 "cons" varA varB))
                          (ap1 "car" (ap1 "cdr" (ap2 "cons" varA varB)))
  equalOf t t
private def builtinsEqGoal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litBuiltinsEq],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litBuiltinsEq, notFlg := false,
                           nodes := [.node ("equal-self", "NIL") litBuiltinsEq Driver.quoteT [] {}],
                           result := Driver.quoteT }] }],
    induction := none, children := [] }
private def builtinsEqTree : ClauseProof :=
  { name := "builtins-self", formula := litBuiltinsEq, root := some builtinsEqGoal }

def builtinsEq_mirror := acl2_replay% builtinsEqTree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, evalOpt f World.empty env litBuiltinsEq = some SExpr.t :=
  builtinsEq_mirror

#print axioms builtinsEq_mirror

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

/-- Run the driver over `pairWorld`. `pair`'s DefInfo + non-shadowing facts are DERIVED
    from `worldVal` by the driver — no hand-written theorems. -/
elab "acl2_replay_pair% " t:term : term => do
  let cpExpr ← Term.elabTermAndSynthesize t (some (mkConst ``ACL2.ClauseProof))
  let cp ← unsafe evalExpr ClauseProof (mkConst ``ACL2.ClauseProof) cpExpr
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``pairWorld, envExpr := env, worldVal := pairWorld }
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

/-! ## END-TO-END FRONTEND — replay a REAL parsed ACL2 proof tree.

This is the first time the driver consumes a real `.proof-log` (parsed →
`Development` → `ClauseProof`) rather than a hand-built tree value. Target:
`sq-rewrites` `(equal (sq n) (* n n))` from `recon-tests/09-defn-unfold` — a
non-inductive def-unfold (`(sq n) ⇒ (binary-* n n)`) + equal-self. The world facts
(`sqWorld` matching the `.lisp`'s `(defun sq (n) (* n n))`, with def/closed/no-let +
non-shadowing proofs) are still established here by hand; `gen-world` will emit them
later. The TREE is genuinely parsed from ACL2's output.

NOTE: `09-defn-unfold.proof-log` is gitignored (regenerate with
`scripts/capture-proof-log.sh acl2_samples/recon-tests/09-defn-unfold.lisp`), same as
`simple.proof-log`. -/

private def sqLog : String := include_str "../acl2_samples/recon-tests/09-defn-unfold.proof-log"

/-- The REAL parsed development (ACL2 output → parse → reconstruct). Both the WORLD
    (`derive_world` below) and the theorem (`sqRealProof`) are projected from THIS — the
    only input is the log. -/
def sqDevelopment : Development :=
  (((ProofLog.parse sqLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

/-- The REAL parsed `sq-rewrites` proof tree, extracted from the development. -/
def sqRealProof : Option ClauseProof := findThm sqDevelopment "sq-rewrites"

/-- Expected body of `(defun sq (n) (* n n))` — `(binary-* n n)` (ACL2 normalizes `*`).
    Used only to VALIDATE the derived world below (a test expectation, not the source). -/
private def sqBody : SExpr :=
  .cons (.atom (.symbol { name := "binary-*" }))
    (.cons (.atom (.symbol { name := "n" })) (.cons (.atom (.symbol { name := "n" })) .nil))

-- (`derive_world` and `findThm` are promoted product helpers — Replay/Driver.lean.)

-- `sqWorld` DERIVED from the parsed development — no hand-written world.
derive_world sqWorld from sqDevelopment

-- Validate the projection: the derived world has `sq ↦ ([n], (binary-* n n))`.
#guard sqWorld.defs.get? { name := "sq" } = some ([{ name := "n" }], sqBody)

/-- Drive the REAL parsed `sq-rewrites` tree over the DERIVED `sqWorld`. The DefInfo +
    non-shadowing facts are derived by the driver (P3); the world itself is derived from
    the development (P4) — the only input is the log. -/
elab "acl2_replay_sq_real% " : term => do
  let cpOpt ← unsafe evalExpr (Option ClauseProof)
    (mkApp (mkConst ``Option [0]) (mkConst ``ACL2.ClauseProof)) (mkConst ``sqRealProof)
  let some cp := cpOpt
    | throwError "sqRealProof: parse/extract failed (is 09-defn-unfold.proof-log present?)"
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``sqWorld, envExpr := env, worldVal := sqWorld }
    let proof ← replayProof cfg cp
    mkLambdaFVars #[env] proof

/-- FIRST REAL TREE replayed end-to-end: the driver-emitted proof of the `sq-rewrites`
    mirror, from ACL2's actual proof-log. -/
def sq_real_mirror := acl2_replay_sq_real%

-- The emitted type is the real theorem (the clause literal, `*` normalized to binary-*).
example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N,
      evalOpt f sqWorld env
        (equalOf (ap1 "sq" (sym "n")) (ap2 "binary-*" (sym "n") (sym "n"))) = some SExpr.t :=
  sq_real_mirror

#print axioms sq_real_mirror

/-! ## END-TO-END on the real inductive tree — `my-len-my-app`.

The driver replays the REAL `simple.proof-log` end-to-end: WF-induction scaffold from
the emitted measure justification, both case-clause spines, the solidify IH bridge —
producing the CONDITIONAL generic mirror (totality + TP obligations explicit in the
type, machine-generated from the development; no sorryAx). -/
private def simpleLog : String := include_str "../acl2_samples/simple.proof-log"
def mylenRealProof : Option ClauseProof := do
  let log ← (ProofLog.parse simpleLog).toOption
  let dev ← (ClauseTree.buildDevelopment log).toOption
  findThm dev "my-len-my-app"

/-- The parsed development of `simple.proof-log` (world + theorem + TPs all
    projected from THIS — the only input is the log). -/
def simpleDevelopment : Development :=
  (((ProofLog.parse simpleLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world simpleWorld from simpleDevelopment

/-- The emitted TP corollaries of the development (my-len, my-app). -/
def simpleTPs : List (String × SExpr) := simpleDevelopment.typePrescriptions

/-- THE c3 TARGET: drive the REAL `my-len-my-app` tree end-to-end — the WF-induction
    scaffold from the EMITTED measure justification, the clause spines, the solidify
    IH bridge — as the CONDITIONAL generic mirror (totality + TP hypotheses
    machine-generated from the development; the c2 pattern). -/
elab "acl2_replay_mylen_real% " : term => do
  let cpOpt ← unsafe evalExpr (Option ClauseProof)
    (mkApp (mkConst ``Option [0]) (mkConst ``ACL2.ClauseProof)) (mkConst ``mylenRealProof)
  let some cp := cpOpt | throwError "mylenRealProof: parse/extract failed"
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``simpleWorld, envExpr := env,
        worldVal := simpleDevelopment.toWorld }
    let (proof, conds) ← replayProofConditional cfg simpleTPs cp
      simpleDevelopment.justifications
    logInfo m!"my-len-my-app replayed; conditions: {conds}"
    mkLambdaFVars #[env] proof

/-- The first DRIVER-replayed INDUCTIVE theorem. As of #37 the driver
    AUTO-DISCHARGES the totality hypotheses from the emitted admission data
    (justification + raw termination clauses), so only the TP hypothesis
    remains explicit in the type. -/
def my_len_my_app_real_mirror := acl2_replay_mylen_real%

/-- PIN the machine-generated statement (audit #38, updated for #37): the
    conclusion is the genuine mirror of the ACL2 defthm
    `(equal (my-len (my-app x y)) (+ (my-len x) (my-len y)))`, and the sole
    remaining hypothesis is my-len's emitted TP corollary, lifted value-only
    (totality of my-len/my-app/fix is auto-discharged from admission). -/
example :
    ∀ (env : Env),
      (∀ (env' : Env) (a0 v : SExpr),
          (∃ N, ∀ f ≥ N, evalOpt f simpleWorld env' (ap1 "my-len" a0) = some v) →
          (bif Logic.toBool (Logic.integerp v) then
            Logic.not (Logic.lt v (SExpr.atom (Atom.number (Number.int 0))))
          else SExpr.nil) = SExpr.t) →
      ∃ N, ∀ f ≥ N,
        evalOpt f simpleWorld env
          (equalOf (ap1 "my-len" (ap2 "my-app" (sym "x") (sym "y")))
                   (ap2 "binary-+" (ap1 "my-len" (sym "x")) (ap1 "my-len" (sym "y"))))
          = some SExpr.t :=
  my_len_my_app_real_mirror

#print axioms my_len_my_app_real_mirror


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
  unfold envOf; simp

/-- The native Lean fact `∀ n : Nat, n = n`, proven THROUGH the driver's mirror output
    `s2_mirror` (via the `Nat → SExpr` encoding), not by `rfl`. -/
theorem native_nat_refl (n : Nat) : n = n := by
  obtain ⟨N, hN⟩ := s2_mirror (envOf n)
  have hvar : evalOpt (N + 1) World.empty (envOf n) (.atom (.symbol { name := "x" }))
      = some (enc n) :=
    evalOpt_var N World.empty (envOf n) { name := "x" } (enc n) (envOf_get n)
  have hno : World.empty.defs.get? ({ name := "equal" } : Symbol) = none := by decide
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

-- NEGATIVE: a RESIDUAL `.boundary` path frame (more nesting in the path than the
-- chain's declared depth) — emitCongruence must hard-fail cleanly, never navigate past.
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

-- NEGATIVE: a consumed-branch `strip` index that does not match the node's path
-- frame (rewrite-if gstack discipline violated) — must hard-fail, never mis-navigate.
elab "#emitcongr_strip_mismatch_fails" : command => Elab.Command.liftTermElabM do
  withLocalDeclD `w (mkConst ``World) fun w =>
  withLocalDeclD `e (mkConst ``Env) fun e => do
    let X := ap1 "cdr" (ap2 "cons" (sym "a") (sym "b"))
    let lit := equalOf X (sym "b")
    let nodeProof ← Term.elabTermAndSynthesize (← `(⟨0, fun _ _ => rfl⟩)) (some (← mkEvalEqExist w e X X))
    -- the chain consumed branch frame 2, but the node's path descends arg 1
    let frames : List PathFrame :=
      [.arg 1 { name := "equal" }, .arg 1 { name := "equal" }, .arg 1 { name := "cdr" }]
    try
      let _ ← emitCongruence w e lit frames X X nodeProof (strip := [2])
      throwError "NEGATIVE TEST FAILED: strip mismatch accepted"
    catch e => logInfo m!"negative test OK (strip mismatch): {e.toMessageData}"

#emitcongr_strip_mismatch_fails

/-! ## NEGATIVE — the driver must fail cleanly (fail-closed, never sorry). -/

/-- Run the driver on a tree and assert it `throwError`s. -/
private def expectDriverFails (label : String) (cp : ClauseProof) : Elab.Command.CommandElabM Unit :=
  Elab.Command.liftTermElabM do
    let emptyEnv ← Term.elabTerm (← `(({} : Env))) none
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``World.empty, envExpr := emptyEnv, worldVal := World.empty }
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
