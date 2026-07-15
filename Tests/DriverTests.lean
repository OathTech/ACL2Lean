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

-- Unescaped ACL2 tokens upcase (readtable :upcase, BUG-002) — the hand-built
-- trees here mirror parser output, so callers pass UPPERCASE symbol names
-- (literal, kept kernel-reducible for the `#guard`/`example` defeq checks).
private def sym (n : String) : SExpr := .atom (.symbol { name := n })
private def quo (v : SExpr) : SExpr := .cons (sym "QUOTE") (.cons v .nil)
private def numv (k : Int) : SExpr := .atom (.number (.int k))
private def equalOf (a b : SExpr) : SExpr := .cons (sym "EQUAL") (.cons a (.cons b .nil))
private def ap1 (f : String) (a : SExpr) : SExpr := .cons (sym f) (.cons a .nil)
private def ap2 (f : String) (a b : SExpr) : SExpr := .cons (sym f) (.cons a (.cons b .nil))

/-! ## The minimal USEFUL tree: one `equal-self` node proving `(equal x x)` for a
    FREE VARIABLE `x` — universally over the environment. -/

/-- The variable `x`. -/
private def varX : SExpr := sym "X"
/-- `(equal x x)` — the literal (x a free variable, NOT a ground constant). -/
private def litEqXX : SExpr := equalOf varX varX

/-- One `equal-self` node: `(equal x x) ⇒ (quote t)`. -/
private def equalSelfNode : ProofNode :=
  .node ("equal-self", "NIL") litEqXX quoteT [] {}

private def litProof : LiteralProof :=
  { index := 1, literal := litEqXX, notFlg := false,
    nodes := [equalSelfNode], result := quoteT }

private def simplifyStep : WaterfallStep :=
  { processor := "simplify-clause", result := default, runes := [],
    newClauses := [], items := [.literal litProof], extraFields := [] }

private def goalNode : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litEqXX],
    steps := [simplifyStep], induction := none, children := [] }

/-- The minimal positive tree (faithful `ClauseProof` value). -/
def s2Tree : ClauseProof := { name := "REFL-EQUAL-X-X", formula := litEqXX, root := some goalNode }

/-! ## Frontend: run the driver over `World.empty`, UNIVERSALLY over the env.

The mirror theorem is `∀ env, ∃ N, ∀ f ≥ N, ∃ v, evalOpt f w env formula = some v ∧
v ≠ nil` (ACL2's truthiness claim, G2) — the
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
    ∀ (env : Env), ∃ N, ∀ f ≥ N, ∃ v,
      evalOpt f World.empty env litEqXX = some v ∧ v ≠ SExpr.nil :=
  s2_mirror

-- Sorry-free: must be {propext, Classical.choice, Quot.sound} — no sorryAx.
#print axioms s2_mirror

/-! ## POSITIVE — S3: a real rewrite rune (`cdr-cons`) + path-directed congruence.

Hand-built tree for `(equal (cdr (cons a b)) b)`: a `cdr-cons` node rewrites
`(cdr (cons a b)) ⇒ b` (lifted through `equal arg1` via its `:PATH`), then equal-self
closes `(equal b b)`. The first node that is a real rewrite, not just a closer —
exercises `replayNode`'s cdr-cons handler + `proveConv` of the (variable) operands +
the path-directed `emitCongruence`. -/
private def varA : SExpr := sym "A"
private def varB : SExpr := sym "B"
/-- `(equal (cdr (cons a b)) b)`. -/
private def litCdrCons : SExpr := equalOf (ap1 "CDR" (ap2 "CONS" varA varB)) varB
private def cdrConsNode : ProofNode :=
  .node ("rewrite", "CDR-CONS") (ap1 "CDR" (ap2 "CONS" varA varB)) varB []
    { path := [.arg 1 { name := "EQUAL" }, .arg 1 { name := "CDR" }] }
private def eqSelfBB : ProofNode :=
  .node ("equal-self", "NIL") (equalOf varB varB) quoteT [] {}
private def s3Goal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litCdrCons],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litCdrCons, notFlg := false,
                           nodes := [cdrConsNode, eqSelfBB], result := quoteT }] }],
    induction := none, children := [] }
private def s3Tree : ClauseProof := { name := "CDR-CONS-REFL", formula := litCdrCons, root := some s3Goal }

/-- Driver-emitted proof that `(equal (cdr (cons a b)) b)` evaluates to `t` for every env. -/
def s3_mirror := acl2_replay% s3Tree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, ∃ v,
      evalOpt f World.empty env litCdrCons = some v ∧ v ≠ SExpr.nil :=
  s3_mirror

#print axioms s3_mirror

/-! ## POSITIVE — convergence analyzer on a COMPOUND operand.

`(equal (cons a b) (cons a b))`: equal-self on a compound term forces `proveConv` to
recurse into the `(cons a b)` application (`re_conv_cons` over the two variable
operands) rather than handle only a bare variable/quote. -/
private def litConsEq : SExpr := equalOf (ap2 "CONS" varA varB) (ap2 "CONS" varA varB)
private def consEqGoal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litConsEq],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litConsEq, notFlg := false,
                           nodes := [.node ("equal-self", "NIL") litConsEq quoteT [] {}],
                           result := quoteT }] }],
    induction := none, children := [] }
private def consEqTree : ClauseProof := { name := "CONS-SELF", formula := litConsEq, root := some consEqGoal }

def consEq_mirror := acl2_replay% consEqTree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, ∃ v,
      evalOpt f World.empty env litConsEq = some v ∧ v ≠ SExpr.nil :=
  consEq_mirror

#print axioms consEq_mirror

/-! ## POSITIVE — convergence analyzer on car/cdr/consp/binary-+ builtins.

`(equal T T)` with `T = (binary-+ (consp (cons a b)) (car (cdr (cons a b))))`: equal-self
forces `proveConv` through every new builtin convergence case at once — `re_conv_plus`
over `re_conv_consp`/`re_conv_car` over `re_conv_cdr`/`re_conv_cons` over the variables.
These are the decoupled (non-case-dependent) convergence builtins; recognizer/
if-simplification need the case context (`ReplayCtx`) and land with the induction scaffold. -/
private def litBuiltinsEq : SExpr :=
  let t := ap2 "BINARY-+" (ap1 "CONSP" (ap2 "CONS" varA varB))
                          (ap1 "CAR" (ap1 "CDR" (ap2 "CONS" varA varB)))
  equalOf t t
private def builtinsEqGoal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litBuiltinsEq],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litBuiltinsEq, notFlg := false,
                           nodes := [.node ("equal-self", "NIL") litBuiltinsEq quoteT [] {}],
                           result := quoteT }] }],
    induction := none, children := [] }
private def builtinsEqTree : ClauseProof :=
  { name := "BUILTINS-SELF", formula := litBuiltinsEq, root := some builtinsEqGoal }

def builtinsEq_mirror := acl2_replay% builtinsEqTree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, ∃ v,
      evalOpt f World.empty env litBuiltinsEq = some v ∧ v ≠ SExpr.nil :=
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
  .cons (.atom (.symbol { name := "CONS" }))
    (.cons (.atom (.symbol { name := "X" })) (.cons (.atom (.symbol { name := "X" })) .nil))

/-- A world with just `(defun pair (x) (cons x x))`. -/
def pairWorld : World :=
  { World.empty with defs := World.empty.defs.insert { name := "PAIR" } ([{ name := "X" }], pairBody) }

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

private def varXp : SExpr := sym "X"
/-- `(equal (pair x) (cons x x))`. -/
private def litPair : SExpr := equalOf (ap1 "PAIR" varXp) (ap2 "CONS" varXp varXp)
private def pairDefNode : ProofNode :=
  .node ("definition", "PAIR") (ap1 "PAIR" varXp) (ap2 "CONS" varXp varXp) []
    { path := [.arg 1 { name := "EQUAL" }, .arg 1 { name := "PAIR" }] }
private def pairEqSelf : ProofNode :=
  .node ("equal-self", "NIL") (equalOf (ap2 "CONS" varXp varXp) (ap2 "CONS" varXp varXp)) quoteT [] {}
private def pairGoal : ClauseNode :=
  { id := default, idStr := "Goal", inputClause := [litPair],
    steps := [{ simplifyStep with
      items := [.literal { index := 1, literal := litPair, notFlg := false,
                           nodes := [pairDefNode, pairEqSelf], result := quoteT }] }],
    induction := none, children := [] }
private def pairTree : ClauseProof := { name := "PAIR-REWRITES", formula := litPair, root := some pairGoal }

def pair_mirror := acl2_replay_pair% pairTree

example :
    ∀ (env : Env), ∃ N, ∀ f ≥ N, ∃ v,
      evalOpt f pairWorld env litPair = some v ∧ v ≠ SExpr.nil :=
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
  .cons (.atom (.symbol { name := "BINARY-*" }))
    (.cons (.atom (.symbol { name := "N" })) (.cons (.atom (.symbol { name := "N" })) .nil))

-- (`derive_world` and `findThm` are promoted product helpers — Replay/Driver.lean.)

-- `sqWorld` DERIVED from the parsed development — no hand-written world.
derive_world sqWorld from sqDevelopment

-- Validate the projection: the derived world has `sq ↦ ([n], (binary-* n n))`.
#guard sqWorld.defs.get? { name := "SQ" } = some ([{ name := "N" }], sqBody)

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
    ∀ (env : Env), ∃ N, ∀ f ≥ N, ∃ v,
      evalOpt f sqWorld env
        (equalOf (ap1 "SQ" (sym "N")) (ap2 "BINARY-*" (sym "N") (sym "N")))
        = some v ∧ v ≠ SExpr.nil :=
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
        worldVal := simpleDevelopment.toWorld,
        gzDefs := simpleDevelopment.groundZeroSnapshotDefs }
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
          (∃ N, ∀ f ≥ N, evalOpt f simpleWorld env' (ap1 "MY-LEN" a0) = some v) →
          (bif Logic.toBool (Logic.integerp v) then
            Logic.not (Logic.lt v (SExpr.atom (Atom.number (Number.int 0))))
          else SExpr.nil) = SExpr.t) →
      ∃ N, ∀ f ≥ N, ∃ v,
        evalOpt f simpleWorld env
          (equalOf (ap1 "MY-LEN" (ap2 "MY-APP" (sym "X") (sym "Y")))
                   (ap2 "BINARY-+" (ap1 "MY-LEN" (sym "X")) (ap1 "MY-LEN" (sym "Y"))))
          = some v ∧ v ≠ SExpr.nil :=
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
private def envOf (n : Nat) : Env := ({} : Env).insert { name := "X" } (enc n)

private theorem envOf_get (n : Nat) : (envOf n).get? { name := "X" } = some (enc n) := by
  unfold envOf; simp

/-- The native Lean fact `∀ n : Nat, n = n`, proven THROUGH the driver's mirror output
    `s2_mirror` (via the `Nat → SExpr` encoding), not by `rfl`. -/
theorem native_nat_refl (n : Nat) : n = n := by
  obtain ⟨N, hN⟩ := s2_mirror (envOf n)
  have hvar : evalOpt (N + 1) World.empty (envOf n) (.atom (.symbol { name := "X" }))
      = some (enc n) :=
    evalOpt_var N World.empty (envOf n) { name := "X" } (enc n) (envOf_get n)
  have hno : World.empty.defs.get? ({ name := "EQUAL" } : Symbol) = none := by decide
  -- the mirror is EvTrue (G2): destructure the truthy value, pin it to the
  -- equal-application's value, decode via equal's two-valuedness
  obtain ⟨v, heq, hnv⟩ := hN (N + 2) (by omega)
  have hev : evalOpt (N + 2) World.empty (envOf n) litEqXX
      = callBuiltin "EQUAL" [enc n, enc n] :=
    evalOpt_builtin_2 (N + 1) World.empty (envOf n) { name := "EQUAL" }
      _ _ (enc n) (enc n) (by simp [Symbol.isNamed]) hno hvar hvar
  have hveq : v = Logic.equal (enc n) (enc n) :=
    Option.some.inj ((heq.symm.trans hev).trans (callBuiltin_equal (enc n) (enc n)))
  exact enc_inj (Logic.eq_of_equal_ne_nil (hveq ▸ hnv))

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
    let X := ap1 "CDR" (ap2 "CONS" (sym "A") (sym "B"))
    let lit := equalOf X (sym "B")
    let nodeTy ← mkEvalEqExist w e X X
    let nodeProof ← Term.elabTermAndSynthesize (← `(⟨0, fun _ _ => rfl⟩)) (some nodeTy)
    let frames : List PathFrame := [.arg 1 { name := "EQUAL" }, .arg 1 { name := "CDR" }]
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
    let X := ap1 "CDR" (ap2 "CONS" (sym "A") (sym "B"))
    let lit := equalOf X (sym "B")
    let nodeProof ← Term.elabTermAndSynthesize (← `(⟨0, fun _ _ => rfl⟩)) (some (← mkEvalEqExist w e X X))
    let frames : List PathFrame :=
      [.arg 1 { name := "EQUAL" }, .boundary { name := "BODY" } { name := "IF" }, .arg 1 { name := "CDR" }]
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
    let X := ap1 "CDR" (ap2 "CONS" (sym "A") (sym "B"))
    let lit := equalOf X (sym "B")
    let nodeProof ← Term.elabTermAndSynthesize (← `(⟨0, fun _ _ => rfl⟩)) (some (← mkEvalEqExist w e X X))
    -- the chain consumed branch frame 2, but the node's path descends arg 1
    let frames : List PathFrame :=
      [.arg 1 { name := "EQUAL" }, .arg 1 { name := "EQUAL" }, .arg 1 { name := "CDR" }]
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
  .node ("definition", "MY-APP") (sym "X") (sym "Y") [] {}
private def treeRewriteFrontier : ClauseProof :=
  { name := "NEG-REWRITE", formula := litEqXX,
    root := some { goalNode with steps := [{ simplifyStep with
      items := [.literal { litProof with nodes := [rewriteNode, equalSelfNode] }] }] } }
#expect_driver_fails "unsupported rewrite rune" treeRewriteFrontier

-- (N2) an induction scheme → replayClause hard-fails.
private def treeInduction : ClauseProof :=
  { name := "NEG-INDUCTION", formula := litEqXX,
    root := some { goalNode with
      induction := some { term := sym "X", subgoalCount := 2, scheme := [] } } }
#expect_driver_fails "induction scheme" treeInduction

-- (N3) a non-equal-self terminal node → replayLiteral hard-fails.
private def treeBadTerminal : ClauseProof :=
  { name := "NEG-BAD-TERMINAL", formula := litEqXX,
    root := some { goalNode with steps := [{ simplifyStep with
      items := [.literal { litProof with nodes := [rewriteNode] }] }] } }
#expect_driver_fails "non-equal-self terminal" treeBadTerminal

-- (N4) the TYPE-SET frontier: a clause closed by `fake-rune-for-type-set` at
-- preprocess-clause, with NO rewrite detail / no closing literal — exactly the shape
-- ACL2 emits for `equal-trans` (transitivity by type-set; see recon-tests/
-- 08-equality-reasoning). The driver must hard-fail (we do NOT re-derive type-set in
-- Lean — that would be inference). Becomes replayable only with type-set
-- instrumentation (the "(B)" track), never by a Lean-side decision.
private def varY : SExpr := sym "Y"
private def varZ : SExpr := sym "Z"
/-- `(implies (and (equal x y) (equal y z)) (equal x z))`. -/
private def transFormula : SExpr :=
  .cons (sym "IMPLIES")
    (.cons (.cons (sym "AND") (.cons (equalOf varX varY) (.cons (equalOf varY varZ) .nil)))
      (.cons (equalOf varX varZ) .nil))
private def typeSetStep : WaterfallStep :=
  { processor := "preprocess-clause", result := default,
    runes := [("fake-rune-for-type-set", "NIL")], newClauses := [], items := [], extraFields := [] }
private def treeTypeSet : ClauseProof :=
  { name := "NEG-TYPE-SET", formula := transFormula,
    root := some { goalNode with inputClause := [transFormula], steps := [typeSetStep] } }
#expect_driver_fails "type-set-closed clause (fake-rune-for-type-set)" treeTypeSet

/-! ## END-TO-END on the real perm book — `perm-cons` (R1, the branch-split
composer). The coverage harness only `Meta.check`s corpus rows; THIS pins the
machine-generated statement to the genuine perm-cons mirror and gates the
axioms (audit 2026-07-03 finding 1) — the same discipline as my-len-my-app. -/
private def permLog : String := include_str "../acl2_samples/sorting/perm.proof-log"

/-- The parsed development of `perm.proof-log` (world + theorems + TPs all
    projected from THIS — the only input is the log). -/
def permDevelopment : Development :=
  (((ProofLog.parse permLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

def permConsProof : Option ClauseProof := do
  let log ← (ProofLog.parse permLog).toOption
  let dev ← (ClauseTree.buildDevelopment log).toOption
  findThm dev "perm-cons"

derive_world permWorld from permDevelopment

def permTPs : List (String × SExpr) := permDevelopment.typePrescriptions

/-- Drive the REAL `perm-cons` tree end-to-end: destructor elimination, the
    assume-true-false composer over the emitted clausify decision trace, the
    sibling-clause residual peel, remove-trivial-equivalences — the whole R1
    node family — as the CONDITIONAL generic mirror. -/
elab "acl2_replay_permcons_real% " : term => do
  let cpOpt ← unsafe evalExpr (Option ClauseProof)
    (mkApp (mkConst ``Option [0]) (mkConst ``ACL2.ClauseProof)) (mkConst ``permConsProof)
  let some cp := cpOpt | throwError "permConsProof: parse/extract failed"
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``permWorld, envExpr := env,
        worldVal := permDevelopment.toWorld,
        gzDefs := permDevelopment.groundZeroSnapshotDefs }
    let (proof, conds) ← replayProofConditional cfg permTPs cp
      permDevelopment.justifications
    logInfo m!"perm-cons replayed; conditions: {conds}"
    mkLambdaFVars #[env] proof

/-- The first replayed theorem of the SORTING corpus (R1). -/
def perm_cons_real_mirror := acl2_replay_permcons_real%

/-- PIN the machine-generated statement: the UNCONDITIONAL mirror of the
    ACL2 defthm
    `(implies (memb a x) (equal (perm x (cons a y)) (perm (rm a x) y)))` —
    no hypotheses at all, no weakening. ALL totality is AUTO-DISCHARGED from
    the emitted admission data (#37; perm fell to the user-fn-if-test +
    opaque-self-call-arg prover extension) and ALL TP corollaries by the TP
    prover (proveTp — the emitted corollary proved from the body by the
    predicate-carrying walk; lifter sprint 2026-07-06). -/
example :
    ∀ (env : Env),
      ∃ N, ∀ f ≥ N, ∃ v,
        evalOpt f permWorld env
          (ap2 "IMPLIES" (ap2 "MEMB" (sym "A") (sym "X"))
            (equalOf (ap2 "PERM" (sym "X") (ap2 "CONS" (sym "A") (sym "Y")))
                     (ap2 "PERM" (ap2 "RM" (sym "A") (sym "X")) (sym "Y"))))
          = some v ∧ v ≠ SExpr.nil :=
  perm_cons_real_mirror

-- Sorry-free: must be {propext, Classical.choice, Quot.sound} — no sorryAx.
#print axioms perm_cons_real_mirror

/-! ### perm-transitive: the theorem-dependency (`rule:<thm>`) conditional mirror

The first theorem replayed THROUGH user-rule applications
(docs/plans/2026-07-05_theorem-dependency-hypotheses.md). The pin locks the
machine-generated statement AFTER the v1 step-5 rule-hypothesis discharge,
the admission-derived totality discharge, AND the TP-prover discharge
(lifter sprint 2026-07-06) — the composed mirror is UNCONDITIONAL: the
whole dependency chain and every base fact machine-discharged. -/

private def ap3 (f : String) (a b c : SExpr) : SExpr :=
  .cons (sym f) (.cons a (.cons b (.cons c .nil)))

def permTransProof : Option ClauseProof := do
  let log ← (ProofLog.parse permLog).toOption
  let dev ← (ClauseTree.buildDevelopment log).toOption
  findThm dev "perm-transitive"

elab "acl2_replay_permtrans_real% " : term => do
  let cpOpt ← unsafe evalExpr (Option ClauseProof)
    (mkApp (mkConst ``Option [0]) (mkConst ``ACL2.ClauseProof)) (mkConst ``permTransProof)
  let some cp := cpOpt | throwError "permTransProof: parse/extract failed"
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``permWorld, envExpr := env,
        worldVal := permDevelopment.toWorld,
        gzDefs := permDevelopment.groundZeroSnapshotDefs }
    let (proof, conds) ← replayProofConditional cfg permTPs cp
      permDevelopment.justifications
      (rulesBefore permDevelopment "perm-transitive")
      ((developmentTheoremsWithRules permDevelopment).map fun (c, _) => (c.name, c))
    logInfo m!"perm-transitive replayed; conditions: {conds}"
    mkLambdaFVars #[env] proof

/-- The first theorem-to-theorem dependency replay of the sorting corpus. -/
def perm_transitive_real_mirror := acl2_replay_permtrans_real%

example :
    ∀ (env : Env),
      -- the genuine perm-transitive mirror (ACL2's and → if _ _ 'nil),
      -- UNCONDITIONAL
      ∃ N, ∀ f ≥ N, ∃ v,
        evalOpt f permWorld env
          (ap2 "IMPLIES"
            (ap3 "IF" (ap2 "PERM" (sym "X") (sym "Y"))
                      (ap2 "PERM" (sym "Y") (sym "Z")) quoteNil)
            (ap2 "PERM" (sym "X") (sym "Z")))
          = some v ∧ v ≠ SExpr.nil :=
  perm_transitive_real_mirror

-- Sorry-free: must be {propext, Classical.choice, Quot.sound} — no sorryAx.
#print axioms perm_transitive_real_mirror

/-! ## WP0 pins — D8 rule flush + D3/D5 ground-zero snapshots (2026-07-15).

These are EMISSION-layer facts (proof-log content), outside the differential
harness's surface (it pins evalOpt-vs-ACL2 VALUE semantics only), so they are
pinned here against the embedded isort log instead: a fork regression — the
flush lost again, snapshots not emitted, or the stored-rule shape drifting —
breaks these guards at the next recapture. -/

private def isortLog : String := include_str "../acl2_samples/sorting/isort.proof-log"

/-- The parsed development of `isort.proof-log` (parse failure ⇒ `.done` ⇒
    every pin below fails loudly). -/
def isortDevelopment : Development :=
  (((ProofLog.parse isortLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

private partial def gzDefunEvents :
    Development → List (String × SExpr × Option Justification)
  | .bind (.groundZeroDefun n _ b j) rest => (n, b, j) :: gzDefunEvents rest
  | .bind _ rest => gzDefunEvents rest
  | .done => []

private partial def gzRuleSpecs : Development → List RuleSpec
  | .bind (.groundZeroRules specs) rest => specs ++ gzRuleSpecs rest
  | .bind _ rest => gzRuleSpecs rest
  | .done => []

-- D8 (audit finding C): the book's LAST theorem's stored rule reaches its
-- OWN log. Pre-fix, HOW-MANY-ISORT's `(:RULES)` entry was stranded in the
-- accumulator (flushed only at a NEXT `:DEFTHM` that never came).
#guard (isortDevelopment.storedRules.map (·.name)).contains "HOW-MANY-ISORT"

-- D3: cited ground-zero defuns are snapshot — TRUE-LISTP with its BODY (the
-- input WP2's definition-fact recompute-check consumes), and the recursive
-- LEN with NONEMPTY recomputed admission clauses (the D6 totality input).
#guard (gzDefunEvents isortDevelopment).any fun (n, b, _) =>
  n == "TRUE-LISTP" && b != .nil
#guard (gzDefunEvents isortDevelopment).any fun (n, _, j) =>
  n == "LEN" && (j.map (·.terminationClauses.length)).getD 0 > 0

-- D5 (audit F2's expected shape, confirmed on the real snapshot): the
-- lexorder ground-zero rules are stored boolean-strengthened — :EQUIV EQUAL
-- with rhs 'T — and LEXORDER-TRANSITIVE carries (:match-free :all). WP3's
-- prelude constants recompute-check against exactly these statements.
#guard (gzRuleSpecs isortDevelopment).any fun r =>
  r.name == "LEXORDER-TRANSITIVE" && r.equiv == "equal" && r.rhs == quoteT
    && r.hyps.length == 2 && r.matchFree == some "all"
#guard (gzRuleSpecs isortDevelopment).any fun r =>
  r.name == "LEXORDER-REFLEXIVE" && r.equiv == "equal" && r.rhs == quoteT
    && r.hyps.isEmpty && r.matchFree == none

/-! ### WP1 pins — snapshot world entry + the no-shadow exclusion.

Non-builtin snapshots become World entries; `callBuiltin`-named ones must
NOT (they would shadow the builtin — D2/hnew). WP2 made the exclusion
TOTAL: the WP1 `FIX` interim keep is retired by FIX's D4 definition
fact. -/

-- a non-builtin ground-zero snapshot IS a world entry (with its body)
#guard (isortDevelopment.toWorld.defs.get? { name := "ACL2-COUNT" }).isSome
#guard (isortDevelopment.toWorld.defs.get? { name := "ALPHORDER" }).isSome
-- a builtin-named snapshot is EXCLUDED (no shadow)
#guard (isortDevelopment.toWorld.defs.get? { name := "LEN" }).isNone
#guard (isortDevelopment.toWorld.defs.get? { name := "TRUE-LISTP" }).isNone
#guard (isortDevelopment.toWorld.defs.get? { name := "LEXORDER" }).isNone
-- WP2: FIX too — its cited snapshot (simple.proof-log) stays OUT of the
-- world; the D4 route reads its body from the snapshot triples instead
#guard (simpleDevelopment.toWorld.defs.get? { name := "FIX" }).isNone
#guard simpleDevelopment.groundZeroSnapshotDefs.any fun (s, _, b) =>
  s == { name := "FIX" } && b != .nil
-- D6: a recursive snapshot's justification (recomputed clauses) reaches
-- the totality prover's input
#guard (isortDevelopment.justifications.map (·.1)).contains "ACL2-COUNT"

/-! ### WP2 pins — D4 definition facts read the EMITTED snapshot bodies.

The `gz_def_<fn>` lemmas (EvalLemmas) state callBuiltin-vs-body agreement
for EXACTLY these bodies; the guards pin the emitted artifact so a fork
drift (a changed ground-zero body no longer matching the lemma's value
composition) is caught here at elaboration, not at replay time. -/

private def gzBodyOf (d : Development) (n : String) : Option SExpr :=
  d.groundZeroSnapshotDefs.find? (fun e => e.1 == { name := n })
    |>.map (·.2.2)

-- (IF (CONSP X) (TRUE-LISTP (CDR X)) (EQUAL X 'NIL))
#guard gzBodyOf isortDevelopment "TRUE-LISTP" ==
  some (.cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" }))
      (.cons (.atom (.symbol { name := "X" })) .nil))
    (.cons (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
      (.cons (.cons (.atom (.symbol { name := "CDR" }))
        (.cons (.atom (.symbol { name := "X" })) .nil)) .nil))
    (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
      (.cons (.atom (.symbol { name := "X" }))
      (.cons quoteNil .nil))) .nil))))
-- (IF (CONSP X) (BINARY-+ '1 (LEN (CDR X))) '0)
#guard gzBodyOf isortDevelopment "LEN" ==
  some (.cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" }))
      (.cons (.atom (.symbol { name := "X" })) .nil))
    (.cons (.cons (.atom (.symbol { name := "BINARY-+" }))
      (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
        (.cons (.atom (.number (.int 1))) .nil))
      (.cons (.cons (.atom (.symbol { name := "LEN" }))
        (.cons (.cons (.atom (.symbol { name := "CDR" }))
          (.cons (.atom (.symbol { name := "X" })) .nil)) .nil)) .nil)))
    (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
      (.cons (.atom (.number (.int 0))) .nil)) .nil))))
-- (IF (ACL2-NUMBERP X) X '0)
#guard gzBodyOf simpleDevelopment "FIX" ==
  some (.cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "ACL2-NUMBERP" }))
      (.cons (.atom (.symbol { name := "X" })) .nil))
    (.cons (.atom (.symbol { name := "X" }))
    (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
      (.cons (.atom (.number (.int 0))) .nil)) .nil))))

end ACL2.Tests.Driver
