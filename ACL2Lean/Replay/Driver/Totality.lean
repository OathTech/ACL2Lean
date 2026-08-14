/-
  Driver/Totality — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  Totality from admission (#37): the decrease-clause prover.
-/
import ACL2Lean.Replay.Driver.BranchFacts
import ACL2Lean.Replay.Driver.Discharge
import ACL2Lean.Replay.CountSim
import ACL2Lean.Replay.Lemmas.DescentExt

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ## Totality from admission (#37)

Discharge the driver's `total:fn` hypotheses from the EMITTED admission data:
the justification (measure/wfrel/measured subset) and the RAW termination
clauses (the per-call-site decrease obligations). The body-convergence walk
is CASE-SPLIT style (`conv_if_split`): each `if` branch proceeds under an
explicit `toBool` fact, which is exactly what the decrease discharge consumes
at recursive call sites. Scope (decision log D5): measure
`(acl2-count <single-formal>)` under `o<`; everything else is a named
frontier and the `total:` hypothesis stays in the replayed statement's type (D6). -/

/-- Is every head of `t` walk-liftable (vars/quote/dp-primitives only)? -/
def totLiftable (t : SExpr) : Bool := (collectOpaques t).isEmpty

/-- `w.defs.get? fn = some (formals, body)` by kernel decision on the
    reflected world (hoisted from `totWalk.totDefFact`; the S4 registry
    needs it ahead of the walk). -/
def defGetFact (cfg : ReplayConfig) (fn : Symbol) (formals : List Symbol)
    (body : SExpr) : MetaM Expr := do
  let defsE ← mkAppM ``World.defs #[cfg.worldExpr]
  let lhs ← mkAppM ``DefMap.get? #[defsE, reflectSymbol fn]
  let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
  let pairE ← mkAppM ``Prod.mk #[formalsE, reflectSExpr body]
  let rhs ← mkAppM ``Option.some #[pairE]
  mkDecideProof (← mkEq lhs rhs)

/-- The value/proof plumbing a decrease discharge runs against — provided
    by each caller (admission walk: `dpVal*`; induction: `ctxVal*` + the
    case-fact inversions). All value `Expr`s must come from the SAME
    rendering so composed lemma applications unify definitionally. -/
structure DecreaseKit where
  cfg : ReplayConfig
  /-- The ambient env `Expr` the values/convergences are stated over. -/
  envE : Expr
  /-- In-scope branch facts `(test term, positive?)` for ruler verification. -/
  facts : List (SExpr × Bool)
  /-- Value `Expr` of an actual-level term. -/
  valOf : SExpr → MetaM Expr
  /-- Convergence proof `∃ N, ∀ f ≥ N, evalOpt f w envE t = some (valOf t)`. -/
  convOf : SExpr → MetaM Expr
  /-- `toBool (consp (valOf b)) = true` for a base term, from in-scope facts. -/
  conspTrueOf : SExpr → MetaM Expr
  /-- `toBool (endp (valOf b)) = false` for a term with a refuted
      `(ENDP b)` ruler fact in scope. -/
  endpFalseOf : SExpr → MetaM Expr

/-- View `(ACL2-COUNT u)` → `u`. -/
def countOfView (t : SExpr) : Option SExpr :=
  match t with
  | .cons (.atom (.symbol c)) (.cons u .nil) =>
    if c.name == "ACL2-COUNT" then some u else none
  | _ => none

/-- View `(LEN u)` → `u` (P3, bsort — BNEXT's `:MEASURE (LEN X)`). -/
def lenOfView (t : SExpr) : Option SExpr :=
  match t with
  | .cons (.atom (.symbol c)) (.cons u .nil) =>
    if c.name == "LEN" then some u else none
  | _ => none

/-- LEN-measure decrease walk (the `lenNat` twin of `chainLt`, P3): prove
    `lenNat (valOf t) < lenNat (valOf base)`. Arms, each keyed to a real
    emitted call-site shape and fail-closed otherwise:
    - `(CDR u)`: strict at the base under consp evidence; `≤`-composed over
      an inner strict chain otherwise (the `chainLt` pattern).
    - `(CONS a (CDR w))`: re-consing onto a cdr PRESERVES length under
      `consp w` (`lenNat_cons_cdr_eq_of_consp` — BNEXT's swap site), so the
      walk collapses to `w` and recurses; `w == base` then fails at the
      recursion's missing arm, never proves a non-decrease. -/
partial def chainLtLen (kit : DecreaseKit) (base t : SExpr) : MetaM Expr := do
  match t with
  | .cons (.atom (.symbol d)) (.cons u .nil) =>
    unless d.name == "CDR" do
      throwFrontier m!"chainLtLen: unary head {d.name} has no LEN decrease \
          arm (frontier): {repr t}"
    if u == base then
      let hConsp ← kit.conspTrueOf base
      mkAppM ``ACL2.Replay.lenNat_cdr_lt_of_consp #[hConsp]
    else
      let inner ← chainLtLen kit base u
      let vu ← kit.valOf u
      mkAppM ``Nat.lt_of_le_of_lt
        #[← mkAppM ``ACL2.Replay.lenNat_cdr_le #[vu], inner]
  | .cons (.atom (.symbol c))
      (.cons a (.cons (.cons (.atom (.symbol d2)) (.cons w .nil)) .nil)) => do
    unless c.name == "CONS" && d2.name == "CDR" do
      throwFrontier m!"chainLtLen: shape {repr t} has no LEN decrease arm \
          (frontier)"
    let hConspW ← kit.conspTrueOf w
    let va ← kit.valOf a
    let hEq ← mkAppM ``ACL2.Replay.lenNat_cons_cdr_eq_of_consp
      #[va, hConspW]
    let hLt ← chainLtLen kit base w
    mkAppM ``Nat.lt_of_le_of_lt #[← mkAppM ``Nat.le_of_eq #[hEq], hLt]
  | _ => throwFrontier m!"chainLtLen: shape {repr t} has no LEN decrease \
      arm (frontier)"

/-- Count-walk ≤ leg: `(valOf t).consCount ≤ (valOf base).consCount` for `t`
    a (possibly empty) cdr/car chain over `base` — unconditional per-step
    `consCount_cdr_le`/`car_le` composed by transitivity. -/
partial def chainLe (kit : DecreaseKit) (base t : SExpr) :
    MetaM Expr := do
  if t == base then
    mkAppM ``Nat.le_refl #[← mkAppM ``SExpr.consCount #[← kit.valOf base]]
  else match t with
  | .cons (.atom (.symbol d)) (.cons u .nil) =>
    if d.name == "CDR" || d.name == "CAR" then
      let inner ← chainLe kit base u
      let vu ← kit.valOf u
      let hLe ← if d.name == "CDR" then mkAppM ``ACL2.consCount_cdr_le #[vu]
        else mkAppM ``ACL2.consCount_car_le #[vu]
      mkAppM ``Nat.le_trans #[hLe, inner]
    else
      throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
          the destructor-chain walk over {repr base} (frontier)"
  | _ => throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
      the destructor-chain walk over {repr base} (frontier)"

/-- Count-walk strict leg: `(valOf t).consCount < (valOf base).consCount`
    for `t` a NON-EMPTY cdr/car chain over `base` — the innermost destructor
    application to `base` is the ONE strict step (from `base`'s consp fact);
    every outer layer composes by `≤`. -/
partial def chainLt (kit : DecreaseKit) (base t : SExpr) : MetaM Expr := do
  match t with
  | .cons (.atom (.symbol d)) (.cons u .nil) =>
    if d.name == "CDR" || d.name == "CAR" then
      if u == base then
        let hConsp ← kit.conspTrueOf base
        if d.name == "CDR" then
          mkAppM ``ACL2.consCount_cdr_lt_of_consp #[hConsp]
        else
          mkAppM ``ACL2.consCount_car_lt_of_consp #[hConsp]
      else
        let inner ← chainLt kit base u
        let vu ← kit.valOf u
        let hLe ← if d.name == "CDR" then mkAppM ``ACL2.consCount_cdr_le #[vu]
          else mkAppM ``ACL2.consCount_car_le #[vu]
        mkAppM ``Nat.lt_of_le_of_lt #[hLe, inner]
    else if d.name == "EVENS" || d.name == "ODDS" then
      -- S4 REGISTRY (#37 plan): measure fns with PROVED Lean models
      -- (`CountSim`): sim lemma bridges the pinned value to the model,
      -- Count lemma gives the model-level strict decrease. Only direct
      -- application to the measured base; the world's shape must be
      -- byte-equal to the shape the sim lemma was proved against.
      unless u == base do
        throwFrontier m!"dischargeDecrease: registry fn {d.name} applied \
            to {repr u} ≠ the measured base {repr base} (frontier)"
      let checkShape (fn : Symbol) (expBody : SExpr) : MetaM Unit := do
        match kit.cfg.worldVal.defs.get? fn with
        | some (formals, body) =>
          unless formals == [simL] && body == expBody do
            throwFrontier m!"dischargeDecrease: the world's {fn.name} \
                differs from the proved sim shape (frontier)"
        | none =>
          throwFrontier m!"dischargeDecrease: registry fn {fn.name} not \
              in the world (frontier)"
      checkShape evensSym evensBody
      let hdefE ← defGetFact kit.cfg evensSym [simL] evensBody
      let hnC ← proveNoShadow kit.cfg { name := "CONSP" }
      let hnCar ← proveNoShadow kit.cfg { name := "CAR" }
      let hnCdr ← proveNoShadow kit.cfg { name := "CDR" }
      let hnCons ← proveNoShadow kit.cfg { name := "CONS" }
      let vT ← kit.valOf t
      let hvT ← kit.convOf t
      let xvE ← kit.valOf base
      let hxv ← kit.convOf base
      let uE := reflectSExpr u
      let hSim ←
        if d.name == "EVENS" then
          mkAppM ``evens_sim
            #[kit.cfg.worldExpr, kit.envE, hdefE, hnC, hnCar, hnCdr, hnCons,
              uE, xvE, vT, hxv, hvT]
        else do
          checkShape oddsSym oddsBody
          let hdefO ← defGetFact kit.cfg oddsSym [simL] oddsBody
          mkAppM ``odds_sim
            #[kit.cfg.worldExpr, kit.envE, hdefE, hdefO, hnC, hnCar, hnCdr,
              hnCons, uE, xvE, vT, hxv, hvT]
      let h1 ← kit.endpFalseOf base
      let h2 ← kit.endpFalseOf
        (.cons (.atom (.symbol { name := "CDR" })) (.cons base .nil))
      let hCnt ←
        if d.name == "EVENS" then mkAppM ``ACL2.consCount_evens_lt #[h1, h2]
        else mkAppM ``ACL2.consCount_odds_lt #[h1, h2]
      mkAppM ``count_lt_of_eq #[hSim, hCnt]
    else
      throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
          the destructor-chain walk over {repr base} (frontier: candidate \
          registry head {d.name})"
  | _ => throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
      the destructor-chain walk over {repr base} (frontier)"

/-- The RECORDED-TERMINATION route's per-defun bundle (sorting arc
    2026-07-28): the replayed admission-waterfall theorem (applied at an
    env by `thmAt`), the emitted non-`O-P` termination clauses in goal
    order, and the byte-checked world facts the `interp_decrease_decode`
    application consumes. Assembled once per defun in `proveTotality`. -/
structure RecTermInfo where
  /-- Apply the termination replayed statement at an env: `EvTrue w env <goal>`. -/
  thmAt : Expr → MetaM Expr
  /-- The goal literal (the root clause's single literal — the IF-encoded
      conjunction of the non-trivial obligations). -/
  goalLit : SExpr
  /-- The emitted termination clauses the goal conjoins, in goal order
      (non-`O-P` only for the ACL2-COUNT class; ALL clauses when the `O-P`
      obligation survives into the waterfall — user measure fns). -/
  clauses : List (List SExpr)
  /-- The count fn (the justification measure's head — `ACL2-COUNT` for the
      default measure, the user fn otherwise). -/
  cntSym : Symbol
  hNsCnt : Expr
  hDefCnt : Expr
  hNoLt : Expr
  hNoConsp : Expr
  hDefF : Expr
  hDefO : Expr
  /-- The count fn's accumulated totality fact (`mkTotalityHypType` shape). -/
  cntTotal : Expr
  /-- The count fn's `tp:` hypothesis fvar (the standard nonneg-int
      corollary — shape-checked by the assembler). -/
  tpFVar : Expr

/-- ACL2's `conjoin` over clause disjunctions: `[c] → c`,
    `c :: rest → (IF c (conjoin rest) 'NIL)` — the admission goal's spine
    (ONE definition; audit F6 deduplicated the two let-rec clones). -/
def conjoinDisjTerm : List SExpr → SExpr
  | [] => quoteT
  | [c] => c
  | c :: rest =>
    .cons (.atom (.symbol { name := "IF" }))
      (.cons c (.cons (conjoinDisjTerm rest) (.cons quoteNil .nil)))

/-- Assemble the RECORDED-TERMINATION bundle for one defun (sorting arc
    2026-07-28): byte-check every world shape the decode consumes, resolve
    the replayed statement's conditions against the consumer telescope's hypothesis
    fvars, and validate the goal literal against the conjoin of the emitted
    clauses (non-`O-P` only or all, emission order or reversed — the goal
    pins which).
    Frontier-throws on any gap, so a failed assembly keeps the fn on the
    destructor route's honest frontier. -/
def mkRecTermInfo (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (hypFVars : List (String × Expr))
    (tpCors : List (String × SExpr))
    (just : Justification)
    (replayedConst : Name) (conds : List String) (goalLits : List SExpr) :
    MetaM RecTermInfo := do
  let [goalLit] := goalLits
    | throwFrontier m!"recorded route: multi-literal termination goal \
        (frontier)"
  -- the count fn IS the justification measure's head (read off the emitted
  -- :MEASURE — ACL2-COUNT for the default, the user fn for a user measure
  -- like bsort's BNEXT-SIZE); every shape below is checked against it
  let cntSym ← match just.measure with
    | .cons (.atom (.symbol c)) (.cons _ .nil) => pure c
    | _ => throwFrontier m!"recorded route: measure {repr just.measure} is \
        not a unary application (frontier)"
  -- the emitted clauses, ordered to match the goal's conjoin spine. ACL2
  -- discharges the `(O-P (cnt v))` obligation BEFORE clausify when its
  -- type-set already knows the measure is an ordinal (the ACL2-COUNT
  -- class — the goal conjoins only the non-O-P clauses); for a USER
  -- measure fn the obligation survives into the waterfall and the goal
  -- conjoins ALL emitted clauses (bsort's BNEXT-SIZE). Both shapes are
  -- recompute-checked against the emitted goal, either order.
  let isOp (c : SExpr) : Bool :=
    match c.toList? with
    | some [.cons (.atom (.symbol op)) _] => op.name == "O-P"
    | _ => false
  let allCl ← just.terminationClauses.mapM
    fun c => match c.toList? with
      | some lits => pure lits
      | none => throwError "recorded route: malformed termination clause \
          {repr c}"
  let nonOp := (just.terminationClauses.zip allCl).filterMap
    fun (c, lits) => if isOp c then none else some lits
  let clauses ←
    if conjoinDisjTerm (nonOp.map disjoinTerm) == goalLit then pure nonOp
    else if conjoinDisjTerm (nonOp.reverse.map disjoinTerm) == goalLit then
      pure nonOp.reverse
    else if conjoinDisjTerm (allCl.map disjoinTerm) == goalLit then
      pure allCl
    else if conjoinDisjTerm (allCl.reverse.map disjoinTerm) == goalLit then
      pure allCl.reverse
    else throwFrontier m!"recorded route: goal literal does not conjoin the \
        emitted clauses (either order) — recompute/emission divergence"
  -- byte-checked world shapes
  let hNsCnt ← proveNotSpecial cntSym
  let some (cntFormals, cntBody) := cfg.worldVal.defs.get? cntSym
    | throwFrontier m!"recorded route: {cntSym.name} not in the world \
        (frontier)"
  let [cntFormal] := cntFormals
    | throwFrontier m!"recorded route: {cntSym.name} arity ≠ 1 (frontier)"
  let hDefCnt ← defGetFact cfg cntSym cntFormals cntBody
  let hNoLt ← proveNoShadow cfg { name := "<" }
  let hNoConsp ← proveNoShadow cfg { name := "CONSP" }
  let some (finpFormals, finpBody) := cfg.worldVal.defs.get? { name := "O-FINP" }
    | throwFrontier m!"recorded route: O-FINP not in the world (frontier)"
  unless finpFormals == [oltXSym] && finpBody == oFinpBodyShape do
    throwFrontier m!"recorded route: the world's O-FINP differs from the \
        proved shape (frontier)"
  let hDefF ← defGetFact cfg { name := "O-FINP" } [oltXSym] oFinpBodyShape
  let hDefF ← mkExpectedTypeHint hDefF (← mkEq
    (← mkAppM ``DefMap.get? #[← mkAppM ``World.defs #[cfg.worldExpr],
        reflectSymbol { name := "O-FINP" }])
    (← mkAppM ``Option.some #[← mkAppM ``Prod.mk
      #[← mkListLit (mkConst ``Symbol) [mkConst ``ACL2.Replay.oltXSym],
        mkConst ``ACL2.Replay.oFinpBodyShape]]))
  let some (oltFormals, oltBody) := cfg.worldVal.defs.get? { name := "O<" }
    | throwFrontier m!"recorded route: O< not in the world (frontier)"
  unless oltFormals == [oltXSym, oltYSym] do
    throwFrontier m!"recorded route: O< formals ≠ (X Y) (frontier)"
  -- extract the else-arm and confirm the byte shape by reconstruction
  let elseBr ← match oltBody with
    | .cons _ (.cons _ (.cons _ (.cons e .nil))) => pure e
    | _ => throwFrontier m!"recorded route: the world's O< body shape \
        (frontier)"
  unless oltBody == (ACL2.Replay.oLtBodyShapeWith elseBr) do
    throwFrontier m!"recorded route: the world's O< differs from the proved \
        shape (frontier)"
  let hDefO ← defGetFact cfg { name := "O<" } [oltXSym, oltYSym] oltBody
  let hDefO ← mkExpectedTypeHint hDefO (← mkEq
    (← mkAppM ``DefMap.get? #[← mkAppM ``World.defs #[cfg.worldExpr],
        reflectSymbol { name := "O<" }])
    (← mkAppM ``Option.some #[← mkAppM ``Prod.mk
      #[← mkListLit (mkConst ``Symbol)
          [mkConst ``ACL2.Replay.oltXSym, mkConst ``ACL2.Replay.oltYSym],
        ← mkAppM ``ACL2.Replay.oLtBodyShapeWith #[reflectSExpr elseBr]]]))
  -- the count fn's accumulated totality + its STANDARD nonneg-int TP hyp
  let cntTotal ← match totalEnv.find? (fun (n, _, _) => n == cntSym.name) with
    | some (_, _, pf) => pure pf
    | none =>
      match hypFVars.lookup s!"total:{cntSym.name}" with
      | some fv => pure fv
      | none => throwFrontier m!"recorded route: total:{cntSym.name} \
          neither proved nor offered (frontier)"
  let some tpFVar := hypFVars.lookup s!"tp:{cntSym.name}"
    | throwFrontier m!"recorded route: tp:{cntSym.name} not offered \
        (frontier)"
  let cntApp : SExpr :=
    .cons (.atom (.symbol cntSym)) (.cons (.atom (.symbol cntFormal)) .nil)
  let expectedCor : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons (.cons (.atom (.symbol { name := "INTEGERP" })) (.cons cntApp .nil))
        (.cons (.cons (.atom (.symbol { name := "NOT" }))
            (.cons (.cons (.atom (.symbol { name := "<" }))
                (.cons cntApp
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                      (.cons (.atom (.number (.int 0))) .nil))
                    .nil)))
              .nil))
          (.cons quoteNil .nil)))
  unless tpCors.lookup cntSym.name == some expectedCor do
    throwFrontier m!"recorded route: {cntSym.name}'s TP corollary is not \
        the standard nonneg-int shape (frontier)"
  let thmAt := fun (envE : Expr) => do
    let condArgs ← conds.mapM fun c => do
      -- a `total:` condition is preferentially resolved from the fixpoint's
      -- OWN accumulated proofs (closed terms — no residual hypothesis);
      -- tp:/rule: conditions come from the consumer telescope's fvars and
      -- surface honestly in the theorem's cond[…] list.
      if c.startsWith "total:" then
        if let some (_, _, pf) := totalEnv.find?
            (fun (n, _, _) => s!"total:{n}" == c) then
          return pf
      match hypFVars.lookup c with
      | some fv => pure fv
      | none => throwFrontier m!"recorded route: condition {c} not offered \
          by the consumer telescope (frontier)"
    let app := mkAppN (mkApp (mkConst replayedConst) envE) condArgs.toArray
    -- condition resolution is by STRING key, positionally (audit 2026-08-05
    -- S3: "ASSUMED:dp-fact" is one key for many leaves; `tp:` can be
    -- offered twice per fn) — type-check the application here so a
    -- mis-paired hypothesis can never be accepted silently.
    Lean.Meta.check app
    pure app
  return { thmAt, goalLit, clauses, cntSym, hNsCnt, hDefCnt, hNoLt,
           hNoConsp, hDefF, hDefO, cntTotal, tpFVar }

/-- The recorded-termination DECREASE at a self-call site: locate the
    emitted clause whose `O<` matches this call's measured actual, verify
    its rulers against the in-scope branch facts (the `dischargeDecrease`
    coverage rule), instantiate the REPLAYED admission theorem at the
    ambient env, extract that clause's conjunct (recompute-checked conjoin
    spine), peel the rulers, and decode the surviving `O<` fact into the
    `interpCount` ordering (`interp_decrease_decode`). Returns
    `interpCount w cnt vσ < interpCount w cnt (value of the measured
    formal)`. Fail-closed at every joint. -/
def dischargeDecreaseRecorded (cfg : ReplayConfig) (envE : Expr)
    (rulerCovered : SExpr → Bool)
    (rulerNilConv : SExpr → MetaM Expr)
    (termConv : SExpr → MetaM Expr)
    (walkConv : SExpr → MetaM Expr)
    (info : RecTermInfo) (measuredFormal : Symbol)
    (aM : SExpr) (hconvσ : Expr) : MetaM Expr := do
  let cntApp (u : SExpr) : SExpr :=
    .cons (.atom (.symbol info.cntSym)) (.cons u .nil)
  let mVar : SExpr := .atom (.symbol measuredFormal)
  let wanted : SExpr :=
    .cons (.atom (.symbol { name := "O<" }))
      (.cons (cntApp aM) (.cons (cntApp mVar) .nil))
  -- locate the covering emitted clause (rulers first, O< LAST — validated)
  -- accept ANY matching emitted clause whose rulers are all covered (audit
  -- F5: `dischargeDecrease` collects all matches — the two carve-out gates
  -- must agree)
  let matching := info.clauses.filter (·.contains wanted)
  if matching.isEmpty then
    throwFrontier m!"recorded decrease: no emitted obligation with \
        {repr wanted} (emission gap)"
  let some cl := matching.find? (fun c =>
      c.getLast? == some wanted && c.dropLast.all rulerCovered)
    | throwFrontier m!"recorded decrease: no matching emitted obligation \
        has all ruling literals established on this branch (frontier): \
        {repr matching}"
  let rulers := cl.dropLast
  -- the goal spine: conjoin of the clauses' disjunctions — recompute-check
  let conjTerms := info.clauses.map (fun c => disjoinTerm c)
  unless conjoinDisjTerm conjTerms == info.goalLit do
    throwError "recorded decrease: conjoin of the emitted clauses ≠ the \
        replayed goal literal (recompute/emission divergence)"
  let some k := info.clauses.findIdx? (· == cl)
    | throwError "recorded decrease: internal — clause index"
  -- extract conjunct k from the instantiated theorem
  let mut curEv ← info.thmAt envE
  let mut rest := conjTerms
  let mut i := 0
  let mut conjEv? : Option Expr := none
  while conjEv?.isNone do
    match rest with
    | [] => throwError "recorded decrease: internal — conjunct walk"
    | [_] =>
      unless i == k do
        throwError "recorded decrease: internal — conjunct index"
      conjEv? := some curEv
    | c :: restTerms => do
      let hEx ← walkConv c
      if i == k then
        let kLam ← withLocalDeclD `va (mkConst ``SExpr) fun va => do
          let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr c) va
          withLocalDeclD `hva convTy fun hva => do
            let hne ← mkAppM ``evtrue_and_left #[hva, curEv]
            mkLambdaFVars #[va, hva]
              (← mkAppM ``evtrue_of_conv_ne_nil #[hva, hne])
        conjEv? := some (← mkAppM ``exists_conv_elim #[hEx, kLam])
      else
        let kLam ← withLocalDeclD `va (mkConst ``SExpr) fun va => do
          let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr c) va
          withLocalDeclD `hva convTy fun hva => do
            let hne ← mkAppM ``evtrue_and_left #[hva, curEv]
            let htrue ← mkAppM ``toBool_true_of_ne_nil #[hne]
            mkLambdaFVars #[va, hva]
              (← mkAppM ``evtrue_and_right #[hva, htrue, curEv])
        curEv ← mkAppM ``exists_conv_elim #[hEx, kLam]
        rest := restTerms
        i := i + 1
  let some conjEv := conjEv? | throwError "recorded decrease: internal"
  -- peel the rulers (the caller's plumbing pins each covered ruler's nil
  -- convergence)
  curEv := conjEv
  for lit in rulers do
    let hcnil ← rulerNilConv lit
    curEv ← mkAppM ``evtrue_tail_of_if_head_nil #[hcnil, curEv]
  -- decode into the interpCount ordering
  let hm ← termConv mVar
  let hcσ ← mkAppM' info.cntTotal
    #[envE, reflectSExpr aM, ← mkAppM ``conv_ex_of_vfix #[hconvσ]]
  let hcm ← mkAppM' info.cntTotal
    #[envE, reflectSExpr mVar, ← mkAppM ``conv_ex_of_vfix #[hm]]
  let htpσ := mkAppN info.tpFVar #[envE, reflectSExpr aM]
  let htpm := mkAppN info.tpFVar #[envE, reflectSExpr mVar]
  mkAppM ``interp_decrease_decode
    #[info.hNsCnt, info.hDefCnt, info.hNoLt, info.hNoConsp, info.hDefF,
      info.hDefO, hconvσ, hm, hcσ, hcm, htpσ, htpm, curEv]

/-- The GENERAL admission-decrease prover (#37 rework, design I4; plan
    `docs/plans/2026-07-18_decrease-prover-rework.md`). Proves the strict
    count decrease of the σ-instance of the measure AT THE VALUE LEVEL:

    1. locate the EMITTED termination clause whose `O<` literal is exactly
       `(O< σ(μ') μ')` — `μ'` the justification's measure with its formals
       RENAMED (`rnFormals ↦ rnArgs`) to the caller's actual terms (identity
       at admission; the induction scheme's actuals at IH time), σ the
       caller's decrease substitution (`sFormals ↦ sArgs`: call args / the
       IH alist). A decrease ACL2 did not emit is NEVER proved (carve-out
       scope) — no matching clause, hard-fail;
    2. verify every OTHER literal of that clause against an in-scope fact:
       `(NOT tst)` needs `(tst, true)`, a bare literal needs `(lit, false)`;
       any uncovered ruler hard-fails;
    3. discharge the `<` by the COUNT WALK: single-count measures via the
       destructor-chain walk (`chainLt`); sum measures componentwise (one
       strict component) or the swap pattern (`consCount_swap_…`).

    `valOf` renders an actual-level term's VALUE `Expr` (the caller's value
    plumbing — dpValExpr at admission, ctxValExpr at IH time);
    `conspProofOf b` returns `toBool (consp (valOf b)) = true` for a base
    term (from in-scope facts; the induction caller's endp/atom/or-form
    inversion lives behind it). -/
def dischargeDecrease (just : Justification)
    (rnFormals : List Symbol) (rnArgs : List SExpr)
    (sFormals : List Symbol) (sArgs : List SExpr)
    (kit : DecreaseKit) : MetaM Expr := do
  let facts := kit.facts
  -- ASSUMPTION (audit R1-3): `substTerm` is binder-blind (treats every
  -- application uniformly, opaque only to QUOTE). Sound here because ACL2
  -- measures/rulers in scope are binder-free ((acl2-count _) / sums /
  -- recognizer-and-equality rulers); a LAMBDA/LET-containing measure would
  -- mis-rename and then fail the wanted-match (frontier), never mis-prove.
  let rn (t : SExpr) : SExpr := ACL2.Replay.substTerm rnFormals rnArgs t
  let sub (t : SExpr) : SExpr := ACL2.Replay.substTerm sFormals sArgs t
  let measure' := rn just.measure
  let sμ := sub measure'
  if sμ == measure' then
    throwFrontier m!"dischargeDecrease: substitution does not move the \
        measure {repr measure'} (identity — no decrease to prove)"
  let wanted : SExpr :=
    .cons (.atom (.symbol { name := "O<" })) (.cons sμ (.cons measure' .nil))
  let renamed ← just.terminationClauses.mapM fun c =>
    match c.toList? with
    | some lits => pure (lits.map rn)
    | none => throwError "dischargeDecrease: malformed emitted termination \
        clause (not a list): {repr c}"
  let matching := renamed.filter (·.contains wanted)
  if matching.isEmpty then
    throwFrontier m!"dischargeDecrease: no emitted decrease obligation \
        matching {repr wanted} (emission gap or unsupported substitution)"
  -- a ruling literal of the (disjunctive) obligation must be established
  -- FALSE on this branch — `branchEstablishes` (Driver/BranchFacts) is the
  -- shared coverage rule: direct facts, recognizer duality
  -- (CONSP/ENDP/ATOM — sorting arc 2026-07-29, extended to ATOM by the
  -- TP-replay arc's ATOM-leg increment 2026-08-13, because ACL2 spells
  -- rulers with `atom` both bare (PERM-COUNTER-EXAMPLE, REV-ACC) and as
  -- the leaves of its or-normal forms), `NOT`, and ACL2's IF-NORMAL FORMS
  -- (`(IF a a c)` = or, `(IF a b 'NIL)` = and), decomposed recursively.
  -- This widens only the COVERAGE check: the decrease PROOF's
  -- conspTrueOf/endpFalseOf independently require the value facts.
  let uncoveredOf (lits : List SExpr) : List SExpr :=
    lits.filter fun lit =>
      lit != wanted && !branchEstablishes facts lit false
  let uncov := matching.map uncoveredOf
  unless uncov.any (·.isEmpty) do
    -- MERGED-IH complementary pair (e.g. how-many: two call sites with the
    -- same substitution under complementary `(eql …)` polarities merge into
    -- ONE induction case whose facts establish neither). ACL2's own merged-
    -- case justification: either polarity's emitted clause applies and both
    -- conclude the SAME `O<` — so exactly two matching clauses whose sole
    -- uncovered rulers are `T` and `(NOT T)` license the decrease.
    let notOf (t : SExpr) : SExpr :=
      .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
    let complementary := match uncov with
      | [[l1], [l2]] => l1 == notOf l2 || l2 == notOf l1
      | _ => false
    unless complementary do
      throwFrontier m!"dischargeDecrease: no matching emitted obligation has \
          all ruling literals established on this branch (uncovered, per \
          clause: {repr uncov}; obligations {repr matching})"
  -- 3. the Count walk, by measure shape
  if let some base := countOfView measure' then
    return ← chainLt kit base (sub base)
  -- 3'. the LEN walk (P3, bsort — `chainLtLen`, the lenNat twin)
  if let some base := lenOfView measure' then
    return ← chainLtLen kit base (sub base)
  match measure' with
  | .cons (.atom (.symbol plus)) (.cons cx (.cons cy .nil)) =>
    unless plus.name == "BINARY-+" do
      throwFrontier m!"dischargeDecrease: measure {repr measure'} beyond \
          count/sum-of-counts (frontier)"
    let some x := countOfView cx
      | throwFrontier m!"dischargeDecrease: sum component {repr cx} is not \
          (ACL2-COUNT _) (frontier)"
    let some y := countOfView cy
      | throwFrontier m!"dischargeDecrease: sum component {repr cy} is not \
          (ACL2-COUNT _) (frontier)"
    let (sx, sy) := (sub x, sub y)
    -- the SWAP pattern (INTERLEAVE's scheme): (x, y) := (y, cdr x)
    let cdrOf (u : SExpr) : SExpr :=
      .cons (.atom (.symbol { name := "CDR" })) (.cons u .nil)
    if sx == y && sy == cdrOf x then
      let hConsp ← kit.conspTrueOf x
      return ← mkAppOptM ``ACL2.consCount_swap_cdr_sum_lt_consp
        #[none, some (← kit.valOf y), some hConsp]
    -- componentwise: each component ≤ its original, at least one strict
    let leg (b t : SExpr) : MetaM (Bool × Expr) := do
      if t == b then pure (false, ← chainLe kit b t)
      else
        try pure (true, ← chainLt kit b t)
        catch e =>
          if isFrontierErr e then pure (false, ← chainLe kit b t)
          else throw e
    let (strictX, px) ← leg x sx
    let (strictY, py) ← leg y sy
    if strictX then
      mkAppM ``add_lt_add_of_lt_of_le #[px, ← chainLe kit y sy]
    else if strictY then
      mkAppM ``add_lt_add_of_le_of_lt #[px, py]
    else
      throwFrontier m!"dischargeDecrease: no strict component in sum \
          decrease ({repr sx}, {repr sy}) vs ({repr x}, {repr y}) (frontier)"
  | _ =>
    throwFrontier m!"dischargeDecrease: measure {repr measure'} beyond \
        count/sum-of-counts (frontier)"


/-- The body-convergence walk: a proof of `∃N∃v ∀f≥N, eval envE t = some v`.
    `vals` carries each formal's VALUE expr and var-convergence proof;
    `facts` the branch context; `totalEnv` earlier functions' totality
    proofs (hypothesis-shaped); `selfC` the recursion data (the IH plus the
    justification whose emitted clauses license its use). -/
partial def totWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (selfC : Option (String × Symbol × Expr × Justification × Option RecTermInfo))
    (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  if totLiftable t then
    -- vars / quote / dp-primitive tree: value-characterize and ∃-pack
    let pf ← dpValProof cfg envE [] [] varP t
    return ← mkAppM ``conv_ex_of_vfix #[pf]
  -- the SHARED application logic (builtins / self-calls / earlier
  -- fns), reachable from BOTH the ternary arm (non-IF heads) and the
  -- general spine arm (sorting arc 2026-07-29)
  let rec goApp (fs : Symbol) (args : List SExpr) : MetaM Expr := do
    -- dp-known BUILTIN over non-liftable args (e.g. a self-call inside
    -- binary-+): walk the args and compose in the ∃∃ shape
    if args.length == 1 then
      if let some (fn, cb) := dpUnary.lookup fs.name then
        let pa ← totWalk cfg envE vals facts totalEnv selfC args[0]!
        let hNs ← proveNotSpecial fs
        let hNo ← proveNoShadow cfg fs
        return ← mkAppM ``conv_builtin1_ex
          #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr args[0]!,
            mkConst fn, hNs, hNo, mkConst cb, pa]
    if args.length == 2 then
      if let some (fn, cb) := dpBinary.lookup fs.name then
        let pa ← totWalk cfg envE vals facts totalEnv selfC args[0]!
        let pb ← totWalk cfg envE vals facts totalEnv selfC args[1]!
        let hNs ← proveNotSpecial fs
        let hNo ← proveNoShadow cfg fs
        return ← mkAppM ``conv_builtin2_ex
          #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr args[0]!,
            reflectSExpr args[1]!, mkConst fn, hNs, hNo, mkConst cb, pa, pb]
    -- SELF-call: the IH, licensed by the emitted decrease obligation
    if let some (selfName, measuredFormal, ih, just, recInfo?) := selfC then
      if fs.name == selfName then
        match cfg.worldVal.defs.get? fs with
        | some (formals, body) =>
          unless args.length == formals.length do
            throwFrontier m!"proveTotality: self-call arity mismatch {repr (SExpr.cons (.atom (.symbol fs)) (args.foldr SExpr.cons .nil))}"
          let mIdx := formals.findIdx (· == measuredFormal)
          -- RECORDED-TERMINATION route (sorting arc 2026-07-28): the
          -- decrease comes from the REPLAYED admission waterfall via
          -- `dischargeDecreaseRecorded`; the measured actual (e.g. qsort's
          -- `(FILTER …)`) is converged by the walk itself and ∃-eliminated.
          -- 1-ary only for now (qsort's class); wider arities stay on the
          -- destructor route's frontier.
          if let some recInfo := recInfo? then
            match formals, args with
            | [f1], [a1] =>
              unless measuredFormal == f1 do
                throwFrontier m!"proveTotality: recorded route measured \
                    formal mismatch (frontier)"
              let hNs ← proveNotSpecial fs
              let hDef ← totDefFact cfg fs formals body
              let hcEx ← totWalk cfg envE vals facts totalEnv selfC a1
              let varP : Symbol → Option (Expr × Expr) := fun s =>
                (vals.find? (fun (f, _, _) => f == s)).map
                  (fun (_, v, p) => (v, p))
              let varVal := dpValProof.dpVarVal envE varP
              let kLam ← withLocalDeclD `vs (mkConst ``SExpr) fun vσ => do
                let convTy ← mkValConvPropEx cfg.worldExpr envE
                  (reflectSExpr a1) vσ
                withLocalDeclD `hcs convTy fun hconvσ => do
                  -- NOT-CONSP DUALITY (audit F1): an emitted negative
                  -- recognizer ruler is refuted by the translated body's
                  -- truthy `(CONSP b)` branch fact. R0 item 9 (2026-08-13):
                  -- this was a hand CLONE of `BranchFacts.recogView` that
                  -- knew ENDP only, so emitted `(ATOM …)` rulers stayed
                  -- uncovered here while every sibling gate handled them —
                  -- now DELEGATED to `recogView` so the two cannot diverge.
                  let notConspDualOf : SExpr → Option SExpr := fun lit =>
                    match recogView lit with
                    | some (b, false) =>
                      some (.cons (.atom (.symbol { name := "CONSP" }))
                        (.cons b .nil))
                    | _ => none
                  -- …and the matching VALUE-level nil lemma, per recognizer
                  -- (the peel states `<recog> vb = nil`, so it must name the
                  -- ruler's own recognizer, not ENDP always).
                  let dualNilLemma : SExpr → Option Name := fun lit =>
                    match lit with
                    | .cons (.atom (.symbol r)) (.cons _ .nil) =>
                      if r.name == "ENDP" then
                        some ``logic_endp_nil_of_consp_toBool
                      else if r.name == "ATOM" then
                        some ``logic_atom_nil_of_consp_toBool
                      else none
                    | _ => none
                  let dec ← dischargeDecreaseRecorded cfg envE
                    (rulerCovered := fun lit =>
                      facts.any (fun (f, pos, _) => f == lit && !pos) ||
                      (match notConspDualOf lit with
                       | some dual =>
                         facts.any (fun (f, pos, _) => f == dual && pos)
                       | none => false))
                    (rulerNilConv := fun lit => do
                      unless totLiftable lit do
                        throwFrontier m!"recorded decrease: non-liftable \
                            ruler {repr lit} (frontier)"
                      let hcnv ← dpValProof cfg envE [] [] varP lit
                      match facts.find?
                          (fun (f, pos, _) => f == lit && !pos) with
                      | some (_, _, hb) =>
                        let vc ← dpValExpr [] varVal lit
                        let hnil ← mkAppM ``Iff.mp
                          #[← mkAppM ``Logic.toBool_eq_false #[vc], hb]
                        mkAppM ``conv_nil_of_conv_eq #[hcnv, hnil]
                      | none =>
                        let some dual := notConspDualOf lit
                          | throwError "recorded decrease: internal — ruler \
                              fact vanished"
                        let some (_, _, hb) := facts.find?
                            (fun (f, pos, _) => f == dual && pos)
                          | throwError "recorded decrease: internal — dual \
                              ruler fact vanished"
                        let some nilLemma := dualNilLemma lit
                          | throwFrontier m!"recorded decrease: not-consp \
                              ruler {repr lit} has no value-level nil lemma \
                              (frontier)"
                        -- hb : toBool (consp vb) = true ⇒ <recog> vb = nil
                        let hnil ← mkAppM nilLemma #[hb]
                        mkAppM ``conv_nil_of_conv_eq #[hcnv, hnil])
                    (termConv := fun u => dpValProof cfg envE [] [] varP u)
                    (walkConv := fun u =>
                      totWalk cfg envE vals facts totalEnv none u)
                    recInfo measuredFormal a1 hconvσ
                  let hbody ← mkAppM' ih #[vσ, dec]
                  let p ← mkAppM ``conv_defn_1_ex
                    #[cfg.worldExpr, envE, reflectSymbol fs,
                      reflectSymbol f1, reflectSExpr body, reflectSExpr a1,
                      vσ, hNs, hDef, hconvσ, hbody]
                  mkLambdaFVars #[vσ, hconvσ] p
              return ← mkAppM ``exists_conv_elim #[hcEx, kLam]
            | _, _ =>
              throwFrontier m!"proveTotality: recorded route arity \
                  {args.length} unsupported (frontier)"
          -- the MEASURED argument must be value-characterized (the decrease
          -- and the IH's count argument are stated about its value)
          unless totLiftable args[mIdx]! do
            throwFrontier m!"proveTotality: self-call MEASURED argument not \
                liftable {repr (SExpr.cons (.atom (.symbol fs)) (args.foldr SExpr.cons .nil))} (frontier)"
          unless vals.any (fun (f, _, _) => f == measuredFormal) do
            throwFrontier m!"proveTotality: measured formal has no bound value"
          let kit : DecreaseKit := {
            cfg := cfg, envE := envE
            facts := facts.map (fun (f, pos, _) => (f, pos))
            valOf := fun u => dpValExpr [] (dpValProof.dpVarVal envE varP) u
            convOf := fun u => dpValProof cfg envE [] [] varP u
            conspTrueOf := fun b => do
              let conspTest : SExpr :=
                .cons (.atom (.symbol { name := "CONSP" })) (.cons b .nil)
              match facts.find? (fun (f, pos, _) => f == conspTest && pos) with
              | some (_, _, pf) => pure pf
              | none => throwFrontier m!"dischargeDecrease: decrease at \
                  {repr b} needs an in-scope (consp {repr b}) fact (frontier)"
            endpFalseOf := fun b => do
              let endpTest : SExpr :=
                .cons (.atom (.symbol { name := "ENDP" })) (.cons b .nil)
              match facts.find? (fun (f, pos, _) => f == endpTest && !pos) with
              | some (_, _, pf) => pure pf
              | none => throwFrontier m!"dischargeDecrease: registry \
                  decrease at {repr b} needs a refuted (endp {repr b}) \
                  fact (frontier)" }
          let dec ← dischargeDecrease just
            formals (formals.map (fun f => .atom (.symbol f)))
            formals args kit
          let hNs ← proveNotSpecial fs
          let hDef ← totDefFact cfg fs formals body
          match formals, args with
          | [f1], [a1] =>
            let av ← dpValExpr [] (dpValProof.dpVarVal envE varP) a1
            let ap ← dpValProof cfg envE [] [] varP a1
            let hbody ← mkAppM' ih #[av, dec]
            return ← mkAppM ``conv_defn_1_ex
              #[cfg.worldExpr, envE, reflectSymbol fs, reflectSymbol f1,
                reflectSExpr body, reflectSExpr a1, av, hNs, hDef, ap, hbody]
          | [f1, f2], [a1, a2] =>
            let aM := args[mIdx]!
            let vM ← dpValExpr [] (dpValProof.dpVarVal envE varP) aM
            let pM ← dpValProof cfg envE [] [] varP aM
            let aO := args[1 - mIdx]!
            -- assemble conv_defn_2_ex from the two positions' value/conv
            -- pairs; the IH's binder order follows the MEASURED formal (the
            -- strong induction is on its count; the other formal is inner-∀)
            let assemble (vO pO : Expr) : MetaM Expr := do
              let hbody ← mkAppM' ih #[vM, dec, vO]
              let (v1, v2, p1, p2) :=
                if mIdx == 0 then (vM, vO, pM, pO) else (vO, vM, pO, pM)
              mkAppM ``conv_defn_2_ex
                #[cfg.worldExpr, envE, reflectSymbol fs, reflectSymbol f1,
                  reflectSymbol f2, reflectSExpr body, reflectSExpr a1,
                  reflectSExpr a2, v1, v2, hNs, hDef, p1, p2, hbody]
            if totLiftable aO then
              let vO ← dpValExpr [] (dpValProof.dpVarVal envE varP) aO
              let pO ← dpValProof cfg envE [] [] varP aO
              return ← assemble vO pO
            else
              -- OPAQUE non-measured argument — e.g. perm's self-call
              -- (perm (cdr x) (rm (car x) y)): converge it by the walk
              -- itself, then ∃-ELIMINATE (exists_conv_elim) to bind its
              -- value for the IH (the dis_perm_total move, mechanized)
              let hcEx ← totWalk cfg envE vals facts totalEnv selfC aO
              let k ← withLocalDeclD `vo (mkConst ``SExpr) fun vO => do
                let convTy ← mkAppM ``ConvTo
                  #[cfg.worldExpr, envE, reflectSExpr aO, vO]
                withLocalDeclD `hcv convTy fun hcv => do
                  mkLambdaFVars #[vO, hcv] (← assemble vO hcv)
              return ← mkAppM ``exists_conv_elim #[hcEx, k]
          | [f1, f2, f3], [a1, a2, a3] =>
            -- 3-ary, measured on the SECOND formal (FILTER/ALL-REL —
            -- sorting arc 2026-07-29); the IH binder order follows
            -- `totality_3_rec_snd_mu`'s step: (measured value, decrease,
            -- first value, third value). Liftable arguments only.
            unless measuredFormal == f2 do
              throwFrontier m!"proveTotality: 3-ary self-call measured \
                  formal mismatch (frontier)"
            unless totLiftable a1 && totLiftable a2 && totLiftable a3 do
              throwFrontier m!"proveTotality: 3-ary self-call argument not \
                  liftable {repr (SExpr.cons (.atom (.symbol fs)) (args.foldr SExpr.cons .nil))} (frontier)"
            let dec ← dischargeDecrease just
              formals (formals.map (fun f => .atom (.symbol f)))
              formals args kit
            let v1 ← dpValExpr [] (dpValProof.dpVarVal envE varP) a1
            let p1 ← dpValProof cfg envE [] [] varP a1
            let v2 ← dpValExpr [] (dpValProof.dpVarVal envE varP) a2
            let p2 ← dpValProof cfg envE [] [] varP a2
            let v3 ← dpValExpr [] (dpValProof.dpVarVal envE varP) a3
            let p3 ← dpValProof cfg envE [] [] varP a3
            let hbody ← mkAppM' ih #[v2, dec, v1, v3]
            return ← mkAppM ``conv_defn_3_ex
              #[cfg.worldExpr, envE, reflectSymbol fs, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3,
                v1, v2, v3, hNs, hDef, p1, p2, p3, hbody]
          | _, _ =>
            throwFrontier m!"proveTotality: self-call arity {args.length} \
                unsupported (frontier)"
        | none => throwFrontier m!"proveTotality: self {fs.name} not in world"
    -- EARLIER defined fn: its accumulated totality proof
    if let some (_, arity, pf) := totalEnv.find? (fun (n, _, _) => n == fs.name) then
      unless args.length == arity do
        throwFrontier m!"proveTotality: call arity mismatch {repr (SExpr.cons (.atom (.symbol fs)) (args.foldr SExpr.cons .nil))}"
      let argPfs ← args.mapM (totWalk cfg envE vals facts totalEnv selfC)
      let argsR := args.map reflectSExpr
      return ← mkAppM' pf (#[envE] ++ argsR.toArray ++ argPfs.toArray)
    throwFrontier m!"proveTotality: call to {fs.name} with no totality fact \
        in scope (frontier: development-order dependency or unsupported head)"

  match t with
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      if totLiftable c then
        let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
        let hc ← dpValProof cfg envE [] [] varP c
        let toBoolVc ← mkAppM ``Logic.toBool #[vc]
        let tTrue ← mkEq toBoolVc (mkConst ``Bool.true)
        let tFalse ← mkEq toBoolVc (mkConst ``Bool.false)
        let he ← withLocalDeclD `hb tFalse fun hb => do
          let p ← totWalk cfg envE vals ((c, false, hb) :: facts) totalEnv selfC e
          mkLambdaFVars #[hb] p
        let ht ←
          if ← isDefEq vc (mkConst ``SExpr.nil) then do
            -- VACUOUS truthy branch (`mkVacuousTruthyBranch`): the test's
            -- value is DEFINITIONALLY nil — `(COMPLEX-RATIONALP _)` in
            -- ACL2-COUNT's own admission body — so the branch hypothesis
            -- refutes itself; close by absurdity instead of walking a
            -- branch whose self-call decrease (`(ACL2-COUNT (REALPART X))`)
            -- the walk could never state.
            mkVacuousTruthyBranch toBoolVc
              (← mkConvPropEx cfg.worldExpr envE (reflectSExpr th))
          else
            withLocalDeclD `hb tTrue fun hb => do
              let p ← totWalk cfg envE vals ((c, true, hb) :: facts)
                totalEnv selfC th
              mkLambdaFVars #[hb] p
        return ← mkAppM ``conv_if_split
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th, reflectSExpr e,
            vc, hc, ht, he]
      else
        -- OPAQUE (user-fn) test — e.g. perm's (memb (car x) y): the walk
        -- itself converges the test (an already-total earlier fn's call),
        -- then the branches split on the EXISTENTIAL verdict via
        -- conv_if_split_ex — the dis_perm_total move, mechanized (lifter
        -- sprint 2026-07-06). The branch fact binds the OPAQUE verdict
        -- fvar; safe because decrease discharge only existence-checks
        -- non-consp ruling tests (their proof Exprs are never consumed),
        -- and consp tests are always liftable (take the branch above).
        let hcEx ← totWalk cfg envE vals facts totalEnv selfC c
        let mkBranch (bval : Name) (pos : Bool) (branch : SExpr) :
            MetaM Expr :=
          withLocalDeclD `vc (mkConst ``SExpr) fun vc => do
            let convTy ← mkAppM ``ConvTo
              #[cfg.worldExpr, envE, reflectSExpr c, vc]
            withLocalDeclD `hcv convTy fun hcv => do
              let hbTy ← mkEq (← mkAppM ``Logic.toBool #[vc]) (mkConst bval)
              withLocalDeclD `hb hbTy fun hb => do
                let p ← totWalk cfg envE vals ((c, pos, hb) :: facts)
                  totalEnv selfC branch
                mkLambdaFVars #[vc, hcv, hb] p
        let ht ← mkBranch ``Bool.true true th
        let he ← mkBranch ``Bool.false false e
        return ← mkAppM ``conv_if_split_ex
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, hcEx, ht, he]
    else
      -- a 3-ary NON-IF application (sorting arc 2026-07-29): route through
      -- the SHARED application logic (self-calls included) — previously
      -- this arm swallowed every ternary and frontiered it.
      goApp fs [c, th, e]
  | .cons (.atom (.symbol fs)) argsSpine =>
    goApp fs ((argsSpine.toList?).getD [])
  | _ => throwFrontier m!"proveTotality: term shape {repr t} unsupported (frontier)"
where
  /-- `w.defs.get? fn = some (formals, body)` by `decide` on the reflected world. -/
  totDefFact (cfg : ReplayConfig) (fn : Symbol) (formals : List Symbol)
      (body : SExpr) : MetaM Expr := do
    let defsE ← mkAppM ``World.defs #[cfg.worldExpr]
    let lhs ← mkAppM ``DefMap.get? #[defsE, reflectSymbol fn]
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let pairE ← mkAppM ``Prod.mk #[formalsE, reflectSExpr body]
    let rhs ← mkAppM ``Option.some #[pairE]
    mkDecideProof (← mkEq lhs rhs)

/-- Replay a decision-procedure DISCHARGE LEAF standalone: prove the discharge
    node's claim `EvTrue w env (disjoin clause)` (G2),
    CONDITIONAL on, per opaque user-fn subterm: its convergence (totality) and —
    when the development carries one — its emitted type-prescription corollary.
    `tps` maps fn name ↦ corollary (from the parsed `:TYPE-PRESCRIPTION` events).
    Returns the (lambda-abstracted) proof and the list of assumed conditions.
    With `assumeFact`, an unclosable DP fact is NOT sorried: it becomes a further
    bound hypothesis (`hfact : <the fact>`) — the proof is CONDITIONAL, its type
    states the exact missing obligation, no `sorryAx` anywhere. -/
def replayDischargeLeaf (cfg : ReplayConfig) (clauseTerm : SExpr)
    (tps : List (String × SExpr) := []) (assumeFact : Bool := false)
    (totalEnv : List (String × Nat × Expr) := []) :
    MetaM (Expr × List String) := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap ACL2.Replay.freeVars).eraseDups
  let opaques := (lits.flatMap collectOpaques).eraseDups
  -- #37: derive each opaque application's convergence from the admission
  -- totality environment where possible — the leaf then carries NO total:
  -- hypothesis for it (an ∃-elimination consumes the derivation instead)
  let derived : List (Option Expr) ← opaques.mapM fun op =>
    try
      pure (some (← totWalk cfg cfg.envExpr [] [] totalEnv none op))
    catch _ =>
      pure none
  -- per-opaque: the instantiated TP corollary (formals ↦ the occurrence's actuals)
  let opCors : List (SExpr × Option SExpr) ← opaques.mapM fun op => do
    let .cons (.atom (.symbol fs)) argsSpine := op
      | throwError "replayDischargeLeaf: opaque is not an application: {repr op}"
    match tps.lookup fs.name with
    | none => return (op, none)
    | some cor =>
      let some (formals, _) := cfg.worldVal.defs.get? fs
        | return (op, none)  -- TP names a fn not in this world: skip the hypothesis
      let args := (argsSpine.toList?).getD []
      unless formals.length == args.length do
        throwError "replayDischargeLeaf: arity mismatch instantiating TP of {fs.name}"
      return (op, some (ACL2.Replay.substTerm formals args cor))
  -- an opaque's convergence hypothesis is ELIMINABLE only when (a) the
  -- totality environment derives it AND (b) no TP hypothesis mentions its
  -- value (a TP-bearing opaque's value must stay universally bound so the
  -- TP hypothesis can be stated over it — restructuring those to the
  -- fn-level TP shape is a tracked follow-up)
  let eliminable : List Bool := (opaques.zip derived).map fun (op, d?) =>
    d?.isSome && (opCors.find? (fun (o, c?) => o == op && c?.isSome)).isNone
  let conds :=
    ((opaques.zip eliminable).filterMap fun (op, e) =>
      if e then none else some s!"total:{op}") ++
    (opCors.filterMap fun (op, c?) => c?.map fun _ =>
      s!"tp:{(op.toList?.getD []).head?.getD .nil}")
  -- quantify the opaque values, their convergence hypotheses, and TP hypotheses
  let vopDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (Array.range opaques.length).map fun i =>
      (Name.mkSimple s!"vop{i}", .default, fun _ => pure (mkConst ``SExpr))
  let (p, assumed) ← withLocalDecls vopDecls fun vops => do
    let opqMap := opaques.zip vops.toList
    let hConvDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (List.range opaques.length).toArray.map fun i =>
        (Name.mkSimple s!"hconv{i}", .default, fun _ => do
          mkEvalSomeExist cfg.worldExpr cfg.envExpr opaques[i]! vops[i]!)
    withLocalDecls hConvDecls fun hconvs => do
      let opqP := opaques.zip hconvs.toList
      -- TP hypothesis types: instantiated corollary lifted CONCRETELY, = t
      let tpCorsPresent := opCors.filterMap (·.2)
      let tpDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
        (List.range tpCorsPresent.length).toArray.map fun i =>
          (Name.mkSimple s!"htp{i}", .default, fun _ => do
            mkEq (← dpValExpr opqMap (dpConcVar cfg.envExpr) tpCorsPresent[i]!)
                 (mkConst ``SExpr.t))
      withLocalDecls tpDecls fun htps => do
        let stmt ← dpFactStmt tests last vars opaques tpCorsPresent
        let total := vars.length + opaques.length
        let cone := dpConeIndices tests last vars opaques tpCorsPresent
        let fact? ←
          tryCatchRuntimeEx
            (try
              pure (some (← proveDpFact stmt total cone))
            catch e =>
              if assumeFact then pure none else throw e)
            (fun e =>
              if assumeFact then pure none else throw e)
        let concArgs ← vars.mapM (fun s => dpConcVar cfg.envExpr s)
        -- close over (vop, hconv) pairs INNER-to-OUTER: a derived opaque's
        -- pair is consumed by exists_conv_elim (its totality derivation);
        -- an underived one stays a λ-bound hypothesis. TP hyps (which may
        -- mention any vop) bind innermost.
        let closeOver (prf0 : Expr) (extra : Array Expr) : MetaM Expr := do
          let mut prf ← mkLambdaFVars (htps ++ extra) prf0
          for i in (List.range opaques.length).reverse do
            match derived[i]!, eliminable[i]! with
            | some tot, true =>
              let k ← mkLambdaFVars #[vops[i]!, hconvs[i]!] prf
              prf ← mkAppM ``exists_conv_elim #[tot, k]
            | _, _ =>
              prf ← mkLambdaFVars #[vops[i]!, hconvs[i]!] prf
          return prf
        let bundle ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
        match fact? with
        | some fact =>
          -- instantiate the fact: concrete var values, opaque value fvars, TP hyps
          let factConc := mkAppN fact (concArgs.toArray ++ vops ++ htps)
          let prf ← dischargeSpine cfg bundle opqMap clauseTerm factConc
          let r ← closeOver prf #[]
          return (r, false)
        | none =>
          withLocalDeclD `hfact stmt fun hFact => do
            let factConc := mkAppN hFact (concArgs.toArray ++ vops ++ htps)
            let prf ← dischargeSpine cfg bundle opqMap clauseTerm factConc
            let r ← closeOver prf #[hFact]
            return (r, true)
  return (p, if assumed then conds ++ [assumedDpFactCond] else conds)

/-- The DP-fact obligation of a discharge leaf, computed from the CLAUSE TERM
    alone plus the AVAILABLE value-only TP corollaries (name → corollary) —
    shared by `replayDischargeNode` (whose ctx.tpHyps carry the same pairs)
    and the conditional harness's dp-fact hypothesis offers, so an offered
    hypothesis's type IS the replay-time obligation (isDefEq-checked at the
    consumption site, fail-closed). -/
def dpFactStmtOfClause (worldVal : World) (tpsAvail : List (String × SExpr))
    (clauseTerm : SExpr) : MetaM Expr := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap ACL2.Replay.freeVars).eraseDups
  let opaques := (lits.flatMap collectOpaques).eraseDups
  let tpCors ← opaques.filterMapM fun op => do
    let .cons (.atom (.symbol fs)) argsSpine := op
      | throwError "dpFactStmtOfClause: opaque is not an application: {repr op}"
    match tpsAvail.lookup fs.name with
    | none => return none
    | some cor =>
      let some (formals, _) := worldVal.defs.get? fs | return none
      let args := (argsSpine.toList?).getD []
      unless formals.length == args.length do
        throwError "dpFactStmtOfClause: arity mismatch instantiating TP of \
            {fs.name}"
      return some (ACL2.Replay.substTerm formals args cor)
  dpFactStmt tests last vars opaques tpCors

/-- First-order ONE-WAY match: bind the pattern's VARIABLES (bare symbol
    atoms — ACL2 constants are quoted, functions are application heads) to
    subterms of `target`. Deterministic; fail-closed on conflicting
    bindings. The replay's ONLY matcher, justified at the verdict-class
    :LINEAR premise site alone (2b): ACL2 records no :SUBST for pot-setup
    rule uses, and the pattern is the EMITTED max-term — nothing is
    invented, and the instantiated premise is re-proved from the
    hypothesis, kernel-checked. -/
partial def oneWayMatch (pat target : SExpr)
    (acc : List (Symbol × SExpr) := []) :
    Option (List (Symbol × SExpr)) :=
  match pat with
  | .atom (.symbol s) =>
    (match acc.find? (fun (v, _) => v == s) with
     | some (_, t) => if t == target then some acc else none
     | none => some ((s, target) :: acc))
  | .cons (.atom (.symbol f)) pargs =>
    if f.name == "QUOTE" then (if pat == target then some acc else none)
    else
      (match target with
       | .cons (.atom (.symbol g)) targs =>
         if f == g then goArgs pargs targs acc else none
       | _ => none)
  | _ => if pat == target then some acc else none
where
  goArgs (pargs targs : SExpr) (acc : List (Symbol × SExpr)) :
      Option (List (Symbol × SExpr)) :=
    match pargs, targs with
    | .nil, .nil => some acc
    | .cons p pr, .cons t tr =>
      (oneWayMatch p t acc).bind fun acc' => goArgs pr tr acc'
    | _, _ => none

/-- TAU-ELIGIBILITY gate for the RULE-content premise pass (fold-back audit
    F1, dp-premises): ACL2's tau system consumes a stored rule only in the
    Signature Form 1 shape — recognizer hypotheses on DISTINCT VARIABLES and a
    recognizer conclusion about `(fn v1 … vn)` (acl2/tau.lisp,
    `tau-boolean-signature-formp` region). A boolean-strengthened rule outside
    this shape (e.g. a compound-argument LHS `(f (h x))`) is invisible to
    tau/type-set/forward-chaining, so offering it as a verdict-leaf premise
    would hand the Lean prover content ACL2's verdict could not have used.
    Checked: `lhs = (q (fn x1 … xn))` with the `xi` distinct variables, and
    the single hypothesis `(p xj)` a recognizer application to one of them.
    Whether the pass should ALSO gate on the leaf's class (tau vs
    fake-rune-for-type-set) is an open ratification question (TODO queue). -/
private def tauSigForm1 (lhs hyp : SExpr) : Bool :=
  match lhs with
  | .cons (.atom (.symbol _)) (.cons (.cons (.atom (.symbol _)) args) .nil) =>
    match argVars args with
    | some vs =>
      vs.eraseDups.length == vs.length &&
      (match hyp with
       | .cons (.atom (.symbol _)) (.cons (.atom (.symbol v)) .nil) =>
         vs.contains v
       | _ => false)
    | none => false
  | _ => false
where
  argVars : SExpr → Option (List Symbol)
    | .nil => some []
    | .cons (.atom (.symbol v)) rest => (argVars rest).map (v :: ·)
    | _ => none

/-- COMPOSE a verdict-only discharge node into a clause/preprocess replay: prove
    `EvTrue w env (disjoin clause)` (G2) under the AMBIENT `ReplayCtx` —
    opaque user-fn values come from the ctx PINS (placed there by
    `replayClause`'s uniform pinning), TP facts from the bound TP hypotheses.
    An unclosable DP fact falls back to the harness-offered ASSUMED:dp-fact
    hypothesis (condition threading, sorting-completion-2); with no offer in
    scope the failure surfaces as a frontier error. -/
def replayDischargeNode (cfg : ReplayConfig) (ctx : ReplayCtx) (clauseTerm : SExpr) :
    MetaM Expr := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap ACL2.Replay.freeVars).eraseDups
  let opaques0 := (lits.flatMap collectOpaques).eraseDups
  -- LINEAR-rule premises (2b-iv): each offered `linear:` hypothesis whose
  -- EMITTED max-term one-way-matches an obligation opaque contributes the
  -- instantiated `(IF hyp (EQUAL l r) 'T)` premise — cond-shaped exactly
  -- like a TP corollary, so the INT-VIEW lift consumes it unchanged. The
  -- concrete fact: the schematic hypothesis applied at
  -- `bindArgsOver env σvars σvals` and transported to the substituted
  -- terms along `evalOpt_substTerm_substN` (the with-lemma recipe's
  -- substN scaffold — inline twin, extraction queued), then
  -- `linear_premise_fact`. v1 gates, all fail-closed: exactly one stored
  -- hyp; EQUAL-headed conclusion; well-scoped rule terms; every rule
  -- variable bound by the match.
  let mut linData : List (SExpr × Expr) := []
  let mut ctxL := ctx  -- BOUNDED FIXPOINT (3 rounds): an instantiated premise can introduce
  -- the opaque a further instance needs (STRONG *1/2.1.2': the first
  -- unfold at (CDR X) introduces (ACL2-COUNT (CDR (CDR X))), which the
  -- second-round match unfolds again). Dedup makes rounds idempotent.
  let mut srcOps := opaques0
  for _round in List.range 3 do
    let mut newOps : List SExpr := []
    -- Match targets here are the OPAQUE set only — deliberately narrower
    -- than the rule pass's ruleTargets (fold-back audit F2): a linear
    -- max-term is the pot LABEL, and pot labels are the linear-arithmetic
    -- ATOMS, which the DP lift represents exactly as opaques. A max-term
    -- headed by a lift primitive has no corpus witness; widen only when a
    -- real book demands it (deterministic gating, no speculative reach).
    for (spec, hypV) in ctx.linearHyps do
      for op in srcOps do
        if let some σ := oneWayMatch spec.maxTerm op then
          -- v1 consumed EQUAL-headed single-hyp fully-bound rules ONLY;
          -- the equal-descent restructure arc (charter item 3) adds the
          -- `<`-headed conclusions item 1's wider snapshot legitimately
          -- carries (HOW-MANY-BAD-PAIRS-BNEXT's rule — the decrease
          -- obligation of termination:BSORT consumes it). Any other
          -- shape still SKIPS (contributes no premise — completeness,
          -- never soundness: the DP prove fails loudly if a needed
          -- premise is missing).
          let some (headS, lT, rT) := (match spec.concl with
            | .cons (.atom (.symbol eqS)) (.cons l (.cons r .nil)) =>
              if eqS.name == "EQUAL" || eqS.name == "<" then
                some (eqS.name, l, r)
              else none
            | _ => none)
            | continue
          let some hT := (match spec.hyps with
            | [h] => some h
            | _ => none)
            | continue
          let ruleFrees := (ACL2.Replay.freeVars hT ++
            ACL2.Replay.freeVars spec.concl).eraseDups
          if ruleFrees.any (fun v => !σ.any (fun (x, _) => x == v)) then
            continue
          let σvars := σ.map (·.1)
          let σterms := σ.map (·.2)
          let inst := ACL2.Replay.substTerm σvars σterms
          let (hI, lI, rI) := (inst hT, inst lT, inst rT)
          let eqI : SExpr := .cons (.atom (.symbol { name := headS }))
            (.cons lI (.cons rI .nil))
          let premise : SExpr := .cons (.atom (.symbol { name := "IF" }))
            (.cons hI (.cons eqI (.cons quoteT .nil)))
          unless linData.any (fun (t, _) => t == premise) do
            ctxL ← pinTermOpaques cfg cfg.envExpr ctxL premise
            -- shared substN bridge (fold-back extraction; pins σ terms — F3)
            let sb ← mkSubstNBridge cfg ctxL σvars σterms
              s!"linear {spec.name}"
            ctxL := sb.ctx
            let w := cfg.worldExpr
            let env := cfg.envExpr
            -- hypInst : EvTrue env (subst h) → EvTrue env (subst concl)
            let evT : SExpr → MetaM Expr := fun t =>
              pure (mkAppN (mkConst ``EvTrue) #[w, env, reflectSExpr t])
            let hypInst ← withLocalDeclD `hh (← evT hI) fun hhV => do
              let hEnv' ← mkAppM ``evtrue_of_fuel_eq
                #[← mkAppM ``fuel_eq_symm #[← sb.bridge hT], hhV]
              let cEnv' := mkAppN hypV #[sb.env', hEnv']
              let cBack ← mkAppM ``evtrue_of_fuel_eq
                #[← sb.bridge spec.concl, cEnv']
              mkLambdaFVars #[hhV] cBack
            -- the premise fact via linear_premise_fact (per concl head)
            let hnd ← proveNoShadow cfg ({ name := headS } : Symbol)
            let phC ← ctxValProof cfg ctxL hI
            let plC ← ctxValProof cfg ctxL lI
            let prC ← ctxValProof cfg ctxL rI
            let factLem := if headS == "EQUAL" then ``linear_premise_fact
                           else ``linear_premise_fact_lt
            let fact ← mkAppM factLem #[hnd, hypInst, phC, plC, prC]
            linData := linData ++ [(premise, fact)]
            newOps := (newOps ++ collectOpaques premise).eraseDups
    -- RULE-content premises (2c): boolean-strengthened stored rules
    -- (equiv EQUAL, rhs 'T, one hyp — TRUE-LISTP-RM / ORDEREDP-RM's
    -- shape) whose LHS one-way-matches an obligation APPLICATION SUBTERM
    -- contribute `(IF hyp (EQUAL lhs 'T) 'T)` premises — the linear
    -- row's twin with the trigger := the stored lhs and the fact via
    -- `rule_premise_fact` (the hypothesis's conclusion is an
    -- EVAL-EQUALITY, transported along the same substN bridges).
    -- Match targets are ALL application subterms of the clause literals
    -- plus the (round-extended) opaque set — NOT opaques alone: a rule
    -- LHS headed by a lift primitive (`(TRUE-LISTP (RM E A))`) never
    -- appears as an opaque (only its inner `RM` application does), and
    -- the opaque-only v1 silently missed exactly that trigger (ORDERED-PERMS
    -- *1/4 vs *1/6). Non-matching rule shapes are simply not offered here.
    let ruleTargets := ((lits.flatMap collectAppSubterms) ++ srcOps).eraseDups
    -- SKIP-vs-HARD-FAIL policy (fold-back audit F5): non-qualifying rules are
    -- SILENTLY skipped here — deliberately unlike the linear pass's
    -- throwFrontier. The linear pass consumes a CURATED emission (gz linear
    -- rules, each expected to instantiate); this pass scans EVERY stored rule
    -- in scope, almost all of which legitimately do not qualify — a frontier
    -- error per non-tau rule would make every book fail. Skipping is
    -- fail-closed: an unmatched rule contributes nothing and the obligation
    -- either proves without it or falls back to ASSUMED honestly.
    -- TAU-BASIS gating + EVG widening (item I consumer, ruled 2026-08-10):
    -- a recorded slice GATES rule premises to slice-named rules (matched
    -- verbatim against `parseTauBasisAllows`; the slice IS the shape
    -- license, so `tauSigForm1` is not re-consulted) and admits EVG-output
    -- rules (`'0` rhs — NOT-MEMB-IMPLIES-HOW-MANY-IS-0) via
    -- `rule_premise_fact_evg`; a basis-less leaf keeps the Form-1 scan.
    let sliceAllows? := ctx.tauBasis.map parseTauBasisAllows
    let isQuoted : SExpr → Bool := fun t => match t with
      | .cons (.atom (.symbol q)) (.cons _ .nil) => q.name == "QUOTE"
      | _ => false
    for (spec, hypV) in ctx.ruleHyps do
      let eligible := match sliceAllows? with
        | some allows =>
          spec.equiv == "equal" && isQuoted spec.rhs &&
          allows.any (fun a =>
            a.hyps == spec.hyps && a.lhs == spec.lhs && a.rhs == spec.rhs)
        | none =>
          spec.equiv == "equal" && spec.rhs == quoteT &&
          (match spec.hyps with
           | [hT] => tauSigForm1 spec.lhs hT
           | _ => false)
      if eligible then
        if let [hT] := spec.hyps then
          for op in ruleTargets do
            if let some σ := oneWayMatch spec.lhs op then
              let ruleFrees := (ACL2.Replay.freeVars hT ++
                ACL2.Replay.freeVars spec.lhs).eraseDups
              let bound := ruleFrees.all fun v =>
                σ.any (fun (x, _) => x == v)
              if bound then do
                let σvars := σ.map (·.1)
                let σterms := σ.map (·.2)
                let inst := ACL2.Replay.substTerm σvars σterms
                let (hI, lI) := (inst hT, inst spec.lhs)
                -- spec.rhs is a closed quote on both eligible shapes
                let eqI : SExpr := .cons (.atom (.symbol { name := "EQUAL" }))
                  (.cons lI (.cons spec.rhs .nil))
                let premise : SExpr := .cons (.atom (.symbol { name := "IF" }))
                  (.cons hI (.cons eqI (.cons quoteT .nil)))
                unless linData.any (fun (t, _) => t == premise) do
                  ctxL ← pinTermOpaques cfg cfg.envExpr ctxL premise
                  -- shared substN bridge (fold-back extraction)
                  let sb ← mkSubstNBridge cfg ctxL σvars σterms
                    s!"rule {spec.name}"
                  ctxL := sb.ctx
                  let w := cfg.worldExpr
                  let env := cfg.envExpr
                  -- hypInst : EvTrue env (subst h) →
                  --   eval env (subst lhs) ≐ eval env (spec.rhs quote)
                  let evT : SExpr → MetaM Expr := fun t =>
                    pure (mkAppN (mkConst ``EvTrue) #[w, env, reflectSExpr t])
                  let hypInst ← withLocalDeclD `hh (← evT hI) fun hhV => do
                    let hEnv' ← mkAppM ``evtrue_of_fuel_eq
                      #[← mkAppM ``fuel_eq_symm #[← sb.bridge hT], hhV]
                    let eqEnv' := mkAppN hypV #[sb.env', hEnv']
                    let c1 ← mkAppM ``fuel_chain_eq
                      #[← sb.bridge spec.lhs, eqEnv']
                    let c2 ← mkAppM ``fuel_chain_eq
                      #[c1, ← mkAppM ``fuel_eq_symm #[← sb.bridge spec.rhs]]
                    mkLambdaFVars #[hhV] c2
                  let phC ← ctxValProof cfg ctxL hI
                  let plC ← ctxValProof cfg ctxL lI
                  let factLem := if spec.rhs == quoteT
                    then ``rule_premise_fact else ``rule_premise_fact_evg
                  let fact ← mkAppM factLem #[hypInst, phC, plC]
                  linData := linData ++ [(premise, fact)]
                  newOps := (newOps ++ collectOpaques premise).eraseDups
    -- EQUIVREFL premises (2c): a stored :EQUIVALENCE rule's reflexivity
    -- content applies to any SYNTACTICALLY reflexive application subterm
    -- `(R u u)` of the clause: contribute `(NOT (NOT (R u u)))` — the
    -- refl instance under `EvTrue` gives only non-nil (hence the double
    -- negation, which lifts to `t` outright); the obligation's TP
    -- booleanp cell then forces `= T` inside the fact, exactly ACL2's
    -- tau composition (refl content + recognizer booleanness). The
    -- instance rides `instantiateEvTrueHypAt` (the shared premise-free
    -- substN slice), so no scaffold copy here.
    for (sp, hypV) in ctx.equivReflHyps do
      for op in ruleTargets do
        if let .cons (.atom (.symbol rS)) (.cons u1 (.cons u2 .nil)) := op then
          if rS == sp.rel && u1 == u2 then
            let notT : SExpr → SExpr := fun t =>
              .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
            let premise := notT (notT op)
            unless linData.any (fun (t, _) => t == premise) do
              let (hev, ctxL') ← instantiateEvTrueHypAt cfg ctxL hypV
                [sp.vx] [u1]
                (.cons (.atom (.symbol sp.rel))
                  (.cons (.atom (.symbol sp.vx))
                    (.cons (.atom (.symbol sp.vx)) .nil)))
              ctxL := ctxL'
              let pa ← ctxValProof cfg ctxL op
              let fact ← mkAppM ``equivrefl_premise_fact #[hev, pa]
              linData := linData ++ [(premise, fact)]
              newOps := (newOps ++ collectOpaques premise).eraseDups
    srcOps := (srcOps ++ newOps).eraseDups
  -- premise instances may mention opaques BEYOND the obligation's (a
  -- max-term match on (CDR X) instantiates the conclusion with
  -- (ACL2-COUNT X)); extend the opaque set so the lift and the
  -- application cover them (their pins came from the pinTermOpaques
  -- pass above)
  let opaques := (opaques0 ++
    ((linData.map (·.1)).flatMap collectOpaques)).eraseDups
  -- audit F3: the lookups consume ctxL (the loop's pin accumulation) —
  -- the earlier `let ctx := ctxL` was a DEAD shadow and premise-introduced
  -- opaques only resolved by luck of the ambient pins
  let pinned ← opaques.mapM fun op => do
    let some (v, p) := ctxL.val? op
      | throwError "replayDischargeNode: opaque {repr op} has no pinned value \
                    (totality hypothesis missing? frontier)"
    pure (op, v, p)
  let opqMap := pinned.map fun (op, v, _) => (op, v)
  let opqP := pinned.map fun (op, _, p) => (op, p)
  -- TP facts at the pinned values, from the bound TP hypotheses
  let tpData ← opaques.filterMapM fun op => do
    let .cons (.atom (.symbol fs)) argsSpine := op
      | throwError "replayDischargeNode: opaque is not an application: {repr op}"
    match ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) with
    | none => return none
    | some (_, cor, tpHyp) =>
      let some (formals, _) := cfg.worldVal.defs.get? fs | return none
      let args := (argsSpine.toList?).getD []
      unless formals.length == args.length do
        throwError "replayDischargeNode: arity mismatch instantiating TP of {fs.name}"
      let instCor := ACL2.Replay.substTerm formals args cor
      let some (v, conv) := ctxL.val? op
        | throwError "replayDischargeNode: unpinned TP opaque {repr op}"
      let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
        ++ (args.map reflectSExpr).toArray ++ #[v, conv])
      return some (op, instCor, fact)
  let stmt ← dpFactStmt tests last vars opaques
    (tpData.map (·.2.1) ++ linData.map (·.1))
  -- an UNPROVABLE fact falls back to the harness-offered dp-fact HYPOTHESIS
  -- for this clause (condition threading — the ambient analog of the
  -- standalone `assumeFact` route; the row reports ASSUMED:dp-fact via the
  -- used-filter). No offer → the failure surfaces (frontier). The OFFER is
  -- the PREMISE-FREE derivation (dpFactStmtOfClause knows no linear
  -- premises), so the fallback path rebuilds and applies that twin — the
  -- consumed hypothesis is the leaf's obligation exactly as the harness
  -- stated it (2b).
  let prove : MetaM Expr :=
    proveDpFact stmt (vars.length + opaques.length)
      (dpConeIndices tests last vars opaques
        (tpData.map (·.2.1) ++ linData.map (·.1)))
  let concArgs ← vars.mapM (dpConcVar cfg.envExpr)
  let hypFallback (e : Lean.Exception) : MetaM Expr := do
    match ctx.dpFactHyps.find? (fun (t, _) => t == clauseTerm) with
    | some (_, hyp) => do
      let pinned0 := pinned.filter (fun (op, _, _) => opaques0.contains op)
      let tpData0 := tpData.filter fun (o, _, _) => opaques0.contains o
      let stmt0 ← dpFactStmt tests last vars opaques0 (tpData0.map (·.2.1))
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType hyp) stmt0 do
        throwError "replayDischargeNode: the offered dp-fact hypothesis for \
            {repr clauseTerm} does not match the replay-time obligation \
            (derivation drift — a defect)"
      let opqMap0 := pinned0.map fun (op, v, _) => (op, v)
      let opqP0 := pinned0.map fun (op, _, p) => (op, p)
      let factConc := mkAppN hyp (concArgs.toArray
        ++ (opqMap0.map (·.2)).toArray ++ (tpData0.map (·.2.2)).toArray)
      let bundle ← mkDpLiftBundle cfg cfg.envExpr vars opqMap0 opqP0
      dischargeSpine cfg bundle opqMap0 clauseTerm factConc
    | none => throw e
  -- F6 (close-out machinery debt, 2026-08-05): only the DP TACTIC's own
  -- failure (the fact is genuinely unprovable) or a RUNTIME bound (the
  -- pathological-leaf guard) may fall back to the ASSUMED hypothesis. A
  -- failure AFTER a successful proveDpFact — the fact application, the
  -- lift bundle, the spine — is a machinery defect on a PROVABLE leaf and
  -- must surface, never silently downgrade.
  let proveOnly : MetaM (Option Expr) :=
    tryCatchRuntimeEx
      (try pure (some (← prove)) catch _ => pure none)
      (fun _ => pure none)
  tryCatchRuntimeEx
    (do
      match ← proveOnly with
      | some fact =>
        let factConc := mkAppN fact (concArgs.toArray
          ++ (opqMap.map (·.2)).toArray
          ++ (tpData.map (·.2.2)).toArray ++ (linData.map (·.2)).toArray)
        let bundle ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
        dischargeSpine cfg bundle opqMap clauseTerm factConc
      | none =>
        try
          throwError "replayDischargeNode: the DP fact for \
            {repr clauseTerm} is unprovable (the tactic failed) — \
            falling back to the offered hypothesis"
        catch e => hypFallback e)
    hypFallback

/-- The whole-clause discharge with a PREFIX-shaped verdict node
    (equal-descent restructure arc — ORDEREDP-WHEN-BNEXT-CONSTANT
    *1/4.1.3''): ACL2's add-literal dropped a trivially-nil tail before
    the contradiction fired, so the recorded obligation is the PREFIX
    disjunction (a read-off); prefix-true ⇒ full-true is monotone
    weakening (`evtrueExtendTail`, no assumption about the dropped
    literals). -/
def prefixDischargeExtend (cfg : ReplayConfig) (ctx : ReplayCtx)
    (idStr : String) (allL : List SExpr) (nodeLhs : SExpr) : MetaM Expr := do
  let k? := (List.range allL.length).find? fun k =>
    k > 0 && disjoinTerm (allL.take k) == nodeLhs
  let some k := k?
    | throwError "replayClauseSpine: whole-clause discharge node lhs \
        {repr nodeLhs} ≠ the clause disjunction \
        {repr (disjoinTerm allL)} (nor any prefix) at {idStr}"
  -- the DROPPED tail must be the class add-literal actually drops
  -- (restructure-arc audit C5: syntactic prefix-hood alone would silently
  -- absorb a reconstruction divergence as monotone weakening) — today's
  -- sole witness class is the trivially-nil (NOT (EQUAL t t)); anything
  -- else hard-fails
  for L in allL.drop k do
    let ok := match L with
      | .cons (.atom (.symbol ns)) (.cons
          (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) .nil) =>
        ns.name == "NOT" && es.name == "EQUAL" && a == b
      | _ => false
    unless ok do
      throwError "replayClauseSpine: prefix discharge would drop \
          {repr L}, which is not the trivially-nil (NOT (EQUAL t t)) \
          class at {idStr} (frontier — reconstruction divergence?)"
  let pPre ← replayDischargeNode cfg ctx (disjoinTerm (allL.take k))
  evtrueExtendTail cfg ctx (allL.take k) (allL.drop k) pPre

end ACL2.Replay.Driver
