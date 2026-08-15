/-
  Driver/Decrease — the ADMISSION-DECREASE machinery, split out of
  Driver/Totality (T1+2 sprint phase 2, 2026-08-14; MOVE-ONLY, at the
  file's own section boundary: everything up to and including
  `dischargeDecrease` lives here, the body-convergence walk and the
  DP-leaf replays stay in Totality).

  The split is the module-size ratchet's doing — the R3 measure-table
  rewiring pushed the combined file past the 1500-line cap — and it lands
  on a real seam: this module is the DECREASE side (the emitted
  termination clauses, the count/len walks, the recorded-admission
  route), Totality is the CONVERGENCE side that consumes it.
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
  /-- THE GENERAL in-scope-fact accessor (T1+2 sprint phase 3a): the branch
      fact for an ARBITRARY ruling test at the given polarity, normalized to
      `Logic.toBool (valOf test) = <sign>`; `none` when the test is not ruled
      on this branch. `conspTrueOf`/`endpFalseOf` above stay as the two
      RECOGNIZER specializations (they additionally bridge the
      CONSP/ENDP/ATOM duality, which is recognizer-specific); the ARITHMETIC
      rows have no recognizer — the NFIX walk's license is a refuted
      `(ZP v)`, and nothing but a general accessor can hand it over. -/
  factOf? : SExpr → Bool → MetaM (Option Expr)

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

/-- View `(NFIX u)` → `u` (the arithmetic-countdown family: `CD2`,
    `COUNT-DOWN`, `MY-EVENP`/`MY-ODDP`). -/
def nfixOfView (t : SExpr) : Option SExpr :=
  match t with
  | .cons (.atom (.symbol c)) (.cons u .nil) =>
    if c.name == "NFIX" then some u else none
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

/-- NFIX-measure decrease walk (T1+2 sprint phase 3a — the ARITHMETIC twin
    of `chainLt`/`chainLtLen`): prove
    `nfixNat (valOf t) < nfixNat (valOf base)`.

    ONE arm, keyed to the emitted call-site shape the whole
    arithmetic-countdown family uses — `(BINARY-+ '<negative int> base)`,
    licensed by the SAME emitted clause's refuted `(ZP base)` ruler
    (`chainLtNfix` is only ever reached after `dischargeDecrease` verified
    that ruler against the branch facts). Anything else is a named
    frontier: an NFIX decrease this walk cannot state is an honest gap,
    never an inferred one. -/
def chainLtNfix (kit : DecreaseKit) (base t : SExpr) : MetaM Expr := do
  let .cons (.atom (.symbol p)) (.cons klit (.cons u .nil)) := t
    | throwFrontier m!"chainLtNfix: shape {repr t} has no NFIX decrease arm \
        (frontier)"
  unless p.name == "BINARY-+" do
    throwFrontier m!"chainLtNfix: head {p.name} has no NFIX decrease arm \
        (frontier): {repr t}"
  unless u == base do
    throwFrontier m!"chainLtNfix: the NFIX decrease's addend {repr u} is not \
        the measured base {repr base} (frontier)"
  let zpTest : SExpr :=
    .cons (.atom (.symbol { name := "ZP" })) (.cons base .nil)
  let some hzp ← kit.factOf? zpTest false
    | throwFrontier m!"chainLtNfix: the NFIX decrease at {repr base} needs a \
        refuted (ZP {repr base}) ruling fact in scope (frontier)"
  -- the summand's negativity is a KERNEL decision on its own value (the
  -- literal comes from the emitted clause; nothing is inferred)
  let vk ← kit.valOf klit
  let hNeg ← proveByDecide
    (← mkAppM ``LT.lt #[← mkAppM ``Logic.toInt #[vk], Lean.toExpr (0 : Int)])
    s!"the NFIX decrease summand {repr klit} is negative"
  mkAppM ``ACL2.Replay.nfixNat_plus_lt_of_not_zp #[hNeg, hzp]

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
  -- 3. the Count walk, by MEASURE-TABLE ROW (R3, 2026-08-14): the row is
  -- classified ONCE, off the justification's own `:MEASURE` (which is
  -- stated over the defun's formals, so its measured arguments are bare
  -- variables); the walk then runs on the RENAMED measure's arguments.
  -- Every row is answered here — either by a walk or by its OWN named
  -- frontier — so a row added to the table cannot silently fall through.
  let some row := measureShape? just.measure
    | throwFrontier m!"dischargeDecrease: measure {repr just.measure} is not \
        a registered measure-table row (frontier)"
  match row with
  | .count _ =>
    let some base := countOfView measure'
      | throwFrontier m!"dischargeDecrease: renamed ACL2-COUNT measure \
          {repr measure'} lost its shape (frontier)"
    chainLt kit base (sub base)
  | .len _ =>
    -- the LEN walk (P3, bsort — `chainLtLen`, the lenNat twin)
    let some base := lenOfView measure'
      | throwFrontier m!"dischargeDecrease: renamed LEN measure \
          {repr measure'} lost its shape (frontier)"
    chainLtLen kit base (sub base)
  | .nfix _ =>
    -- the ARITHMETIC walk (T1+2 sprint phase 3a — `chainLtNfix`): an NFIX
    -- decrease is `(NFIX (+ 'k v)) < (NFIX v)` under a refuted `(ZP v)`,
    -- not a destructor chain.
    let some base := nfixOfView measure'
      | throwFrontier m!"dischargeDecrease: renamed NFIX measure \
          {repr measure'} lost its shape (frontier)"
    chainLtNfix kit base (sub base)
  | .userFn f _ =>
    throwFrontier m!"dischargeDecrease: user measure fn {f.name} has no \
        destructor-chain decrease walk — the recorded-termination route \
        owns this row (frontier)"
  | .sumCount _ _ =>
    let (cx, cy) ← match measure' with
      | .cons (.atom (.symbol _)) (.cons cx (.cons cy .nil)) => pure (cx, cy)
      | _ => throwFrontier m!"dischargeDecrease: renamed sum measure \
          {repr measure'} lost its shape (frontier)"
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


end ACL2.Replay.Driver
