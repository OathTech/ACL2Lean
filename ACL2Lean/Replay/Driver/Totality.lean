/-
  Driver/Totality — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  Totality from admission (#37): the decrease-clause prover.
-/
import ACL2Lean.Replay.Driver.Discharge

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
frontier and the `total:` hypothesis stays in the mirror's type (D6). -/

/-- Is every head of `t` walk-liftable (vars/quote/dp-primitives only)? -/
def totLiftable (t : SExpr) : Bool := (collectOpaques t).isEmpty

/-- View `(ACL2-COUNT u)` → `u`. -/
def countOfView (t : SExpr) : Option SExpr :=
  match t with
  | .cons (.atom (.symbol c)) (.cons u .nil) =>
    if c.name == "ACL2-COUNT" then some u else none
  | _ => none

/-- Count-walk ≤ leg: `(valOf t).acl2Count ≤ (valOf base).acl2Count` for `t`
    a (possibly empty) cdr/car chain over `base` — unconditional per-step
    `acl2Count_cdr_le`/`car_le` composed by transitivity. -/
partial def chainLe (valOf : SExpr → MetaM Expr) (base t : SExpr) :
    MetaM Expr := do
  if t == base then
    mkAppM ``Nat.le_refl #[← mkAppM ``SExpr.acl2Count #[← valOf base]]
  else match t with
  | .cons (.atom (.symbol d)) (.cons u .nil) =>
    if d.name == "CDR" || d.name == "CAR" then
      let inner ← chainLe valOf base u
      let vu ← valOf u
      let hLe ← if d.name == "CDR" then mkAppM ``ACL2.acl2Count_cdr_le #[vu]
        else mkAppM ``ACL2.acl2Count_car_le #[vu]
      mkAppM ``Nat.le_trans #[hLe, inner]
    else
      throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
          the destructor-chain walk over {repr base} (frontier)"
  | _ => throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
      the destructor-chain walk over {repr base} (frontier)"

/-- Count-walk strict leg: `(valOf t).acl2Count < (valOf base).acl2Count`
    for `t` a NON-EMPTY cdr/car chain over `base` — the innermost destructor
    application to `base` is the ONE strict step (from `base`'s consp fact);
    every outer layer composes by `≤`. -/
partial def chainLt (valOf : SExpr → MetaM Expr)
    (conspProofOf : SExpr → MetaM Expr) (base t : SExpr) : MetaM Expr := do
  match t with
  | .cons (.atom (.symbol d)) (.cons u .nil) =>
    if d.name == "CDR" || d.name == "CAR" then
      if u == base then
        let hConsp ← conspProofOf base
        if d.name == "CDR" then
          mkAppM ``ACL2.acl2Count_cdr_lt_of_consp #[hConsp]
        else
          mkAppM ``ACL2.acl2Count_car_lt_of_consp #[hConsp]
      else
        let inner ← chainLt valOf conspProofOf base u
        let vu ← valOf u
        let hLe ← if d.name == "CDR" then mkAppM ``ACL2.acl2Count_cdr_le #[vu]
          else mkAppM ``ACL2.acl2Count_car_le #[vu]
        mkAppM ``Nat.lt_of_le_of_lt #[hLe, inner]
    else
      throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
          the destructor-chain walk over {repr base} (frontier: candidate \
          registry head {d.name})"
  | _ => throwFrontier m!"dischargeDecrease: decrease argument {repr t} beyond \
      the destructor-chain walk over {repr base} (frontier)"

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
       strict component) or the swap pattern (`acl2Count_swap_…`).

    `valOf` renders an actual-level term's VALUE `Expr` (the caller's value
    plumbing — dpValExpr at admission, ctxValExpr at IH time);
    `conspProofOf b` returns `toBool (consp (valOf b)) = true` for a base
    term (from in-scope facts; the induction caller's endp/atom/or-form
    inversion lives behind it). -/
def dischargeDecrease (just : Justification)
    (rnFormals : List Symbol) (rnArgs : List SExpr)
    (sFormals : List Symbol) (sArgs : List SExpr)
    (facts : List (SExpr × Bool))
    (valOf : SExpr → MetaM Expr)
    (conspProofOf : SExpr → MetaM Expr) : MetaM Expr := do
  let rn (t : SExpr) : SExpr := ACL2.Replay.substTerm rnFormals rnArgs t
  let sub (t : SExpr) : SExpr := ACL2.Replay.substTerm sFormals sArgs t
  let measure' := rn just.measure
  let sμ := sub measure'
  if sμ == measure' then
    throwFrontier m!"dischargeDecrease: substitution does not move the \
        measure {repr measure'} (identity — no decrease to prove)"
  let wanted : SExpr :=
    .cons (.atom (.symbol { name := "O<" })) (.cons sμ (.cons measure' .nil))
  let matching := (just.terminationClauses.filterMap
        (fun c => c.toList?.map (·.map rn))).filter (·.contains wanted)
  if matching.isEmpty then
    throwFrontier m!"dischargeDecrease: no emitted decrease obligation \
        matching {repr wanted} (emission gap or unsupported substitution)"
  -- a ruling literal is COVERED by an in-scope fact: `(NOT tst)` needs
  -- `(tst, true)`; a bare literal needs `(lit, false)`
  let uncoveredOf (lits : List SExpr) : List SExpr :=
    lits.filter fun lit =>
      if lit == wanted then false
      else match lit with
      | .cons (.atom (.symbol n)) (.cons tst .nil) =>
        if n.name == "NOT" then !facts.any (fun (f, pos) => f == tst && pos)
        else !facts.any (fun (f, pos) => f == lit && !pos)
      | _ => !facts.any (fun (f, pos) => f == lit && !pos)
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
    return ← chainLt valOf conspProofOf base (sub base)
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
      let hConsp ← conspProofOf x
      return ← mkAppOptM ``ACL2.acl2Count_swap_cdr_sum_lt_consp
        #[none, some (← valOf y), some hConsp]
    -- componentwise: each component ≤ its original, at least one strict
    let leg (b t : SExpr) : MetaM (Bool × Expr) := do
      if t == b then pure (false, ← chainLe valOf b t)
      else
        try pure (true, ← chainLt valOf conspProofOf b t)
        catch e =>
          if isFrontierErr e then pure (false, ← chainLe valOf b t)
          else throw e
    let (strictX, px) ← leg x sx
    let (strictY, py) ← leg y sy
    if strictX then
      mkAppM ``add_lt_add_of_lt_of_le #[px, ← chainLe valOf y sy]
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
    (selfC : Option (String × Symbol × Expr × Justification))
    (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  if totLiftable t then
    -- vars / quote / dp-primitive tree: value-characterize and ∃-pack
    let pf ← dpValProof cfg envE [] [] varP t
    return ← mkAppM ``conv_ex_of_vfix #[pf]
  match t with
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      if totLiftable c then
        let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
        let hc ← dpValProof cfg envE [] [] varP c
        let toBoolVc ← mkAppM ``Logic.toBool #[vc]
        let tTrue ← mkEq toBoolVc (mkConst ``Bool.true)
        let tFalse ← mkEq toBoolVc (mkConst ``Bool.false)
        let ht ← withLocalDeclD `hb tTrue fun hb => do
          let p ← totWalk cfg envE vals ((c, true, hb) :: facts) totalEnv selfC th
          mkLambdaFVars #[hb] p
        let he ← withLocalDeclD `hb tFalse fun hb => do
          let p ← totWalk cfg envE vals ((c, false, hb) :: facts) totalEnv selfC e
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
      throwFrontier m!"proveTotality: ternary {fs.name} unsupported (frontier)"
  | .cons (.atom (.symbol fs)) argsSpine =>
    let args := (argsSpine.toList?).getD []
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
    if let some (selfName, measuredFormal, ih, just) := selfC then
      if fs.name == selfName then
        match cfg.worldVal.defs.get? fs with
        | some (formals, body) =>
          unless args.length == formals.length do
            throwFrontier m!"proveTotality: self-call arity mismatch {repr t}"
          let mIdx := formals.findIdx (· == measuredFormal)
          -- the MEASURED argument must be value-characterized (the decrease
          -- and the IH's count argument are stated about its value)
          unless totLiftable args[mIdx]! do
            throwFrontier m!"proveTotality: self-call MEASURED argument not \
                liftable {repr t} (frontier)"
          unless vals.any (fun (f, _, _) => f == measuredFormal) do
            throwFrontier m!"proveTotality: measured formal has no bound value"
          let dec ← dischargeDecrease just
            formals (formals.map (fun f => .atom (.symbol f)))
            formals args
            (facts.map (fun (f, pos, _) => (f, pos)))
            (fun u => dpValExpr [] (dpValProof.dpVarVal envE varP) u)
            (fun b => do
              let conspTest : SExpr :=
                .cons (.atom (.symbol { name := "CONSP" })) (.cons b .nil)
              match facts.find? (fun (f, pos, _) => f == conspTest && pos) with
              | some (_, _, pf) => pure pf
              | none => throwFrontier m!"dischargeDecrease: decrease at \
                  {repr b} needs an in-scope (consp {repr b}) fact (frontier)")
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
          | _, _ =>
            throwFrontier m!"proveTotality: self-call arity {args.length} \
                unsupported (frontier)"
        | none => throwFrontier m!"proveTotality: self {fs.name} not in world"
    -- EARLIER defined fn: its accumulated totality proof
    if let some (_, arity, pf) := totalEnv.find? (fun (n, _, _) => n == fs.name) then
      unless args.length == arity do
        throwFrontier m!"proveTotality: call arity mismatch {repr t}"
      let argPfs ← args.mapM (totWalk cfg envE vals facts totalEnv selfC)
      let argsR := args.map reflectSExpr
      return ← mkAppM' pf (#[envE] ++ argsR.toArray ++ argPfs.toArray)
    throwFrontier m!"proveTotality: call to {fs.name} with no totality fact \
        in scope (frontier: development-order dependency or unsupported head)"
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
        let fact? ←
          tryCatchRuntimeEx
            (try
              pure (some (← proveDpFact stmt total))
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
  return (p, if assumed then conds ++ ["ASSUMED:dp-fact"] else conds)

/-- COMPOSE a verdict-only discharge node into a clause/preprocess replay: prove
    `EvTrue w env (disjoin clause)` (G2) under the AMBIENT `ReplayCtx` —
    opaque user-fn values come from the ctx PINS (placed there by
    `replayClause`'s uniform pinning), TP facts from the bound TP hypotheses.
    An unclosable DP fact is a frontier error here (the standalone harness
    reports such leaves ◌; conditional COMPOSITION needs condition threading —
    tracked in TODO). -/
def replayDischargeNode (cfg : ReplayConfig) (ctx : ReplayCtx) (clauseTerm : SExpr) :
    MetaM Expr := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap ACL2.Replay.freeVars).eraseDups
  let opaques := (lits.flatMap collectOpaques).eraseDups
  let pinned ← opaques.mapM fun op => do
    let some (v, p) := ctx.val? op
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
      let some (v, conv) := ctx.val? op
        | throwError "replayDischargeNode: unpinned TP opaque {repr op}"
      let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
        ++ (args.map reflectSExpr).toArray ++ #[v, conv])
      return some (instCor, fact)
  let stmt ← dpFactStmt tests last vars opaques (tpData.map (·.1))
  let fact ← proveDpFact stmt (vars.length + opaques.length)
  let concArgs ← vars.mapM (dpConcVar cfg.envExpr)
  let factConc := mkAppN fact (concArgs.toArray ++ (opqMap.map (·.2)).toArray
    ++ (tpData.map (·.2)).toArray)
  let bundle ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
  dischargeSpine cfg bundle opqMap clauseTerm factConc

end ACL2.Replay.Driver
