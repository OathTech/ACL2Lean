/-
  Driver/Totality — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  Totality from admission (#37): the body-CONVERGENCE walk (`totWalk`)
  and the decision-procedure leaf replays. The decrease machinery it
  consumes (the emitted-clause matching and the count/len/recorded
  walks) moved to `Driver/Decrease.lean` at the 2026-08-14 ratchet split.
-/
import ACL2Lean.Replay.Driver.Decrease

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

-- `TotFacts` MOVED to Driver/Decrease (T1+2 sprint P5b): the shared
-- recorded-decrease plumbing `recordedDecreaseAtCall` reads a walk's
-- branch facts, and it sits upstream of both walkers.

/-- The body-convergence walk: a proof of `∃N∃v ∀f≥N, eval envE t = some v`.
    `vals` carries each formal's VALUE expr and var-convergence proof;
    `facts` the branch context (`TotFacts`); `totalEnv` earlier functions'
    totality proofs (hypothesis-shaped); `selfC` the recursion data (the IH,
    the admission's MEASURE-TABLE ROW — R3, which fixes the IH's binder
    shape — plus the justification whose emitted clauses license its use). -/
partial def totWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (selfC : Option (String × MeasureShape × Expr × Justification ×
      Option RecTermInfo))
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
    if let some (selfName, mRow, ih, just, recInfo?) := selfC then
      if fs.name == selfName then
        match cfg.worldVal.defs.get? fs with
        | some (formals, body) =>
          unless args.length == formals.length do
            throwFrontier m!"proveTotality: self-call arity mismatch {repr (SExpr.cons (.atom (.symbol fs)) (args.foldr SExpr.cons .nil))}"
          -- the UNARY rows' single measured formal (the sum row is handled
          -- by its own arm below, which needs both)
          let measuredFormal := (mRow.vars.head?).getD { name := "" }
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
              let kLam ← withLocalDeclD `vs (mkConst ``SExpr) fun vσ => do
                let convTy ← mkValConvPropEx cfg.worldExpr envE
                  (reflectSExpr a1) vσ
                withLocalDeclD `hcs convTy fun hconvσ => do
                  -- the ruler coverage / nil-convergence plumbing is SHARED
                  -- with the TP prover's opaque-measured self-call arm
                  -- (`recordedDecreaseAtCall`, Driver/Decrease — extracted
                  -- at T1+2 sprint P5b when the second copy appeared)
                  let dec ← recordedDecreaseAtCall cfg envE vals facts
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
          -- RECOGNIZER DUALITY in the decrease PLUMBING (R3, 2026-08-14):
          -- `dischargeDecrease`'s COVERAGE check has understood the
          -- CONSP/ENDP/ATOM duality since the sorting arc
          -- (`branchEstablishes`), but this kit — which supplies the
          -- decrease's actual VALUE facts — knew only the literal
          -- spelling, so an emitted `(ENDP …)` ruler refuted by a
          -- translated `(CONSP …)` branch fact passed coverage and then
          -- failed here (MSORT's EVENS/ODDS registry decrease is exactly
          -- that gap BETWEEN two fragments). Both directions bridge
          -- through ACL2's own `(atom x) = (not (consp x))` axiom.
          let factOf (test : SExpr) (pos : Bool) : Option Expr :=
            (facts.find? (fun (f, p, _) => f == test && p == pos)).map
              (fun (_, _, pf, _) => pf)
          let recogTest (r : String) (b : SExpr) : SExpr :=
            .cons (.atom (.symbol { name := r })) (.cons b .nil)
          let kit : DecreaseKit := {
            cfg := cfg, envE := envE
            facts := facts.map (fun (f, pos, _) => (f, pos))
            valOf := fun u => dpValExpr [] (dpValProof.dpVarVal envE varP) u
            convOf := fun u => dpValProof cfg envE [] [] varP u
            conspTrueOf := fun b => do
              match factOf (recogTest "CONSP" b) true with
              | some pf => pure pf
              | none =>
                -- a refuted `(ENDP b)` / `(ATOM b)` IS `(consp b)`
                let fromNil (r : String) (lem : Name) : MetaM (Option Expr) := do
                  match factOf (recogTest r b) false with
                  | none => pure none
                  | some hb =>
                    let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP)
                      (recogTest r b)
                    let hnil ← mkAppM ``Iff.mp
                      #[← mkAppM ``Logic.toBool_eq_false #[vc], hb]
                    pure (some (← mkAppM lem #[hnil]))
                -- THE ORDINAL LEG (T1+2 sprint P3b): ACL2's ground-zero
                -- ordinal bodies branch on `(O-FINP b)`, whose emitted
                -- body is literally `(IF (CONSP X) 'NIL 'T)` — so the
                -- REFUTED `(O-FINP b)` ruler IS the consp evidence `O<` /
                -- `O-P`'s decreases need. The test is OPAQUE (a world
                -- call), so its verdict VALUE and convergence come from
                -- the split's CARRIED pair; nothing else can state it.
                -- Byte-checked against the emitted body before use.
                let fromOFinp : MetaM (Option Expr) := do
                  let test := recogTest "O-FINP" b
                  let some (_, _, hb, some (_, hcv)) :=
                      facts.find? (fun (f, p, _, _) => f == test && !p)
                    | return none
                  let some (fml, bdy) :=
                      cfg.worldVal.defs.get? { name := "O-FINP" } | return none
                  unless fml == [ACL2.Replay.oltXSym] &&
                      bdy == ACL2.Replay.oFinpBodyShape do
                    return none
                  unless totLiftable b do return none
                  let hbv ← dpValProof cfg envE [] [] varP b
                  let hnoConsp ← proveNoShadow cfg { name := "CONSP" }
                  let hdefF ← ordDefFact cfg { name := "O-FINP" }
                    ``ACL2.Replay.oFinpBodyShape ACL2.Replay.oFinpBodyShape
                  pure (some (← mkAppM ``ACL2.Replay.consp_toBool_of_ofinp_false
                    #[hnoConsp, hdefF, hbv, hcv, hb]))
                match ← fromNil "ENDP" ``consp_toBool_of_endp_nil with
                | some pf => pure pf
                | none =>
                  match ← fromNil "ATOM" ``consp_toBool_of_atom_nil with
                  | some pf => pure pf
                  | none =>
                    match ← fromOFinp with
                    | some pf => pure pf
                    | none => throwFrontier m!"dischargeDecrease: decrease at \
                        {repr b} needs an in-scope (consp {repr b}) fact \
                        (frontier)"
            endpFalseOf := fun b => do
              match factOf (recogTest "ENDP" b) false with
              | some pf => pure pf
              | none =>
                -- a truthy `(CONSP b)` makes `(endp b)` NIL, hence falsy
                match factOf (recogTest "CONSP" b) true with
                | some hb =>
                  mkAppM ``toBool_false_of_eq_nil
                    #[← mkAppM ``logic_endp_nil_of_consp_toBool #[hb]]
                | none => throwFrontier m!"dischargeDecrease: registry \
                    decrease at {repr b} needs a refuted (endp {repr b}) \
                    fact (frontier)"
            -- the GENERAL accessor: the admission walk's facts already
            -- carry each ruling test's `toBool = <sign>` proof, so an
            -- arbitrary ruler (the NFIX row's refuted `(ZP v)`) is a
            -- direct lookup
            factOf? := fun test pos => pure (factOf test pos) }
          let hNs ← proveNotSpecial fs
          let hDef ← totDefFact cfg fs formals body
          -- THE SUM-MEASURE ROW (R3; audit F6's single largest table cell —
          -- `MERGE2`/`INTERLEAVE`, `:MEASURE (BINARY-+ (ACL2-COUNT X)
          -- (ACL2-COUNT Y))` with `:MEASURED (Y X)`). BOTH formals are
          -- measured, so the IH is over the PAIR (`totality_2_rec_sum_mu`)
          -- and BOTH arguments must be value-characterized.
          if let .sumCount _ _ := mRow then
            match formals, args with
            | [f1, f2], [a1, a2] =>
              unless totLiftable a1 && totLiftable a2 do
                throwFrontier m!"proveTotality: sum-measure self-call \
                    argument not liftable {repr (SExpr.cons (.atom (.symbol fs)) (args.foldr SExpr.cons .nil))} (frontier)"
              let dec ← dischargeDecrease just
                formals (formals.map (fun f => .atom (.symbol f)))
                formals args kit
              let v1 ← dpValExpr [] (dpValProof.dpVarVal envE varP) a1
              let p1 ← dpValProof cfg envE [] [] varP a1
              let v2 ← dpValExpr [] (dpValProof.dpVarVal envE varP) a2
              let p2 ← dpValProof cfg envE [] [] varP a2
              let hbody ← mkAppM' ih #[v1, v2, dec]
              return ← mkAppM ``conv_defn_2_ex
                #[cfg.worldExpr, envE, reflectSymbol fs, reflectSymbol f1,
                  reflectSymbol f2, reflectSExpr body, reflectSExpr a1,
                  reflectSExpr a2, v1, v2, hNs, hDef, p1, p2, hbody]
            | _, _ =>
              throwFrontier m!"proveTotality: sum-measure self-call at \
                  arity {args.length} unsupported (frontier)"
          -- OPAQUE MEASURED argument on the DESTRUCTOR route (1-ary).
          -- `chainLt`'s S4 REGISTRY heads (`EVENS`/`ODDS`, with proved
          -- `CountSim` models) are USER-FN applications, so `MSORT`'s
          -- `(MSORT (EVENS X))` measured actual is not liftable and this
          -- arm's liftability gate rejected it — even though the decrease
          -- walk right below understands the shape. That was a gap
          -- BETWEEN two fragments, not a missing capability: bind the
          -- actual's VALUE by ∃-elimination over its own convergence walk
          -- (the same device the recorded route and the 2-ary
          -- non-measured argument already use) and hand it to the kit.
          if !totLiftable args[mIdx]! then
            match formals, args with
            | [f1], [a1] =>
              let hcEx ← totWalk cfg envE vals facts totalEnv selfC a1
              let kLam ← withLocalDeclD `vs (mkConst ``SExpr) fun vσ => do
                let convTy ← mkValConvPropEx cfg.worldExpr envE
                  (reflectSExpr a1) vσ
                withLocalDeclD `hcs convTy fun hconvσ => do
                  let kitO : DecreaseKit := { kit with
                    valOf := fun u =>
                      if u == a1 then pure vσ else kit.valOf u
                    convOf := fun u =>
                      if u == a1 then pure hconvσ else kit.convOf u }
                  let dec ← dischargeDecrease just
                    formals (formals.map (fun f => .atom (.symbol f)))
                    formals args kitO
                  let hbody ← mkAppM' ih #[vσ, dec]
                  let p ← mkAppM ``conv_defn_1_ex
                    #[cfg.worldExpr, envE, reflectSymbol fs,
                      reflectSymbol f1, reflectSExpr body, reflectSExpr a1,
                      vσ, hNs, hDef, hconvσ, hbody]
                  mkLambdaFVars #[vσ, hconvσ] p
              return ← mkAppM ``exists_conv_elim #[hcEx, kLam]
            | [f1, f2], [a1, a2] =>
              -- ARITY 2, opaque measured actual (T1+2 sprint P3b — the
              -- ORDINAL family: `O<`'s own self-calls
              -- `(O< (O-RST X) (O-RST Y))` / `(O< (O-FIRST-EXPT X)
              -- (O-FIRST-EXPT Y))`, whose actuals are ground-zero DEFUN
              -- applications and so not walk-liftable at EITHER position).
              -- Same device as the 1-ary arm, applied per position: a
              -- liftable actual is pinned by the DP lift, an opaque one by
              -- ∃-elimination over its own convergence walk.
              let pin (a : SExpr) (k : Expr → Expr → MetaM Expr) :
                  MetaM Expr := do
                if totLiftable a then
                  k (← dpValExpr [] (dpValProof.dpVarVal envE varP) a)
                    (← dpValProof cfg envE [] [] varP a)
                else
                  let hcEx ← totWalk cfg envE vals facts totalEnv selfC a
                  let kLam ← withLocalDeclD `vs (mkConst ``SExpr) fun v => do
                    let convTy ← mkValConvPropEx cfg.worldExpr envE
                      (reflectSExpr a) v
                    withLocalDeclD `hcs convTy fun hc => do
                      mkLambdaFVars #[v, hc] (← k v hc)
                  mkAppM ``exists_conv_elim #[hcEx, kLam]
              return ← pin a1 fun v1 p1 => pin a2 fun v2 p2 => do
                let kitO : DecreaseKit := { kit with
                  valOf := fun u =>
                    if u == a1 then pure v1
                    else if u == a2 then pure v2 else kit.valOf u
                  convOf := fun u =>
                    if u == a1 then pure p1
                    else if u == a2 then pure p2 else kit.convOf u }
                let dec ← dischargeDecrease just
                  formals (formals.map (fun f => .atom (.symbol f)))
                  formals args kitO
                let (vM, vO) := if mIdx == 0 then (v1, v2) else (v2, v1)
                let hbody ← mkAppM' ih #[vM, dec, vO]
                mkAppM ``conv_defn_2_ex
                  #[cfg.worldExpr, envE, reflectSymbol fs, reflectSymbol f1,
                    reflectSymbol f2, reflectSExpr body, reflectSExpr a1,
                    reflectSExpr a2, v1, v2, hNs, hDef, p1, p2, hbody]
            | _, _ => pure ()
          -- the MEASURED argument must be value-characterized (the decrease
          -- and the IH's count argument are stated about its value)
          unless totLiftable args[mIdx]! do
            throwFrontier m!"proveTotality: self-call MEASURED argument not \
                liftable {repr (SExpr.cons (.atom (.symbol fs)) (args.foldr SExpr.cons .nil))} (frontier)"
          unless vals.any (fun (f, _, _) => f == measuredFormal) do
            throwFrontier m!"proveTotality: measured formal has no bound value"
          let dec ← dischargeDecrease just
            formals (formals.map (fun f => .atom (.symbol f)))
            formals args kit
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
            -- 3-ary, measured on the FIRST (`ZIP3`) or SECOND
            -- (`FILTER`/`ALL-REL`) formal — audit F7: the position
            -- restriction to the second formal was fitted to FILTER's
            -- `(fn x e)` shape while `recon-tests/16-three-way` sat in the
            -- corpus demanding the first. The IH binder order follows the
            -- applied lemma's step: (measured value, decrease, then the
            -- remaining values in formal order). Liftable arguments only.
            unless measuredFormal == f1 || measuredFormal == f2 do
              throwFrontier m!"proveTotality: 3-ary self-call measured \
                  formal {measuredFormal.name} is neither the first nor \
                  the second formal (frontier)"
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
            let hbody ←
              if measuredFormal == f1 then mkAppM' ih #[v1, dec, v2, v3]
              else mkAppM' ih #[v2, dec, v1, v3]
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
          let p ← totWalk cfg envE vals ((c, false, hb, none) :: facts)
            totalEnv selfC e
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
              let p ← totWalk cfg envE vals ((c, true, hb, none) :: facts)
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
                let p ← totWalk cfg envE vals ((c, pos, hb, some (vc, hcv)) :: facts)
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
