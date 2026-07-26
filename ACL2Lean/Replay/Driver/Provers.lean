/-
  Driver/Provers — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  Walker-independent obligation provers: totality from admission
  (proveTotality/buildTotalEnv), the TP prover (tpWalk/proveTp), and the
  D5 ground-zero rule-hypothesis dischargers.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Prove `total:fn` (the `mkTotalityHypType` statement) from the admission
    data; throws a named-frontier error when out of the D5 scope. -/
def proveTotality (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (name : String) (formals : List Symbol) (body : SExpr)
    (just? : Option Justification) : MetaM Expr := do
  let fs : Symbol := { name := name }
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) : MetaM (List (Symbol × Expr × Expr)) := do
    match formals, avs with
    | [f], [av] =>
      let g ← mkAppM ``bindArgs_single_get_self #[reflectSymbol f, av]
      let p ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f, av, g]
      return [(f, av, p)]
    | [f1, f2], [av1, av2] =>
      let hne ← mkDecideProof (← mkAppM ``Ne #[reflectSymbol f1, reflectSymbol f2])
      let g1 ← mkAppM ``bindArgs_pair_get_fst #[reflectSymbol f1, reflectSymbol f2, av1, av2]
      let g2 ← mkAppM ``bindArgs_pair_get_snd #[reflectSymbol f1, reflectSymbol f2, av1, av2, hne]
      let p1 ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f1, av1, g1]
      let p2 ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f2, av2, g2]
      return [(f1, av1, p1), (f2, av2, p2)]
    | _, _ => throwFrontier m!"proveTotality: arity {formals.length} unsupported (frontier)"
  match just? with
  | none =>
    -- NON-RECURSIVE: the body walk alone
    match formals with
    | [_] =>
      let hbody ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let envE ← mkEnvE [av]
        let vals ← varProofs envE [av]
        let p ← totWalk cfg envE vals [] totalEnv none body
        mkLambdaFVars #[av] p
      mkAppM ``totality_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol formals[0]!,
          reflectSExpr body, hNs, hDef, hbody]
    | [_, _] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let envE ← mkEnvE [av1, av2]
          let vals ← varProofs envE [av1, av2]
          let p ← totWalk cfg envE vals [] totalEnv none body
          mkLambdaFVars #[av1, av2] p
      mkAppM ``totality_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol formals[0]!,
          reflectSymbol formals[1]!, reflectSExpr body, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTotality: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope): measure (acl2-count m), o<, single measured formal
    unless just.wfRel.name == "O<" do
      throwFrontier m!"proveTotality: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some measuredFormal := just.measuredSubset.head?
      | throwFrontier m!"proveTotality: empty measured subset"
    unless just.measuredSubset.length == 1 do
      throwFrontier m!"proveTotality: multi-formal measured subset unsupported \
          (frontier)"
    let wantedMeasure : SExpr :=
      .cons (.atom (.symbol { name := "ACL2-COUNT" }))
        (.cons (.atom (.symbol { name := measuredFormal.name })) .nil)
    unless just.measure == wantedMeasure do
      throwFrontier m!"proveTotality: measure {repr just.measure} unsupported \
          (frontier: (acl2-count <measured-formal>) only)"
    -- D9: the (o-p (measure)) obligation is absorbed by the Nat-typed
    -- measure; SHAPE-CHECK it (hard-fail on anything unexpected)
    let opClause : SExpr :=
      .cons (.cons (.atom (.symbol { name := "O-P" }))
        (.cons wantedMeasure .nil)) .nil
    unless just.terminationClauses.any (· == opClause) do
      throwFrontier m!"proveTotality: expected (o-p {repr wantedMeasure}) \
          obligation not found (emission shape changed?)"
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.consCount #[e]
    match formals with
    | [f1] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTotality: measured formal mismatch"
      let step ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let envEat := fun (bv : Expr) => do
          let formalsE ← mkListLit (mkConst ``Symbol) [reflectSymbol f1]
          let avsE ← mkListLit (mkConst ``SExpr) [bv]
          mkAppM ``bindArgs #[formalsE, avsE]
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av]
          let envB ← envEat bv
          let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
          mkForallFVars #[bv] (← mkArrow lt conv)
        withLocalDeclD `ih ihType fun ih => do
          let envE ← envEat av
          let vals ← varProofs envE [av]
          let p ← totWalk cfg envE vals [] totalEnv
            (some (name, measuredFormal, ih, just)) body
          mkLambdaFVars #[av, ih] p
      mkAppM ``totality_1_rec
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, hNs, hDef, step]
    | [f1, f2] =>
      let envEat := fun (bv cv : Expr) => do
        let formalsE ← mkListLit (mkConst ``Symbol)
          [reflectSymbol f1, reflectSymbol f2]
        let avsE ← mkListLit (mkConst ``SExpr) [bv, cv]
        mkAppM ``bindArgs #[formalsE, avsE]
      if measuredFormal == f1 then
        let step ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
          let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
            let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
            let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
              let envB ← envEat bv cv
              let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
              mkForallFVars #[cv] conv
            mkForallFVars #[bv] (← mkArrow lt inner)
          withLocalDeclD `ih ihType fun ih =>
            withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
              let envE ← envEat av1 av2
              let vals ← varProofs envE [av1, av2]
              let p ← totWalk cfg envE vals [] totalEnv
                (some (name, measuredFormal, ih, just)) body
              mkLambdaFVars #[av1, ih, av2] p
        mkAppM ``totality_2_rec
          #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr body, hNs, hDef, step]
      else if measuredFormal == f2 then
        -- measured on the SECOND formal (e.g. (rm e x) / (memb a x) on x):
        -- strong induction on av2's count, av1 inner-∀ (totality_2_rec_snd)
        let step ← withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let ihType ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
            let lt ← mkAppM ``Nat.lt #[← countOf cv, ← countOf av2]
            let inner ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let envB ← envEat bv cv
              let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
              mkForallFVars #[bv] conv
            mkForallFVars #[cv] (← mkArrow lt inner)
          withLocalDeclD `ih ihType fun ih =>
            withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
              let envE ← envEat av1 av2
              let vals ← varProofs envE [av1, av2]
              let p ← totWalk cfg envE vals [] totalEnv
                (some (name, measuredFormal, ih, just)) body
              mkLambdaFVars #[av2, ih, av1] p
        mkAppM ``totality_2_rec_snd
          #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr body, hNs, hDef, step]
      else
        throwError "proveTotality: measured formal {measuredFormal.name} is \
            not among the formals (internal)"
    | _ => throwFrontier m!"proveTotality: recursive arity {formals.length} \
        unsupported (frontier)"

/-- #37: the admission-derived totality environment. `defs.entries` lists the
    USER defuns in DEVELOPMENT order followed by the ground-zero defs
    (`Development.toWorld` folds ground zero at the bottom and inserts user
    defuns while unwinding — the old `.reverse` here iterated BACKWARDS, a
    latent order bug that never bit until a fn depended on another user fn's
    totality: perm calls memb/rm). Robust fix: FIXPOINT — passes over the
    candidate set until no progress, so each fn is proved once its
    dependencies are in scope regardless of entry order. A fn that never
    proves stays out (hypothesis-backed downstream — D6). -/
def buildTotalEnv (cfg : ReplayConfig)
    (justs : List (String × Justification))
    (upTo : Option String := none) :
    MetaM (List (String × Nat × Expr)) := do
  -- candidate set: the dev-order prefix up to `upTo` (the lazy-discharge
  -- optimization) plus the ground-zero defs (in scope for every fn).
  -- ASSUMES define-before-use (ACL2 admission order), so the prefix is
  -- dependency-closed; if that were ever violated the only effect is a
  -- frontier failure keeping the hypothesis (D6) — completeness, never
  -- soundness (audit #4)
  let gz := cfg.gzDefs.map (·.1.name)
  let all := cfg.worldVal.defs.entries
  let cands ← match upTo with
    | none => pure all
    | some target => do
      let userEntries := all.filter (fun (s, _) => !gz.contains s.name)
      let rec takeTo : List (Symbol × List Symbol × SExpr) →
          List (Symbol × List Symbol × SExpr)
        | [] => []
        | e :: rest => if e.1.name == target then [e] else e :: takeTo rest
      pure (takeTo userEntries ++ all.filter (fun (s, _) => gz.contains s.name))
  let mut totalEnv : List (String × Nat × Expr) := []
  let mut pending := cands
  let mut progress := true
  while progress do
    progress := false
    let mut still : List (Symbol × List Symbol × SExpr) := []
    for (s, formals, body) in pending do
      try
        let pf ← proveTotality cfg totalEnv s.name formals body
          (justs.lookup s.name)
        totalEnv := (s.name, formals.length, pf) :: totalEnv
        progress := true
      catch e =>
        -- keep ONLY the prover's TAGGED frontier-class failures (the fn
        -- stays hypothesis-backed — D6); anything else is a real defect:
        -- surface it (typed tag, not message prefix — fail-closed audit N1)
        unless isFrontierErr e do
          throw e
        still := still ++ [(s, formals, body)]
    pending := still
  return totalEnv

/-- The TP body walk: a proof of `ConvToP w envE t P` — the body converges
    to a value SATISFYING the lifted-corollary predicate `P` (the TP prover,
    lifter sprint 2026-07-06; the `memb_body_bool` route, mechanized).
    Return-path arms: quote leaves (`P` by kernel decision), `if`-splits
    (liftable or OPAQUE tests — tests need only CONVERGENCE, from the plain
    walk over `totalEnv`), and self-calls (the admission-licensed strong
    IH). Every other body shape is a tagged frontier (D6: the `tp:`
    hypothesis stays). -/
partial def tpWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (P : Expr) (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  match t with
  | .cons (.atom (.symbol qs)) (.cons qv .nil) =>
    if qs.name == "QUOTE" then
      -- leaf constant: the corollary holds of it by ground kernel decision
      let hP ← proveByDecide (mkApp P (reflectSExpr qv)).headBeta
        s!"tp corollary at leaf {repr qv}"
      return ← mkAppM ``convP_quote
        #[cfg.worldExpr, envE, reflectSExpr qv, P, hP]
    else
      tpWalkCall cfg envE vals facts totalEnv self P t
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      if totLiftable c then
        let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
        let hc ← dpValProof cfg envE [] [] varP c
        let toBoolVc ← mkAppM ``Logic.toBool #[vc]
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr := do
          withLocalDeclD `hb (← mkEq toBoolVc (mkConst bval)) fun hb => do
            let p ← tpWalk cfg envE vals ((c, pos, hb) :: facts)
              totalEnv self P branch
            mkLambdaFVars #[hb] p
        let ht ← mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, vc, P, hc, ht, he]
      else
        -- OPAQUE (user-fn) test: converge it by the PLAIN walk (the fn's
        -- own totality is in totalEnv — buildTpEnv runs after totality),
        -- split on the existential verdict
        let hcEx ← totWalk cfg envE vals facts totalEnv none c
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr :=
          withLocalDeclD `vc (mkConst ``SExpr) fun vc => do
            let convTy ← mkAppM ``ConvTo
              #[cfg.worldExpr, envE, reflectSExpr c, vc]
            withLocalDeclD `hcv convTy fun hcv => do
              let hbTy ← mkEq (← mkAppM ``Logic.toBool #[vc]) (mkConst bval)
              withLocalDeclD `hb hbTy fun hb => do
                let p ← tpWalk cfg envE vals ((c, pos, hb) :: facts)
                  totalEnv self P branch
                mkLambdaFVars #[vc, hcv, hb] p
        let ht ← mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split_ex
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, P, hcEx, ht, he]
    else
      tpWalkCall cfg envE vals facts totalEnv self P t
  | _ => tpWalkCall cfg envE vals facts totalEnv self P t
where
  /-- Call arms: SELF-calls via the strong IH; everything else a frontier. -/
  tpWalkCall (cfg : ReplayConfig) (envE : Expr)
      (vals : List (Symbol × Expr × Expr))
      (facts : List (SExpr × Bool × Expr))
      (totalEnv : List (String × Nat × Expr))
      (self : Option (String × Symbol × Expr × Justification))
      (P : Expr) (t : SExpr) : MetaM Expr := do
    let varP : Symbol → Option (Expr × Expr) := fun s =>
      (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
    let .cons (.atom (.symbol fs)) argsSpine := t
      | throwFrontier m!"proveTp: body shape {repr t} unsupported (frontier)"
    let some (selfName, measuredFormal, ih, just) := self
      | throwFrontier m!"proveTp: call to {fs.name} on the return path of a \
          non-recursive body (frontier)"
    unless fs.name == selfName do
      throwFrontier m!"proveTp: return-path call to {fs.name} (not the \
          self-call) unsupported (frontier)"
    let args := (argsSpine.toList?).getD []
    match cfg.worldVal.defs.get? fs with
    | none => throwFrontier m!"proveTp: self {fs.name} not in world"
    | some (formals, body) =>
      unless args.length == formals.length do
        throwFrontier m!"proveTp: self-call arity mismatch {repr t}"
      let mIdx := formals.findIdx (· == measuredFormal)
      unless totLiftable args[mIdx]! do
        throwFrontier m!"proveTp: self-call MEASURED argument not liftable \
            {repr t} (frontier)"
      unless vals.any (fun (f, _, _) => f == measuredFormal) do
        throwFrontier m!"proveTp: measured formal has no bound value"
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
          | none => throwFrontier m!"dischargeDecrease: registry decrease \
              at {repr b} needs a refuted (endp {repr b}) fact (frontier)" }
      let dec ← dischargeDecrease just
        formals (formals.map (fun f => .atom (.symbol f)))
        formals args kit
      let hNs ← proveNotSpecial fs
      let hDef ← totWalk.totDefFact cfg fs formals body
      match formals, args with
      | [f1], [a1] =>
        let av ← dpValExpr [] (dpValProof.dpVarVal envE varP) a1
        let ap ← dpValProof cfg envE [] [] varP a1
        let hbody ← mkAppM' ih #[av, dec]
        return ← mkAppM ``convP_defn_1
          #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1, av,
            reflectSymbol f1, reflectSExpr body, P, hNs, hDef, ap, hbody]
      | [f1, f2], [a1, a2] =>
        let aM := args[mIdx]!
        let vM ← dpValExpr [] (dpValProof.dpVarVal envE varP) aM
        let pM ← dpValProof cfg envE [] [] varP aM
        let aO := args[1 - mIdx]!
        let assemble (vO pO : Expr) : MetaM Expr := do
          let hbody ← mkAppM' ih #[vM, dec, vO]
          let (v1, v2, p1, p2) :=
            if mIdx == 0 then (vM, vO, pM, pO) else (vO, vM, pO, pM)
          mkAppM ``convP_defn_2
            #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1,
              reflectSExpr a2, v1, v2, reflectSymbol f1, reflectSymbol f2,
              reflectSExpr body, P, hNs, hDef, p1, p2, hbody]
        if totLiftable aO then
          let vO ← dpValExpr [] (dpValProof.dpVarVal envE varP) aO
          let pO ← dpValProof cfg envE [] [] varP aO
          return ← assemble vO pO
        else
          -- opaque non-measured argument: plain-walk convergence, value
          -- bound by ∃-elimination (as in the totality prover)
          let hcEx ← totWalk cfg envE vals facts totalEnv none aO
          let k ← withLocalDeclD `vo (mkConst ``SExpr) fun vO => do
            let convTy ← mkAppM ``ConvTo
              #[cfg.worldExpr, envE, reflectSExpr aO, vO]
            withLocalDeclD `hcv convTy fun hcv => do
              mkLambdaFVars #[vO, hcv] (← assemble vO hcv)
          return ← mkAppM ``exists_conv_elim #[hcEx, k]
      | _, _ =>
        throwFrontier m!"proveTp: self-call arity {args.length} unsupported \
            (frontier)"

/-- Prove `tp:fn` (the `mkTpHypType` statement) from the fn's body and its
    EMITTED `:TYPE-PRESCRIPTION` corollary — the TP prover. The corollary is
    CONSUMED (ACL2's emitted type fact — never inferred); the walk proves the
    body's value satisfies it; argument strictness + determinism pin every
    convergence value (`tp_hyp_*_of_body`). Frontier failures are tagged
    (D6: the hypothesis stays visible). -/
def proveTp (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (justs : List (String × Justification))
    (name : String) (cor : SExpr) : MetaM Expr := do
  let fs : Symbol := { name := name }
  let some (formals, body) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: {name} not defined in the world (frontier)"
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  -- P := fun v => <corollary, (fn formals…) ↦ v, value-lifted> = SExpr.t —
  -- EXACTLY mkTpHypType's conclusion, so the proof inhabits the offered type
  let appPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let P ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
    let lifted ← dpValExpr [(appPat, vV)]
      (fun s => throwFrontier m!"proveTp: corollary of {name} mentions the \
          free variable {s.name} outside the application (frontier)") cor
    mkLambdaFVars #[vV] (← mkEq lifted (mkConst ``SExpr.t))
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) :
      MetaM (List (Symbol × Expr × Expr)) := do
    match formals, avs with
    | [f], [av] =>
      let g ← mkAppM ``bindArgs_single_get_self #[reflectSymbol f, av]
      let p ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f, av, g]
      return [(f, av, p)]
    | [f1, f2], [av1, av2] =>
      let hne ← mkDecideProof (← mkAppM ``Ne #[reflectSymbol f1, reflectSymbol f2])
      let g1 ← mkAppM ``bindArgs_pair_get_fst #[reflectSymbol f1, reflectSymbol f2, av1, av2]
      let g2 ← mkAppM ``bindArgs_pair_get_snd #[reflectSymbol f1, reflectSymbol f2, av1, av2, hne]
      let p1 ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f1, av1, g1]
      let p2 ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f2, av2, g2]
      return [(f1, av1, p1), (f2, av2, p2)]
    | _, _ => throwFrontier m!"proveTp: arity {formals.length} unsupported (frontier)"
  let mkConvToPTy (envB : Expr) : MetaM Expr :=
    mkAppM ``ConvToP #[cfg.worldExpr, envB, reflectSExpr body, P]
  match justs.lookup name with
  | none =>
    -- NON-RECURSIVE: the walk alone gives the ∀-body form
    match formals with
    | [f1] =>
      let hbody ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let envE ← mkEnvE [av]
        let vals ← varProofs envE [av]
        let p ← tpWalk cfg envE vals [] totalEnv none P body
        mkLambdaFVars #[av] p
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let envE ← mkEnvE [av1, av2]
          let vals ← varProofs envE [av1, av2]
          let p ← tpWalk cfg envE vals [] totalEnv none P body
          mkLambdaFVars #[av1, av2] p
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTp: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope, as in proveTotality)
    unless just.wfRel.name == "O<" do
      throwFrontier m!"proveTp: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some measuredFormal := just.measuredSubset.head?
      | throwFrontier m!"proveTp: empty measured subset"
    unless just.measuredSubset.length == 1 do
      throwFrontier m!"proveTp: multi-formal measured subset unsupported (frontier)"
    unless just.measure ==
        (.cons (.atom (.symbol { name := "ACL2-COUNT" }))
          (.cons (.atom (.symbol { name := measuredFormal.name })) .nil)) do
      throwFrontier m!"proveTp: measure {repr just.measure} unsupported \
          (frontier: (acl2-count <measured-formal>) only)"
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.consCount #[e]
    let selfC := fun (ih : Expr) => some (name, measuredFormal, ih, just)
    match formals with
    | [f1] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTp: measured formal mismatch"
      let step ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av]
          let cvty ← mkConvToPTy (← mkEnvE [bv])
          mkForallFVars #[bv] (← mkArrow lt cvty)
        withLocalDeclD `ih ihType fun ih => do
          let envE ← mkEnvE [av]
          let vals ← varProofs envE [av]
          let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) P body
          mkLambdaFVars #[av, ih] p
      let hbody ← mkAppM ``tp_1_rec
        #[reflectSymbol f1, reflectSExpr body, cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let step ←
        if measuredFormal == f1 then
          withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
            let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
              let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
                mkForallFVars #[cv] (← mkConvToPTy (← mkEnvE [bv, cv]))
              mkForallFVars #[bv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
                let envE ← mkEnvE [av1, av2]
                let vals ← varProofs envE [av1, av2]
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) P body
                mkLambdaFVars #[av1, ih, av2] p
        else if measuredFormal == f2 then
          withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
            let ihType ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
              let lt ← mkAppM ``Nat.lt #[← countOf cv, ← countOf av2]
              let inner ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
                mkForallFVars #[bv] (← mkConvToPTy (← mkEnvE [bv, cv]))
              mkForallFVars #[cv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
                let envE ← mkEnvE [av1, av2]
                let vals ← varProofs envE [av1, av2]
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) P body
                mkLambdaFVars #[av2, ih, av1] p
        else
          throwError "proveTp: measured formal not among the formals (internal)"
      let recLemma :=
        if measuredFormal == f1 then ``tp_2_rec else ``tp_2_rec_snd
      let hbody ← mkAppM recLemma
        #[reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTp: recursive arity {formals.length} \
        unsupported (frontier)"

/-- Substitute a hypothesis fvar by LET-BINDING its discharge proof instead
    of textual replacement (`replaceFVar`): `k` uses of the hypothesis share
    ONE copy of the (potentially enormous) discharge term instead of `k`
    copies. Proof-term scale fix (2026-07-06): perm-is-an-equivalence
    measured 3.87e9 Expr nodes (without sharing) from duplicated rule-hyp
    discharge proofs alone. No-op when the fvar does not occur. -/
def letBindFVar (body v value : Expr) : MetaM Expr := do
  if !body.containsFVar v.fvarId! then return body
  let ty ← inferType v
  let name ← v.fvarId!.getUserName
  return .letE name ty value (body.abstract #[v]) false

/-- Flatten an ACL2 `and`-antecedent: `(if A rest 'nil)` right-nesting →
    `[A, …]`; anything else is a single hypothesis. -/
partial def flattenAnd : SExpr → List SExpr
  | t@(.cons (.atom (.symbol ifS)) (.cons a (.cons rest (.cons e .nil)))) =>
    if ifS.name == "IF" && e == quoteNil then a :: flattenAnd rest else [t]
  | t => [t]

/-- D5 PRELUDE-CONSTANT registry (design §D5, WP3): ground-zero rules ACL2
    admits at boot with proofs SKIPPED (`ld-skip-proofsp`) — no replayable
    evidence exists, so each is proved ONCE in Lean about the trusted-core
    primitive (`GzRules.lean`), resting on the `LexorderOrder` theorems.
    Entry: rule name ↦ (the constant, the primitive's no-shadow fn). A
    ground-zero rule name can never collide with a user rule — ACL2 refuses
    the redefinition at admission. -/
def d5GzRules : List (String × Name × String) :=
  [("LEXORDER-REFLEXIVE",  (``gz_rule_lexorder_reflexive,  "LEXORDER")),
   ("LEXORDER-TRANSITIVE", (``gz_rule_lexorder_transitive, "LEXORDER"))]

/-- Discharge a GROUND-ZERO rule's `rule:<name>` hypothesis by its D5
    prelude constant: instantiate at the theorem's world + the primitive's
    no-shadow fact, then type-hint against the hypothesis type built FROM
    THE EMITTED SPEC (`mkRuleHypType`) — a drifted emission or a mis-stated
    constant fails here (fail-closed recompute-check, kernel-backed at
    `Meta.check`). -/
def dischargeGzRuleHyp (cfg : ReplayConfig) (spec : RuleSpec) (decl : Name)
    (noShadowFn : String) : MetaM Expr := do
  let hno ← proveNoShadow cfg { name := noShadowFn }
  mkExpectedTypeHint (mkApp2 (mkConst decl) cfg.worldExpr hno)
    (← mkRuleHypType cfg spec)

/-- D1 MIRROR REGISTRY (design §D1, WP4): replayed theorems as per-theorem
    Lean CONSTANTS. Entry: theorem name ↦ (the `addDecl`'d constant — type
    `∀ env, <kept-condition telescope> → EvTrue w ⟪Goal⟫` — and its kept
    condition strings, `total:`/`tp:`/`rule:` in telescope order).
    `dischargeRuleHyp` APPLIES the constant instead of re-replaying the
    dependency's tree per consumer — the kernel checks each proof once and a
    reference is O(1), collapsing the multiplicative dependency-tree blowup
    (the ≈557M-node perm-equivalence precedent, design §4). -/
abbrev MirrorRegistry := List (String × Name × List String)

end ACL2.Replay.Driver
