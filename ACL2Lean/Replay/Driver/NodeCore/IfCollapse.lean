import ACL2Lean.Replay.Driver.TypeSetQuery

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The PCE-class chain-end IF-COLLAPSE bridge (final-closeout arc):
    when a literal's composed chain reaches an IF-nest whose recorded
    result has the ifs COLLAPSED (rewrite-atm's boundary
    normalization), prove the two terms' VALUES equal and bridge by
    `fuel_eq_of_conv`. Every collapse is justified, never inferred:
    a test resolves `'t` ONLY via an emitted `:IF-TEST-TRUE` marker
    for that exact test (the type-set basis then PROVED by
    `replayRecognizer`'s closure machinery) or by the recursive
    structure; the `(IF x 'T 'NIL) ⇒ x` collapse ONLY by the branch
    values' two-valued RANGE (the emitted case-split shapes'
    primitives). `none` on any other shape — the caller's loud
    frontier stays. -/
partial def bridgeIfCollapseFromRecords
    (recognize : ReplayConfig → ReplayCtx → SExpr → SExpr → MetaM Expr)
    (cfg : ReplayConfig) (ctx : ReplayCtx)
    (ifMarkers : List (SExpr × Bool × SExpr))
    (reached recorded : SExpr) : MetaM (Option Expr) := do
  -- (no top-level marker gate: each collapse case carries its own
  -- anchor — markers for test-true, the emitted TP corollary for the
  -- boolean-TP fold, the two-valued primitives for the range collapse)
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx reached
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx recorded
  let quoteT' : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons SExpr.t .nil)
  let quoteNil' : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons SExpr.nil .nil)
  -- v(t) = 't, justified: quoted 'T; a marker-anchored test (the
  -- type-set basis proved by the recognizer closure); or a
  -- (IF x 'T 'NIL) whose x is itself so justified
  let rec valIsT (ctx : ReplayCtx) (t : SExpr) : MetaM (Option Expr) := do
    if t == quoteT' then
      return some (← mkEqRefl (mkConst ``SExpr.t))
    if let some just := ifMarkers.findSome?
        (fun (mt, sense, j) => if sense && mt == t then some j else none) then
      if let some p ← replayIfTypeQuery? cfg ctx t true just then return some p
      let pT ← try some <$> recognize cfg ctx t SExpr.t
        catch _ => pure none
      match pT with
      | some pT =>
        let pV ← ctxValProof cfg ctx t
        return some (← mkAppM ``conv_val_eq #[pV, pT])
      | none =>
        let some (arg, mask, lemmaName) := tsTestTrueOf t | return none
        let citedCr ← ofExcept (ifMarkerCitedCr just)
        let ctxA ← pinTermOpaques cfg cfg.envExpr ctx arg
        let va ← ctxValExpr cfg ctxA arg
        let some h ← inTsFromCtx cfg ctxA [] citedCr arg va mask | return none
        return some (← mkAppM lemmaName #[← tsSubsumedProofM mask mask, h])
    match t with
    | .cons (.atom (.symbol ifS)) (.cons c (.cons th (.cons el .nil))) =>
      if ifS.name == "IF" && th == quoteT' && el == quoteNil' then
        match ← valIsT ctx c with
        | some hc => return some (← Lean.Meta.mkAppOptM ``cond_of_val_t
            #[none, some (mkConst ``SExpr.t), some (mkConst ``SExpr.nil),
              some hc])
        | none => return none
      else return none
    | _ => return none
  -- v(t) = 'nil, justified: quoted 'NIL, or an emitted :IF-TEST-FALSE
  -- marker for exactly this test whose falsity the walk can PROVE — from
  -- the in-scope facts (`typeSetWalk`), or, for a test ACL2 resolved by
  -- TYPE-SET, by the D-A algebra: the test's own TRUE type-set is
  -- DISJOINT from the type-set the clause context gives its argument
  -- (`tsTestNilOf` + `inTsFromCtx`). The marker is the ANCHOR; the
  -- falsity is never assumed from it — and the typing probes the algebra
  -- may use are gated on the MARKER'S OWN cited compound-recognizer
  -- runes (`ifMarkerCitedCr`, the BUG-023 direction), so the reason ACL2
  -- recorded for the collapse is the reason the replay is allowed to use.
  let valIsNil (ctx : ReplayCtx) (t : SExpr) : MetaM (Option Expr) := do
    if t == quoteNil' then
      return some (← mkEqRefl (mkConst ``SExpr.nil))
    let some just := ifMarkers.findSome?
        (fun (mt, sense, j) => if !sense && mt == t then some j else none)
      | return none
    if let some p ← replayIfTypeQuery? cfg ctx t false just then return some p
    let citedCr ← ofExcept (ifMarkerCitedCr just)
    let ctxT ← pinTermOpaques cfg cfg.envExpr ctx t
    match ← typeSetWalk cfg ctxT (.isNil t) with
    | some h => return some h
    | none =>
      let some (a, mT, lem) := tsTestNilOf t | return none
      let ctxA ← pinTermOpaques cfg cfg.envExpr ctxT a
      let va ← ctxValExpr cfg ctxA a
      -- Refute the test's TRUE mask using the existing intersection
      -- algebra. Individual facts may overlap it even when their
      -- intersection does not: with complex values present, INTEGERP
      -- and (< 0 N) are both needed for CLASSIFY-POS's recorded collapse.
      -- The target is the exact mask complement, not a guessed type fact.
      let m := -mT - 1
      let some hv ← inTsFromCtx cfg ctxA [] citedCr a va m | return none
      let hd ← mkDecideProof (← mkEq
        (← mkAppM ``ACL2.Replay.tsDisjointM
          #[Lean.toExpr m, Lean.toExpr mT])
        (mkConst ``Bool.true))
      return some (← mkAppM lem #[hd, hv])
  -- v(a) = v(b), by justified collapses only
  let rec go (ctx : ReplayCtx) (a b : SExpr) : MetaM (Option Expr) := do
    if a == b then
      return some (← mkEqRefl (← ctxValExpr cfg ctx a))
    -- Equality compares two values; a recorded IF collapse can occur in
    -- either operand. Transport those checked operand equalities without
    -- changing the marker requirement for any nested conditional.
    if let some (eqA, [p, q]) := asApp a then
      if let some (eqB, [p', q']) := asApp b then
        if eqA.name == "EQUAL" && eqA == eqB then
          let some hp ← go ctx p p' | return none
          let some hq ← go ctx q q' | return none
          return some (← mkCongr (← mkCongrArg (mkConst ``Logic.equal) hp) hq)
    match a, b with
    | .cons (.atom (.symbol na)) (.cons xa .nil),
      .cons (.atom (.symbol nb)) (.cons xb .nil) =>
      if na.name == "NOT" && nb.name == "NOT" then
        match ← go ctx xa xb with
        | some h =>
          return some (← Lean.Meta.mkCongrArg (mkConst ``Logic.not) h)
        | none => return none
      else return none
    | .cons (.atom (.symbol ifS)) (.cons c (.cons th (.cons el .nil))), _ =>
      if ifS.name != "IF" then return none
      -- Same outer IF: descend under its own branch hypothesis. The
      -- recorded target chooses the structural correspondence; only an
      -- explicitly recorded test verdict can remove an inner IF.
      if let .cons (.atom (.symbol ifS')) (.cons c' (.cons th' (.cons el' .nil))) := b then
        if ifS'.name == "IF" && c == c' then
          let vc ← ctxValExpr cfg ctx c
          let ht? ← withLocalDeclD `hThen (← mkAppM ``Ne #[vc, mkConst ``SExpr.nil]) fun ht => do
            let ctxT ← installBranchTrueFacts cfg ctx c vc ht
            let some hp ← go ctxT th th' | return none
            return some (← mkLambdaFVars #[ht] hp)
          let hf? ← withLocalDeclD `hElse (← mkEq vc (mkConst ``SExpr.nil)) fun hf => do
            let ctxF := { ctx with branchFacts := ctx.branchFacts ++ [(c, vc, false, hf)] }
            let some hp ← go ctxF el el' | return none
            return some (← mkLambdaFVars #[hf] hp)
          match ht?, hf? with
          | some ht, some hf => return some (← mkAppM ``cond_value_congr #[ht, hf])
          | _, _ => return none
      -- (i) marker-justified test-true: take the then-branch
      match ← valIsT ctx c with
      | some hc =>
        let hstep ← Lean.Meta.mkAppOptM ``cond_of_val_t
          #[none, some (← ctxValExpr cfg ctx th),
            some (← ctxValExpr cfg ctx el), some hc]
        match ← go ctx th b with
        | some hrest => return some (← mkAppM ``Eq.trans #[hstep, hrest])
        | none => return none
      | none =>
        -- (i') marker-justified test-FALSE: take the else-branch (ACL2's
        -- rewrite-if-finish returns the surviving branch directly and
        -- records only the :IF-TEST-FALSE marker)
        match ← valIsNil ctx c with
        | some hc =>
          let hstep ← Lean.Meta.mkAppOptM ``cond_of_val_nil
            #[none, some (← ctxValExpr cfg ctx th),
              some (← ctxValExpr cfg ctx el), some hc]
          match ← go ctx el b with
          | some hrest => return some (← mkAppM ``Eq.trans #[hstep, hrest])
          | none => return none
        | none =>
        -- (ii) the boolean collapse (IF b 'T 'NIL) ⇒ b
        if th == quoteT' && el == quoteNil' && c == b then
          match ← boolDisj? cfg ctx b with
          | some hr => return some (← mkAppM ``cond_tnil_of_range #[hr])
          | none => return none
        else return none
    | .cons (.atom (.symbol eqS)) (.cons p (.cons qt' .nil)), _ =>
      -- (iii) the BOOLEAN-TP fold under composition: (EQUAL p 'T) vs p,
      -- where p's fn carries the emitted boolean TP corollary
      -- (IF (EQUAL p 'T) 'T (EQUAL p 'NIL)) — the value identity
      -- logic_equal_t_self_of_boolean_tp (consumed, not inferred)
      if eqS.name == "EQUAL" && qt' == quoteT' && p == b then
        match p with
        | .cons (.atom (.symbol fs)) argsSpine =>
          match ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) with
          | none => return none
          | some (_, cor, tpHyp) =>
            let some (formals, _) := cfg.worldVal.defs.get? fs
              | return none
            let args := (argsSpine.toList?).getD []
            if formals.length != args.length then return none
            let eqT' (x y : SExpr) : SExpr :=
              .cons (.atom (.symbol { name := "EQUAL" }))
                (.cons x (.cons y .nil))
            let inst := ACL2.Replay.substTerm formals args cor
            let expected : SExpr :=
              .cons (.atom (.symbol { name := "IF" }))
                (.cons (eqT' p quoteT')
                  (.cons quoteT' (.cons (eqT' p quoteNil') .nil)))
            if inst != expected then return none
            let some (vp, convp) := ctx.val? p | return none
            let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
              ++ (args.map reflectSExpr).toArray ++ #[vp, convp])
            return some (← mkAppM ``logic_equal_t_self_of_boolean_tp
              #[fact])
        | _ => return none
      else return none
    | _, _ => return none
  match ← go ctx reached recorded with
  | none => return none
  | some hval =>
    let pA ← ctxValProof cfg ctx reached
    let pB ← ctxValProof cfg ctx recorded
    return some (← mkAppM ``fuel_eq_of_conv #[pA, pB, hval])

end ACL2.Replay.Driver
