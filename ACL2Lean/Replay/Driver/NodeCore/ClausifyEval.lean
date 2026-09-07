import ACL2Lean.Replay.Driver.NodeCore.HypRelief
import ACL2Lean.Replay.Driver.NodeCore.GroundFold

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The literal-clausify DECISION TREE, reconstructed from the flat
    `SplitDecision` trace (docs/notes/2026-07-03_branch-split-spine.md).
    `if-interp` pushes events else-branch-FIRST at splits; every event is
    self-located by its `path`, which the parser validates against its
    position (fail-closed). -/
inductive TraceTree where
  /-- `segment` (segment-* outcomes): the EMITTED clause segment for this
      leaf — the exact leaf→branch link the composer selects by. -/
  | leaf (value : SExpr) (outcome : String) (segment : Option (List SExpr))
      (calls : List ClausifyCallAssumption := [])
      (reductions : Option (List ClausifyReduction) := none)
  | resolved (test : SExpr) (verdict : String) (how : String) (sub : TraceTree)
  /-- A genuine split: `fSide` (test assumed false — the ELSE branch,
      logged first) and `tSide`. -/
  | split (test : SExpr) (fSide tSide : TraceTree)
  deriving Repr, Inhabited

partial def parseTraceTree (path : List (Bool × SExpr)) :
    List SplitDecision → Except String (TraceTree × List SplitDecision)
  | [] => throw "parseTraceTree: trace ended without a leaf"
  | .test t v h p :: rest => do
    unless p == path do
      throw s!"parseTraceTree: test {repr t} at path {repr p}, expected \
               {repr path}"
    if v == "split" then
      let (fSide, rest) ← parseTraceTree (path ++ [(false, t)]) rest
      let (tSide, rest) ← parseTraceTree (path ++ [(true, t)]) rest
      return (.split t fSide tSide, rest)
    else
      let (sub, rest) ← parseTraceTree path rest
      return (.resolved t v h sub, rest)
  | .leaf v o p seg calls reductions :: rest => do
    unless p == path do
      throw s!"parseTraceTree: leaf {repr v} at path {repr p}, expected \
               {repr path}"
    for call in calls do
      unless call.path == path do
        throw "parseTraceTree: call assumption path differs from its leaf (frontier)"
    -- ∧-DECOMPOSITION (observed: ALL-REL-FILTER-1 literal 2): on a term
    -- `(if v X 'nil)`, if-interp emits the SEGMENT-OPEN leaf `v` (the
    -- `[v]`-segment child clause of `lit ≡ v ∧ X`) and CONTINUES
    -- enumerating X's segments at the SAME path — the leaf is not
    -- terminal. For the composer this is the decision split on `v`:
    -- under ¬v the literal is 'nil (and the `[v]` branch's segment —
    -- carried over from the open leaf's emitted :SEGMENT — is selected
    -- right there); under v the continuation's decisions apply.
    -- Synthesize exactly that split — every downstream check
    -- (collapse-vs-leaf-value, branch selection) stays fail-closed.
    let nextSamePath := match rest with
      | .test _ _ _ p' :: _ => p' == path
      | .leaf _ _ p' _ _ _ :: _ => p' == path
      | [] => false
    if o == "segment-open" && nextSamePath then
      unless calls.isEmpty do
        throw "parseTraceTree: call assumptions before conjunction continuation (frontier)"
      let (k, rest') ← parseTraceTree path rest
      return (.split v (.leaf quoteNil "segment-false" seg [] reductions) k, rest')
    return (.leaf v o seg calls reductions, rest)

/-- Follow the actual later reductions of this generated segment, in emitted
order. Every replacement must be a strengthening by literal inclusion;
the composer separately kernel-checks each final literal's falsity. -/
def followClausifyReductions (segment : List SExpr) (reductions : List ClausifyReduction) :
    Except String (List SExpr) := do
  let mut current := segment
  for reduction in reductions do
    unless ["subsumed-new", "subsumed-old", "subsumed", "replaced"].contains reduction.kind do
      throw "clausify reductions: unsupported selected operation"
    unless reduction.afterClause.all reduction.beforeClause.contains do
      throw "clausify reductions: result is not a subset of its selected source (frontier)"
    if current == reduction.beforeClause then current := reduction.afterClause
  return current

/-- Collapse `t`'s ifs whose tests are DECIDED by the in-scope facts (the
    branch-split composer's byCases hypotheses + re-derived resolved
    verdicts), plus the two `call-stack` folds if-interp applied — `(not 'c)`
    by ground re-execution, `(equal X X)` by reflexivity — bottom-up,
    mirroring if-interp's interpretation of the rewritten literal. Returns
    the fuel-eq chain `eval t ≡ eval t'` and the collapsed `t'`. Anything the
    enumerated rule set cannot decide is left in place; the composer's
    leaf-value check fail-closes on divergence from the emitted trace.
    With `assumptionCall?`, assumption folds come only from that recorded-call
    consumer; the legacy clause-context reconstruction is disabled. -/
partial def collapseEval (cfg : ReplayConfig) (ctx : ReplayCtx)
    (facts : List (SExpr × Expr × Bool × Expr)) (t : SExpr)
    (assumptionCall? : Option (SExpr → MetaM (Option (Expr × SExpr))) := none) :
    MetaM (Option Expr × SExpr) := do
  let w := cfg.worldExpr
  let e := cfg.envExpr
  let some (fs, args) := asApp t | return (none, t)
  if fs.name == "QUOTE" then return (none, t)
  if assumptionCall?.isNone then
    -- an in-scope SPINE falsity fact resolves the term outright: if-interp
    -- consults the clause-segment ASSUMPTIONS for the terms it encounters (the
    -- other literals are assumed false) — e.g. a collapsed residual that IS
    -- another clause literal. Divergence still fail-closes at the composer's
    -- leaf-value check.
    if let some hNil := ctx.litFactByTerm? t then
      let pl ← ctxValProof cfg ctx t
      let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
      let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
      return (some step, quoteNil)
    -- EQUAL falsity via the spine facts (if-interp-assumed-value2's rule
    -- set): the commuted form, and ONE transport step through an in-scope
    -- segment EQUALITY (a `(not (equal a b))` literal's falsity, i.e. a = b —
    -- ACL2's type-alist canonicalizes the test through it; observed:
    -- (EQUAL D E) resolved from D = (CAR X) and (EQUAL (CAR X) E) = nil,
    -- ALL-REL-RM-2). All derivations are proof-carrying; anything beyond
    -- this bounded rule set stays unresolved and fail-closes downstream.
    if let .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) := t then
      if eqS.name == "EQUAL" then
        let mkEqT (u v : SExpr) : SExpr :=
          .cons (.atom (.symbol eqS)) (.cons u (.cons v .nil))
        -- falsity of `(equal u v)` from a direct or commuted spine fact,
        -- stated over the given value exprs
        let eqFalsity (u v : SExpr) (vu vv : Expr) : MetaM (Option Expr) := do
          if let some h := ctx.litFactByTerm? (mkEqT u v) then
            return some h
          if let some h := ctx.litFactByTerm? (mkEqT v u) then
            return some (← mkAppM ``Eq.trans #[← mkAppM ``logic_equal_comm #[vu, vv], h])
          return none
        let vx ← ctxValExpr cfg ctx x
        let vy ← ctxValExpr cfg ctx y
        let mut hNil? ← eqFalsity x y vx vy
        if hNil?.isNone then
          -- one transport step through each in-scope segment equality a = b
          for (st, h) in ctx.segFacts do
            if hNil?.isSome then break
            let .cons (.atom (.symbol ns)) (.cons
                (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) .nil) := st
              | continue
            unless ns.name == "NOT" && es.name == "EQUAL" do continue
            let va ← ctxValExpr cfg ctx a
            let vb ← ctxValExpr cfg ctx b
            let hab ← mkAppM ``logic_not_equal_nil_eq #[va, vb, h]  -- va = vb
            -- try rewriting x (a→b / b→a), then y likewise
            let tryPos (isX : Bool) (frm tgt : SExpr) (hft : Expr) :
                MetaM (Option Expr) := do
              unless (if isX then x else y) == frm do return none
              let vto ← ctxValExpr cfg ctx tgt
              let some hf ← (if isX then eqFalsity tgt y vto vy
                             else eqFalsity x tgt vx vto) | return none
              -- v(equal x y) = v(equal [to/frm]) = nil
              let f ← withLocalDeclD `v (mkConst ``SExpr) fun vV =>
                mkLambdaFVars #[vV]
                  (if isX then mkApp2 (mkConst ``Logic.equal) vV vy
                   else mkApp2 (mkConst ``Logic.equal) vx vV)
              let step ← mkAppM ``congrArg #[f, hft]
              return some (← mkAppM ``Eq.trans #[step, hf])
            let hba ← mkAppM ``Eq.symm #[hab]
            for (isX, frm, tgt, hft) in
                [(true, a, b, hab), (true, b, a, hba),
                 (false, a, b, hab), (false, b, a, hba)] do
              if hNil?.isNone then
                hNil? ← tryPos isX frm tgt hft
        if let some hNil := hNil? then
          let pl ← ctxValProof cfg ctx t
          let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
          let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
          return (some step, quoteNil)
  if fs.name == "IF" then
    match args with
    | [c, a, b] =>
      -- collapse the test first; decide; then only the LIVE branch
      let (chC, c') ← collapseEval cfg ctx facts c assumptionCall?
      let mut acc : Option Expr := none
      let mut cur := t
      if let some ch := chC then
        let st : PathStep := { fn := fs, arity := 3, argIdx := 0, siblings := [a, b] }
        acc := some (← applyStep w e st c c' ch)
        cur := .cons (.atom (.symbol fs)) ([c', a, b].foldr .cons .nil)
      -- the test collapsed to a QUOTED CONSTANT (an in-scope litFact or fold
      -- resolved it): take the branch, exactly as if-interp does
      if let .cons (.atom (.symbol q)) (.cons cv .nil) := c' then
        if q.name == "QUOTE" then
          let (step, sel) ← mkConstTestCollapse cfg ctx c' cv a b
          let acc' ← chainAfter acc step
          let (chSel, final) ← collapseEval cfg ctx facts sel assumptionCall?
          match chSel with
          | none => return (some acc', final)
          | some m => return (some (← mkAppM ``fuel_chain_eq #[acc', m]), final)
      match facts.find? (fun (T, _, _, _) => T == c') with
      | some (_, vT, sign, h) =>
        let hc ← ctxValProof cfg ctx c'
        let step ←
          if sign then
            let hcv ← mkAppM ``toBool_true_of_ne_nil #[h]
            let va ← ctxValExpr cfg ctx a
            let ha ← ctxValProof cfg ctx a
            let _ := va
            mkAppM ``re_if_true
              #[w, e, reflectSExpr c', reflectSExpr a, reflectSExpr b, vT, va, hc, hcv, ha]
          else
            let hcNil ← mkAppM ``re_val_cast
              #[w, e, reflectSExpr c', vT, mkConst ``SExpr.nil, hc, h]
            let vb ← ctxValExpr cfg ctx b
            let hb ← ctxValProof cfg ctx b
            let _ := vb
            mkAppM ``re_if_false
              #[w, e, reflectSExpr c', reflectSExpr a, reflectSExpr b, vb, hcNil, hb]
        let sel := if sign then a else b
        let acc' ← chainAfter acc step
        let (chSel, final) ← collapseEval cfg ctx facts sel assumptionCall?
        match chSel with
        | none => return (some acc', final)
        | some m => return (some (← mkAppM ``fuel_chain_eq #[acc', m]), final)
      | none =>
        -- unresolved test: collapse both branches in place
        let (chA, a') ← collapseEval cfg ctx facts a assumptionCall?
        if let some ch := chA then
          let st : PathStep := { fn := fs, arity := 3, argIdx := 1, siblings := [c', b] }
          let lifted ← applyStep w e st a a' ch
          acc := some (← chainAfter acc lifted)
          cur := .cons (.atom (.symbol fs)) ([c', a', b].foldr .cons .nil)
        let (chB, b') ← collapseEval cfg ctx facts b assumptionCall?
        if let some ch := chB then
          let st : PathStep := { fn := fs, arity := 3, argIdx := 2, siblings := [c', a'] }
          let lifted ← applyStep w e st b b' ch
          acc := some (← chainAfter acc lifted)
          cur := .cons (.atom (.symbol fs)) ([c', a', b'].foldr .cons .nil)
        let _ := cur
        return (acc, .cons (.atom (.symbol fs)) ([c', a', b'].foldr .cons .nil))
    | _ => throwError "collapseEval: malformed if {repr t}"
  -- if-compile PUSHes an IF-free application unchanged; only a CALL
  -- rebuilds arguments and applies call-stack's head folds (BUG-032).
  unless args.any clausifyContainsIf do return (none, t)
  -- generic application: collapse arguments left-to-right, then head folds
  let mut curArgs := args.toArray
  let mut acc : Option Expr := none
  for i in [0:args.length] do
    let a := curArgs[i]!
    let (chA, a') ← collapseEval cfg ctx facts a assumptionCall?
    if let some ch := chA then
      let siblings := (curArgs.toList.zipIdx.filterMap fun (x, j) =>
        if j == i then none else some x)
      let st : PathStep := { fn := fs, arity := args.length, argIdx := i, siblings }
      let lifted ← applyStep w e st a a' ch
      acc := some (← chainAfter acc lifted)
      curArgs := curArgs.set! i a'
  let cur : SExpr := .cons (.atom (.symbol fs)) (curArgs.toList.foldr .cons .nil)
  if let some call := assumptionCall? then
    if let some (proof, output) ← call cur then
      return (some (← chainAfter acc proof), output)
  if assumptionCall?.isNone then
    -- the POST-COLLAPSE term may be the form an in-scope assumption is about
    -- (argument collapse rebuilt it into another clause literal)
    if let some hNil := ctx.litFactByTerm? cur then
      let pl ← ctxValProof cfg ctx cur
      let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
      let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
      let acc' ← chainAfter acc step
      return (some acc', quoteNil)
  -- call-stack folds (rewrite.lisp:call-stack; cons-term's primitive
  -- domain and guards are emitted from basis-b.lisp's own table).
  let fold? ← do
    -- Only the emitted primitive/guard table licenses cons-term folding.
    -- An interpreter builtin can still be an ACL2 defun: EXPT must remain
    -- intact here, even after its arguments collapse to constants.
    if curArgs.all (fun a => match a with
        | .cons (.atom (.symbol q)) (.cons _ .nil) => q.name == "QUOTE"
        | _ => false) &&
       cfg.worldVal.defs.get? fs == none && fs.name != "NOT" then
      let v? ← consTermGroundValue? cfg fs curArgs.toList
      match v? with
      | none => pure none  -- ACL2 does not fold this head/guard instance
      | some v =>
        let foldedT : SExpr :=
          .cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)
        let p ← replayExecGround cfg cur v
        let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr v]
        pure (some (← mkAppM ``fuel_eq_of_conv
          #[p, pQ, ← mkEqRefl (reflectSExpr v)], foldedT))
    else if fs.name == "NOT" then
      match curArgs.toList with
      | [.cons (.atom (.symbol q)) (.cons cc .nil)] =>
        if q.name == "QUOTE" then
          let foldedV : SExpr := if cc == SExpr.nil then SExpr.t else SExpr.nil
          let foldedT : SExpr :=
            .cons (.atom (.symbol { name := "QUOTE" })) (.cons foldedV .nil)
          let pNot ← replayExecGround cfg cur foldedV
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr foldedV]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pNot, pQ, ← mkEqRefl (reflectSExpr foldedV)], foldedT))
        else pure none
      | _ => pure none
    else if fs.name == "EQUAL" then
      let isEqualApp : SExpr → Bool := fun t =>
        match t with
        | .cons (.atom (.symbol es)) (.cons _ (.cons _ .nil)) => es.name == "EQUAL"
        | _ => false
      match curArgs.toList with
      | [x, y] =>
        if x == y then
          let hX ← proveConv cfg e ctx x
          let hNoEqual ← proveNoShadow cfg { name := "EQUAL" }
          let pEq ← mkAppM ``re_equal_self #[w, e, reflectSExpr x, hX, hNoEqual]
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.t]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pEq, pQ, ← mkEqRefl (mkConst ``SExpr.t)], quoteT))
        else if y == quoteT && isEqualApp x then
          -- (equal (equal a b) 't) = (equal a b) — rewrite.lisp:3791
          let pl ← ctxValProof cfg ctx cur
          let pr ← ctxValProof cfg ctx x
          let .cons _ (.cons a (.cons b .nil)) := x
            | throwError "collapseEval: internal — isEqualApp shape"
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pl, pr, ← mkAppM ``logic_equal_equal_t_r #[va, vb]], x))
        else if x == quoteT && isEqualApp y then
          -- (equal 't (equal a b)) = (equal a b) — rewrite.lisp:3785
          let pl ← ctxValProof cfg ctx cur
          let pr ← ctxValProof cfg ctx y
          let .cons _ (.cons a (.cons b .nil)) := y
            | throwError "collapseEval: internal — isEqualApp shape"
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pl, pr, ← mkAppM ``logic_equal_equal_t_l #[va, vb]], y))
        else pure none
      | _ => pure none
    else pure none
  match fold? with
  | none => return (acc, cur)
  | some (stepPf, next) =>
    let acc' ← chainAfter acc stepPf
    return (some acc', next)



end ACL2.Replay.Driver
