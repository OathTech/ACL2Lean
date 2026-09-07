import ACL2Lean.Replay.Driver.Waterfall.ClauseEdits

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private def constructionField (fs : List (String × SExpr)) (k : String) : MetaM SExpr :=
  tsQueryRead (TsQueryCapture.required fs k)

/-- Match the nested original-call fold against the same flat event in the
reconstructed continuation. Its position in this expression is structural;
the rewriter path is still cross-checked as source provenance. -/
private def consumeConstructionFold (raw : SExpr) (items : List ClauseItem) :
    MetaM (ProofNode × List ClauseItem) := do
  let .cons (.atom (.keyword "REWRITE-STEP")) body := raw
    | throwError "clause construction: malformed local fold"
  let fs ← tsQueryRead (TsQueryCapture.fields body ["PATH", "RUNE", "ORIGIN", "EQUIV", "LHS", "RHS"])
  let some r := ProofLog.parseRune? (← constructionField fs "RUNE")
    | throwError "clause construction: malformed fold rune"
  let .atom (.symbol origin) ← constructionField fs "ORIGIN"
    | throwError "clause construction: malformed fold origin"
  let path ← (← tsQueryRead (TsQueryCapture.asList (← constructionField fs "PATH"))).mapM
    (fun p => tsQueryRead (ProofLog.parsePathFrame p))
  let .step n :: rest := items | throwError "clause construction: missing recorded fold step"
  let .node actual lhs rhs children prov := n
  unless actual == r && children.isEmpty && prov.origin == origin.name.toLower &&
      prov.equiv == "equal" && prov.path == path &&
      (← constructionField fs "EQUIV") == .atom (.symbol { name := "EQUAL" }) &&
      lhs == (← constructionField fs "LHS") && rhs == (← constructionField fs "RHS") do
    throwError "clause construction: local fold differs from continuation record"
  unless ["scons-term/exec", "scons-term/if-simp", "scons-term/equal-self"].contains prov.origin do
    throwFrontier m!"clause construction: unsupported local folding mechanism {prov.origin}"
  return (n, rest)

/-- Certify one executed substitution construction. Argument congruence is
positional, so repeated terms are processed separately. A fold must start
at the actual assembled term and reach the recorded output. -/
private partial def replayConstructionTerm (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lhs rhs : SExpr) (substitution : Expr) (raw : SExpr) (items : List ClauseItem) :
    MetaM (SExpr × SExpr × Expr × List ClauseItem) := do
  let fs ← tsQueryRead (TsQueryCapture.fields raw ["INPUT", "OUTPUT", "ROUTE", "ASSEMBLED", "FOLDS", "CHILDREN"])
  let input ← constructionField fs "INPUT"
  let output ← constructionField fs "OUTPUT"
  let route ← constructionField fs "ROUTE"
  let assembled ← constructionField fs "ASSEMBLED"
  let folds ← tsQueryRead (TsQueryCapture.asList (← constructionField fs "FOLDS"))
  let children ← tsQueryRead (TsQueryCapture.asList (← constructionField fs "CHILDREN"))
  if route == .atom (.keyword "REPLACE") || route == .atom (.keyword "UNCHANGED") then
    unless children.isEmpty && folds.isEmpty && assembled == .nil do
      throwError "clause construction: terminal construction has recursive work"
    if route == .atom (.keyword "REPLACE") then
      unless input == lhs && output == rhs do throwError "clause construction: replacement endpoint mismatch"
      return (input, output, substitution, items)
    let isOpaque := match input with
      | .atom (.symbol _) => true
      | _ => (asApp input).any (fun (f, _) => f.name == "QUOTE" || f.name == "HIDE")
    unless isOpaque && input == output do throwError "clause construction: unsupported unchanged terminal"
    return (input, output, ← mkIdFuelEq cfg input, items)
  unless route == .atom (.keyword "APPLICATION") do
    throwFrontier m!"clause construction: unsupported expression route {repr route}"
  let some (fn, args) := asApp input | throwError "clause construction: application has no head"
  unless fn.name != "QUOTE" && fn.name != "HIDE" && children.length == args.length do
    throwError "clause construction: application children/head mismatch"
  let mut arguments := args
  let mut chain ← mkIdFuelEq cfg input
  let mut remaining := items
  for (child, index) in children.zipIdx do
    let (a, b, p, rest) ← replayConstructionTerm cfg ctx lhs rhs substitution child remaining
    unless arguments[index]? == some a do throwError "clause construction: child input/order mismatch"
    let step : PathStep := {
      fn := fn, arity := args.length, argIdx := index,
      siblings := arguments.zipIdx.filterMap (fun (t, i) => if i == index then none else some t) }
    chain ← chainWith chain (some (← applyStep cfg.worldExpr cfg.envExpr step a b p))
    arguments := arguments.set index b
    remaining := rest
  let mut current := SExpr.ofList (.atom (.symbol fn) :: arguments)
  unless current == assembled do throwError "clause construction: assembled term differs from child outputs"
  for fold in folds do
    let (n, rest) ← consumeConstructionFold fold remaining
    let (a, b) := nodeLhsRhs n
    unless a == current do throwError "clause construction: fold input differs from the assembled term"
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx a
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx b
    let (p, relation) ← replayNode cfg ctx n
    unless relation.isNone do throwError "clause construction: local fold is not equality"
    chain ← chainWith chain (some p)
    current := b
    remaining := rest
  unless current == output do throwError "clause construction: result differs from the executed fold endpoint"
  return (input, output, chain, remaining)

private structure LiteralConstruction where
  position : Nat
  input : SExpr
  action : String
  expressions : List SExpr
  cleanup : SExpr
  output : List SExpr

private def literalConstruction (raw : SExpr) : MetaM LiteralConstruction := do
  let fs ← tsQueryRead (TsQueryCapture.fields raw ["POSITION", "INPUT", "ACTION", "EXPRESSIONS", "CLEANUP", "OUTPUT-CLAUSE"])
  let position ← tsQueryRead (TsQueryCapture.asInt (← constructionField fs "POSITION"))
  unless position ≥ 0 do throwError "clause construction: negative literal position"
  let .atom (.keyword action) ← constructionField fs "ACTION"
    | throwError "clause construction: malformed literal action"
  return {
    position := position.toNat,
    input := ← constructionField fs "INPUT",
    action := action,
    expressions := ← tsQueryRead (TsQueryCapture.asList (← constructionField fs "EXPRESSIONS")),
    cleanup := ← constructionField fs "CLEANUP",
    output := ← tsQueryRead (TsQueryCapture.asList (← constructionField fs "OUTPUT-CLAUSE")) }

private def negatedLiteral? (lit : SExpr) : Option SExpr :=
  match asApp lit with
  | some (fn, [argument]) => if fn.name == "NOT" then some argument else none
  | _ => none

private def commutedLiteral? (lit : SExpr) : Option SExpr :=
  match asApp lit with
  | some (fn, [a, b]) =>
    if fn.name == "EQUAL" || fn.name == "IFF" then
      some (SExpr.ofList [.atom (.symbol fn), b, a])
    else none
  | _ => none

mutual
/-- The membership predicates used by ADD-LITERAL-AND-PT, from
MEMBER-TERM/MEMBER-COMPLEMENT-TERM. These are deliberately distinct from
clausification's DUMB-NEGATE-LIT: that operation also simplifies EQUAL-NIL,
which this source scan does not do. -/
private partial def constructionMember (lit : SExpr) (tail : List SExpr) : Bool :=
  if let some commuted := commutedLiteral? lit then
    tail.contains lit || tail.contains commuted
  else if let some argument := negatedLiteral? lit then
    constructionComplement argument tail
  else tail.contains lit

private partial def constructionComplement (lit : SExpr) (tail : List SExpr) : Bool :=
  if let some commuted := commutedLiteral? lit then
    tail.any fun other => (negatedLiteral? other).any (fun a => a == lit || a == commuted)
  else
    ((negatedLiteral? lit).any (constructionMember · tail)) ||
      tail.any (fun other => negatedLiteral? other == some lit)
end

/-- Validate the recorded tail reconstruction in source return order.
All local folds have already been consumed in argument execution order;
duplicate events occur while the recursive clause calls return. -/
private def checkConstructionCleanup (records : List LiteralConstruction)
    (literals : List SExpr) (items : List ClauseItem) : MetaM (List SExpr × List ClauseItem) := do
  let mut tail : List SExpr := []
  let mut remaining := items
  for (r, lit) in (records.zip literals).reverse do
    if r.action == "DELETE" then
      unless r.cleanup == .nil && r.output == tail do throwError "clause construction: deletion changes its tail"
      continue
    let fs ← tsQueryRead (TsQueryCapture.fields r.cleanup ["LITERAL", "TAIL", "RESULT"])
    unless (← constructionField fs "LITERAL") == lit &&
        (← tsQueryRead (TsQueryCapture.asList (← constructionField fs "TAIL"))) == tail &&
        (← tsQueryRead (TsQueryCapture.asList (← constructionField fs "RESULT"))) == r.output do
      throwError "clause construction: cleanup literal/tail/result mismatch"
    let quoted := match asApp lit with
      | some (q, [v]) => if q.name == "QUOTE" then some v else none
      | _ => none
    let next ← if let some value := quoted then
        pure (if value == .nil then tail else [quoteT])
      else if tail == [quoteT] || constructionComplement lit tail then pure [quoteT]
      else if constructionMember lit tail then do
        let .dedupDrop dropped :: rest := remaining
          | throwError "clause construction: duplicate has no recorded cleanup"
        unless dropped == lit do throwError "clause construction: duplicate cleanup order/literal mismatch"
        remaining := rest
        pure tail
      else pure (lit :: tail)
    unless next == r.output do throwFrontier m!"clause construction: unsupported cleanup result for {repr lit}"
    tail := next
  return (tail, remaining)

/-- The complete recorded EQUAL edit behind the shared clause implication.
The selected equality is local to the parent contradiction. Recursive
construction supplies each literal's conversion; cleanup supplies the exact
result and consumes every original fold and duplicate event. -/
def certifyConstructedClauseSubstitution (cfg : ReplayConfig) (ctx : ReplayCtx)
    (clause : List SExpr) (n : ProofNode) (items : List ClauseItem) :
    MetaM (List SExpr × List ClauseItem × Expr) := do
  let .node rune lhs rhs children prov := n
  unless rune.ty == "branch-substitution" && children.isEmpty &&
      prov.equivTerm == some (.atom (.symbol { name := "EQUAL" })) do
    throwFrontier m!"clause construction: unsupported substitution relation or children"
  let some raw := prov.branchSubstitutionBasis | throwError "clause construction: absent selection"
  let selection ← selectedClauseSubstitution raw
  unless selection.input == clause do throwError "clause construction: selected input differs from the current clause"
  let some rawRecords := selection.constructions | throwError "clause construction: absent construction"
  let some after := selection.resultClause | throwError "clause construction: absent result"
  let records ← (← tsQueryRead (TsQueryCapture.asList rawRecords)).mapM literalConstruction
  unless records.map (·.position) == List.range clause.length && records.map (·.input) == clause do
    throwError "clause construction: literal inventory/order mismatch"
  let mut ctx := ctx
  for t in lhs :: rhs :: clause ++ after do ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let editCtx := ctx
  let inputType ← mkAppM ``EvTrue #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm clause)]
  let resultType ← mkAppM ``EvTrue #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm after)]
  let (proof, remaining) ← withLocalDeclD `hEdited resultType fun hEdited => do
    let (contra, remaining) ← withLocalDeclD `hInputFalse (← mkAppM ``Not #[inputType]) fun hf => do
      let (_, hLiteral) ← clauseLiteralFalsity cfg editCtx clause hf selection.position
      let hEq ← selectedClauseEquation cfg editCtx selection lhs rhs hLiteral
      let substitution ← mkAppM ``fuel_eq_of_conv
        #[← ctxValProof cfg editCtx lhs, ← ctxValProof cfg editCtx rhs, hEq]
      let mut folded := clause
      let mut remaining := items
      let mut chain : Option Expr := none
      for r in records do
        let (output, p) ← if r.position == selection.position then do
            unless r.action == (if selection.deleteLiteral then "DELETE" else "RETAIN") && r.expressions.isEmpty do
              throwError "clause construction: selected action differs from its deletion decision"
            pure (r.input, ← mkIdFuelEq cfg r.input)
          else if r.action == "COPY" then do
            unless r.expressions.isEmpty && replaceTermOcc lhs rhs r.input == r.input do
              throwError "clause construction: copy contains substitution work"
            pure (r.input, ← mkIdFuelEq cfg r.input)
          else if r.action == "SUBSTITUTE" then do
            let [expr] := r.expressions | throwError "clause construction: expected one executed expression root"
            let (input, output, p, rest) ← replayConstructionTerm cfg editCtx lhs rhs substitution expr remaining
            unless input == r.input do throwError "clause construction: expression input differs from its literal"
            remaining := rest
            pure (output, p)
          else throwFrontier m!"clause construction: unsupported literal action {r.action}"
        let next := folded.set r.position output
        let lifted ← diffCollapse cfg.worldExpr cfg.envExpr r.input output p
          (disjoinTerm folded) (disjoinTerm next)
        chain ← chainOptWith chain lifted
        folded := next
      let (checkedAfter, rest) ← checkConstructionCleanup records folded remaining
      unless checkedAfter == after do throwError "clause construction: final result differs from the returned clause"
      let ctx ← pinTermOpaques cfg cfg.envExpr editCtx (disjoinTerm folded)
      let hFolded ← if after == [quoteT] then do
          let p ← match ← groundConstClose cfg ctx folded [] [] with
            | some p => pure p
            | none => tautClauseClose cfg ctx folded "recorded clause construction"
          withLetDecl `hRecordedContinuation resultType hEdited fun h =>
            mkLetFVars #[h] p (usedLetOnly := false)
        else liftClauseSubset cfg ctx folded after hEdited
      let p ← evtrueWith chain hFolded
      return (← mkLambdaFVars #[hf] (mkApp hf p), rest)
    return (← mkLambdaFVars #[hEdited] (← mkAppM ``Classical.byContradiction #[contra]), remaining)
  let expected ← mkAppM ``ClauseEditSound
    #[cfg.worldExpr, cfg.envExpr, ← mkListLit (mkConst ``SExpr) (clause.map reflectSExpr),
      ← mkListLit (mkConst ``SExpr) (after.map reflectSExpr)]
  return (after, remaining, ← mkExpectedTypeHint proof expected)

/-- CRUNCH-CLAUSE-SEGMENTS2 removes the marker separating unrewritten and
rewritten literals. At a finished scan its prefix must be empty; a remaining
prefix needs its own recorded literal scan, not a guessed child permutation. -/
private def finishedCrunchedClause (clause : List SExpr) : MetaM (List SExpr) := do
  let marker := SExpr.ofList [.atom (.symbol {name := "CAR"}),
    .atom (.keyword "CRUNCH-CLAUSE-SEGMENTS-MARKER")]
  let first :: rest := clause | throwError "clause construction: absent crunch marker"
  unless first == marker && !rest.contains marker do
    throwFrontier m!"clause construction: unfinished or malformed crunch segments"
  return rest

/-- Shared continuation for complete construction records. Reset facts
indexed by the preceding clause; each edit proves its selected premise
locally and the child reconstructs its own clause facts. -/
partial def replayConstructedClauseEdits (rec : ClauseRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (idStr : String) (clause : List SExpr)
    (items : List ClauseItem) (children : List ClauseNode) (crunched : Bool := false) : MetaM Expr := do
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm clause)
  match items with
  | [] =>
    let next ← if crunched then finishedCrunchedClause clause else pure clause
    let [child] := children.filter (·.inputClause == next)
      | throwError "clause construction: no unique exact continuation child at {idStr}"
    let p ← rec.clause cfg { ctx with litFacts := [], dedupDrops := [], segFacts := [], contextSubsts := [] } child
    if next == clause then return p
    liftClauseSubset cfg ctx clause next p
  | [.literal lp] =>
    unless clause == [quoteT] && lp.literal == quoteT do
      throwError "clause construction: final scan differs from the resulting true clause"
    rec.clauseSpine cfg ctx idStr [(lp.index, lp.literal)] items [] []
  | .step n :: rest =>
    let .node rune lhs rhs childNodes _ := n
    if rune.ty == "context-subst" then
      unless childNodes.isEmpty do throwError "clause construction: context alias has children"
      -- This is the existing selector channel, not an assumed equation.
      -- A later query must still justify any fact obtained through it.
      return ← replayConstructedClauseEdits rec cfg
        { ctx with contextSubsts := ctx.contextSubsts ++ [(lhs, rhs)] }
        idStr clause rest children crunched
    let (after, remaining, edit) ← certifyConstructedClauseSubstitution cfg ctx clause n rest
    let p ← replayConstructedClauseEdits rec cfg
      { ctx with litFacts := [], dedupDrops := [], segFacts := [], contextSubsts := [] }
      idStr after remaining children crunched
    return mkApp edit p
  | _ => throwFrontier m!"clause construction: unsupported continuation at {idStr}"

/-- Crunching may prepend already false context literals and a structural
marker to the residual passed by the spine. Check every extra literal's
falsity; the recorded full clause is never silently identified with the
smaller residual. -/
def constructedResidualToCurrent (cfg : ReplayConfig) (ctx : ReplayCtx)
    (full current : List SExpr) (pFull : Expr) : MetaM Expr := do
  if full == current then return pFull
  let mut ctx := ctx
  for t in full ++ current do ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  withClauseFalsity cfg ctx current fun ctxF =>
    vacuousResidualClose cfg ctxF full pFull (disjoinTerm current) fun literal => do
      if let some hf ← typeSetWalk cfg ctxF (.isNil literal) then return hf
      let value ← ctxValExpr cfg ctxF literal
      unless ← isDefEq value (mkConst ``SExpr.nil) do
        throwError "clause construction: extra input literal lacks checked falsity: {repr literal}"
      mkExpectedTypeHint (← mkEqRefl value) (← mkEq value (mkConst ``SExpr.nil))

end ACL2.Replay.Driver
