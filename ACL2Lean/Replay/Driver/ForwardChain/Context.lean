import ACL2Lean.Replay.Driver.ForwardChain.Basis
import ACL2Lean.Replay.Driver.TypeSetQuery
import ACL2Lean.Replay.Driver.StoredImplication

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private def readField (fs : List (String × SExpr)) (k : String) : MetaM SExpr :=
  tsQueryRead (TsQueryCapture.required fs k)

/-- Trigger/match-free describe activation, already checked on the source.
The implication's content is exactly its antecedents and conclusion. -/
def sameFcImplication (a b : FcRuleSpec) : Bool :=
  a.name == b.name && a.hyps == b.hyps && a.concls == b.concls

private partial def contextRecordsInNode : ProofNode → List SExpr
  | .node _ _ _ children prov => prov.clauseContextBasis.toList ++ children.flatMap contextRecordsInNode
private partial def contextRecordsInItem : ClauseItem → List SExpr
  | .step n => contextRecordsInNode n
  | .literal lp => lp.nodes.flatMap contextRecordsInNode
  | .branch _ its => its.flatMap contextRecordsInItem
  | _ => []
private partial def contextRecordsInClause (cn : ClauseNode) : List SExpr :=
  cn.steps.flatMap (fun s => s.items.flatMap contextRecordsInItem) ++
    cn.children.flatMap contextRecordsInClause
private partial def sourceSpecs (raw : SExpr) : MetaM (List FcRuleSpec) := do
  let s ← tsQueryRead (FcCapture.source raw)
  let supports ← s.supports.flatMapM sourceSpecs
  pure (supports ++ [s.rule])

/-- Offers come only from sources actually selected in this tree. They are
content-deduplicated, and a theorem is never offered to its own proof. -/
def recordedFcSpecs (cp : ClauseProof) : MetaM (List FcRuleSpec) := do
  let mut specs := []
  for raw in cp.root.toList.flatMap contextRecordsInClause do
    let context ← tsQueryRead (FcCapture.context raw)
    for selection in context.selected do
      let fs ← tsQueryRead (TsQueryCapture.fields selection ["LITERAL", "SOURCE", "TTREE"])
      for spec in ← sourceSpecs (← readField fs "SOURCE") do
        if spec.name != cp.name && !specs.any (sameFcImplication spec) then
          specs := specs ++ [spec]
  pure specs

/-- The source is the actual selected derivation, including its stored
implication and each recorded successful relief. Ordinary book implications
remain explicit hypotheses until their source clause trees replay. -/
partial def replayFcSource (cfg : ReplayConfig) (ctx : ReplayCtx) (raw : SExpr) : MetaM Expr := do
  let s ← tsQueryRead (FcCapture.source raw)
  let inst := ACL2.Replay.substTerm (s.subst.map (·.1)) (s.subst.map (·.2))
  let [concl] := s.rule.concls | throwFrontier m!"FC source: multiple stored conclusions"
  unless inst concl == s.concl && inst s.rule.trigger == s.trigger do
    throwFrontier m!"FC source: trigger/conclusion differs from the recorded substitution"
  let mut ctx := ctx
  for support in s.supports do
    let parent ← tsQueryRead (FcCapture.source support)
    unless parent.round < s.round do throwError "FC source: support is not from an earlier round"
    ctx ← pinTermOpaques cfg cfg.envExpr ctx parent.concl
    let p ← replayFcSource cfg ctx support
    let hn ← mkAppM ``ne_nil_of_evtrue_conv #[p, ← ctxValProof cfg ctx parent.concl]
    ctx := { ctx with branchFacts := ctx.branchFacts ++ [(parent.concl, ← ctxValExpr cfg ctx parent.concl, true, hn)] }
  for t in s.rule.hyps.map inst ++ [s.concl] do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let mut remaining := s.rule.hyps
  let mut proofs : Array Expr := #[]
  let mut initialSeen := false
  for rawHyp in s.reliefs do
    let fs ← tsQueryRead (TsQueryCapture.fields rawHyp ["ROUTE", "HYP", "INSTANCE", "SUBST",
      "REMAINING-HYPS", "RESULT", "TTREE", "TYPE-ALIST", "QUERIES"])
    let _ ← tsQueryRead (TsQueryCapture.asList (← readField fs "TTREE"))
    let ta ← tsQueryRead (TsQueryCapture.typeAlist (← readField fs "TYPE-ALIST"))
    let sigma ← tsQueryRead (FcCapture.substitution (← readField fs "SUBST"))
    unless sigma.all (fun (v, t) => s.subst.lookup v == some t) do
      throwError "FC relief: substitution differs from its final source"
    let next ← tsQueryRead (TsQueryCapture.asList (← readField fs "REMAINING-HYPS"))
    let route ← readField fs "ROUTE"
    -- Activations begin with the recorded sentinel query 'T. It consumes
    -- no rule hypothesis; its remaining-hypothesis list must be unchanged.
    if !initialSeen then
      unless route == .atom (.keyword "TYPE-SET") && fs.lookup "HYP" == none &&
          (← readField fs "INSTANCE") == quoteT && next == remaining &&
          (← tsQueryRead (TsQueryCapture.asInt (← readField fs "RESULT"))) == 256 do
        throwFrontier m!"FC relief: unsupported activation entry"
      let [query] ← tsQueryRead (TsQueryCapture.asList (← readField fs "QUERIES"))
        | throwError "FC relief: sentinel query count"
      checkTsQueryLookups ta query
      let _ ← replayTsQueryTrue cfg ctx quoteT query
      initialSeen := true
    else
      let h :: tail := remaining | throwError "FC relief: extra hypothesis record"
      unless next == tail do throwError "FC relief: recorded hypothesis order differs"
      let target := inst h
      unless ACL2.Replay.substTerm (sigma.map (·.1)) (sigma.map (·.2)) h == target do
        throwError "FC relief: hypothesis uses a binding absent from this recorded step"
      let p ← if route == .atom (.keyword "FREE-VARS") then do
          unless (← readField fs "HYP") == h do throwError "FC relief: free hypothesis mismatch"
          let some (notS, [atom]) := asApp target
            | throwFrontier m!"FC relief: unsupported free-variable lookup shape"
          unless notS.name == "NOT" do
            throwFrontier m!"FC relief: unsupported positive free-variable lookup"
          let some (_, mask, _) := ta.find? (fun (t, _, _) => t == atom)
            | throwError "FC relief: matched atom absent from recorded type-alist"
          unless mask == 128 do throwFrontier m!"FC relief: unsupported matched mask {mask}"
          let some hn ← typeSetWalk cfg ctx (.isTruthy target)
            | throwFrontier m!"FC relief: missing checked matched fact {repr target}"
          mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx target, hn]
        else if route == .atom (.keyword "TYPE-SET") then do
          unless (← readField fs "INSTANCE") == target &&
              (← tsQueryRead (TsQueryCapture.asInt (← readField fs "RESULT"))) == 256 do
            throwFrontier m!"FC relief: folded instance or unsupported result"
          if let some rawH := fs.lookup "HYP" then
            unless rawH == h do throwError "FC relief: source hypothesis mismatch"
          let [query] ← tsQueryRead (TsQueryCapture.asList (← readField fs "QUERIES"))
            | throwError "FC relief: root query count"
          checkTsQueryLookups ta query
          replayTsQueryTrue cfg ctx target query
        else throwFrontier m!"FC relief: unsupported route {repr route}"
      proofs := proofs.push p
      remaining := tail
  unless initialSeen && remaining.isEmpty do throwError "FC source: missing hypothesis reliefs"
  let some (_, ruleProof) := ctx.fcHyps.find? (fun (r, _) => sameFcImplication r s.rule)
    | throwFrontier m!"FC source: no offered replayed implication for {s.rune}"
  let sb ← mkSubstNBridge cfg ctx (s.subst.map (·.1)) (s.subst.map (·.2)) s!"FC {s.rune.name}"
  let p ← instantiateStoredImplication cfg sb s.rule.hyps concl inst ruleProof
  pure (mkAppN p proofs)

/-- Consume the actual selected suffix at a context-contradiction leaf.
The first supported shape excludes the sole remaining current literal;
every disjunct of the emitted obligation has an independently checked
falsity proof, so the actual DP proof closes that residual by contradiction. -/
def replayFcContext (cfg : ReplayConfig) (ctx : ReplayCtx) (accClause allL : List SExpr)
    (nodeLhs raw : SExpr) (discharge : ReplayCtx → SExpr → MetaM Expr) : MetaM Expr := do
  let basis ← tsQueryRead (FcCapture.context raw)
  unless basis.accumulator == accClause && basis.tail == allL do
    throwError "FC context: recorded accumulator/tail differs from the branch walk"
  unless basis.selected.length == basis.literals.length do
    throwError "FC context: selected source/literal count mismatch"
  let [current] := allL | throwFrontier m!"FC context: nonempty residual tail is not yet supported"
  let expected := accClause ++ basis.literals
  unless !basis.literals.isEmpty && disjoinTerm expected == nodeLhs do
    throwError "FC context: selected suffix does not reconstruct the emitted obligation"
  let mut ctx := ctx
  for t in current :: expected do ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let mut falseSuffix : List (SExpr × Expr) := []
  for (rawSelection, literal) in basis.selected.zip basis.literals do
    let fs ← tsQueryRead (TsQueryCapture.fields rawSelection ["LITERAL", "SOURCE", "TTREE"])
    let _ ← tsQueryRead (TsQueryCapture.asList (← readField fs "TTREE"))
    unless (← readField fs "LITERAL") == literal do throwError "FC context: selected literal mismatch"
    let rawSource ← readField fs "SOURCE"
    let source ← tsQueryRead (FcCapture.source rawSource)
    ctx ← pinTermOpaques cfg cfg.envExpr ctx source.concl
    let p ← replayFcSource cfg ctx rawSource
    let hn ← mkAppM ``ne_nil_of_evtrue_conv #[p, ← ctxValProof cfg ctx source.concl]
    let negated := SExpr.ofList [.atom (.symbol { name := "NOT" }), source.concl]
    let hf ← if source.concl == SExpr.ofList [.atom (.symbol { name := "NOT" }), literal] then
        mkAppM ``nil_of_logic_not_ne_nil #[hn]
      else if literal == negated then mkAppM ``not_nil_of_truthy #[hn]
      else throwError "FC context: literal is not the selected conclusion's negation"
    let ty ← mkEq (← ctxValExpr cfg ctx literal) (mkConst ``SExpr.nil)
    falseSuffix := falseSuffix ++ [(literal, ← mkExpectedTypeHint hf ty)]
  let p ← discharge ctx nodeLhs
  let falseFact (t : SExpr) : MetaM Expr := do
    let ty ← mkEq (← ctxValExpr cfg ctx t) (mkConst ``SExpr.nil)
    if let some p := falseSuffix.lookup t then return ← mkExpectedTypeHint p ty
    let some p ← ctx.litFactByTermChecked? t ty
      | throwError "FC context: missing checked branch falsity for {repr t}"
    pure p
  vacuousResidualClose cfg ctx expected p current falseFact

end ACL2.Replay.Driver
