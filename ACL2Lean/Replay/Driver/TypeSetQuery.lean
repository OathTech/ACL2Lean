import ACL2Lean.Replay.Driver.TypeSetQuery.Basis
import ACL2Lean.Replay.Driver.TypeSetQuery.Conditional
import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk
import ACL2Lean.Replay.Lemmas.TsQueryCells
import ACL2Lean.Replay.Lemmas.TsNegation

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private def primitiveQueryEntry (tag : String) (entry : SExpr) : MetaM Unit := do
  if tag == "PT" then
    let .atom (.number (.int n)) := entry | throwError "type-set query: unsupported parent tree"
    unless n ≥ 0 do throwError "type-set query: negative parent index"
  else if tag == "LEMMA" then
    let some r := ProofLog.parseRune? entry | throwError "type-set query: malformed ttree rune"
    unless r.ty == "fake-rune-for-type-set" || r.ty == "fake-rune-for-anonymous-enabled-rule" do
      throwFrontier m!"type-set query: ordinary evidence needs replay: {r}"
  else throwFrontier m!"type-set query: unsupported evidence tag {tag}"

/-- Ordinary rule or FC evidence requires its own proof channel. -/
def primitiveQueryTtree (t : SExpr) : MetaM Unit := do
  for (tag, entry) in ← tsQueryRead (queryTtreeEntries t) do primitiveQueryEntry tag entry

/-- TYPE-SET's ttree is an accumulator: the caller may have already rewritten
the queried term. Preserve incoming citations as provenance, and check only
new evidence as this computation's own inference. Child outputs may be
discarded by a primitive's unconditional range; every child still replays. -/
private def primitiveQueryEvidence (q : TsQueryCapture.Query) : MetaM Unit := do
  let incoming ← tsQueryRead (queryTtreeEntries q.inputTtree)
  let actual ← tsQueryRead (queryTtreeEntries q.ttree)
  unless incoming.all actual.contains do
    throwError "type-set query: computation lost incoming evidence"
  let childEvidence ← q.children.flatMapM fun raw => do
    let child ← tsQueryRead (TsQueryCapture.query raw)
    tsQueryRead (queryTtreeEntries child.ttree)
  let ordinary ← if q.recognizer == .nil then pure [] else do
    let some basis ← tsQueryRead (ACL2.parseHypRecognizerBasis ProofLog.parseRune? (some q.recognizer))
      | throwError "type-set query: malformed recognizer evidence"
    pure (if basis.rune.ty == "compound-recognizer" then [basis.rune] else [])
  for (tag, entry) in actual do
    unless incoming.contains (tag, entry) || childEvidence.contains (tag, entry) do
      unless tag == "LEMMA" && (ProofLog.parseRune? entry).any ordinary.contains do
        primitiveQueryEntry tag entry

/-- Apply a primitive recognizer's recorded partition to checked argument
membership. Both a recursive query and an explicit rewrite use this boundary.
Ordinary compound recognizers use their replayed source theorem instead. -/
private def primitiveRecognizerQueryVerdict (term verdict : SExpr)
    (argTs trueTs falseTs : Int) (strong : Bool) (argument : Expr) : MetaM Expr := do
  let some (fn, [_]) := asApp term | throwError "recognizer query: unary application required"
  unless ["ACL2-NUMBERP", "INTEGERP", "RATIONALP", "COMPLEX-RATIONALP", "CONSP"].contains fn.name do
    throwFrontier m!"recognizer query: ordinary predicate requires its replayed source"
  let entries := if verdict == .t then tsRecogTrue else if verdict == .nil then tsRecogNil else []
  let some (_, mask, rule) := entries.find? (fun (name, _, _) => name == fn.name)
    | throwFrontier m!"recognizer query: unsupported primitive verdict"
  unless trueTs == mask && falseTs == -mask - 1 && strong do
    throwError "recognizer query: primitive partition differs from recorded tuple"
  let inclusion ← if verdict == .t then tsSubsumedProofM argTs mask else
    mkDecideProof (← mkEq (← mkAppM ``tsDisjointM #[toExpr argTs, toExpr mask]) (toExpr true))
  mkAppM rule #[inclusion, argument]

/-- Consume a recorded recursive type-set call. Children are checked in
their execution order; a mask alone never proves a fact. No hypothesis DP. -/
partial def replayTsQuery (cfg : ReplayConfig) (ctx : ReplayCtx) (raw : SExpr)
    (expectedDwp : SExpr := .nil) : MetaM Expr := do
  let q ← tsQueryRead (TsQueryCapture.query raw)
  let isQuoted := (asApp q.term).any (fun (fn, args) => fn.name == "QUOTE" && args.length == 1)
  let propagatesDwp := q.recognizer == .nil && q.route == .nil &&
    (asApp q.term).any (fun (fn, _) => fn.name != "IF" && fn.name != "NOT")
  unless q.dwp == expectedDwp do throwError "type-set query: double-whammy parent tuple mismatch"
  if q.dwp != .nil then let _ ← tsQueryRead (TsQueryCapture.recognizerDwp q.dwp)
  -- Incoming tags belong to earlier recorded work. A lookup may add only
  -- its selected entry's evidence; its ordinary recognizer is proved below.
  if q.route == .atom (.keyword "LOOKUP") then
    let [_, tt] ← tsQueryRead (TsQueryCapture.asList q.lookup)
      | throwError "type-set query: malformed lookup pair"
    let incoming ← tsQueryRead (queryTtreeEntries q.inputTtree)
    let selected ← tsQueryRead (queryTtreeEntries tt)
    let actual ← tsQueryRead (queryTtreeEntries q.ttree)
    unless actual.all (fun e => incoming.contains e || selected.contains e) &&
        (incoming ++ selected).all actual.contains do
      throwError "type-set query: lookup ttree is not the recorded evidence union"
  else
    primitiveQueryEvidence q
  if let .cons (.atom (.keyword "IF")) _ := q.route then
    return ← replayConditionalQuery (fun ctx raw dwp => replayTsQuery cfg ctx raw dwp) cfg ctx q
  let cs ← q.children.mapM fun raw => do
    let c ← tsQueryRead (TsQueryCapture.query raw)
    let mut childDwp := SExpr.nil
    -- TYPE-SET-PRIMITIVE passes DWP unchanged through these primitive arguments.
    -- A recognizer instead supplies its own recorded recognizer tuple.
    if propagatesDwp then
      childDwp := q.dwp
    else if c.dwp != .nil then
      let some (fn, [_]) := asApp q.term | throwError "type-set query: DWP child lacks a recognizer parent"
      let some basis ← tsQueryRead (ACL2.parseHypRecognizerBasis ProofLog.parseRune? (some q.recognizer))
        | throwError "type-set query: DWP child lacks its parent tuple"
      let tuple ← tsQueryRead (TsQueryCapture.recognizerDwp c.dwp)
      unless tuple.fn == fn && tuple.trueTs == basis.trueTs && tuple.falseTs == basis.falseTs &&
          tuple.strong == basis.strongp && tuple.rune == basis.rune do
        throwError "type-set query: child DWP differs from the selected recognizer tuple"
      childDwp := c.dwp
    pure (c, ← replayTsQuery cfg ctx raw childDwp)
  let finish (p : Expr) := do mkExpectedTypeHint p (← tsQueryType cfg ctx q)
  if q.route == .atom (.keyword "LOOKUP") then
    unless cs.isEmpty && q.recognizer == .nil do throwError "type-set query: lookup has computation children"
    if q.dwp != .nil then
      let tuple ← tsQueryRead (TsQueryCapture.recognizerDwp q.dwp)
      unless tsDisjointM q.result tuple.trueTs || tsDisjointM q.result tuple.falseTs do
        throwFrontier m!"type-set query: propagated DWP lookup does not decide its recognizer"
    let [m, tt] ← tsQueryRead (TsQueryCapture.asList q.lookup) | throwError "type-set query: malformed lookup pair"
    unless (← tsQueryRead (TsQueryCapture.asInt m)) == q.result do throwError "type-set query: lookup mask mismatch"
    let some [.atom (.keyword "LOOKUP"), .atom (.keyword "ENTRY"), entry,
        .atom (.keyword "RESULT"), result] := q.comparison.toList?
      | throwError "type-set query: lookup basis mismatch"
    unless result == m do throwError "type-set query: lookup result mismatch"
    match q.term with
    | .atom (.symbol _) =>
      unless entry == .nil do throwError "type-set query: variable lookup has a compound entry"
    | _ =>
      let [selected] ← tsQueryRead (TsQueryCapture.typeAlist (SExpr.ofList [entry]))
        | throwError "type-set query: malformed compound lookup entry"
      unless selected == (q.term, q.result, tt) do
        throwError "type-set query: compound lookup differs from returned pair"
    let ordinary ← tsQueryRead (queryTtreeCrRunes tt)
    let p ← if ordinary.isEmpty then do
        primitiveQueryTtree tt
        let some p ← inTsFromCtx cfg ctx [] [] q.term (← ctxValExpr cfg ctx q.term) q.result []
          | throwFrontier m!"type-set query: missing checked lookup fact for {repr q.term} : {q.result}"
        pure p
      else do
        for (tag, entry) in ← tsQueryRead (queryTtreeEntries tt) do
          unless tag == "LEMMA" && (ProofLog.parseRune? entry).any (ordinary.contains ·) do
            throwFrontier m!"type-set query: unsupported ordinary lookup evidence"
        queryRecognizerLookup cfg ctx q.term q.result ordinary
    return ← finish p
  unless q.lookup == SExpr.ofList [.nil, .nil] do
    throwFrontier m!"type-set query: nontrivial lookup/computation intersection"
  -- TYPE-SET-REC computes a quote's mask directly, preserving but not using DWP.
  if isQuoted then
    unless cs.isEmpty && q.route == .nil && q.comparison == .nil && q.recognizer == .nil do
      throwError "type-set query: quoted query has an unexpected route"
    return ← finish (← mkDecideProof (← withTransparency .all <| whnf (← tsQueryType cfg ctx q)))
  if let .atom (.symbol name) := q.term then
    unless name.name != "T" && cs.isEmpty && q.route == .nil && q.comparison == .nil &&
        q.recognizer == .nil && q.result == -1 do
      throwFrontier m!"type-set query: unsupported variable computation"
    return ← finish (← mkAppM ``inTs_unknown #[← ctxValExpr cfg ctx q.term])
  let some (fn, args) := asApp q.term | throwFrontier m!"type-set query: unsupported non-application"
  unless cs.map (fun (c, _) => c.term) == args do
    throwError "type-set query: executed children do not match the primitive arguments"
  if q.recognizer != .nil then
    let some basis ← tsQueryRead (ACL2.parseHypRecognizerBasis ProofLog.parseRune? (some q.recognizer))
      | throwError "type-set query: malformed recognizer tuple"
    if basis.rune.ty == "compound-recognizer" then
      let [(c, p)] := cs | throwError "type-set query: ordinary recognizer arity"
      unless q.route == .nil && q.comparison == .nil && q.result == 256 &&
          basis.argTs == c.result && basis.trueTs == 384 && basis.falseTs == -385 && basis.strongp do
        throwFrontier m!"type-set query: unsupported ordinary recognizer partition"
      unless (← tsQueryRead (queryTtreeCrRunes q.ttree)).contains basis.rune do
        throwError "type-set query: selected recognizer lacks its citation"
      let (predicate, heq, ctx) ← queryBooleanRecognizerEquivalence cfg ctx basis.rune c.term
      unless predicate == q.term do throwError "type-set query: source predicate differs from queried recognizer"
      let hb ← mkAppM ``inTs_weaken #[← tsSubsumedProofM c.result 384, p]
      let fact ← mkAppM ``recognizer_equivalence_of_inTs #[heq, hb]
      let result ← mkAppM ``inTs_of_eq_t #[fact]
      return ← mkExpectedTypeHint result (← tsQueryType cfg ctx q)
  if fn.name == "UNARY--" then
    let [(c, p)] := cs | throwError "type-set query: negation arity"
    unless q.route == .nil && q.comparison == .nil && q.recognizer == .nil do
      throwError "type-set query: negation has an unexpected route"
    unless tsNegTransfer c.result q.result do
      throwFrontier m!"type-set query: invalid negation transfer {c.result} → {q.result}"
    let transfer ← mkDecideProof (← mkEq
      (← mkAppM ``tsNegTransfer #[toExpr c.result, toExpr q.result]) (toExpr true))
    return ← finish (← mkAppM ``inTs_neg_transfer #[transfer, p])
  if ["REALPART", "IMAGPART", "NUMERATOR", "DENOMINATOR"].contains fn.name then
    let [(c, p)] := cs | throwError "type-set query: unary primitive arity"
    unless q.route == .nil && q.comparison == .nil && q.recognizer == .nil do
      throwError "type-set query: unary primitive has an unexpected route"
    let some (input, _, ruleName) := (tsUnaryOf fn.name).find? fun (input, out, _) =>
        out == q.result && (input.isNone || input == some c.result)
      | throwFrontier m!"type-set query: unsupported {fn.name} masks {c.result} → {q.result}"
    match input with
    | some _ => return ← finish (← mkAppM ruleName #[p])
    | none =>
      let result ← finish (← mkAppM ruleName #[← ctxValExpr cfg ctx c.term])
      -- The primitive's unconditional range does not need a child premise,
      -- but the actual executed query still carries that checked child.
      return ← retainQueryChild p result
  if fn.name == "UNARY-/" then
    let [(c, p)] := cs | throwError "type-set query: reciprocal arity"
    unless q.route == .nil && q.comparison == .nil && q.recognizer == .nil &&
        c.result == 7 && q.result == 11 do
      throwFrontier m!"type-set query: unsupported reciprocal masks {c.result} → {q.result}"
    return ← finish (← mkAppM ``inTs_reciprocal_nonneg_int #[p])
  if fn.name == "BINARY-+" || fn.name == "BINARY-*" || fn.name == "COMPLEX" then
    let [(l, pl), (r, pr)] := cs | throwError "type-set query: binary arithmetic arity"
    unless q.route == .nil && q.comparison == .nil && q.recognizer == .nil do
      throwError "type-set query: binary arithmetic has an unexpected route"
    if fn.name == "BINARY-*" && l.result == -128 && q.result == 1 then
      let result ← finish (← mkAppM ``inTs_times_nonnumber_left
        #[← ctxValExpr cfg ctx r.term, pl])
      -- Completion needs only the nonnumber premise, but retain the other
      -- executed operand query as a checked child of this proof.
      return ← retainQueryChild pr result
    if fn.name == "BINARY-*" && r.result == 1 && q.result == 1 then
      let result ← finish (← mkAppM ``inTs_times_singleton_zero_right
        #[← ctxValExpr cfg ctx l.term, pr])
      return ← retainQueryChild pl result
    let some (lm, rm, _, ruleName) := (tsBinaryOf fn.name).find? fun (lm, rm, out, _) =>
        tsSubsumedM l.result lm && tsSubsumedM r.result rm && out == q.result
      | throwFrontier m!"type-set query: unsupported {fn.name} masks {l.result}/{r.result} → {q.result}"
    let hl ← mkAppM ``inTs_weaken #[← tsSubsumedProofM l.result lm, pl]
    let hr ← mkAppM ``inTs_weaken #[← tsSubsumedProofM r.result rm, pr]
    return ← finish (← mkAppM ruleName #[hl, hr])
  if fn.name == "<" then
    let [(l, pl), (r, pr)] := cs | throwError "type-set query: comparison arity"
    -- The unconditional range return has no successful table/bound record.
    -- TYPE-SET-< discards the argument ttrees here, but their calls occurred.
    if q.route == .nil && q.recognizer == .nil && q.comparison == .nil && q.result == 384 then
      let result ← finish (← mkAppM ``inTs_of_boolean_range #[← mkAppM ``logic_lt_range
        #[← ctxValExpr cfg ctx l.term, ← ctxValExpr cfg ctx r.term]])
      return ← retainQueryChild pl (← retainQueryChild pr result)
    if let some [.atom (.keyword "CONSTANT-BOUND"), .atom (.keyword "RESULT"), result,
        .atom (.keyword "ENTRY"), entry, .atom (.keyword "DERIVATION"), derivation] := q.comparison.toList? then
      unless q.route == .nil && q.recognizer == .nil && q.result == 128 &&
          (← tsQueryRead (TsQueryCapture.asInt result)) == q.result do
        throwFrontier m!"type-set query: unsupported constant-bound result"
      primitiveQueryTtree derivation
      let [(term, mask, tt)] ← tsQueryRead (TsQueryCapture.typeAlist (SExpr.ofList [entry]))
        | throwError "type-set query: malformed bound entry"
      let some (boundFn, [a, b]) := asApp term | throwError "type-set query: non-comparison bound"
      let rationalQuote (term : SExpr) := (asApp term).any fun (fn, args) =>
        fn.name == "QUOTE" && args.length == 1 && args.any (fun v => Logic.rationalp v == .t)
      unless boundFn.name == "<" && a == r.term && b == l.term &&
          (rationalQuote a || rationalQuote b) && mask == 256 do
        throwFrontier m!"type-set query: unsupported selected constant bound"
      primitiveQueryTtree tt
      let some hn ← typeSetWalk cfg ctx (.isTruthy term)
        | throwFrontier m!"type-set query: selected reverse bound has no checked context fact"
      let h ← mkAppM ``Or.resolve_right #[← mkAppM ``logic_lt_range
        #[← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx b], hn]
      let fact ← mkAppM ``logic_lt_nil_of_reverse_t #[h]
      let result ← finish (← mkAppM ``inTs_of_eq_nil #[fact])
      return ← retainQueryChild pl (← retainQueryChild pr result)
    let some [.atom (.keyword "TABLE"), .atom (.keyword "LEFT-TS"), lm,
        .atom (.keyword "RIGHT-TS"), rm, .atom (.keyword "NUMERIC-LEFT-TS"), nl,
        .atom (.keyword "NUMERIC-RIGHT-TS"), nr, .atom (.keyword "RESULT"), result] := q.comparison.toList?
      | throwFrontier m!"type-set query: unsupported comparison route"
    unless q.route == .nil && q.recognizer == .nil &&
        (← tsQueryRead (TsQueryCapture.asInt lm)) == l.result &&
        (← tsQueryRead (TsQueryCapture.asInt rm)) == r.result && nl == lm && nr == rm &&
        (← tsQueryRead (TsQueryCapture.asInt result)) == q.result do
      throwFrontier m!"type-set query: inconsistent or unsupported comparison masks"
    if q.result == 128 && r.result == 1 && quotedInt? r.term == some 0 && tsDisjointM l.result 112 then
      let fact ← mkAppM ``logic_lt_zero_nil_of_ts_disjoint
        #[← mkDecideProof (← mkEq (← mkAppM ``tsDisjointM #[toExpr l.result, toExpr (112 : Int)]) (toExpr true)), pl]
      return ← finish (← mkAppM ``inTs_of_eq_nil #[fact])
    if q.result == 256 && l.result == 1 && quotedInt? l.term == some 0 && r.result == 14 then
      let fact ← mkAppM ``zero_lt_of_inTs #[← tsSubsumedProofM 14 14, pr]
      return ← finish (← mkAppM ``inTs_of_eq_t #[fact])
    throwFrontier m!"type-set query: unsupported comparison table cell {l.result}/{r.result} → {q.result}"
  if fn.name == "NOT" then
    let [(c, p)] := cs | throwError "type-set query: NOT arity"
    unless q.comparison == .nil && q.recognizer == .nil && c.result == 128 && q.result == 256 &&
        q.route == SExpr.ofList [.atom (.keyword "NOT"), .atom (.keyword "ARG-TS"), .atom (.number (.int c.result))] do
      throwFrontier m!"type-set query: unsupported NOT masks"
    let fact ← mkAppM ``logic_not_t_of_nil #[← mkAppM ``nil_of_inTs128 #[p]]
    return ← finish (← mkAppM ``inTs_of_eq_t #[fact])
  if ["INTEGERP", "RATIONALP", "ACL2-NUMBERP"].contains fn.name then
    let [(c, p)] := cs | throwError "type-set query: recognizer arity"
    let some basis ← tsQueryRead (ACL2.parseHypRecognizerBasis ProofLog.parseRune? (some q.recognizer))
      | throwError "type-set query: recognizer lacks its tuple"
    let some (_, mask, _) := tsRecogTrue.find? (fun (name, _, _) => name == fn.name)
      | throwFrontier m!"type-set query: primitive recognizer has no checked mask contract"
    let resultMask : Int := (if tsDisjointM c.result mask then 0 else 256) +
      (if tsDisjointM c.result (-mask - 1) then 0 else 128)
    unless q.route == .nil && q.comparison == .nil && q.result == resultMask &&
        basis.argTs == c.result && basis.trueTs == mask && basis.falseTs == -mask - 1 && basis.strongp &&
        basis.rune.ty == "fake-rune-for-anonymous-enabled-rule" &&
        basis.rune.name == "NIL" && basis.rune.idx.isNone do
      throwFrontier m!"type-set query: unsupported recognizer tuple"
    if q.result == 384 then
      let some hr ← boolDisj? cfg ctx q.term
        | throwFrontier m!"type-set query: primitive recognizer lacks its Boolean range law"
      return ← retainQueryChild p (← finish (← mkAppM ``inTs_of_boolean_range #[hr]))
    unless q.result == 256 do
      throwFrontier m!"type-set query: unsupported primitive recognizer verdict {q.result}"
    let fact ← primitiveRecognizerQueryVerdict q.term .t c.result
      basis.trueTs basis.falseTs basis.strongp p
    return ← finish (← mkAppM ``inTs_of_eq_t #[fact])
  throwFrontier m!"type-set query: unsupported primitive {fn.name}"

def replayTsQueryTrue (cfg : ReplayConfig) (ctx : ReplayCtx) (term raw : SExpr) : MetaM Expr := do
  let q ← tsQueryRead (TsQueryCapture.query raw)
  unless q.term == term && !tsMember q.result 7 do throwError "type-set relief: root query mismatch or nullable result"
  let p ← replayTsQuery cfg ctx raw
  let hm ← mkDecideProof (← mkEq (← mkAppM ``tsMember #[toExpr q.result, toExpr (7 : Nat)]) (toExpr false))
  let hn ← mkAppM ``ne_nil_of_inTs #[hm, p]
  mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx term, hn]

/-- One executed operand query, with its own context snapshot. New records
are consumed strictly; a rejected record cannot fall back to legacy typing. -/
def replayOperandTsQuery (cfg : ReplayConfig) (ctx : ReplayCtx)
    (term raw : SExpr) : MetaM (Int × Expr) := do
  let fs ← tsQueryRead (TsQueryCapture.fields raw ["TYPE-ALIST", "QUERIES"])
  let ta ← tsQueryRead (TsQueryCapture.typeAlist (← tsQueryRead (TsQueryCapture.required fs "TYPE-ALIST")))
  let [rawQuery] ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "QUERIES")))
    | throwError "operand query: expected exactly one executed root"
  let q ← tsQueryRead (TsQueryCapture.query rawQuery)
  unless q.term == term do throwError "operand query: root differs from recorded operand"
  checkTsQueryLookups ta rawQuery
  return (q.result, ← replayTsQuery cfg ctx rawQuery)

/-- The explicit recognizer rewrite consumes the same argument-query
judgment as hypothesis relief. A present record is mandatory evidence;
rejection cannot select the legacy recognizer walk. -/
def replayRecognizerOperandQuery (cfg : ReplayConfig) (ctx : ReplayCtx)
    (term verdict raw : SExpr) (prov : StepProvenance) : MetaM Expr := do
  let some (_, [arg]) := asApp term | throwError "recognizer query: malformed rewrite term"
  let some argTs := prov.typeSet | throwError "recognizer query: absent argument mask"
  let some trueTs := prov.trueTs | throwError "recognizer query: absent true partition"
  let some falseTs := prov.falseTs | throwError "recognizer query: absent false partition"
  let some strong := prov.strongp | throwError "recognizer query: absent strength"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx term
  let (mask, p) ← replayOperandTsQuery cfg ctx arg raw
  unless mask == argTs do throwError "recognizer query: operand mask differs from rewrite tuple"
  let h ← primitiveRecognizerQueryVerdict term verdict mask trueTs falseTs strong p
  mkAppM ``re_val_cast #[cfg.worldExpr, cfg.envExpr, reflectSExpr term,
    ← ctxValExpr cfg ctx term, reflectSExpr verdict, ← ctxValProof cfg ctx term, h]

/-- Consume an IF marker's actual assume-true-false query. The snapshot
selects lookup evidence; only checked context facts prove its entries.
The singleton verdict cells are shared with the recorded FC queries. -/
def replayIfTypeQuery? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (term : SExpr) (sense : Bool) (justification : SExpr) : MetaM (Option Expr) := do
  let some rawFields := justification.toList? | return none
  let some raw := ProofLog.lookupKeyword "TYPE-SET-BASIS" rawFields | return none
  let fs ← tsQueryRead (TsQueryCapture.fields justification ["RUNES", "PARENTS", "TYPE-SET-BASIS"])
  let runes ← tsQueryRead (ProofLog.parseRunes (← tsQueryRead (TsQueryCapture.required fs "RUNES")))
  unless runes.all (fun r => r.ty == "fake-rune-for-type-set" && r.name == "NIL" && r.idx.isNone) do
    throwFrontier m!"IF query: ordinary cited evidence needs its own replay"
  let _ ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "PARENTS")))
  let fs ← tsQueryRead (TsQueryCapture.fields raw ["TYPE-ALIST", "QUERIES"])
  let ta ← tsQueryRead (TsQueryCapture.typeAlist (← tsQueryRead (TsQueryCapture.required fs "TYPE-ALIST")))
  let [rawQuery] ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "QUERIES")))
    | throwFrontier m!"IF query: multiple assume-true-false calls are unsupported"
  let q ← tsQueryRead (TsQueryCapture.query rawQuery)
  unless q.term == term do throwError "IF query: root differs from marker test"
  unless q.result == (if sense then 256 else 128) do
    throwFrontier m!"IF query: unsupported test mask {q.result} for verdict {sense}"
  checkTsQueryLookups ta rawQuery
  return some (← mkAppM (if sense then ``t_of_inTs256 else ``nil_of_inTs128)
    #[← replayTsQuery cfg ctx rawQuery])

end ACL2.Replay.Driver
