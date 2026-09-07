import ACL2Lean.Replay.Driver.TypeSetQuery.Basis
import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk
import ACL2Lean.Replay.Lemmas.TsQueryCells

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

def tsQueryRead (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError e

/-- For the supported lookup route, the returned pair must be
the actual first association in the recorded hypothesis context. The
query replay separately proves this mask from checked branch facts. -/
partial def checkTsQueryLookups (ta : List (SExpr × Int × SExpr)) (raw : SExpr) : MetaM Unit := do
  let q ← tsQueryRead (TsQueryCapture.query raw)
  if q.route == .atom (.keyword "LOOKUP") then
    let some (_, mask, tt) := ta.find? (fun (t, _, _) => t == q.term)
      | throwError "type-set query: lookup term absent from recorded type-alist"
    unless q.lookup == SExpr.ofList [.atom (.number (.int mask)), tt] do
      throwError "type-set query: lookup differs from recorded type-alist entry"
  if let some [.atom (.keyword "CONSTANT-BOUND"), .atom (.keyword "RESULT"), _,
      .atom (.keyword "ENTRY"), entry, .atom (.keyword "DERIVATION"), _] := q.comparison.toList? then
    let [selected] ← tsQueryRead (TsQueryCapture.typeAlist (SExpr.ofList [entry]))
      | throwError "type-set query: malformed selected bound entry"
    unless ta.contains selected do
      throwError "type-set query: selected bound entry absent from recorded type-alist"
  for child in q.children do checkTsQueryLookups ta child

private def queryType (cfg : ReplayConfig) (ctx : ReplayCtx)
    (q : TsQueryCapture.Query) : MetaM Expr := do
  mkAppM ``InTs #[toExpr q.result, ← ctxValExpr cfg ctx q.term]

/-- Retain an executed query even when the primitive cell needs only its
sibling premise or has an unconditional range. -/
private def retainQueryChild (child result : Expr) : MetaM Expr := do
  withLetDecl `hQueryArgument (← inferType child) child fun h =>
    mkLetFVars #[h] result (usedLetOnly := false)

/-- Ordinary rule or FC evidence requires its own proof channel. The present
primitive query fragment consumes only parent facts and ACL2's fake type-set
runes, preserving a frontier for every other ttree tag or cited rule. -/
def primitiveQueryTtree (t : SExpr) : MetaM Unit := do
  for entry in ← tsQueryRead (TsQueryCapture.asList t) do
    let .cons (.atom (.symbol tag)) items := entry
      | throwError "type-set query: unsupported ttree entry {repr entry}"
    let items ← tsQueryRead (TsQueryCapture.asList items)
    if tag.name == "PT" then
      unless items.all (fun | .atom (.number (.int n)) => n ≥ 0 | _ => false) do
        throwError "type-set query: unsupported parent tree"
    else if tag.name == "LEMMA" then
      for r in items do
        let some r := ProofLog.parseRune? r | throwError "type-set query: malformed ttree rune"
        unless r.ty == "fake-rune-for-type-set" || r.ty == "fake-rune-for-anonymous-enabled-rule" do
          throwFrontier m!"type-set query: ordinary evidence needs replay: {r}"
    else throwFrontier m!"type-set query: unsupported evidence tag {tag.name}"

/-- Consume a recorded recursive type-set call. Children are checked in
their execution order; a mask alone never proves a fact. No hypothesis DP. -/
partial def replayTsQuery (cfg : ReplayConfig) (ctx : ReplayCtx) (raw : SExpr)
    (expectedDwp : SExpr := .nil) : MetaM Expr := do
  let q ← tsQueryRead (TsQueryCapture.query raw)
  let propagatesDwp := (asApp q.term).any fun (fn, args) =>
    ((fn.name == "REALPART" || fn.name == "IMAGPART") && args.length == 1) ||
      (fn.name == "BINARY-*" && args.length == 2)
  unless q.dwp == expectedDwp && (q.dwp == .nil ||
      q.route == .atom (.keyword "LOOKUP") || (propagatesDwp && q.route == .nil)) do
    throwFrontier m!"type-set query: unsupported double-whammy computation or parent tuple"
  primitiveQueryTtree q.ttree
  primitiveQueryTtree q.inputTtree
  let cs ← q.children.mapM fun raw => do
    let c ← tsQueryRead (TsQueryCapture.query raw)
    let mut childDwp := SExpr.nil
    -- TYPE-SET-WITH-RULES passes DWP unchanged through projections and products.
    -- A recognizer instead supplies its own recorded recognizer tuple.
    if propagatesDwp then
      childDwp := q.dwp
    else if c.dwp != .nil then
      let some (fn, [_]) := asApp q.term | throwError "type-set query: DWP child lacks a recognizer parent"
      let some [_, tm, fm, strong, rune] := q.recognizer.toList?
        | throwError "type-set query: DWP child lacks its parent tuple"
      childDwp := .cons (.atom (.symbol fn)) (.cons (.cons .nil tm) (.cons (.cons fm strong) rune))
      unless tsDisjointM c.result (← tsQueryRead (TsQueryCapture.asInt tm)) ||
          tsDisjointM c.result (← tsQueryRead (TsQueryCapture.asInt fm)) do
        throwFrontier m!"type-set query: DWP lookup does not decide the recorded recognizer"
    pure (c, ← replayTsQuery cfg ctx raw childDwp)
  let finish (p : Expr) := do mkExpectedTypeHint p (← queryType cfg ctx q)
  if q.route == .atom (.keyword "LOOKUP") then
    unless cs.isEmpty && q.recognizer == .nil do throwError "type-set query: lookup has computation children"
    if q.dwp != .nil then
      let .cons (.atom (.symbol _)) (.cons (.cons .nil tm) (.cons (.cons fm _) _)) := q.dwp
        | throwError "type-set query: malformed propagated recognizer tuple"
      unless tsDisjointM q.result (← tsQueryRead (TsQueryCapture.asInt tm)) ||
          tsDisjointM q.result (← tsQueryRead (TsQueryCapture.asInt fm)) do
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
    primitiveQueryTtree tt
    let some p ← inTsFromCtx cfg ctx [] [] q.term (← ctxValExpr cfg ctx q.term) q.result []
      | throwFrontier m!"type-set query: missing checked lookup fact for {repr q.term} : {q.result}"
    return ← finish p
  unless q.lookup == SExpr.ofList [.nil, .nil] do
    throwFrontier m!"type-set query: nontrivial lookup/computation intersection"
  if (asApp q.term).any (fun (fn, args) => fn.name == "QUOTE" && args.length == 1) then
    unless cs.isEmpty && q.route == .nil && q.comparison == .nil && q.recognizer == .nil do
      throwError "type-set query: quoted query has an unexpected route"
    return ← finish (← mkDecideProof (← withTransparency .all <| whnf (← queryType cfg ctx q)))
  let some (fn, args) := asApp q.term | throwFrontier m!"type-set query: unsupported non-application"
  unless cs.map (fun (c, _) => c.term) == args do
    throwError "type-set query: executed children do not match the primitive arguments"
  if fn.name == "REALPART" || fn.name == "IMAGPART" then
    let [(c, p)] := cs | throwError "type-set query: component projection arity"
    unless q.route == .nil && q.comparison == .nil && q.recognizer == .nil do
      throwError "type-set query: component projection has an unexpected route"
    let some (input, _, ruleName) := (tsUnaryOf fn.name).find? fun (input, out, _) =>
        out == q.result && (input.isNone || input == some c.result)
      | throwFrontier m!"type-set query: unsupported {fn.name} masks {c.result} → {q.result}"
    match input with
    | some _ => return ← finish (← mkAppM ruleName #[p])
    | none =>
      let result ← finish (← mkAppM ruleName #[← ctxValExpr cfg ctx c.term])
      -- The projection's unconditional range does not need a child premise,
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
    let some (_, _, _, ruleName) := (tsBinaryOf fn.name).find? fun (lm, rm, out, _) =>
        lm == l.result && rm == r.result && out == q.result
      | throwFrontier m!"type-set query: unsupported {fn.name} masks {l.result}/{r.result} → {q.result}"
    return ← finish (← mkAppM ruleName #[pl, pr])
  if fn.name == "<" then
    let [(l, pl), (r, pr)] := cs | throwError "type-set query: comparison arity"
    if let some [.atom (.keyword "CONSTANT-BOUND"), .atom (.keyword "RESULT"), result,
        .atom (.keyword "ENTRY"), entry, .atom (.keyword "DERIVATION"), derivation] := q.comparison.toList? then
      unless q.route == .nil && q.recognizer == .nil && q.result == 128 &&
          (← tsQueryRead (TsQueryCapture.asInt result)) == q.result do
        throwFrontier m!"type-set query: unsupported constant-bound result"
      primitiveQueryTtree derivation
      let [(term, mask, tt)] ← tsQueryRead (TsQueryCapture.typeAlist (SExpr.ofList [entry]))
        | throwError "type-set query: malformed bound entry"
      let some (boundFn, [a, b]) := asApp term | throwError "type-set query: non-comparison bound"
      unless boundFn.name == "<" && a == r.term && b == l.term &&
          quotedInt? a == some 0 && mask == 256 do
        throwFrontier m!"type-set query: unsupported selected constant bound"
      primitiveQueryTtree tt
      let some hn ← typeSetWalk cfg ctx (.isTruthy term)
        | throwFrontier m!"type-set query: selected reverse bound has no checked context fact"
      let h ← mkAppM ``Or.resolve_right #[← mkAppM ``logic_lt_range
        #[← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx b], hn]
      let fact ← mkAppM ``logic_lt_nil_of_reverse_t #[h]
      return ← finish (← mkAppM ``inTs_of_eq_nil #[fact])
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
  if fn.name == "RATIONALP" || fn.name == "ACL2-NUMBERP" then
    let [(c, p)] := cs | throwError "type-set query: recognizer arity"
    let some basis ← tsQueryRead (ACL2.parseHypRecognizerBasis ProofLog.parseRune? (some q.recognizer))
      | throwError "type-set query: recognizer lacks its tuple"
    let mask : Int := if fn.name == "RATIONALP" then 63 else 127
    let lemmaName := if fn.name == "RATIONALP" then ``logic_rationalp_t_of_inTs else ``logic_acl2Numberp_t_of_inTs
    unless q.route == .nil && q.comparison == .nil && q.result == 256 &&
        basis.argTs == c.result && basis.trueTs == mask && basis.falseTs == -mask - 1 && basis.strongp &&
        basis.rune.ty == "fake-rune-for-anonymous-enabled-rule" &&
        basis.rune.name == "NIL" && basis.rune.idx.isNone do
      throwFrontier m!"type-set query: unsupported recognizer tuple"
    let fact ← mkAppM lemmaName #[← tsSubsumedProofM c.result mask, p]
    return ← finish (← mkAppM ``inTs_of_eq_t #[fact])
  throwFrontier m!"type-set query: unsupported primitive {fn.name}"

def replayTsQueryTrue (cfg : ReplayConfig) (ctx : ReplayCtx) (term raw : SExpr) : MetaM Expr := do
  let q ← tsQueryRead (TsQueryCapture.query raw)
  unless q.term == term && !tsMember q.result 7 do throwError "type-set relief: root query mismatch or nullable result"
  let p ← replayTsQuery cfg ctx raw
  let hm ← mkDecideProof (← mkEq (← mkAppM ``tsMember #[toExpr q.result, toExpr (7 : Nat)]) (toExpr false))
  let hn ← mkAppM ``ne_nil_of_inTs #[hm, p]
  mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx term, hn]

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
