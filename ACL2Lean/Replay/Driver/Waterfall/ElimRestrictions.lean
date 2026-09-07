import ACL2Lean.Replay.Driver.TypeSetQuery

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The observer's actual type query and conversion before generalization.
Values in this record are evidence to check, never Lean assumptions. -/
structure ElimRestriction where
  term : SExpr
  var : Symbol
  inputClause : List SExpr
  typeAlist : List (SExpr × Int × SExpr)
  mask : Int
  query : SExpr
  formula : SExpr
  clauses : List (List SExpr)

def readElimRestrictions (raw : SExpr) : MetaM (List ElimRestriction) := do
  (← tsQueryRead (TsQueryCapture.asList raw)).mapM fun entry => do
    let .cons (.atom (.keyword "TYPE-RESTRICTION")) tail := entry
      | throwError "elim restrictions: malformed record"
    let fs ← tsQueryRead (TsQueryCapture.fields tail ["BASIS", "FORMULA", "CLAUSES", "TTREE"])
    let basis ← tsQueryRead (TsQueryCapture.required fs "BASIS")
    let bs ← tsQueryRead (TsQueryCapture.fields basis
      ["TERM", "VAR", "INPUT-CLAUSE", "TYPE-ALIST", "MASK", "TTREE", "QUERIES"])
    let term ← tsQueryRead (TsQueryCapture.required bs "TERM")
    let .atom (.symbol var) ← tsQueryRead (TsQueryCapture.required bs "VAR")
      | throwError "elim restrictions: fresh variable is not a symbol"
    let mask ← tsQueryRead (TsQueryCapture.asInt (← tsQueryRead (TsQueryCapture.required bs "MASK")))
    let [query] ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required bs "QUERIES")))
      | throwError "elim restrictions: expected exactly the executed destructor query"
    let q ← tsQueryRead (TsQueryCapture.query query)
    unless q.term == term && q.result == mask &&
        q.ttree == (← tsQueryRead (TsQueryCapture.required bs "TTREE")) do
      throwError "elim restrictions: query differs from the recorded result"
    primitiveQueryTtree (← tsQueryRead (TsQueryCapture.required fs "TTREE"))
    let typeAlist ← tsQueryRead (TsQueryCapture.typeAlist (← tsQueryRead (TsQueryCapture.required bs "TYPE-ALIST")))
    checkTsQueryLookups typeAlist query
    return {
      term, var, mask, query, typeAlist,
      inputClause := ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required bs "INPUT-CLAUSE"))),
      formula := ← tsQueryRead (TsQueryCapture.required fs "FORMULA"),
      clauses := ← (← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "CLAUSES")))).mapM
        (fun c => tsQueryRead (TsQueryCapture.asList c)) }

private def restrictionApp (name : String) (args : List SExpr) : SExpr :=
  SExpr.ofList (.atom (.symbol { name }) :: args)

/-- The primitive mask conversions executed at the current ELIM nodes.
Both formula and clausified segment must match the actual observer record. -/
def elimRestrictionSegment (r : ElimRestriction) : MetaM (List SExpr) := do
  let rational := restrictionApp "RATIONALP" [r.term]
  let zeroEq := restrictionApp "EQUAL" [r.term, tsQuotedZero]
  let (formula, truths) ← match r.mask with
    | 1 => pure (zeroEq, [zeroEq])
    | 63 => pure (rational, [rational])
    | m => do
      let test ← match m with
        | 14 => pure (restrictionApp "<" [tsQuotedZero, r.term])
        | 15 => pure (restrictionApp "NOT" [restrictionApp "<" [r.term, tsQuotedZero]])
        | 48 => pure (restrictionApp "<" [r.term, tsQuotedZero])
        | 62 => pure (restrictionApp "NOT" [zeroEq])
        | _ => throwFrontier m!"elim restrictions: unsupported recorded mask conversion {m}"
      pure (restrictionApp "IF" [rational, test, quoteNil], [rational, test])
  let segment := truths.map (fun t => restrictionApp "NOT" [t])
  unless r.formula == formula && r.clauses == [segment] do
    throwError "elim restrictions: recorded conversion formula or clause segment differs"
  return segment

/-- Prove each actual restriction literal false on the original destructor
values, using the recorded query. The caller later strips these literals
after transporting the generalized child back to this environment. -/
def replayElimRestriction (cfg : ReplayConfig) (ctx : ReplayCtx)
    (r : ElimRestriction) : MetaM (List (SExpr × Expr)) := do
  let segment ← elimRestrictionSegment r
  let p ← replayTsQuery cfg ctx r.query
  let trueProofs ← if r.mask == 1 then do
      pure [← mkAppM ``equal_zero_t_of_inTs #[p]]
    else do
      let rat ← mkAppM ``logic_rationalp_t_of_inTs #[← tsSubsumedProofM r.mask 63, p]
      if r.mask == 63 then pure [rat] else do
        let second ← match r.mask with
          | 14 => mkAppM ``zero_lt_of_inTs #[← tsSubsumedProofM r.mask 14, p]
          | 48 => mkAppM ``lt_zero_of_inTs #[p]
          | 15 => do
            let ltNil ← mkAppM ``logic_lt_zero_nil_of_ts_disjoint
              #[← mkDecideProof (← mkEq (← mkAppM ``tsDisjointM #[toExpr r.mask, toExpr (112 : Int)]) (toExpr true)), p]
            mkAppM ``logic_not_t_of_nil #[ltNil]
          | 62 => do
            let zeroNil ← mkAppM ``equal_zero_nil_of_inTs
              #[← mkDecideProof (← mkEq (← mkAppM ``tsDisjointM #[toExpr r.mask, toExpr (1 : Int)]) (toExpr true)), p]
            mkAppM ``logic_not_t_of_nil #[zeroNil]
          | m => throwFrontier m!"elim restrictions: unsupported mask {m}"
        pure [rat, second]
  let tNeNil ← mkDecideProof (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil])
  (segment.zip trueProofs).mapM fun (lit, trueProof) => do
    let falseProof ← mkAppM ``not_nil_of_truthy #[← mkAppM ``ne_of_eq_of_ne #[trueProof, tNeNil]]
    let expected ← mkEq (← ctxValExpr cfg ctx lit) (mkConst ``SExpr.nil)
    return (lit, ← mkExpectedTypeHint falseProof expected)

end ACL2.Replay.Driver
