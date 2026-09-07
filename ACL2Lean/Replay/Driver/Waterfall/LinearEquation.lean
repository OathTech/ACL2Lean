import ACL2Lean.Replay.Driver.Waterfall.ClauseFalsity
import ACL2Lean.Replay.Driver.Waterfall.LinearNumeric
import ACL2Lean.Replay.Lemmas.TsLinearFacts

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private def linearApp (name : String) (args : List SExpr) : SExpr :=
  .cons (.atom (.symbol { name })) (args.foldr SExpr.cons .nil)

private def linearNat (x : SExpr) : Except String Nat := do
  let .atom (.number (.int k)) := x | throw "linear equation: noninteger parent"
  unless k ≥ 0 do throw "linear equation: negative parent"
  pure k.toNat

/-- The selected unit row's parent and tag-tree provenance. Its construction
class is checked separately against a direct comparison or captured query. -/
private structure UnitLinearRow where
  parents : List Nat
  tips : List Nat
  ttree : SExpr
  rational : Bool

private def readUnitLinearRow (p a b : SExpr) (positive hasNumericBasis : Bool) :
    Except String UnitLinearRow := do
  -- LINEAR-A.LISP's DEFREC POLY: outer singleton, then metadata and
  -- constant/relation/rational/derived-from-not-equality fields.
  let some [fields] := p.toList? | throw "linear equation: malformed poly wrapper"
  let some [source, c, rel, rat] := fields.toList?
    | throw "linear equation: unsupported poly fields"
  unless c == .atom (.number (.int 0)) &&
      rel == .atom (.symbol { name := "<=" }) && (rat == .t || (hasNumericBasis && rat == .nil)) do
    throw "linear equation: expected a rational weak zero row"
  let some (alist :: parents :: tags) := source.toList?
    | throw "linear equation: unsupported polynomial derivation tags"
  let n : Int := if positive then 1 else -1
  let expected := ([a, b].zip [n, -n]).filterMap fun (term, coefficient) =>
    if quotedInt? term == some 0 then none
    else some (SExpr.cons term (.atom (.number (.int coefficient))))
  unless alist.toList? == some expected do
    throw "linear equation: coefficients do not isolate the recorded unit equation"
  let some parents := parents.toList?
    | throw "linear equation: malformed row parents"
  let ptTags := tags.filter fun t => (asApp t).any (fun (s, _) => s.name == "PT")
  let [pts] := ptTags | throw "linear equation: expected one PT provenance tag"
  let some (.atom (.symbol tag) :: tips) := pts.toList?
    | throw "linear equation: malformed PT tag"
  unless tag.name == "PT" do throw "linear equation: missing PT provenance"
  let expectedLemmas := linearApp "LEMMA"
    [(.cons (.atom (.keyword "FAKE-RUNE-FOR-TYPE-SET")) (.cons .nil .nil))]
  let otherTags := tags.filter (· != pts)
  unless otherTags.isEmpty || otherTags == [expectedLemmas] do
    throw "linear equation: row uses an unsupported lemma derivation"
  let parents ← parents.mapM linearNat
  let tips ← tips.mapM linearNat
  unless parents.all tips.contains && parents.eraseDups == parents && tips.eraseDups == tips do
    throw "linear equation: parent/PT provenance differs"
  pure { parents, tips, ttree := SExpr.ofList tags, rational := rat == .t }

/-- Check only equality of the emitted polynomial and the source
comparison's primitive arithmetic expansion. This is deterministic additive
normalization (ADD-LINEAR-TERM's + / unary-minus class), with no branch
hypotheses and no implication solver. Unsupported normalization fails. -/
private def checkLinearNormalization (lhs rhs : Expr) : MetaM Expr := do
  let goal ← mkFreshExprMVar (← mkEq lhs rhs)
  let tac ← `(tactic|
    apply Prod.ext <;>
    simp only [Logic.linearDifference, Logic.plus_parts, Logic.neg_parts,
      Logic.numberParts_mkParts, Logic.linear_int_parts, Int.ofNat_eq_natCast,
      Int.ofNat_zero, Rat.intCast_zero,
      Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.neg_zero,
      Rat.zero_add, Rat.add_zero, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm])
  let remaining ← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.withoutErrToSorry <|
    Lean.Elab.Term.withSynthesize do
      Lean.Elab.Tactic.run goal.mvarId! <| Lean.Elab.Tactic.withoutRecover do
        Lean.Elab.Tactic.evalTactic tac
        Lean.Elab.Tactic.pruneSolvedGoals
  unless remaining.isEmpty do
    throwError "linear equation: polynomial normalization remains open: {← remaining.head!.getType}"
  instantiateMVars goal

/-- Replay the executed zero-cell query which constructed this exact row.
Only its recorded PT facts enter the context; the type-alist is checked data. -/
private def replayTypeZeroRow (cfg : ReplayConfig) (ctx : ReplayCtx)
    (info : LinearEquationInsertion) (row : UnitLinearRow) (basis term : SExpr)
    (positive : Bool) (parentFalse : Nat → MetaM (SExpr × Expr)) : MetaM Expr := do
  let fs ← tsQueryRead (TsQueryCapture.fields basis
    ["KIND", "TERM", "MASK", "TYPE-ALIST", "QUERIES", "TTREE"])
  unless (← tsQueryRead (TsQueryCapture.required fs "KIND")) == .atom (.keyword "TYPE-SET") &&
      (← tsQueryRead (TsQueryCapture.required fs "TERM")) == term &&
      (← tsQueryRead (TsQueryCapture.required fs "MASK")) == .atom (.number (.int 1)) do
    throwError "linear type row: unsupported construction term or mask"
  let tt ← tsQueryRead (TsQueryCapture.required fs "TTREE")
  unless row.rational && tt == row.ttree && row.parents == row.tips do
    throwError "linear type row: construction tag tree differs from selected row"
  primitiveQueryTtree tt
  let ta ← tsQueryRead (TsQueryCapture.typeAlist (← tsQueryRead (TsQueryCapture.required fs "TYPE-ALIST")))
  let [query] ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "QUERIES")))
    | throwError "linear type row: expected the single construction query"
  let q ← tsQueryRead (TsQueryCapture.query query)
  unless q.term == term && q.result == 1 && q.ttree == tt do
    throwError "linear type row: construction query mismatch"
  checkTsQueryLookups ta query
  let mut queryCtx := ctx
  for k in row.parents do
    let (lit, h) ← parentFalse k
    queryCtx := {queryCtx with litFacts := queryCtx.litFacts ++
      [(info.inputClause.length - info.parentClause.length + k, lit, h)]}
  let h ← replayTsQuery cfg queryCtx query
  mkAppM (if positive then ``linear_zero_cell_positive else ``linear_zero_cell_negative) #[h]

/-- Prove an insertion from the actual selected complementary pair, then
consume the complete recorded continuation at its output clause. -/
def replayLinearEquation (cfg : ReplayConfig) (ctx : ReplayCtx)
    (clause : List SExpr) (info : LinearEquationInsertion)
    (continueAt : List SExpr → MetaM Expr) : MetaM Expr := do
  unless clause == info.inputClause && !clause.isEmpty &&
      info.outputClause == info.newLiteral :: clause &&
      info.parentClause.length ≤ clause.length &&
      clause.drop (clause.length - info.parentClause.length) == info.parentClause do
    throwError "linear equation: input/output/parent clause mismatch"
  unless info.numericFlags == ["KNOWN-TRUE", "KNOWN-TRUE"] && info.assumptions.isEmpty do
    throwError "linear equation: numeric completion or forcing requires another consumer"
  unless info.runes == [⟨"fake-rune-for-type-set", "NIL", none⟩] ||
      (info.numericBasis.isSome && info.runes.isEmpty) do
    throwError "linear equation: insertion cites an unsupported derivation"
  let some (notS, [eqTerm]) := asApp info.newLiteral
    | throwError "linear equation: inserted literal is not a negation"
  let some (eqS, [a, b]) := asApp eqTerm
    | throwError "linear equation: inserted atom is not a binary equation"
  unless notS.name == "NOT" && eqS.name == "EQUAL" do
    throwError "linear equation: inserted literal is not NOT EQUAL"
  let [.cons p1 p2] := info.polyPairs
    | throwError "linear equation: expected one selected polynomial pair"
  let readRow (p : SExpr) (positive : Bool) : MetaM UnitLinearRow :=
    match readUnitLinearRow p a b positive info.numericBasis.isSome with
    | .ok r => pure r
    | .error msg => throwError msg
  let r1 ← readRow p1 true
  let r2 ← readRow p2 false
  let (basis1, basis2) ← match info.polyTypeBasis with
    | none => pure (SExpr.nil, SExpr.nil)
    | some raw => do
      let [pair] ← tsQueryRead (TsQueryCapture.asList raw)
        | throwError "linear type row: basis count differs from selected pairs"
      let [b1, b2] ← tsQueryRead (TsQueryCapture.asList pair)
        | throwError "linear type row: expected both row basis slots"
      pure (b1, b2)
  let mut ctx := ctx
  for t in info.outputClause do ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let va ← ctxValExpr cfg ctx a
  let vb ← ctxValExpr cfg ctx b
  let goal ← mkAppM ``EvTrue
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm clause)]
  let outputProof ← continueAt info.outputClause
  let contradiction ← withLocalDeclD `hInputFalse (← mkAppM ``Not #[goal]) fun hFalse => do
    let parentFalse (k : Nat) : MetaM (SExpr × Expr) := do
      let some lit := info.parentClause[k]?
        | throwError "linear equation: PT outside original clause"
      let index := clause.length - info.parentClause.length + k
      let (actual, proof) ← clauseLiteralFalsity cfg ctx clause hFalse index
      unless actual == lit do throwError "linear equation: indexed parent differs from its record"
      pure (lit, proof)
    let numeric ← replayLinearNumericBasis cfg ctx info a b parentFalse
    let checkRow (row : UnitLinearRow) (basis : SExpr) (positive : Bool)
        (x y : SExpr) : MetaM (Expr × Expr × Expr) := do
      if basis != .nil then
        unless quotedInt? b == some 0 do throwError "linear type row: only zero-cell bounds are supported"
        let some (ha, hb) := numeric | throwError "linear type row: numeric query basis required"
        let h ← replayTypeZeroRow cfg ctx info row basis a positive parentFalse
        return (h, ha, hb)
      let [parent] := row.parents | throwError "linear equation: row is not from one direct parent"
      let (lit, hLit) ← parentFalse parent
      let some (ltS, [lhs, rhs]) := asApp lit
        | throwError "linear equation: direct parent is not a comparison"
      unless ltS.name == "<" do throwError "linear equation: unsupported direct parent"
      let mut ha : Option Expr := numeric.map (·.1)
      let mut hb : Option Expr := numeric.map (·.2)
      for tip in row.tips do
        if tip == parent then continue
        let (typeLit, hType) ← parentFalse tip
        let some (n, [ratTerm]) := asApp typeLit
          | throwError "linear equation: PT is not a negated rationality fact"
        let some (r, [term]) := asApp ratTerm
          | throwError "linear equation: PT rationality term malformed"
        unless n.name == "NOT" && r.name == "RATIONALP" && (term == a || term == b) do
          throwError "linear equation: PT requires an unsupported type derivation"
        let hBool ← mkAppM ``Iff.mp #[← mkAppM ``Logic.not_nil_iff
          #[← ctxValExpr cfg ctx ratTerm], hType]
        let hRat ← mkAppM ``Iff.mp #[← mkAppM ``Logic.toBool_eq_true
          #[← ctxValExpr cfg ctx ratTerm], hBool]
        let hNum ← mkAppM ``Logic.linear_number_of_rational #[← ctxValExpr cfg ctx term, hRat]
        if term == a then ha := some hNum else hb := some hNum
      let some numberA := ha | throwError "linear equation: missing recorded lhs number premise"
      let some numberB := hb | throwError "linear equation: missing recorded rhs number premise"
      let vl ← ctxValExpr cfg ctx lhs
      let vr ← ctxValExpr cfg ctx rhs
      let raw ← mkAppM ``Logic.linear_difference_nonnegative #[vl, vr, hLit]
      let source ← mkAppM ``Logic.linearDifference #[vl, vr]
      let target ← mkAppM ``Logic.linearDifference
        #[← ctxValExpr cfg ctx x, ← ctxValExpr cfg ctx y]
      let eq ← checkLinearNormalization source target
      let transported ← mkEqMP (← mkCongrArg (mkConst ``Logic.LinearNonnegative) eq) raw
      pure (transported, numberA, numberB)
    let (hp, ha, hb) ← checkRow r1 basis1 true a b
    let (hn, _, _) ← checkRow r2 basis2 false b a
    let eq ← mkAppM ``Logic.linear_unit_pair #[va, vb, ha, hb, hp, hn]
    let hEq ← mkAppM ``Iff.mpr #[← mkAppM ``Logic.equal_ne_nil_iff #[va, vb], eq]
    let pEq ← mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx eqTerm, hEq]
    let pNot ← mkAppM ``conv_not_nil_of_evtrue #[← proveNoShadow cfg notS, pEq]
    let restored ← mkAppM ``evtrue_extract_else #[pNot, outputProof]
    mkLambdaFVars #[hFalse] (mkApp hFalse restored)
  mkAppM ``Classical.byContradiction #[contradiction]

end ACL2.Replay.Driver
