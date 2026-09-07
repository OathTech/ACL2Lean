/-
  Driver/Waterfall/Elim — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The destructor-ELIMINATION processor (primitive CAR/CDR and REALPART/IMAGPART recipes). Generalized to
  MULTI-RECORD rounds (emission arc 2026-07-21): a round's records nest as
  guard splits — record k cases on `(consp v_k)`; record 1's guard is the
  clause's own `(not (consp v))` head literal (nil-case closes the
  disjunction), while each LATER record's nil-case consumes its own GUARD
  CHILD (`(consp v_k) :: C_{k-1}` — the clause ACL2 pushes for the
  not-a-cons case, peeled via `evtrue_extract_else`); the success side
  extends the env and recurses, bottoming out at the fully-eliminated
  child with one `evalOpt_substTerm_substN` bridge per level.
-/
import ACL2Lean.Replay.Driver.Waterfall.ClauseFalsity
import ACL2Lean.Replay.Driver.Waterfall.ElimRestrictions
import ACL2Lean.Replay.Driver.Waterfall.ClauseSubset
import ACL2Lean.NumericComponents

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- The fixed primitive axiom supplies the semantic part of a recorded
elimination. Guard splitting, fresh environments, and substitution transport
are shared by both constructor/destructor families. -/
private structure ElimRecipe where
  ctor : String
  guardName : String
  firstName : String
  secondName : String
  guardValue : Name
  firstValue : Name
  secondValue : Name
  reassemble : Name

private def elimRecipe (rune : String) : MetaM ElimRecipe := do
  match rune with
  | "CAR-CDR-ELIM" => return {
      ctor := "CONS", guardName := "CONSP", firstName := "CAR", secondName := "CDR",
      guardValue := ``Logic.consp, firstValue := ``Logic.car, secondValue := ``Logic.cdr,
      reassemble := ``logic_cons_car_cdr_of_consp }
  | "REALPART-IMAGPART-ELIM" => return {
      ctor := "COMPLEX", guardName := "ACL2-NUMBERP", firstName := "REALPART", secondName := "IMAGPART",
      guardValue := ``Logic.acl2Numberp, firstValue := ``Logic.realpart, secondValue := ``Logic.imagpart,
      reassemble := ``Logic.complex_realpart_imagpart }
  | _ => throwFrontier m!"replayElim: unsupported primitive elimination rule {rune}"

private structure ElimRecord where
  recipe : ElimRecipe
  var : Symbol
  first : Symbol
  second : Symbol
  restricted : List Symbol
  restrictions : Option (List ElimRestriction) := none
  restrictionDrops : List SExpr := []

/-- Parse + validate one primitive constructor/destructor record
    `((:ELIM CAR-CDR-ELIM) v (CONS v1 v2) (((CAR v) . v1) ((CDR v) . v2))
      NIL NIL NIL)` → `(v, v1, v2)`. -/
private def parseElimRecord (idStr : String) (recS : SExpr) :
    MetaM ElimRecord := do
  let some [runeS, varS, targetS, destS, crit1, crit2, crit3] := recS.toList?
    | throwError "replayElim: elim record shape at {idStr}: {repr recS}"
  -- trailing fields (sorting-completion-2, ORDERED-PERMS Subgoal *1/7):
  -- ACL2's elim-sequence entry tail — RESTRICTED-VARS (a symbol list; the
  -- generalized variables ACL2 recorded type restrictions for) and the
  -- elim's own ttree (the side-condition lemmas, e.g.
  -- (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL))). ADVISORY here: the replay
  -- reconstructs the child clauses and validates them against the RECORDED
  -- children downstream, so a restriction that changed the clause set
  -- fails loudly at that match — permitting these shapes stays
  -- fail-closed. crit2 (var-to-runes between them) unobserved non-nil.
  let symListOrNil : SExpr → Bool := fun e =>
    e == .nil || (e.toList?.map (·.all fun x =>
      match x with | .atom (.symbol _) => true | _ => false)).getD false
  unless symListOrNil crit1 do
    throwError "replayElim: elim record restricted-vars {repr crit1} is not \
                a symbol list at {idStr} (frontier): {repr recS}"
  unless crit2 == .nil do
    throwError "replayElim: elim record var-to-runes field non-nil at \
                {idStr} (frontier): {repr recS}"
  unless crit3 == .nil || crit3.toList?.isSome do
    throwError "replayElim: elim record ttree field {repr crit3} shape at \
                {idStr} (frontier): {repr recS}"
  let some [.atom (.keyword "ELIM"), .atom (.symbol runeName)] := runeS.toList?
    | throwError "replayElim: elim record rune {repr runeS} at {idStr}"
  let recipe ← elimRecipe runeName.name
  let .atom (.symbol v) := varS
    | throwError "replayElim: eliminated var {repr varS} at {idStr}"
  let .cons (.atom (.symbol consS))
      (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil)) := targetS
    | throwError "replayElim: elim target {repr targetS} is not a binary constructor on fresh variables \
                  at {idStr}"
  unless consS.name == recipe.ctor && v1 != v2 && v1 != v && v2 != v do
    throwError "replayElim: elim target vars ({consS.name} {v1.name} {v2.name}) \
                at {idStr}"
  let vT : SExpr := .atom (.symbol v)
  let carT : SExpr := .cons (.atom (.symbol { name := recipe.firstName })) (.cons vT .nil)
  let cdrT : SExpr := .cons (.atom (.symbol { name := recipe.secondName })) (.cons vT .nil)
  let expectedDest : List SExpr :=
    [.cons carT (.atom (.symbol v1)), .cons cdrT (.atom (.symbol v2))]
  unless destS.toList? == some expectedDest do
    throwError "replayElim: destructor map {repr destS} ≠ ((car {v.name}) . \
                {v1.name}) ((cdr {v.name}) . {v2.name}) at {idStr}"
  let restricted : List Symbol :=
    (crit1.toList?.getD []).filterMap fun x =>
      match x with | .atom (.symbol sy) => some sy | _ => none
  return { recipe, var := v, first := v1, second := v2, restricted }

/-- Reproduce the type-restriction prefix before destructor substitution.
Segments already included in the original clause do not restrict a variable.
Duplicate removal from the original clause is checked separately against
the ELIM step's actual ADD-LITERAL records. -/
private def elimRecordPrefix (er : ElimRecord) (clause : List SExpr) : MetaM (List SExpr) := do
  let some restrictions := er.restrictions | return []
  let mut addedLits := []
  let mut restricted := []
  for r in restrictions do
    unless r.inputClause == clause do
      throwError "replayElim: restriction query input differs from this record's guarded clause"
    let segment ← elimRestrictionSegment r
    unless segment.all clause.contains do
      unless segment.all (fun lit => !addedLits.contains lit) do
        throwFrontier m!"replayElim: duplicate between restriction segments needs replay"
      addedLits := addedLits ++ segment
      restricted := restricted ++ [r.var]
  unless restricted == er.restricted do
    throwError "replayElim: type queries differ from the record's restricted variables"
  return addedLits

/-- Select the emitted ELIM suffix after an in-node preprocessing pass.
The clause at the boundary comes from both the actual STEP input and the
preceding processor's output. This is a view of those records, not a new
clause-tree event. The caller consumes the preprocessing chain/clausifier. -/
def elimAfterClausifyView (cn : ClauseNode) (cl : List SExpr) :
    MetaM (ClauseNode × WaterfallStep) := do
  let idx := cn.steps.findIdx (fun s => s.processor.toLower == "eliminate-destructors-clause")
  let some st := cn.steps[idx]? | throwError "elim after clausify: no recorded ELIM step"
  unless st.inputClause? == some cl do
    throwError "elim after clausify: recorded input differs from clausify output"
  let before := cn.steps.take idx
  let [pre] := before.filter (fun s => s.processor.toLower == "preprocess-clause")
    | throwError "elim after clausify: expected one preceding preprocessing pass"
  unless pre.inputClause? == some cn.inputClause && pre.newClauses == [SExpr.ofList cl] do
    throwError "elim after clausify: preprocessing STEP boundaries differ"
  let .clausify _ :: reversedSteps := pre.items.reverse
    | throwError "elim after clausify: preprocessing does not end at its clausifier"
  unless reversedSteps.all (fun | .step _ => true | _ => false) do
    throwError "elim after clausify: preprocessing carries unconsumed non-chain items"
  for s in before do
    unless s.processor.toLower == "preprocess-clause" do
      unless s.processor.toLower == "settled-down-clause" && s.items.isEmpty &&
          s.inputClause? == some cl && s.newClauses == [SExpr.ofList cl] do
        throwError "elim after clausify: preceding processor is not an inert settling pass"
  return ({ cn with inputClause := cl, steps := cn.steps.drop idx }, st)

/-- Replay a DESTRUCTOR-ELIMINATION node (`eliminate-destructors-clause`,
    a registered primitive rune, one round of ≥1 records — see the module doc):
    prove `EvTrue w env (disjoin C)` from the children, the emitted
    `:ELIMSEQUENCE` recomputed and REQUIRED to match at every level, never
    inferred. Per record, by cases on the value of `(consp v)`:
    - nil: record 1 closes via the clause's `(not (consp v))` head literal
      (required — frontier otherwise); a later record peels its GUARD child;
    - non-nil: recurse/replay at `env' = env[v1 ↦ car vv, v2 ↦ cdr vv]`;
      `evalOpt_substTerm_substN` bridges `eval env' (disjoin C')` to
      `eval env ((disjoin C')σ)` for `σ = v1↦(car v), v2↦(cdr v)`; the
      residual gap `disjoin C` vs `(disjoin C')σ` is exactly bare-`v` vs
      `(cons (car v) (cdr v))`, collapsed by `diffCollapse` under
      `logic_cons_car_cdr_of_consp`. -/
partial def replayElim (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode)
    (st : WaterfallStep) : MetaM Expr := do
  -- companions must be inert; literal items are identity displays only
  for s in cn.steps do
    unless s.processor.toLower == "eliminate-destructors-clause" ||
           s.processor.toLower == "settled-down-clause" do
      throwError "replayElim: processor {s.processor} alongside elim at \
                  {cn.idStr} (frontier)"
  for (_, lp) in flattenLiterals (cn.steps.flatMap (·.items)) do
    unless identityLiteralItem lp do
      throwError "replayElim: non-identity literal item at {cn.idStr} \
                  (frontier): {repr lp.literal}"
  -- the emitted justification: ONE round of ≥1 registered elimination records
  let some seqS := st.extraFields.lookup "elimsequence"
    | throwError "replayElim: no :ELIMSEQUENCE at {cn.idStr}"
  let some [roundS] := seqS.toList?
    | throwError "replayElim: :ELIMSEQUENCE is not a single round at {cn.idStr} \
                  (frontier): {repr seqS}"
  let some recSs := roundS.toList?
    | throwError "replayElim: elim round {repr roundS} is not a list at {cn.idStr}"
  if recSs.isEmpty then
    throwError "replayElim: EMPTY elim round at {cn.idStr}"
  let records ← recSs.mapM (parseElimRecord cn.idStr)
  let records ← match st.extraFields.lookup "type-restrictions" with
    | none => pure records
    | some raw => do
      let restrictions ← readElimRestrictions raw
      unless restrictions.length == 2 * records.length do
        throwError "replayElim: expected the two executed restriction queries per record"
      records.zipIdx |>.mapM fun (er, index) => do
        let pair := (restrictions.drop (2 * index)).take 2
        let expected := [
          (SExpr.ofList [.atom (.symbol {name := er.recipe.firstName}), .atom (.symbol er.var)], er.first),
          (SExpr.ofList [.atom (.symbol {name := er.recipe.secondName}), .atom (.symbol er.var)], er.second)]
        unless pair.map (fun r => (r.term, r.var)) == expected do
          throwError "replayElim: restriction query order or destructor/variable mapping differs"
        return { er with restrictions := some pair }
  -- :ELIMVARS — one flat list of the round's fresh vars, in record order
  let some varsS := st.extraFields.lookup "elimvars"
    | throwError "replayElim: no :ELIMVARS at {cn.idStr}"
  let expectedVars : SExpr := .cons
    ((records.flatMap fun er =>
        [SExpr.atom (.symbol er.first), SExpr.atom (.symbol er.second)]).foldr .cons .nil)
    .nil
  unless varsS == expectedVars do
    throwError "replayElim: :ELIMVARS {repr varsS} does not match the \
                records' fresh vars at {cn.idStr}"
  let restrictedAll := records.flatMap (·.restricted)
  if cn.inputClause.length < 2 then
    throwError "replayElim: singleton clause at {cn.idStr} (frontier)"
  -- round-trip: recompute EVERY output clause (each later record's guard
  -- clause + the fully-eliminated clause) and REQUIRE the emitted set.
  -- A later record whose (not (consp v)) guard literal IS in the current
  -- clause pushes NO guard child — the `(consp v) :: C` case is a tautology
  -- ACL2 drops (G1 arc 2026-07-29: the *1/3'' chained-elim shape, where
  -- record 2's guard literal σ-descended into the clause).
  let mut computed : List (List SExpr) := []
  let mut guards : Nat := 0
  let mut curC := cn.inputClause
  let mut remainingEdits := st.items.filterMap fun
    | .dedupDrop lit => some ("DEDUP-DROP", lit)
    | .complementClose lit => some ("COMPLEMENT-CLOSE", lit)
    | _ => none
  let consumeEdit (tag : String) (lit : SExpr)
      (edits : List (String × SExpr)) : MetaM (List (String × SExpr)) := do
    let (actualTag, actualLit) :: rest := edits
      | throwError "replayElim: {tag} has no recorded clause edit at {cn.idStr}"
    unless actualTag == tag && actualLit == lit do
      throwError "replayElim: expected {tag} {repr lit}, recorded {actualTag} {repr actualLit} at {cn.idStr}"
    pure rest
  let mut checkedRecords := []
  for er in records do
    let recipe := er.recipe
    let (v, v1, v2) := (er.var, er.first, er.second)
    let vT : SExpr := .atom (.symbol v)
    let carT : SExpr := .cons (.atom (.symbol { name := recipe.firstName })) (.cons vT .nil)
    let cdrT : SExpr := .cons (.atom (.symbol { name := recipe.secondName })) (.cons vT .nil)
    let uT : SExpr := .cons (.atom (.symbol { name := recipe.ctor }))
      (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil))
    -- applying a record MOVES the eliminated var's (not (consp v)) literal
    -- to the FRONT (σ-image) — erase it (first occurrence; absent for a
    -- later record's fresh var), prepend its σ-image, σ the rest
    let litV : SExpr := .cons (.atom (.symbol { name := "NOT" }))
      (.cons (.cons (.atom (.symbol { name := recipe.guardName })) (.cons vT .nil)) .nil)
    let guardPresent := curC.contains litV
    unless guardPresent do
      computed := computed ++
        [(SExpr.cons (.atom (.symbol { name := recipe.guardName })) (.cons vT .nil)) :: curC]
      guards := guards + 1
    -- APPLY-INSTANTIATED-ELIM-RULE disjoins the guard twice: first for
    -- fresh-variable selection, then for GENERALIZE1's actual input.
    -- Both calls record the duplicate when this guard is already present.
    if guardPresent then
      remainingEdits ← consumeEdit "DEDUP-DROP" litV remainingEdits
      remainingEdits ← consumeEdit "DEDUP-DROP" litV remainingEdits
    let curRest := match curC.idxOf? litV with
      | some i => curC.eraseIdx i
      | none => curC
    let effClause := litV :: curRest
    let addedLits ← elimRecordPrefix er effClause
    -- DISJOIN-CLAUSES starts with the restriction prefix, then ADD-LITERAL
    -- visits the original clause from left to right. A repeated literal
    -- keeps its prefix occurrence and drops this later occurrence.
    let drops := effClause.filter addedLits.contains
    for lit in drops do
      remainingEdits ← consumeEdit "DEDUP-DROP" lit remainingEdits
    checkedRecords := checkedRecords ++ [{er with restrictionDrops := drops}]
    curC := (addedLits ++ effClause.filter (fun lit => !drops.contains lit)).map
      (elimReplace carT cdrT vT uT v1 v2)
    -- SPLIT-ON-ASSUMPTIONS adds the positive guard to the original
    -- clause. Its recorded complement close accounts for the absent
    -- guard child; the proof below closes this same branch by the guard.
    if guardPresent then
      remainingEdits ← consumeEdit "COMPLEMENT-CLOSE"
        (.cons (.atom (.symbol {name := recipe.guardName})) (.cons vT .nil)) remainingEdits
  unless remainingEdits.isEmpty do
    throwError "replayElim: unconsumed clause edit at {cn.idStr}"
  let records := checkedRecords
  computed := computed ++ [curC]
  -- children: the fully-eliminated clause + the recomputed guard clauses
  unless cn.children.length == 1 + guards do
    throwError "replayElim: {cn.children.length} children for \
                {records.length} elim record(s) with {guards} guard \
                clause(s) at {cn.idStr} (frontier)"
  unless st.newClauses.length == 1 + guards do
    throwError "replayElim: {st.newClauses.length} output clauses for \
                {records.length} elim record(s) with {guards} guard \
                clause(s) at {cn.idStr} (frontier)"
  -- a recorded child may carry RESTRICTION-literal prefixes for the
  -- records' restricted vars (sorting-completion-2, ORDERED-PERMS *1/7:
  -- ACL2 generalizes a destructor under a type restriction and prepends
  -- `(not (pred var))` — the record names the var, the child carries the
  -- literal; its VALUE duplicates the σ-image literal's, so the replay
  -- strips it by cases at consumption)
  let isRestrictionLit : SExpr → Bool := fun l =>
    match l with
    | .cons (.atom (.symbol ns))
        (.cons (.cons (.atom (.symbol _))
          (.cons (.atom (.symbol var)) .nil)) .nil) =>
      ns.name == "NOT" && restrictedAll.contains var
    | _ => false
  let matchWithRestrictions : List SExpr → Option (List SExpr) := fun c =>
    (st.newClauses.filterMap fun nc => do
      let ncL ← nc.toList?
      let pre := ncL.take (ncL.length - c.length)
      guard (ncL.drop (ncL.length - c.length) == c)
      guard (pre.all isRestrictionLit)
      pure pre).head?
  for c in computed do
    unless (st.newClauses.any (·.toList? == some c)) ||
        (matchWithRestrictions c).isSome do
      throwError "replayElim: recomputed clause {repr c} is not among the \
                  emitted :NEWCLAUSES at {cn.idStr} (record/output divergence)"
  -- the per-level recursion
  let rec go (recs : List ElimRecord) (curClause : List SExpr)
      (cfgK : ReplayConfig) (isTop : Bool) : MetaM Expr := do
    let ctxK0 : ReplayCtx := if isTop then ctx
      else ctx.clearEnvFacts
    -- pin the level's clause opaques AGAINST THIS LEVEL'S ENV (a deeper
    -- level's fresh env has none of the outer pins)
    let ctxK ← pinTermOpaques cfg cfgK.envExpr ctxK0 (disjoinTerm curClause)
    let build : ReplayCtx → MetaM Expr := fun ctxK => do
      match recs with
      | [] =>
        let restPrefix : List SExpr :=
          (matchWithRestrictions curClause).getD []
        let target := restPrefix ++ curClause
        let some child := cn.children.find? (·.inputClause == target)
          | throwError "replayElim: no child matches the fully-eliminated \
                        clause {repr target} at {cn.idStr}"
        let ctxFresh := ctxK.clearEnvFacts
        let mut p ← rec.clause cfgK ctxFresh child
        -- STRIP each restriction literal: its value DUPLICATES a member
        -- literal's value in the remaining clause (the σ-image literal —
        -- e.g. trueListp (cons a d) = trueListp d definitionally); byCases:
        -- nil strips the head frame (transport p); non-nil closes the
        -- remaining disjunction at the duplicate member directly.
        let mut remaining := target
        for rLit in restPrefix do
          let rest := remaining.drop 1
          let ctxR ← pinTermOpaques cfg cfgK.envExpr ctxK (disjoinTerm remaining)
          let vR ← ctxValExpr { cfg with envExpr := cfgK.envExpr } ctxR rLit
          -- the duplicate member: same VALUE up to defeq
          let mut dup? : Option (Nat × SExpr) := none
          for (l, i) in rest.zipIdx do
            if dup?.isNone then
              let vL ← ctxValExpr { cfg with envExpr := cfgK.envExpr } ctxR l
              if ← Lean.Meta.isDefEq vR vL then
                dup? := some (i, l)
          let some (dupIdx, dupLit) := dup?
            | throwError "replayElim: restriction literal {repr rLit} has no \
                value-duplicate member in the eliminated clause at {cn.idStr} \
                (frontier)"
          let nilC := mkConst ``SExpr.nil
          let restT := disjoinTerm rest
          let pIn := p
          let negL ← withLocalDeclD `hnil (← mkEq vR nilC) fun hNil => do
            let hcNil ← mkAppM ``re_val_cast
              #[cfg.worldExpr, cfgK.envExpr, reflectSExpr rLit, vR, nilC,
                ← ctxValProof { cfg with envExpr := cfgK.envExpr } ctxR rLit, hNil]
            let hRest ← ctxValProof { cfg with envExpr := cfgK.envExpr } ctxR restT
            let vRest ← ctxValExpr { cfg with envExpr := cfgK.envExpr } ctxR restT
            let hIf ← mkAppM ``re_if_false
              #[cfg.worldExpr, cfgK.envExpr, reflectSExpr rLit, reflectSExpr quoteT,
                reflectSExpr restT, vRest, hcNil, hRest]
            -- evtrue_of_fuel_eq (hab : eval a ≡ eval b) (hb : EvTrue b) :
            -- EvTrue a — we HAVE the if-form (pIn) and WANT rest, so a := rest
            -- with hab := symm hIf (eval rest ≡ eval if-form)
            let pR ← mkAppM ``evtrue_of_fuel_eq
              #[← mkAppM ``fuel_eq_symm #[hIf], pIn]
            mkLambdaFVars #[hNil] pR
          let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vR, nilC]) fun hNe => do
            -- vR ≠ nil and v(dupLit) = vR (defeq) → the member is truthy
            let pOut ← evtrueOfLitTrue { cfg with envExpr := cfgK.envExpr } ctxR
              rest dupIdx dupLit hNe
            mkLambdaFVars #[hNe] pOut
          p ← (try mkAppM ``Classical.byCases #[negL, posL]
            catch e => throwError "replayElim: restriction strip compose failed \
              at {cn.idStr}: {e.toMessageData}")
          remaining := rest
        pure p
      | er :: rest =>
        let recipe := er.recipe
        let (v, v1, v2) := (er.var, er.first, er.second)
        let vT : SExpr := .atom (.symbol v)
        let carT : SExpr := .cons (.atom (.symbol { name := recipe.firstName })) (.cons vT .nil)
        let cdrT : SExpr := .cons (.atom (.symbol { name := recipe.secondName })) (.cons vT .nil)
        let uT : SExpr := .cons (.atom (.symbol { name := recipe.ctor }))
          (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil))
        let notConspLit : SExpr := .cons (.atom (.symbol { name := "NOT" }))
          (.cons (.cons (.atom (.symbol { name := recipe.guardName })) (.cons vT .nil)) .nil)
        -- the SUCCESS side's clause: erase the (not (consp v)) literal (first
        -- occurrence; absent for a later record's fresh var), REORDER it to
        -- the front, σ everything — mirroring ACL2's own clause construction
        let litIdx? := curClause.idxOf? notConspLit
        let restClause := match litIdx? with
          | some i => curClause.eraseIdx i
          | none => curClause
        let effClause := notConspLit :: restClause
        let addedLits ← elimRecordPrefix er effClause
        let restrictionClause := addedLits ++ effClause.filter
          (fun lit => !er.restrictionDrops.contains lit)
        let nextClause := restrictionClause.map (elimReplace carT cdrT vT uT v1 v2)
        let w := cfg.worldExpr
        let env := cfgK.envExpr
        let vE ← ctxValExpr cfgK ctxK vT
        let pV ← ctxValProof cfgK ctxK vT
        let conspVE := mkApp (mkConst recipe.guardValue) vE
        let nilC := mkConst ``SExpr.nil
        let conspLit : SExpr := .cons (.atom (.symbol { name := recipe.guardName }))
          (.cons vT .nil)
        -- CASE (consp v) = nil
        let negL ← withLocalDeclD `hnil (← mkEq conspVE nilC) fun hNil => do
          let p ←
            if let some litIdx := curClause.idxOf? notConspLit then do
              -- the clause's own (not (consp v)) literal is true and closes
              -- the disjunction (at its actual position — need not be first).
              -- LEVEL-GENERIC (G1 arc 2026-07-29): a later record whose guard
              -- literal σ-descended into the clause closes the same way (ACL2
              -- pushed no guard child — the tautology drop, see the recompute
              -- loop above).
              let notLit : SExpr := .cons (.atom (.symbol { name := "NOT" }))
                (.cons conspLit .nil)
              let hT ← mkAppM ``logic_not_t_of_nil #[hNil]
              let tNeNil ← proveByDecide
                (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
              let hTrue ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
              evtrueOfLitTrue cfgK ctxK curClause litIdx notLit hTrue
            else do
              -- the not-a-cons case is a pushed GUARD child
              -- `(consp v) :: curClause` — peel its false head literal.
              -- This arises for a LATER record's fresh var, and ALSO for a
              -- record whose clause simply has no (not (consp v)) literal
              -- (ORDERED-PERMS Subgoal *1/2.1: B guarded only by
              -- (NOT (TRUE-LISTP B)) — ACL2 pushes *1/2.1.2).
              let _ := isTop
              let gClause := conspLit :: curClause
              let some gChild := cn.children.find? (·.inputClause == gClause)
                | throwError "replayElim: the clause has no \
                              (not (consp {v.name})) literal and no guard \
                              child matches {repr gClause} at {cn.idStr}"
              let ctxFresh := ctxK.clearEnvFacts
              let pG ← rec.clause cfgK ctxFresh gChild
              let pNil ← mkAppM ``re_val_cast
                #[w, env, reflectSExpr conspLit, conspVE, nilC,
                  ← ctxValProof cfgK ctxK conspLit, hNil]
              mkAppM ``evtrue_extract_else #[pNil, pG]
          mkLambdaFVars #[hNil] p
        -- CASE (consp v) ≠ nil: recurse at the elim env and bridge back
        let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[conspVE, nilC]) fun hNe => do
          let queryCtx := { ctxK with branchFacts := ctxK.branchFacts ++ [(conspLit, conspVE, true, hNe)] }
          let mut restrictionProofs := []
          for r in er.restrictions.getD [] do
            let proofs ← replayElimRestriction cfgK queryCtx r
            restrictionProofs := restrictionProofs ++ proofs.filter (fun (lit, _) => addedLits.contains lit)
          unless restrictionProofs.map (·.1) == addedLits do
            throwError "replayElim: restriction proofs differ from the emitted prefix"
          let carV := mkApp (mkConst recipe.firstValue) vE
          let cdrV := mkApp (mkConst recipe.secondValue) vE
          let formalsE ← mkListLit (mkConst ``Symbol) [reflectSymbol v1, reflectSymbol v2]
          let valsE ← mkListLit (mkConst ``SExpr) [carV, cdrV]
          let env' ← mkAppM ``bindArgsOver #[env, formalsE, valsE]
          let cfg' := { cfgK with envExpr := env' }
          let pInner ← go rest nextClause cfg' false
          -- substN bridge: eval env ((disjoin C')σ) ≡ eval env' (disjoin C')
          let bodyT := disjoinTerm nextClause
          let argsS : List SExpr := [carT, cdrT]
          let argsE ← mkListLit (mkConst ``SExpr) (argsS.map reflectSExpr)
          let hWellScoped ← proveByDecide
            (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr bodyT])
                    (mkConst ``Bool.true)) "WellScoped elim child"
          let hlenPf ← proveByDecide
            (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
            "substN arg/val lengths"
          let pCar ← ctxValProof cfgK ctxK carT
          let pCdr ← ctxValProof cfgK ctxK cdrT
          let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
          let pFn ← withLocalDeclD `pr prodTy fun prV => do
            let fst ← mkAppM ``Prod.fst #[prV]
            let snd ← mkAppM ``Prod.snd #[prV]
            mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
          let entries ← (argsS.zip [carV, cdrV]).mapM fun (a, av) =>
            mkAppM ``Prod.mk #[reflectSExpr a, av]
          let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip [pCar, pCdr])
          let zipE ← mkAppM ``List.zip #[argsE, valsE]
          let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
            let mem ← mkAppM ``Membership.mem #[zipE, prV]
            mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
          let hargs ← mkExpectedTypeHint hargsRaw hargsTy
          let pBridge ← mkAppM ``evalOpt_substTerm_substN
            #[w, env, formalsE, argsE, valsE, reflectSExpr bodyT, hWellScoped, hlenPf, hargs]
          -- diff-collapse: eval env (disjoin C) ≡ eval env ((disjoin C')σ)
          let sTermS := ACL2.Replay.substTerm [v1, v2] argsS bodyT
          let uSig : SExpr := .cons (.atom (.symbol { name := recipe.ctor }))
            (.cons carT (.cons cdrT .nil))
          let hVeq ← mkAppM ``Eq.symm #[← mkAppM recipe.reassemble #[hNe]]
          let pU ← ctxValProof cfgK ctxK uSig
          let nodeEq ← mkAppM ``fuel_eq_of_conv #[pV, pU, hVeq]
          let chainOpt ← diffCollapse w env vT uSig nodeEq
            (disjoinTerm restrictionClause) sTermS
          let pAll ← chainAfter chainOpt pBridge
          let mut pEff ← mkAppM ``evtrue_of_fuel_eq #[pAll, pInner]
          if !er.restrictionDrops.isEmpty then
            pEff ← liftClauseSubset cfgK queryCtx (addedLits ++ effClause) restrictionClause pEff
          for (lit, hNil) in restrictionProofs do
            let pNil ← mkAppM ``re_val_cast
              #[w, env, reflectSExpr lit, ← ctxValExpr cfgK queryCtx lit, nilC,
                ← ctxValProof cfgK queryCtx lit, hNil]
            pEff ← mkAppM ``evtrue_extract_else #[pNil, pEff]
          -- pEff : EvTrue(disjoin (litV :: restClause)) at env. litV is FALSE
          -- under hne — peel it off the front (fuel-eq of the head frame,
          -- transported by fuel_eq_symm), then — when litV sat at position i
          -- of curClause — re-insert by the SAME frame collapse at i, lifted
          -- through the preceding frames.
          let hNotNil ← mkAppM ``not_nil_of_truthy #[hNe]
          let pLitNil ← mkAppM ``re_val_cast
            #[w, env, reflectSExpr notConspLit,
              mkApp (mkConst ``Logic.not) conspVE, nilC,
              ← ctxValProof cfgK ctxK notConspLit, hNotNil]
          let restTerm := disjoinTerm restClause
          let vRest ← ctxValExpr cfgK ctxK restTerm
          let hRest ← ctxValProof cfgK ctxK restTerm
          let _ := vRest
          let chainHead ← mkAppM ``re_if_false
            #[w, env, reflectSExpr notConspLit, reflectSExpr quoteT,
              reflectSExpr restTerm, vRest, pLitNil, hRest]
          let pRest ← mkAppM ``evtrue_of_fuel_eq
            #[← mkAppM ``fuel_eq_symm #[chainHead], pEff]
          let p ← match litIdx? with
            | none => pure pRest
            | some i => do
              if i + 1 == curClause.length then do
                -- LAST-position re-insert (final-closeout, PCE *1/1.1'):
                -- litV sits in the ELSE of the PRECEDING literal's frame —
                -- (IF b 'T litV) ⟿ (IF b 'T 'NIL) ⟿ b, the boolean-wrap
                -- collapse (boolwrapIdentFor: two-valued b only — consumed,
                -- not inferred), lifted through the earlier frames.
                let some b := (curClause.take i).getLast?
                  | throwError "replayElim: last-position reorder with no \
                      preceding literal at {cn.idStr} (frontier)"
                let litEqStep ← mkAppM ``fuel_eq_of_conv
                  #[pLitNil,
                    ← mkAppM ``re_val_quote #[w, env, reflectSExpr SExpr.nil],
                    ← mkEqRefl (mkConst ``SExpr.nil)]
                let quoteNil' : SExpr := .cons
                  (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.nil .nil)
                let tailStp : PathStep := { fn := { name := "IF" }, arity := 3,
                                            argIdx := 2, siblings := [b, quoteT] }
                let s1 ← applyStep w env tailStp notConspLit quoteNil' litEqStep
                let ctxB ← pinTermOpaques cfgK env ctxK b
                let vB ← ctxValExpr cfgK ctxB b
                let hB ← ctxValProof cfgK ctxB b
                let hident ← boolwrapIdentFor cfgK ctxB b vB
                let hwrap ← mkAppM ``re_val_if_t_nil
                  #[w, env, reflectSExpr b, vB, hB]
                let s2 ← mkAppM ``fuel_eq_of_conv #[hwrap, hB, hident]
                let mut inner ← mkAppM ``fuel_chain_eq #[s1, s2]
                let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
                  (.cons b (.cons quoteT (.cons notConspLit .nil)))
                let mut curR : SExpr := b
                for l in (curClause.take (i - 1)).reverse do
                  let stp : PathStep := { fn := { name := "IF" }, arity := 3,
                                          argIdx := 2, siblings := [l, quoteT] }
                  inner ← applyStep w env stp curL curR inner
                  curL := rebuild stp curL
                  curR := rebuild stp curR
                unless curL == disjoinTerm curClause &&
                       curR == disjoinTerm restClause do
                  throwError "replayElim: last-position reorder lift \
                      reconstructed {repr curL} / {repr curR} at {cn.idStr}"
                mkAppM ``evtrue_of_fuel_eq #[inner, pRest]
              else do
              -- eval(disjoin curClause) ≡ eval(disjoin restClause): the litV
              -- frame collapse at position i, lifted through i else-descents
              let mut inner ← mkAppM ``re_if_false
                #[w, env, reflectSExpr notConspLit, reflectSExpr quoteT,
                  reflectSExpr (disjoinTerm (curClause.drop (i + 1))),
                  ← ctxValExpr cfgK ctxK (disjoinTerm (curClause.drop (i + 1))),
                  pLitNil, ← ctxValProof cfgK ctxK (disjoinTerm (curClause.drop (i + 1)))]
              let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
                (.cons notConspLit (.cons quoteT
                  (.cons (disjoinTerm (curClause.drop (i + 1))) .nil)))
              let mut curR : SExpr := disjoinTerm (curClause.drop (i + 1))
              for l in (curClause.take i).reverse do
                let stp : PathStep := { fn := { name := "IF" }, arity := 3,
                                        argIdx := 2, siblings := [l, quoteT] }
                inner ← applyStep w env stp curL curR inner
                curL := rebuild stp curL
                curR := rebuild stp curR
              unless curL == disjoinTerm curClause &&
                     curR == disjoinTerm restClause do
                throwError "replayElim: reorder lift reconstructed \
                            {repr curL} / {repr curR} at {cn.idStr}"
              mkAppM ``evtrue_of_fuel_eq #[inner, pRest]
          mkLambdaFVars #[hNe] p
        mkAppM ``Classical.byCases #[negL, posL]
    if (recs.head?).any (fun er => er.restrictions.isSome) then
      withClauseFalsity cfgK ctxK curClause build
    else build ctxK
  go records cn.inputClause cfg true

end ACL2.Replay.Driver
