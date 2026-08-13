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

/-- The bound-formal VALUE facts for a `bindArgs formals avs` environment:
    per formal, its value expr and a proof of `∃N ∀f≥N, eval env formal =
    some av` (the `re_val_var_get` route over the positional `bindArgs`
    lookup lemmas). Shared by both provers — `proveTotality` and `proveTp`
    carried byte-identical copies differing only in the frontier message,
    and increment 4's arity-3 TP arm would have made a third (the
    de-duplication norm; `who` keeps the frontier text per-prover). -/
def bindArgsVarProofs (cfg : ReplayConfig) (who : String) (envE : Expr)
    (formals : List Symbol) (avs : List Expr) :
    MetaM (List (Symbol × Expr × Expr)) := do
  let sy := reflectSymbol
  let ne (a b : Symbol) : MetaM Expr := do
    mkDecideProof (← mkAppM ``Ne #[sy a, sy b])
  let valOf (f : Symbol) (av g : Expr) : MetaM Expr :=
    mkAppM ``re_val_var_get #[cfg.worldExpr, envE, sy f, av, g]
  match formals, avs with
  | [f], [av] =>
    let g ← mkAppM ``bindArgs_single_get_self #[sy f, av]
    return [(f, av, ← valOf f av g)]
  | [f1, f2], [av1, av2] =>
    let hne ← ne f1 f2
    let g1 ← mkAppM ``bindArgs_pair_get_fst #[sy f1, sy f2, av1, av2]
    let g2 ← mkAppM ``bindArgs_pair_get_snd #[sy f1, sy f2, av1, av2, hne]
    return [(f1, av1, ← valOf f1 av1 g1), (f2, av2, ← valOf f2 av2 g2)]
  | [f1, f2, f3], [av1, av2, av3] =>
    let g1 ← mkAppM ``bindArgs_triple_get_fst
      #[sy f1, sy f2, sy f3, av1, av2, av3]
    let g2 ← mkAppM ``bindArgs_triple_get_snd
      #[sy f1, sy f2, sy f3, av1, av2, av3, ← ne f1 f2]
    let g3 ← mkAppM ``bindArgs_triple_get_thd
      #[sy f1, sy f2, sy f3, av1, av2, av3, ← ne f1 f3, ← ne f2 f3]
    return [(f1, av1, ← valOf f1 av1 g1), (f2, av2, ← valOf f2 av2 g2),
            (f3, av3, ← valOf f3 av3 g3)]
  | _, _ =>
    throwFrontier m!"{who}: arity {formals.length} unsupported (frontier)"

/-- Prove `total:fn` (the `mkTotalityHypType` statement) from the admission
    data; throws a named-frontier error when out of the D5 scope.
    `recTerm?` (sorting arc 2026-07-28): the RECORDED-TERMINATION bundle —
    when present, the strong induction runs over the INTERPRETED count
    (`interpCount`, design I1 bookkeeping) and self-call decreases come
    from the replayed admission waterfall instead of the destructor walk. -/
def proveTotality (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (name : String) (formals : List Symbol) (body : SExpr)
    (just? : Option Justification)
    (recTerm? : Option RecTermInfo := none) : MetaM Expr := do
  let fs : Symbol := { name := name }
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) : MetaM (List (Symbol × Expr × Expr)) :=
    bindArgsVarProofs cfg "proveTotality" envE formals avs
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
    | [_, _, _] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 =>
          withLocalDeclD `av3 (mkConst ``SExpr) fun av3 => do
            let envE ← mkEnvE [av1, av2, av3]
            let vals ← varProofs envE [av1, av2, av3]
            let p ← totWalk cfg envE vals [] totalEnv none body
            mkLambdaFVars #[av1, av2, av3] p
      mkAppM ``totality_3_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol formals[0]!,
          reflectSymbol formals[1]!, reflectSymbol formals[2]!,
          reflectSExpr body, hNs, hDef, hbody]
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
    -- the induction MEASURE: `consCount` on the destructor route, the
    -- INTERPRETED count on the recorded route (μ is proof bookkeeping —
    -- design I1; the statement never mentions it). The recorded route is
    -- 1-ary ONLY for now (audit F4: at other arities the wrapper lemmas
    -- and the self-call decrease are consCount-typed, and a mismatched μ
    -- aborts UNTAGGED instead of frontiering — gate it here).
    let recTerm? := if formals.length == 1 then recTerm? else none
    let countOf (e : Expr) : MetaM Expr :=
      match recTerm? with
      | some info => mkAppM ``ACL2.Replay.interpCount
          #[cfg.worldExpr, reflectSymbol info.cntSym, e]
      | none => mkAppM ``SExpr.consCount #[e]
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
            (some (name, measuredFormal, ih, just, recTerm?)) body
          mkLambdaFVars #[av, ih] p
      match recTerm? with
      | some info =>
        let μE ← withLocalDeclD `v (mkConst ``SExpr) fun v => do
          mkLambdaFVars #[v] (← mkAppM ``ACL2.Replay.interpCount
            #[cfg.worldExpr, reflectSymbol info.cntSym, v])
        mkAppM ``totality_1_rec_mu
          #[μE, cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
            reflectSExpr body, hNs, hDef, step]
      | none =>
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
                (some (name, measuredFormal, ih, just, none)) body
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
                (some (name, measuredFormal, ih, just, none)) body
              mkLambdaFVars #[av2, ih, av1] p
        mkAppM ``totality_2_rec_snd
          #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr body, hNs, hDef, step]
      else
        throwError "proveTotality: measured formal {measuredFormal.name} is \
            not among the formals (internal)"
    | [f1, f2, f3] =>
      -- 3-ary, measured on the SECOND formal (sorting arc 2026-07-29 —
      -- FILTER/ALL-REL's `(fn x e)` shape); other positions stay frontier
      -- until a book demands them.
      unless measuredFormal == f2 do
        throwFrontier m!"proveTotality: 3-ary measured formal \
            {measuredFormal.name} is not the second formal (frontier)"
      let envEat := fun (bv cv dv : Expr) => do
        let formalsE ← mkListLit (mkConst ``Symbol)
          [reflectSymbol f1, reflectSymbol f2, reflectSymbol f3]
        let avsE ← mkListLit (mkConst ``SExpr) [bv, cv, dv]
        mkAppM ``bindArgs #[formalsE, avsE]
      let step ← withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av2]
          let inner ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
            withLocalDeclD `av3 (mkConst ``SExpr) fun av3 => do
              let envB ← envEat av1 bv av3
              let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
              mkForallFVars #[av1, av3] conv
          mkForallFVars #[bv] (← mkArrow lt inner)
        withLocalDeclD `ih ihType fun ih =>
          withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
            withLocalDeclD `av3 (mkConst ``SExpr) fun av3 => do
              let envE ← envEat av1 av2 av3
              let vals ← varProofs envE [av1, av2, av3]
              let p ← totWalk cfg envE vals [] totalEnv
                (some (name, measuredFormal, ih, just, recTerm?)) body
              mkLambdaFVars #[av2, ih, av1, av3] p
      let μE ←
        match recTerm? with
        | some info =>
          withLocalDeclD `v (mkConst ``SExpr) fun v => do
            mkLambdaFVars #[v] (← mkAppM ``ACL2.Replay.interpCount
              #[cfg.worldExpr, reflectSymbol info.cntSym, v])
        | none =>
          withLocalDeclD `v (mkConst ``SExpr) fun v => do
            mkLambdaFVars #[v] (← mkAppM ``SExpr.consCount #[v])
      mkAppM ``totality_3_rec_snd_mu
        #[μE, cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSymbol f3, reflectSExpr body, hNs, hDef,
          step]
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
    (upTo : Option String := none)
    (termReplayed : List (String × Name × List String × List SExpr) := [])
    (hypFVars : List (String × Expr) := [])
    (tpCors : List (String × SExpr) := []) :
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
  let mut purePhaseDone := false
  while progress || !purePhaseDone do
    unless progress do purePhaseDone := true
    progress := false
    let mut still : List (Symbol × List Symbol × SExpr) := []
    for (s, formals, body) in pending do
      try
        -- RECORDED-TERMINATION route (sorting arc 2026-07-28): when this
        -- defun's admission waterfall was replayed as a replayed statement, assemble
        -- the bundle (byte-checks inside; frontier keeps the fn on the
        -- destructor route's honest frontier).
        -- PHASE ordering: the recorded route only fires once the PURE
        -- routes have SATURATED (`!progress` on the previous sweep of this
        -- pass — `pending` unchanged), so its hyp-backed augmentation
        -- covers only genuinely route-less dependencies (O<), not fns a
        -- later pure pass would have proved unconditionally.
        let recTerm? ←
          match purePhaseDone, termReplayed.find? (fun (n, _, _, _) => n == s.name),
                justs.lookup s.name with
          | true, some (_, c, conds, goalLits), some just =>
            try
              pure (some (← mkRecTermInfo cfg totalEnv hypFVars tpCors just
                c conds goalLits))
            catch e =>
              unless isFrontierErr e do throw e
              pure none
          | _, _, _ => pure none
        -- HYPOTHESIS-backed totality entries for the recorded route (audit
        -- F1 follow-through): the conjunct walk must converge O</ACL2-COUNT
        -- applications whose own admissions are beyond every route (O<'s
        -- O-FIRST-EXPT decreases). The telescope OFFERS their totality —
        -- augmenting with the hyp fvars makes the resulting proof honestly
        -- CONDITIONAL on them (Stage-5's kept recompute surfaces the fvars
        -- in the theorem's cond list; the audit verified that accounting
        -- fail-closes). Recorded-route calls only — the fixpoint's normal
        -- entries stay unconditional.
        let hypBacked : String × Expr → Option (String × Nat × Expr) :=
          fun (c, fv) =>
            if c.startsWith "total:" then
              let n := (c.drop "total:".length).toString
              if totalEnv.any (fun (m, _, _) => m == n) then none
              else
                (cfg.worldVal.defs.get? { name := n }).map
                  (fun (fs, _) => (n, fs.length, fv))
            else none
        let totalEnvFor := match recTerm? with
          | none => totalEnv
          | some _ => totalEnv ++ hypFVars.filterMap hypBacked
        let pf ← proveTotality cfg totalEnvFor s.name formals body
          (justs.lookup s.name) recTerm?
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

/-- The EMITTED type-prescription corollary's CLASS — the shape of the
    value predicate `P` the TP prover builds from it. A return-path
    PRIMITIVE can only be admitted for a recognized class, because the
    Lean-side content of such a step is exactly that class's value-CLOSURE
    lemma (`tpClosure2`); an unrecognized corollary keeps the honest
    frontier. -/
inductive TpCorClass where
  /-- `(IF (INTEGERP (f …)) (NOT (< (f …) '0)) 'NIL)` — ACL2's
      `*ts-non-negative-integer*` (the emitted `:BASICTS 7`). -/
  | nonNegInt
  /-- `(CONSP (f …))` — ACL2's `*ts-cons*` (the emitted `:BASICTS 3072`). -/
  | consp
  /-- `(TRUE-LISTP (f …))` — ACL2's `*ts-true-list*` (`:BASICTS 1152`). -/
  | trueListp
  /-- `(IF (CONSP (f …)) 'T (EQUAL (f …) 'NIL))` — ACL2's
      `*ts-cons*` ∪ `*ts-nil*` (the emitted `:BASICTS 3200`), the
      "a list, possibly empty" prescription of a list-returning
      recursion (TP-replay arc increment 3). -/
  | conspOrNil
  /-- `(IF (CONSP (f …)) 'T (EQUAL (f …) <formal>))` — the ARGS-VALUED
      class (TP-replay arc increment 5): ACL2's prescription for
      `BINARY-APPEND`/`APP`, whose else-disjunct names a FORMAL, so the
      lifted predicate is indexed by that argument's VALUE
      (`mkTpHypTypeAv`'s hypothesis shape). The emitted `:BASICTS` is
      `*ts-cons*` (3072) — the corollary's TYPE-SET part; the equality
      disjunct is what covers the residue leaf (verdict `-1`), and it is
      carried by `tpArgLeafFact`, never by a mask. Which formal it is
      comes from `tpCorArgVar?`, off the emitted corollary. -/
  | conspOrArg
  deriving BEq, Repr, Inhabited

/-- ACL2's basic type-set MASK the class covers (`acl2/type-set-a.lisp`'s
    `def-basic-type-sets` bit order: 2^0 `*ts-zero*`, 2^1 `*ts-one*`, 2^2
    `*ts-integer>1*`, 2^3 positive-ratio, 2^4 negative-integer, 2^5
    negative-ratio, 2^6 complex-rational, 2^7 `*ts-nil*`, 2^8 `*ts-t*`,
    2^9 non-t-non-nil-symbol, 2^10 `*ts-proper-cons*`, 2^11
    `*ts-improper-cons*`, 2^12 string, 2^13 character). A leaf whose
    EMITTED verdict has a bit outside the mask is not covered by the
    corollary — frontier. Each mask is the ACL2 constant the corollary's
    recognizer names: `*ts-non-negative-integer*` = 0|1|2 = 7,
    `*ts-cons*` = proper|improper = 1024|2048 = 3072, `*ts-true-list*` =
    nil|proper-cons = 128|1024 = 1152, and the consp-or-nil `IF` =
    `*ts-cons*`|`*ts-nil*` = 3072|128 = 3200. -/
def TpCorClass.tsMask : TpCorClass → Int
  | .nonNegInt => 7
  | .consp => 3072
  | .trueListp => 1152
  | .conspOrNil => 3200
  | .conspOrArg => 3072

/-- Does the class's lifted predicate mention an ARGUMENT value (the
    args-valued corollaries — `mkTpHypTypeAv`'s shape)? Such a class's
    closure/leaf facts take that value as their leading parameter, and its
    hypothesis shape binds the argument values alongside the
    application's. -/
def TpCorClass.argIndexed : TpCorClass → Bool
  | .conspOrArg => true
  | _ => false

/-- Is the emitted leaf verdict `ts` inside the class's type-set `mask`?
    A NEGATIVE `ts` is a complement type-set (ACL2's `-1` = every type) and
    is never inside a finite mask. -/
def tsSubsumed (ts mask : Int) : Bool :=
  0 ≤ ts && (Nat.land ts.toNat mask.toNat == ts.toNat)

/-- The RESIDUE ARGUMENT of an args-valued corollary (TP-replay arc
    increment 5): the bare variable `Y` in
    `(IF (CONSP (f …)) 'T (EQUAL (f …) Y))`. The single matcher for that
    shape — `tpCorClass?` recognizes the class through it, and the walk
    reads the variable through it, so the two can never disagree. A
    QUOTED else-argument (`'NIL`) does not match here: it is the
    value-only `.conspOrNil` class. -/
def tpCorArgVar? (appPat cor : SExpr) : Option Symbol :=
  let app1 (f : String) (a : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a .nil)
  match cor with
  | .cons (.atom (.symbol ifS))
      (.cons c (.cons th (.cons (.cons (.atom (.symbol eqS))
        (.cons l (.cons (.atom (.symbol v)) .nil))) .nil))) =>
    if ifS.name == "IF" && eqS.name == "EQUAL" && c == app1 "CONSP" appPat
        && th == app1 "QUOTE" SExpr.t && l == appPat then some v
    else none
  | _ => none

/-- Recognize the EMITTED corollary's class. `appPat` is the fn's own
    application `(f formal…)` — the corollary's only non-constant part
    (except the args-valued class's residue formal, `tpCorArgVar?`).
    Exact-shape match: a corollary ACL2 emits in any other shape is
    unrecognized (frontier), never approximated. -/
def tpCorClass? (appPat cor : SExpr) : Option TpCorClass :=
  let app1 (f : String) (a : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a .nil)
  let app2 (f : String) (a b : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a (.cons b .nil))
  let quo (v : SExpr) : SExpr := app1 "QUOTE" v
  let ifE (c th e : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons c (.cons th (.cons e .nil)))
  if cor == ifE (app1 "INTEGERP" appPat)
      (app1 "NOT" (app2 "<" appPat (quo (.atom (.number (.int 0))))))
      (quo .nil) then some .nonNegInt
  else if cor == app1 "CONSP" appPat then some .consp
  else if cor == app1 "TRUE-LISTP" appPat then some .trueListp
  else if cor == ifE (app1 "CONSP" appPat) (quo SExpr.t)
      (app2 "EQUAL" appPat (quo .nil)) then some .conspOrNil
  else if (tpCorArgVar? appPat cor).isSome then some .conspOrArg
  else none

/-- Which ARGUMENTS of a registered return-path primitive must themselves
    satisfy the corollary predicate (TP-replay arc increment 2,
    2026-08-13). The profile is a property of the (class, primitive) PAIR,
    not of any function: `CONSP`×`CONS` constrains NEITHER argument (any
    cons is a cons), `TRUE-LISTP`×`CONS` constrains the TAIL only (the head
    is arbitrary), `NON-NEGATIVE-INTEGER`×`BINARY-+` constrains BOTH.
    Unconstrained positions still have to CONVERGE — they carry
    `TpArgAny`, discharged by the plain walk. -/
inductive TpArgProfile where
  /-- neither argument constrained -/
  | neither
  /-- the second argument only (the constructor's tail) -/
  | sndOnly
  /-- both arguments -/
  | both
  deriving BEq, Repr, Inhabited

/-- Is the FIRST argument constrained by the corollary predicate? -/
def TpArgProfile.fstConstrained : TpArgProfile → Bool
  | .both => true
  | _ => false

/-- Is the SECOND argument constrained by the corollary predicate? -/
def TpArgProfile.sndConstrained : TpArgProfile → Bool
  | .neither => false
  | _ => true

/-- Value-CLOSURE registry, (corollary class, 2-ary primitive) ↦ the
    argument-obligation PROFILE plus the Lean fact
    `∀ u v, Pa u → Pb v → P (g u v)` for that class's predicate (`Pa`/`Pb`
    being `P` at the profile's constrained positions and `TpArgAny`
    elsewhere). The driver RECOMPUTES the obligation from its own `P` and
    the profile, then type-hints the registered constant against it, so a
    drifted lift OR a mis-registered profile fails closed. -/
def tpClosure2 : List ((TpCorClass × String) × TpArgProfile × Name) :=
  [((.nonNegInt, "BINARY-+"), .both, ``ACL2.Replay.nonNegIntCor_closed_plus),
   ((.consp, "CONS"), .neither, ``ACL2.Replay.conspCor_closed_cons),
   ((.trueListp, "CONS"), .sndOnly,
    ``ACL2.Replay.trueListpCor_closed_cons),
   ((.conspOrNil, "CONS"), .neither,
    ``ACL2.Replay.conspOrNilCor_closed_cons),
   ((.conspOrArg, "CONS"), .neither,
    ``ACL2.Replay.conspOrArgCor_closed_cons)]

/-- RESIDUE-LEAF registry (TP-replay arc increment 5, 2026-08-13): for an
    ARG-INDEXED class, the Lean fact `∀ y, P y` at the residue argument's
    own value — the `Y` return leaf of `BINARY-APPEND`/`APP`, which the
    corollary covers by its EQUALITY disjunct (ACL2 emits that leaf with
    the unknown verdict `-1`, so no type-set mask applies or is used).
    The driver recomputes `P` at the bound argument value and type-hints
    the registered constant against it. -/
def tpArgLeafFact : List (TpCorClass × Name) :=
  [(.conspOrArg, ``ACL2.Replay.conspOrArgCor_at_arg)]

/-- CLASS-IMPLICATION registry (TP-replay arc increment 3, 2026-08-13):
    (callee's corollary class, position's corollary class) ↦ the Lean
    fact `∀ v, P_from v → P_to v`. A CALLEE-TP return-path step whose
    callee's emitted corollary is in the SAME class as the caller's needs
    nothing here (the predicates coincide); a callee in a STRICTLY
    STRONGER class needs exactly one such fact — e.g. `SORTFN1`'s
    consp-or-nil prescription is supplied at its `SORTFN1-INSERT` leaf by
    that callee's bare `CONSP` prescription. Both corollaries are
    EMITTED; the entry states only that our value model agrees the one
    implies the other. The driver RECOMPUTES the obligation from its own
    `P` and the callee's, type-hints the registered constant against it,
    and separately checks the classes' emitted type-set MASKS are
    contained the same way — a drifted lift or a backwards entry fails
    closed. -/
def tpClassImp : List ((TpCorClass × TpCorClass) × Name) :=
  [((.consp, .conspOrNil), ``ACL2.Replay.conspOrNilCor_of_conspCor)]

/-- CLASS-IMPLICATION registry, ARGS-VALUED callee form (TP-replay arc
    increment 5, 2026-08-13): (callee's arg-indexed class, position's
    class) ↦ the Lean fact `∀ y v, P_to y → P_from[y] v → P_to v`. The
    extra premise is the position's OWN predicate at the callee's residue
    ARGUMENT value — the driver proves it by walking that argument term
    with the same walker (never assumed), so the entry adds no type
    content beyond "our value model agrees". Mask containment is
    cross-checked exactly as for `tpClassImp`. NOTE the asymmetry with
    `tpClassImp`: there is NO identity shortcut here even when the two
    classes coincide, because an arg-indexed callee's predicate is
    indexed by the CALLEE's argument values, not the caller's — such a
    position needs its own registered entry (frontier until one exists). -/
def tpClassImpAv : List ((TpCorClass × TpCorClass) × Name) :=
  [((.conspOrArg, .conspOrNil),
    ``ACL2.Replay.conspOrNilCor_of_conspOrArgCor)]

/-- The per-function EMITTED type-prescription data the TP walk consumes on
    its return paths (TP-replay arc increment 1, 2026-08-12): the fn's
    name, ACL2's OWN `:LEAVES` enumeration (return-path leaf term + the
    type-set verdict ACL2 computed for it), and the corollary's recognized
    class. Nothing here is derived Lean-side. -/
structure TpKit where
  fnName : String
  leaves : List (SExpr × Int)
  cls : Option TpCorClass
  /-- The development's admission justifications, as the CALLER passed
      them to `proveTp` — threaded so the CALLEE-TP arm can invoke the
      prover on a callee with exactly the same data (increment 3). -/
  justs : List (String × Justification) := []
  /-- The EMITTED `:TYPE-PRESCRIPTION` corollaries (fn ↦ corollary) the
      caller offered as `tp:` hypotheses — the SAME table, so the
      CALLEE-TP arm can only consume a corollary the harness itself
      offered. Empty (the default) makes that arm a frontier. -/
  cors : List (String × SExpr) := []
  /-- The CALLEE-TP recursion stack, innermost last: the fns whose type
      prescriptions are currently being proved. A call to a fn already on
      the stack is a CYCLE (mutual/self TP dependence) and is a tagged
      frontier — the prover never loops and never assumes. -/
  seen : List String := []
  /-- The RESIDUE ARGUMENT of an args-valued corollary (increment 5) —
      `tpCorArgVar?` of the fn's OWN emitted corollary. `none` for every
      value-only class, which makes the residue-leaf arm a frontier. -/
  argVar : Option Symbol := none

/-- Does `t` occur in `u` (as `u` itself or as a subterm)? The CALLEE-TP
    arm's containment check against ACL2's emitted `:LEAVES`. -/
def sexprOccurs (t : SExpr) : SExpr → Bool
  | u@(.cons a d) => u == t || sexprOccurs t a || sexprOccurs t d
  | u => u == t

/-- ACL2'S OWN LEAF DATA — the admissibility check every return-path arm
    shares (increment 3's rule, generalized to the primitive arm in
    increment 5): a term that IS one of the fn's emitted `:LEAVES` must
    carry a verdict inside the class's type-set; a term that merely
    OCCURS INSIDE a leaf is a NESTED position, covered by the enclosing
    leaf's own check in the arm that admitted it (the args-valued callee
    step walks the residue ARGUMENT, e.g. `REV`'s `(CONS (CAR X) 'NIL)`
    inside its `(APP …)` leaf); a term in neither place is a frontier. -/
def tpEmittedLeafOk (kit : TpKit) (cls : TpCorClass) (t : SExpr) :
    MetaM Unit := do
  match kit.leaves.find? (fun (leaf, _) => leaf == t) with
  | some (_, ts) =>
    unless tsSubsumed ts cls.tsMask do
      throwFrontier m!"proveTp: emitted leaf verdict {ts} of {repr t} is \
          not inside the {repr cls} corollary class's type-set \
          {cls.tsMask} (frontier)"
  | none =>
    unless kit.leaves.any (fun (leaf, _) => sexprOccurs t leaf) do
      throwFrontier m!"proveTp: {repr t} occurs in no emitted \
          :TYPE-PRESCRIPTION leaf of {kit.fnName} (frontier)"

/-- Pin every argument term of a return-path call to a VALUE plus its
    convergence proof, then run the continuation (TP-replay arc increment
    5, 2026-08-13). A liftable argument is pinned by the DP value lift; an
    OPAQUE one (a user-fn call, e.g. `REV`'s `(REV (CDR X))`) by
    ∃-elimination over the plain totality walk — the same device the
    self-call arm uses for its non-measured argument. Needed because the
    ARGS-VALUED hypothesis shape (`mkTpHypTypeAv`) is stated at the
    argument VALUES, so a callee step must supply them. -/
partial def tpArgValues (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (args : List SExpr) (acc : List (Expr × Expr))
    (k : List (Expr × Expr) → MetaM Expr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  match args with
  | [] => k acc.reverse
  | a :: rest =>
    if totLiftable a then
      let v ← dpValExpr [] (dpValProof.dpVarVal envE varP) a
      let p ← dpValProof cfg envE [] [] varP a
      tpArgValues cfg envE vals facts totalEnv rest ((v, p) :: acc) k
    else
      let hcEx ← totWalk cfg envE vals facts totalEnv none a
      let cont ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let convTy ← mkAppM ``ConvTo
          #[cfg.worldExpr, envE, reflectSExpr a, av]
        withLocalDeclD `hcv convTy fun hcv => do
          mkLambdaFVars #[av, hcv]
            (← tpArgValues cfg envE vals facts totalEnv rest
              ((av, hcv) :: acc) k)
      mkAppM ``exists_conv_elim #[hcEx, cont]

-- THE TP PROVER (mutual since increment 3): the body walk, its call
-- arms, the CALLEE-TP arm, and `proveTp` itself — the callee arm proves
-- the CALLEE's prescription by re-entering the prover.
mutual

/-- The TP body walk: a proof of `ConvToP w envE t P` — the body converges
    to a value SATISFYING the lifted-corollary predicate `P` (the TP prover,
    lifter sprint 2026-07-06; the `memb_body_bool` route, mechanized).
    Return-path arms: quote leaves (`P` by kernel decision), `if`-splits
    (liftable or OPAQUE tests — tests need only CONVERGENCE, from the plain
    walk over `totalEnv`), self-calls (the admission-licensed strong IH),
    2-ary registered PRIMITIVES over ACL2's own emitted leaves (`kit`), and
    CALLEE calls whose own emitted type prescription supplies the position
    (`tpWalkCallee`, increment 3). Every other body shape is a tagged
    frontier (D6: the `tp:` hypothesis stays). -/
partial def tpWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (kit : TpKit) (P : Expr) (t : SExpr) : MetaM Expr := do
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
      tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      if totLiftable c then
        let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
        let hc ← dpValProof cfg envE [] [] varP c
        let toBoolVc ← mkAppM ``Logic.toBool #[vc]
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr := do
          withLocalDeclD `hb (← mkEq toBoolVc (mkConst bval)) fun hb => do
            let p ← tpWalk cfg envE vals ((c, pos, hb) :: facts)
              totalEnv self kit P branch
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
                  totalEnv self kit P branch
                mkLambdaFVars #[vc, hcv, hb] p
        let ht ← mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split_ex
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, P, hcEx, ht, he]
    else
      tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    -- RETURN-PATH PRIMITIVE (TP-replay arc increments 1–2, 2026-08-12): a
    -- 2-ary registered builtin ACL2 itself enumerated as a return-path
    -- LEAF of this fn's type prescription. ADMISSIBILITY IS ENTIRELY
    -- EMITTED — the term must be one of ACL2's `:LEAVES` and the type-set
    -- verdict ACL2 computed for it must lie inside the corollary class's
    -- type-set. The Lean side contributes only the class's value CLOSURE
    -- lemma and its ARG-OBLIGATION PROFILE; it never derives a type.
    -- Anything unregistered falls through to the call arms (self-call,
    -- else frontier).
    match dpBinary.lookup fs.name, kit.cls with
    | some (fn, cb), some cls =>
      let some (prof, closure) := tpClosure2.lookup (cls, fs.name)
        | throwFrontier m!"proveTp: return-path {fs.name} has no value-closure \
            lemma for the {repr cls} corollary class (frontier)"
      tpEmittedLeafOk kit cls t
      -- PER-ARGUMENT obligation, off the registered PROFILE: a constrained
      -- position carries `P` (the TP walk); an unconstrained one carries
      -- only `TpArgAny`, i.e. plain convergence by the totality walk — the
      -- Lean side never invents a type for it
      let argOf (constrained : Bool) (u : SExpr) : MetaM (Expr × Expr) := do
        if constrained then
          return (P, ← tpWalk cfg envE vals facts totalEnv self kit P u)
        else
          let hEx ← totWalk cfg envE vals facts totalEnv none u
          return (mkConst ``ACL2.Replay.TpArgAny, ← mkAppM ``convP_any #[hEx])
      let (pA, pa) ← argOf prof.fstConstrained a
      let (pB, pb) ← argOf prof.sndConstrained b
      let hNs ← proveNotSpecial fs
      let hNo ← proveNoShadow cfg fs
      -- the CLOSURE obligation, RECOMPUTED from the driver's own `P` and
      -- the profile's per-argument predicates — a registered lemma that
      -- does not state exactly this (wrong class, or a profile claiming
      -- more/less than the lemma proves) fails here
      let clTy ← withLocalDeclD `u (mkConst ``SExpr) fun u =>
        withLocalDeclD `v (mkConst ``SExpr) fun v => do
          let pg := (mkApp P (mkApp2 (mkConst fn) u v)).headBeta
          mkForallFVars #[u, v]
            (← mkArrow (mkApp pA u).headBeta
              (← mkArrow (mkApp pB v).headBeta pg))
      -- an ARG-INDEXED class's facts take the residue argument's VALUE as
      -- their leading parameter (increment 5); the type hint below is
      -- still the whole check
      let closureE ←
        if cls.argIndexed then
          let some (av, _) := kit.argVar.bind varP
            | throwFrontier m!"proveTp: the {repr cls} residue argument has \
                no bound value in {kit.fnName}'s walk (frontier)"
          pure (mkApp (mkConst closure) av)
        else pure (mkConst closure)
      let hcl ← mkExpectedTypeHint closureE clTy
      return ← mkAppM ``convP_builtin2
        #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a,
          reflectSExpr b, mkConst fn, P, pA, pB, hNs, hNo, mkConst cb,
          hcl, pa, pb]
    | _, _ => tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .atom (.symbol vsym) =>
    -- RESIDUE-ARGUMENT LEAF (TP-replay arc increment 5, 2026-08-13):
    -- `BINARY-APPEND`/`APP` return their second argument `Y` on the
    -- base path, and ACL2's own corollary covers exactly that leaf by
    -- its EQUALITY disjunct `(EQUAL (fn X Y) Y)` — which is why the
    -- emitted verdict there is the unknown `-1` and no mask applies.
    -- ADMISSIBILITY IS EMITTED: the variable must BE the corollary's
    -- residue argument (`tpCorArgVar?` of the fn's own corollary) and
    -- must be one of ACL2's enumerated `:LEAVES`. Any other return-path
    -- variable is a frontier.
    let some cls := kit.cls
      | throwFrontier m!"proveTp: return-path variable {vsym.name} under an \
          UNRECOGNIZED corollary class for {kit.fnName} (frontier)"
    let some leafFact := tpArgLeafFact.lookup cls
      | throwFrontier m!"proveTp: the {repr cls} corollary class has no \
          residue-leaf fact — a return-path variable {vsym.name} is not \
          covered by it (frontier)"
    unless kit.argVar == some vsym do
      throwFrontier m!"proveTp: return-path variable {vsym.name} is not \
          {kit.fnName}'s corollary residue argument (frontier)"
    unless kit.leaves.any (fun (leaf, _) => leaf == t) do
      throwFrontier m!"proveTp: {repr t} is not an emitted \
          :TYPE-PRESCRIPTION leaf of {kit.fnName} (frontier)"
    let some (av, hav) := varP vsym
      | throwFrontier m!"proveTp: residue argument {vsym.name} has no bound \
          value (frontier)"
    -- RECOMPUTED against the driver's own `P` at that value
    let hP ← mkExpectedTypeHint (mkApp (mkConst leafFact) av)
      (mkApp P av).headBeta
    -- every implicit given (the predicate is higher-order: inference from
    -- `hP`'s concrete type alone would mis-solve `P`/`v`)
    return ← mkAppOptM ``convP_of_val
      #[cfg.worldExpr, envE, reflectSExpr t, P, av, hP, hav]
  | _ => tpWalkCall cfg envE vals facts totalEnv self kit P t
/-- Call arms: the SELF-call via the strong IH; a call to ANOTHER
    function via that callee's own type prescription (`tpWalkCallee`);
    everything else a frontier. -/
partial def tpWalkCall (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (kit : TpKit) (P : Expr) (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  let .cons (.atom (.symbol fs)) argsSpine := t
    | throwFrontier m!"proveTp: body shape {repr t} unsupported (frontier)"
  let args := (argsSpine.toList?).getD []
  -- NOT the self-call: the only admissible route is the CALLEE's OWN
  -- emitted type prescription (increment 3). Reachable from a
  -- non-recursive body too — `self` is consulted only to recognize the
  -- self-call, never to license the callee route.
  let isSelfCall : Bool := match self with
    | some (selfName, _, _, _) => fs.name == selfName
    | none => false
  unless isSelfCall do
    return ← tpWalkCallee cfg envE vals facts totalEnv kit P t fs args
  let some (selfName, measuredFormal, ih, just) := self
    | throwFrontier m!"proveTp: call to {fs.name} on the return path of a \
        non-recursive body (frontier)"
  unless fs.name == selfName do
    throwFrontier m!"proveTp: return-path call to {fs.name} (not the \
        self-call) unsupported (frontier)"
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
    | [f1, f2, f3], [a1, a2, a3] =>
      -- 3-ary self-call (TP-replay arc increment 4, 2026-08-13):
      -- `(ALL-REL FN (CDR X) E)` / `(ZIP3 (CDR X) (CDR Y) (CDR Z))`. The
      -- IH's argument order is (measured value, decrease, the remaining
      -- values in FORMAL order) — the `tp_3_rec`/`tp_3_rec_snd` shape,
      -- mirroring `proveTotality`'s 3-ary scaffold. A non-measured
      -- argument that is not liftable is a frontier here (the 2-ary
      -- opaque ∃-elimination has no 3-ary customer yet).
      let vals3 ← [a1, a2, a3].mapM fun a => do
        unless totLiftable a do
          throwFrontier m!"proveTp: 3-ary self-call argument {repr a} not \
              liftable (frontier)"
        let v ← dpValExpr [] (dpValProof.dpVarVal envE varP) a
        let p ← dpValProof cfg envE [] [] varP a
        pure (v, p)
      let vs := vals3.map (·.1)
      let ps := vals3.map (·.2)
      let others := (List.range 3).filter (· != mIdx)
      let hbody ← mkAppM' ih (#[vs[mIdx]!, dec] ++ (others.map (vs[·]!)).toArray)
      return ← mkAppM ``convP_defn_3
        #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1,
          reflectSExpr a2, reflectSExpr a3, vs[0]!, vs[1]!, vs[2]!,
          reflectSymbol f1, reflectSymbol f2, reflectSymbol f3,
          reflectSExpr body, P, hNs, hDef, ps[0]!, ps[1]!, ps[2]!, hbody]
    | _, _ =>
      throwFrontier m!"proveTp: self-call arity {args.length} unsupported \
          (frontier)"

/-- The CALLEE-TP return-path arm (TP-replay arc increment 3, 2026-08-13):
    a return-path call to a function OTHER than the one whose prescription
    is being proved — `SORTFN1`'s `(SORTFN1-INSERT (CAR X) (SORTFN1 (CDR X)))`
    leaf, or the `BINARY-+` summand `(HOW-MANY-SMALLER (CAR X) (CDR X))`
    inside `BNEXT-SIZE`'s. ADMISSIBILITY IS ENTIRELY EMITTED:
    * the callee is a world fn with its OWN emitted `:TYPE-PRESCRIPTION`
      corollary (`kit.cors` — the caller's own offer table), in a
      recognized class;
    * that class either IS the position's class, or IMPLIES it by a
      registered `tpClassImp` fact whose direction is cross-checked
      against ACL2's own emitted type-set masks;
    * the call OCCURS in ACL2's `:LEAVES` enumeration for the fn being
      proved and — when the call IS one of those leaves — the verdict
      ACL2 computed for it lies inside the position class's type-set (a
      NESTED position is covered by the enclosing leaf's own check, in
      the arm that admitted it).
    The P-fact is not assumed: the prover runs RECURSIVELY on the callee
    (cycle-guarded by `kit.seen`, with the caller's own justification and
    totality data), so the callee's prescription is proved from ITS body
    and ITS emitted corollary by exactly this machinery. The call's
    CONVERGENCE is the plain totality walk. -/
partial def tpWalkCallee (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (kit : TpKit) (P : Expr) (t : SExpr) (fs : Symbol) (args : List SExpr) :
    MetaM Expr := do
  let some cls := kit.cls
    | throwFrontier m!"proveTp: return-path call to {fs.name} under an \
        UNRECOGNIZED corollary class for {kit.fnName} (frontier)"
  let some (gFormals, _) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: return-path call to {fs.name}, which is not \
        a world fn (frontier)"
  unless args.length == gFormals.length do
    throwFrontier m!"proveTp: return-path call arity mismatch {repr t} \
        (frontier)"
  let some gcor := kit.cors.lookup fs.name
    | throwFrontier m!"proveTp: {fs.name} has no emitted \
        :TYPE-PRESCRIPTION corollary (frontier)"
  let gAppPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((gFormals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let some gcls := tpCorClass? gAppPat gcor
    | throwFrontier m!"proveTp: {fs.name}'s emitted corollary {repr gcor} is \
        not a recognized class (frontier)"
  -- ACL2'S OWN LEAF DATA (shared with the primitive arm)
  tpEmittedLeafOk kit cls t
  -- CYCLE GUARD: never re-enter a prescription already on the stack
  if kit.seen.contains fs.name then
    throwFrontier m!"proveTp: CYCLE in the callee-TP chain {kit.seen} → \
        {fs.name} (frontier)"
  -- the direction check both implication registries share: a registered
  -- entry whose direction ACL2's own emitted type-set masks contradict is
  -- refused
  let checkedImp (reg : List ((TpCorClass × TpCorClass) × Name)) :
      MetaM Name := do
    let some n := reg.lookup (gcls, cls)
      | throwFrontier m!"proveTp: {fs.name}'s corollary class {repr gcls} \
          neither matches nor implies the {repr cls} class \
          {kit.fnName}'s prescription needs (frontier)"
    unless tsSubsumed gcls.tsMask cls.tsMask do
      throwFrontier m!"proveTp: registered class implication {repr gcls} ⇒ \
          {repr cls} contradicts the emitted type-set masks \
          ({gcls.tsMask} not inside {cls.tsMask}) (frontier)"
    pure n
  let hEx ← totWalk cfg envE vals facts totalEnv none t
  if gcls.argIndexed then
    -- ARGS-VALUED CALLEE (TP-replay arc increment 5, 2026-08-13):
    -- `REV`'s `(APP (REV (CDR X)) (CONS (CAR X) 'NIL))` leaf. The callee's
    -- own prescription is the args-valued shape — "a cons, OR the residue
    -- ARGUMENT's value" — so the position's predicate follows only once it
    -- holds of that argument's value too. That premise is PROVED, by
    -- walking the residue argument under the position's own predicate
    -- (the same walker, the same registries); nothing is assumed about it.
    let some gArgVar := tpCorArgVar? gAppPat gcor
      | throwFrontier m!"proveTp: {fs.name}'s corollary is arg-indexed but \
          its residue argument does not resolve (frontier)"
    let some gArgIdx := gFormals.findIdx? (· == gArgVar)
      | throwFrontier m!"proveTp: {fs.name}'s residue argument \
          {gArgVar.name} is not one of its formals (frontier)"
    let impName ← checkedImp tpClassImpAv
    let gTp ← proveTp cfg totalEnv kit.justs fs.name gcor
      (cors := kit.cors) (seen := kit.seen) (argValued := true)
    tpArgValues cfg envE vals facts totalEnv args [] fun avs => do
      let (yv, hyConv) := avs[gArgIdx]!
      -- the POSITION's predicate at the residue argument's value
      let hresWalk ← tpWalk cfg envE vals facts totalEnv none kit P
        args[gArgIdx]!
      let hresY ← mkAppM ``convP_at_val #[hresWalk, hyConv]
      let hP ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
        let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr t) vV
        withLocalDeclD `hc convTy fun hc => do
          let inst := mkAppN gTp
            (#[envE] ++ (args.map reflectSExpr).toArray ++
             (avs.map (·.1)).toArray ++ #[vV] ++
             (avs.map (·.2)).toArray ++ #[hc])
          let body := mkAppN (mkConst impName) #[yv, vV, hresY, inst]
          mkLambdaFVars #[vV, hc]
            (← mkExpectedTypeHint body (mkApp P vV).headBeta)
      return mkAppN (mkConst ``ACL2.Replay.convP_of_conv_ex)
        #[cfg.worldExpr, envE, reflectSExpr t, P, hEx, hP]
  else
    -- CLASS MATCH: same class, or a registered implication whose direction
    -- ACL2's own emitted type-set masks confirm
    let imp? : Option Name ←
      if gcls == cls then pure none else pure (some (← checkedImp tpClassImp))
    let gTp ← proveTp cfg totalEnv kit.justs fs.name gcor
      (cors := kit.cors) (seen := kit.seen)
    -- the position's obligation, RECOMPUTED from the driver's own `P`:
    -- `∀ v, (the call converges to v) → P v`. A callee proof of the wrong
    -- statement, or a class implication that does not close the gap, fails
    -- at this type hint (kernel-backed at `Meta.check`).
    let hP ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr t) vV
      withLocalDeclD `hc convTy fun hc => do
        let inst := mkAppN gTp
          (#[envE] ++ (args.map reflectSExpr).toArray ++ #[vV, hc])
        let body := match imp? with
          | none => inst
          | some n => mkApp2 (mkConst n) vV inst
        mkLambdaFVars #[vV, hc]
          (← mkExpectedTypeHint body (mkApp P vV).headBeta)
    return mkAppN (mkConst ``ACL2.Replay.convP_of_conv_ex)
      #[cfg.worldExpr, envE, reflectSExpr t, P, hEx, hP]

/-- Prove `tp:fn` (the `mkTpHypType` statement) from the fn's body and its
    EMITTED `:TYPE-PRESCRIPTION` corollary — the TP prover. The corollary is
    CONSUMED (ACL2's emitted type fact — never inferred); the walk proves the
    body's value satisfies it; argument strictness + determinism pin every
    convergence value (`tp_hyp_*_of_body`). Frontier failures are tagged
    (D6: the hypothesis stays visible).
    `seen` is the CALLEE-TP recursion stack (increment 3): the prescriptions
    already being proved further up. An empty stack is the ordinary entry
    point; `tpWalkCallee` re-enters with the caller's stack, and a fn that
    is already on it is a cycle (frontier, never an assumption).
    `argValued` (increment 5) targets the ARGS-VALUED hypothesis shape
    instead (`mkTpHypTypeAv`): the corollary's bare-formal occurrences —
    `BINARY-APPEND`'s `(EQUAL (BINARY-APPEND X Y) Y)` disjunct — lift to
    the ARGUMENT VALUES, so the predicate is built under the walk's own
    argument binders and the assembly is the `*_av` lemma family. -/
partial def proveTp (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (justs : List (String × Justification))
    (name : String) (cor : SExpr)
    (cors : List (String × SExpr) := []) (seen : List String := [])
    (argValued : Bool := false) :
    MetaM Expr := do
  let fs : Symbol := { name := name }
  let some (formals, body) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: {name} not defined in the world (frontier)"
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  -- P := fun v => <corollary, (fn formals…) ↦ v, value-lifted> = SExpr.t —
  -- EXACTLY mkTpHypType's conclusion, so the proof inhabits the offered
  -- type. In the ARGS-VALUED mode a bare FORMAL occurrence lifts to that
  -- argument's bound VALUE instead of frontiering — exactly
  -- `mkTpHypTypeAv`'s lift, so `mkP avs` at the walk's binders IS the
  -- offered hypothesis's predicate at those arguments.
  let appPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let mkP (avs : List Expr) : MetaM Expr :=
    withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let lifted ← dpValExpr [(appPat, vV)]
        (fun s => do
          unless argValued do
            throwFrontier m!"proveTp: corollary of {name} mentions the \
                free variable {s.name} outside the application (frontier)"
          let some i := formals.findIdx? (· == s)
            | throwFrontier m!"proveTp: corollary of {name} mentions the \
                free variable {s.name} outside the application/formals \
                (frontier)"
          let some e := avs[i]?
            | throwFrontier m!"proveTp: corollary of {name} mentions the \
                formal {s.name}, which has no bound argument value here \
                (frontier)"
          pure e) cor
      mkLambdaFVars #[vV] (← mkEq lifted (mkConst ``SExpr.t))
  -- the EMITTED return-path data this fn's walk may consume: ACL2's own
  -- `:LEAVES` (leaf term + type-set verdict) and the corollary's class
  let kit : TpKit :=
    { fnName := name, leaves := (cfg.tpLeaves.lookup name).getD []
      cls := tpCorClass? appPat cor
      justs := justs, cors := cors, seen := name :: seen
      argVar := if argValued then tpCorArgVar? appPat cor else none }
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) :
      MetaM (List (Symbol × Expr × Expr)) :=
    bindArgsVarProofs cfg "proveTp" envE formals avs
  -- the D5 admission scope shared by both modes: `o<` on
  -- `(acl2-count <single measured formal>)`
  let measuredOf (just : Justification) : MetaM Symbol := do
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
    pure measuredFormal
  if argValued then
    -- THE ARGS-VALUED ASSEMBLY (increment 5). Only the shape the corpus
    -- demands is covered — 2-ary, recursive, measured on the FIRST formal
    -- (`BINARY-APPEND`/`APP`); anything else keeps the honest frontier.
    let some just := justs.lookup name
      | throwFrontier m!"proveTp: args-valued {name} is not recursive \
          (frontier)"
    let measuredFormal ← measuredOf just
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.consCount #[e]
    match formals with
    | [f1, f2] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTp: args-valued 2-ary measured formal \
            {measuredFormal.name} is not the first formal (frontier)"
      let Pav ← withLocalDeclD `u0 (mkConst ``SExpr) fun u0 =>
        withLocalDeclD `u1 (mkConst ``SExpr) fun u1 => do
          mkLambdaFVars #[u0, u1] (← mkP [u0, u1])
      let step ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
          let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
            let ty ← mkAppM ``ConvToP #[cfg.worldExpr, ← mkEnvE [bv, cv],
              reflectSExpr body, ← mkP [bv, cv]]
            mkForallFVars #[cv] ty
          mkForallFVars #[bv] (← mkArrow lt inner)
        withLocalDeclD `ih ihType fun ih =>
          withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
            let envE ← mkEnvE [av1, av2]
            let vals ← varProofs envE [av1, av2]
            let p ← tpWalk cfg envE vals [] totalEnv
              (some (name, measuredFormal, ih, just)) kit (← mkP [av1, av2])
              body
            mkLambdaFVars #[av1, ih, av2] p
      let hbody ← mkAppM ``tp_2_rec_av
        #[reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, Pav, step]
      return ← mkAppM ``tp_hyp_2_av_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, Pav, hNs, hDef, hbody]
    | _ =>
      throwFrontier m!"proveTp: args-valued arity {formals.length} \
          unsupported (frontier)"
  -- the VALUE-ONLY predicate (`mkTpHypType`'s): built with no argument
  -- values in scope, so a bare-formal occurrence is the honest frontier
  let P ← mkP []
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
        let p ← tpWalk cfg envE vals [] totalEnv none kit P body
        mkLambdaFVars #[av] p
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let envE ← mkEnvE [av1, av2]
          let vals ← varProofs envE [av1, av2]
          let p ← tpWalk cfg envE vals [] totalEnv none kit P body
          mkLambdaFVars #[av1, av2] p
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTp: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope, as in proveTotality)
    let measuredFormal ← measuredOf just
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
          let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
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
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
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
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
                mkLambdaFVars #[av2, ih, av1] p
        else
          -- (unreached: the 2-ary arm's measured formal is f1 or f2 by
          -- construction) — TAGGED like proveTotality's twin, so a future
          -- reachable path keeps the hypothesis instead of aborting
          throwFrontier m!"proveTp: measured formal not among the formals \
              (frontier)"
      let recLemma :=
        if measuredFormal == f1 then ``tp_2_rec else ``tp_2_rec_snd
      let hbody ← mkAppM recLemma
        #[reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2, f3] =>
      -- 3-ary (TP-replay arc increment 4, 2026-08-13): the measured
      -- formal's POSITION is read off the emitted justification, never
      -- special-cased — `ZIP3` is measured on its first formal, `ALL-REL`
      -- and `FILTER` on their second (the `(fn x e)` shape). The third
      -- position has no corpus customer and stays a tagged frontier.
      let mIdx3 := [f1, f2, f3].findIdx (· == measuredFormal)
      let others := (List.range 3).filter (· != mIdx3)
      let step ←
        if mIdx3 ≥ 2 then
          throwFrontier m!"proveTp: 3-ary measured formal \
              {measuredFormal.name} is not the first or second formal \
              (frontier)"
        else
          withLocalDeclD `avm (mkConst ``SExpr) fun avm => do
            let envAt := fun (mv o1 o2 : Expr) => do
              let avs := (List.range 3).map fun i =>
                if i == mIdx3 then mv else if i == others[0]! then o1 else o2
              mkEnvE avs
            let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf avm]
              let inner ← withLocalDeclD `ov1 (mkConst ``SExpr) fun ov1 =>
                withLocalDeclD `ov2 (mkConst ``SExpr) fun ov2 => do
                  mkForallFVars #[ov1, ov2]
                    (← mkConvToPTy (← envAt bv ov1 ov2))
              mkForallFVars #[bv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
                withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
                  let envE ← envAt avm av1 av2
                  let avs := (List.range 3).map fun i =>
                    if i == mIdx3 then avm
                    else if i == others[0]! then av1 else av2
                  let vals ← varProofs envE avs
                  let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
                  mkLambdaFVars #[avm, ih, av1, av2] p
      let recLemma := if mIdx3 == 0 then ``tp_3_rec else ``tp_3_rec_snd
      let hbody ← mkAppM recLemma
        #[reflectSymbol f1, reflectSymbol f2, reflectSymbol f3,
          reflectSExpr body, cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_3_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSymbol f3, reflectSExpr body, P, hNs,
          hDef, hbody]
    | _ => throwFrontier m!"proveTp: recursive arity {formals.length} \
        unsupported (frontier)"

end

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
    Entry: rule name ↦ (the constant, the primitives' no-shadow fns, in
    the constant's hypothesis order). A ground-zero rule name can never
    collide with a user rule — ACL2 refuses the redefinition at
    admission. -/
def d5GzRules : List (String × Name × List String) :=
  [("LEXORDER-REFLEXIVE",  (``gz_rule_lexorder_reflexive,  ["LEXORDER"])),
   ("LEXORDER-TRANSITIVE", (``gz_rule_lexorder_transitive, ["LEXORDER"])),
   ("DEFAULT-CAR",         (``gz_rule_default_car,
                            ["CAR", "CONSP", "NOT"])),
   ("DEFAULT-CDR",         (``gz_rule_default_cdr,
                            ["CDR", "CONSP", "NOT"])),
   ("CONS-CAR-CDR",        (``gz_rule_cons_car_cdr,
                            ["CONSP", "CAR", "CDR", "CONS"])),
   ("FOLD-CONSTS-IN-+",    (``gz_rule_fold_consts_in_plus, ["BINARY-+"]))]

/-- Discharge a GROUND-ZERO rule's `rule:<name>` hypothesis by its D5
    prelude constant: instantiate at the theorem's world + the primitives'
    no-shadow facts, then type-hint against the hypothesis type built FROM
    THE EMITTED SPEC (`mkRuleHypType`) — a drifted emission or a mis-stated
    constant fails here (fail-closed recompute-check, kernel-backed at
    `Meta.check`). -/
def dischargeGzRuleHyp (cfg : ReplayConfig) (spec : RuleSpec) (decl : Name)
    (noShadowFns : List String) : MetaM Expr := do
  let mut e := mkApp (mkConst decl) cfg.worldExpr
  for fn in noShadowFns do
    e := mkApp e (← proveNoShadow cfg { name := fn })
  mkExpectedTypeHint e (← mkRuleHypType cfg spec)

/-- D1 REPLAYED REGISTRY (design §D1, WP4): replayed theorems as per-theorem
    Lean CONSTANTS. Entry: theorem name ↦ (the `addDecl`'d constant — type
    `∀ env, <kept-condition telescope> → EvTrue w ⟪Goal⟫` — and its kept
    condition strings, `total:`/`tp:`/`rule:` in telescope order).
    `dischargeRuleHyp` APPLIES the constant instead of re-replaying the
    dependency's tree per consumer — the kernel checks each proof once and a
    reference is O(1), collapsing the multiplicative dependency-tree blowup
    (the ≈557M-node perm-equivalence precedent, design §4). -/
abbrev ReplayedRegistry := List (String × Name × List String)

/-- Macro-side D1 registry (P3, the capstone-mirror finding): each
    `driver_replayed%` invocation registers its enclosing definition
    (world, ACL2 theorem name, decl, kept conds) so LATER same-world
    invocations' dependency discharges APPLY the constant instead of
    re-replaying the tree — parity with the runner's ReplayedStatements
    route. The re-replay route can frontier where the standalone replay
    was green (TRUE-LISTP-RM inside the ORDERED-PERMS telescope); the
    registry route maps the dep's kept conds onto the consumer's own
    telescope fvars (`depReplayedProofAt`). Lives here (upstream) because
    an `initialize` cannot be evaluated in its defining module. -/
initialize replayedRegistryExt :
    Lean.SimplePersistentEnvExtension
      (Name × String × Name × List String)
      (List (Name × String × Name × List String)) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun l e => e :: l
    addImportedFn := fun ess => (ess.map (·.toList)).toList.flatten }

end ACL2.Replay.Driver
