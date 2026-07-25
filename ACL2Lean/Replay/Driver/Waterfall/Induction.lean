/-
  Driver/Waterfall/Induction — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The INDUCTION processor (scheme replay, IH solidify, measure decrease) —
  the home of the #37 decrease-fragment rework.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ### ACL2's induction clean-up mirror — `remove-trivial-clauses`
    (induct.lisp:6778 → `trivial-clause-p`, simplify.lisp:6808):
    `member 'T` ∨ (`possible-trivial-clause-p` ∧ `tautologyp (disjoin cl)`),
    where `tautologyp` (rewrite.lisp:5908) expands a fixed boot-strap
    non-rec fn list and runs `if-tautologyp` — pure propositional truth over
    the IF/NOT/QUOTE skeleton, every other application an OPAQUE atom,
    EQUAL/IFF resolved up to argument commutation. Pure RECOMPUTE logic (like
    `dumbNegateLit`/`substTerm`): any divergence from ACL2 is caught loudly
    by the scheme-set count/containment validation, never silent. -/

/-- The fn-name gate of `possible-trivial-clause-p` (simplify.lisp:6779),
    verbatim (ACL2's own comment: the `tautologyp` expansion list plus IF and
    NOT). -/
def tautGateFns : List String :=
  ["IF", "NOT", "IFF", "IMPLIES", "EQ", "ATOM", "EQL", "=", "/=", "NULL",
   "ZEROP", "PLUSP", "MINUSP", "LISTP", "MV-LIST", "CONS-WITH-HINT",
   "RETURN-LAST", "WORMHOLE-EVAL", "FORCE", "CASE-SPLIT", "DOUBLE-REWRITE"]

/-- Does the term mention one of `fns` in function position (quote-guarded)? —
    `ffnnamesp`. -/
partial def mentionsFn (fns : List String) : SExpr → Bool
  | .cons (.atom (.symbol s)) argSpine =>
    if s.name == "QUOTE" then false
    else fns.contains s.name ||
      ((argSpine.toList?).getD []).any (mentionsFn fns)
  | _ => false

private def ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))
private def notT (x : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "NOT" })) (.cons x .nil)
private def equalT (x y : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "EQUAL" })) (.cons x (.cons y .nil))

/-- Boot-strap body of `tautologyp`'s `expand-some-non-rec-fns` list — the
    COMMON entries (axioms.lisp definitions). An unlisted fn stays
    unexpanded: the check can then only UNDER-drop (keep a clause ACL2
    dropped), surfaced by the scheme-count mismatch — never silent, never
    over-dropping. -/
def tautExpandBody? (fn : String) (args : List SExpr) : Option SExpr :=
  match fn, args with
  | "IMPLIES", [p, q] => some (ifT p (ifT q quoteT quoteNil) quoteT)
  | "IFF", [p, q] => some (ifT p (ifT q quoteT quoteNil) (ifT q quoteNil quoteT))
  | "EQ", [x, y] => some (equalT x y)
  | "EQL", [x, y] => some (equalT x y)
  | "=", [x, y] => some (equalT x y)
  | "/=", [x, y] => some (notT (equalT x y))
  | "NULL", [x] => some (equalT x quoteNil)
  | "ATOM", [x] =>
    some (notT (.cons (.atom (.symbol { name := "CONSP" })) (.cons x .nil)))
  | "ZEROP", [x] =>
    -- zerop's bbody is `(eql x 0)` (axioms.lisp:7286) and ACL2's expansion is
    -- SINGLE-PASS: the introduced EQL stays unexpanded and is OPAQUE to
    -- if-tautologyp (only EQUAL/IFF commute) — audit 2026-07-22 finding;
    -- emitting EQUAL here would be strictly more permissive than ACL2
    some (.cons (.atom (.symbol { name := "EQL" }))
      (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
        (.cons (.atom (.number (.int 0))) .nil)) .nil)))
  | "SYNP", [_, _, _] => some quoteT
  | "FORCE", [x] => some x
  | "CASE-SPLIT", [x] => some x
  | "DOUBLE-REWRITE", [x] => some x
  | "RETURN-LAST", [_, _, x] => some x
  | "MV-LIST", [_, x] => some x
  | _, _ => none

/-- `expand-some-non-rec-fns` over the list above (args first, then body). -/
partial def tautExpand : SExpr → SExpr
  | t@(.cons (.atom (.symbol s)) argSpine) =>
    if s.name == "QUOTE" then t
    else
      let args := ((argSpine.toList?).getD []).map tautExpand
      match tautExpandBody? s.name args with
      | some b => b
      | none => .cons (.atom (.symbol s)) (args.foldr SExpr.cons .nil)
  | t => t

/-- Atom identity up to EQUAL/IFF argument commutation (`if-tautologyp`'s
    "Boolean commutative interpretations for EQUAL and IFF"). -/
def tautAtomEq (a b : SExpr) : Bool :=
  a == b ||
  (match a, b with
   | .cons (.atom (.symbol f1)) (.cons x1 (.cons y1 .nil)),
     .cons (.atom (.symbol f2)) (.cons x2 (.cons y2 .nil)) =>
     f1.name == f2.name && (f1.name == "EQUAL" || f1.name == "IFF") &&
     x1 == y2 && y1 == x2
   | _, _ => false)

/-- `if-tautologyp` mirror (rewrite.lisp:5852): `some true` = tautology,
    `some false` = not, `none` = fuel exhausted (treated as NOT a tautology
    by the caller — under-dropping only, loudly caught). Fuel-bounded like
    the original's 100000 if-interp step limit. -/
def ifTaut : Nat → List (SExpr × Bool) → SExpr → Option Bool
  | 0, _, _ => none
  | fuel + 1, ctx, t =>
    let lookupAtom (a : SExpr) : Option Bool :=
      (ctx.find? (fun (x, _) => tautAtomEq x a)).map (·.2)
    let atomVal (a : SExpr) : Option Bool :=
      some ((lookupAtom a).getD false)   -- unknown atom may be nil: not taut
    -- branch on an OPAQUE-atom test: resolve from ctx, else both ways
    let splitOn (a b c : SExpr) : Option Bool :=
      match lookupAtom a with
      | some true => ifTaut fuel ctx b
      | some false => ifTaut fuel ctx c
      | none =>
        match ifTaut fuel ((a, true) :: ctx) b,
              ifTaut fuel ((a, false) :: ctx) c with
        | some tb, some tc => some (tb && tc)
        | _, _ => none
    match t with
    | .cons (.atom (.symbol q)) (.cons c .nil) =>
      if q.name == "QUOTE" then some (c != SExpr.nil)
      else if q.name == "NOT" then ifTaut fuel ctx (ifT c quoteNil quoteT)
      else atomVal t
    | .cons (.atom (.symbol f)) (.cons a (.cons b (.cons c .nil))) =>
      if f.name == "IF" then
        match a with
        | .cons (.atom (.symbol qa)) (.cons k .nil) =>
          if qa.name == "QUOTE" then
            ifTaut fuel ctx (if k != SExpr.nil then b else c)
          else if qa.name == "NOT" then
            ifTaut fuel ctx (ifT k c b)
          else splitOn a b c
        | .cons (.atom (.symbol fa)) (.cons a1 (.cons b1 (.cons c1 .nil))) =>
          if fa.name == "IF" then
            -- distribute a nested test: (IF (IF a1 b1 c1) b c)
            -- ≡ (IF a1 (IF b1 b c) (IF c1 b c))
            ifTaut fuel ctx (ifT a1 (ifT b1 b c) (ifT c1 b c))
          else splitOn a b c
        | _ => splitOn a b c
      else atomVal t
    | t => atomVal t

/-- Replay an INDUCTION pool-root from its EMITTED justification
    (REWIRED at J2 — induction-generality design §I1–I5, spike-validated by
    `Imported/FlattenSpike.lean` and `Imported/InterleaveSpike.lean`):
    the motive is ENV-LEVEL (`P env := EvTrue w env ⟪pushed⟫`) under strong
    induction on the μ-registry interpretation of the EMITTED measure term
    (`measure_strong_induction`); cases follow the emitted decision tree;
    each emitted IH alist instantiates the ONE strong hypothesis at the
    updated env (swaps and ride-along substitutions are plain env updates),
    justified by a decrease covered by the scheme fn's emitted termination
    clauses (`checkCoveringClause`) and discharged from the case's ruling
    facts by the Count library. J2's DISCHARGE FRAGMENT: single measured
    variable with `(CDR v)`/`(CAR v)` substitution under a direct
    `(consp v)`/`(not (endp v))` ruling fact; compound-test inversion is J3,
    sum-measure discharge is J4 — both hard-fail here until then. -/
partial def replayInduction (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) :
    MetaM Expr := do
  let some ind := cn.induction | throwError "replayInduction: no induction"
  -- 1. validate the justification shape (J2: μ-registry + T3 + I4 covering)
  let μE ← buildMeasureFn ind.measure
  let relOk := match ind.rel with
    | .atom (.symbol r) => r.name == "O<"
    | _ => false
  unless relOk do throwError "replayInduction: rel {repr ind.rel} ≠ o< (frontier)"
  -- T3 (theory audit): measured subset := free vars of the FLESHED-OUT
  -- measure term; must be ⊆ the emitted :CONTROLLERS
  let measuredVars := ACL2.Replay.freeVars ind.measure
  if measuredVars.isEmpty then
    throwError "replayInduction: measure {repr ind.measure} has no measured \
                variables (frontier)"
  unless measuredVars.all (ind.controllers.contains ·) do
    throwError "replayInduction: measured vars {repr measuredVars} ⊄ \
                :CONTROLLERS {repr ind.controllers} (T3 — frontier)"
  -- 2. per-case validation: distinct alist vars; every IH's measured
  -- substitution covered by an EMITTED termination clause (I4)
  for c in ind.cases do
    if c.tests.isEmpty then
      throwError "replayInduction: a case has no ruling tests (frontier)"
    for alist in c.alists do
      let vars := alist.map (·.1)
      unless vars.eraseDups.length == vars.length do
        throwError "replayInduction: IH alist vars {repr vars} not distinct"
      checkCoveringClause cfg ind alist measuredVars
  -- 3. the pushed clause (k literals) and recomputed child clauses. The
  -- induction formula for clause C under IHs σ1…σm is
  -- (tests ∧ (∨C)σ1 ∧ … ∧ (∨C)σm) → (∨C); each IH's ¬(∨C)σi is a
  -- CONJUNCTION of the per-literal negations, so clausification yields the
  -- CROSS PRODUCT: one clause per choice of one literal per IH —
  -- negTests ++ [¬L_{j1}σ1, …, ¬L_{jm}σm] ++ C.
  let pushedLits := cn.inputClause
  if pushedLits.isEmpty then
    throwError "replayInduction: empty pushed clause"
  let pushedTerm := disjoinTerm pushedLits
  -- per case: the list of IH-literal SELECTIONS (cartesian product; a base
  -- case has the single empty selection). Each selection entry is
  -- (alist, literal index j, the clause literal ¬L_jσ).
  let selectionsOf : InductionCase → List (List (List (Symbol × SExpr) × Nat × SExpr)) :=
    fun c => c.alists.foldl (init := [[]]) fun acc alist =>
      let formals := alist.map (·.1)
      let args := alist.map (·.2)
      acc.flatMap fun sel =>
        pushedLits.zipIdx.map fun (l, j) =>
          sel ++ [(alist, j, dumbNegateLit (ACL2.Replay.substTerm formals args l))]
  let expected : List (Nat × InductionCase × List (List (Symbol × SExpr) × Nat × SExpr) × List SExpr) :=
    ind.cases.zipIdx.flatMap fun (c, i) =>
      let negTests := c.tests.map dumbNegateLit
      (selectionsOf c).map fun sel =>
        (i, c, sel, negTests ++ sel.map (·.2.2) ++ pushedLits)
  -- the EMITTED scheme clause set (the recomputation's validation target)
  let schemeClauses ← ind.scheme.mapM fun cl => do
    let some lits := cl.toList?
      | throwError "replayInduction: scheme clause {repr cl} is not a list"
    pure lits
  -- ACL2's induction CLEAN-UP drops trivially-true clauses, two layers:
  -- (i) `add-literal` complement folding while the clause set is built (a
  -- cross-product clause where σ leaves an IH literal UNCHANGED — ¬Lσ = ¬L
  -- complements the goal's own L — becomes *true-clause*), mirrored by the
  -- CHEAP arm on our raw literal lists; (ii) `remove-trivial-clauses`
  -- (induct.lisp:7047): `trivial-clause-p` = member-'T ∨ (the
  -- `possible-trivial-clause-p` fn gate ∧ `tautologyp (disjoin cl)`) —
  -- mirrored by `tautExpand` + `ifTaut` (ORDEREDP-MEMB's merged base case:
  -- the clause's (NOT (EQUAL E (CAR A))) literal propositionally truthifies
  -- the IMPLIES conclusion). The (ii) mirror runs LAZILY — only when the
  -- cheap layer leaves an excess vs the emitted scheme — because `ifTaut`
  -- is compiled code the heartbeat guard cannot interrupt and its nested-
  -- test distribution can blow up on large cross-product clauses;
  -- observationally identical (drops are validated against the emitted
  -- scheme either way), and ANY divergence from ACL2 is caught by the
  -- scheme-count/containment/children checks below, never silent. Dropped
  -- selections are discharged at the walk: a complement drop by its truthy
  -- goal literal, a trivial-clause-p drop by the carve-out's closed-form
  -- discharge of the full dropped clause.
  let isTautCheap : List SExpr → Bool := fun cl =>
    cl.any (fun l => l == quoteT || cl.contains (dumbNegateLit l))
  let keptCheap := expected.filter (fun (_, _, _, cl) => !isTautCheap cl)
  let isTaut : List SExpr → Bool :=
    if keptCheap.length == schemeClauses.length then isTautCheap
    else fun cl =>
      isTautCheap cl ||
      (cl.any (mentionsFn tautGateFns) &&
        ifTaut 10000 [] (tautExpand (disjoinTerm cl)) == some true)
  let kept := expected.filter (fun (_, _, _, cl) => !isTaut cl)
  let dropped := expected.filter (fun (_, _, _, cl) => isTaut cl)
  -- POSITIVE-record validation (audit 2026-07-22): the (ii)-class drops —
  -- clauses only the `trivial-clause-p` mirror catches (the cheap complement
  -- layer's clauses are folded away by add-literal at construction and never
  -- reach `remove-trivial-clauses`) — must be EXACTLY the emitted
  -- `:SCHEME-DROPPED` set, both directions; the carve-out discharge at the
  -- walk is additionally gated on membership. When the lazy layer was
  -- skipped, this correctly demands an empty emitted set.
  let schemeDroppedClauses ← ind.schemeDropped.mapM fun cl => do
    let some lits := cl.toList?
      | throwError "replayInduction: :SCHEME-DROPPED clause {repr cl} is not a list"
    pure lits
  let droppedTaut := dropped.filter (fun (_, _, _, cl) => !isTautCheap cl)
  unless droppedTaut.length == schemeDroppedClauses.length &&
         droppedTaut.all (fun (_, _, _, cl) => schemeDroppedClauses.contains cl) do
    throwError "replayInduction: recomputed trivially-dropped clauses \
                {repr (droppedTaut.map (·.2.2.2))} ≠ emitted :SCHEME-DROPPED \
                {repr schemeDroppedClauses} (recompute/emission divergence)"
  unless schemeClauses.length == kept.length do
    throwError "replayInduction: {schemeClauses.length} scheme clauses for \
                {kept.length} recomputed (non-tautological) case clauses \
                (mismatch)"
  for (_, _, _, cl) in kept do
    unless schemeClauses.contains cl do
      throwError "replayInduction: recomputed case clause {repr cl} not in \
                  the emitted :SCHEME (recompute/emission divergence)"
  -- link children 1:1 by exact clause match (duplicate expected clauses would
  -- make the match ambiguous — hard-fail rather than guess)
  unless (kept.map (·.2.2.2)).eraseDups.length == kept.length do
    throwError "replayInduction: duplicate recomputed case clauses (frontier)"
  unless cn.children.length == kept.length do
    throwError "replayInduction: {cn.children.length} children for \
                {kept.length} recomputed case clauses (frontier)"
  let linked ← kept.mapM fun (i, c, sel, cl) => do
    let some child := cn.children.find? (·.inputClause == cl)
      | throwError "replayInduction: no child with clause {repr cl} (case {i})"
    pure (i, c, sel, cl, child)
  let tree ← ofExcept (buildCaseTree (ind.cases.zipIdx.map fun (c, i) => (i, c.tests)))
  let w := cfg.worldExpr
  let pushedE := reflectSExpr pushedTerm
  let nilC := mkConst ``SExpr.nil
  -- 4. P : Env → Prop — the pushed pool entry's truth at the ambient env
  -- (J2, design I2: the ENV-LEVEL motive — spike-validated)
  let P ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
    mkLambdaFVars #[eV] (← mkAppM ``EvTrue #[w, eV, pushedE])
  let conspOf := fun (v : Expr) => mkApp (mkConst ``Logic.consp) v
  let hNoLet ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[pushedE]) (mkConst ``Bool.true))
    "NoLet pushed"
  -- 5. the strong-induction STEP: ∀ e, (∀ e', μ e' < μ e → P e') → P e,
  -- dispatching the emitted decision tree.
  let step ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
    let sihTy ← withLocalDeclD `e2 (mkConst ``ACL2.Env) fun e2V => do
      let lt ← mkAppM ``LT.lt #[(mkApp μE e2V).headBeta, (mkApp μE eV).headBeta]
      mkForallFVars #[e2V] (← mkArrow lt (mkApp P e2V).headBeta)
    let inner ← withLocalDeclD `sih sihTy fun sihV => do
          let cfg' := { cfg with envExpr := eV }
          let ctx0 : ReplayCtx :=
            { ctx with varVals := [], vals := [], litFacts := [] }
          -- ONE IH's truth: instantiate the strong IH at the UPDATED env —
          -- every alist pair is a plain env update (swaps and arbitrary
          -- ride-along terms included, design I3) — and bridge to this env
          -- by substN: EvTrue of the σ-instance of the pushed DISJUNCTION
          let ihDisjTruth (ctxD : ReplayCtx) (facts : List TestFact)
              (alist : List (Symbol × SExpr)) :
              MetaM (ReplayCtx × Expr) := do
            -- pin every substituted term's value IN THIS ENV (simultaneous-
            -- substitution semantics, J1(b)-validated)
            let formals := alist.map (·.1)
            let args := alist.map (·.2)
            let mut ctxD := ctxD
            let mut vals : List (Expr × Expr) := []
            for (_, atm) in alist do
              ctxD ← pinTermOpaques cfg' eV ctxD atm
              let aE ← ctxValExpr cfg' ctxD atm
              let aP ← ctxValProof cfg' ctxD atm
              vals := vals ++ [(aE, aP)]
            -- DECREASE derivation (design I4/I5): consp-ness of a measured
            -- variable from the case's ruling facts — direct (consp v),
            -- falsy (endp v), falsy (atom v), or a NIL or-form compound
            -- test inverted along the EMITTED term (J3); else hard-fail.
            let conspToBoolOf (mv : Symbol) : MetaM Expr := do
              let mvT : SExpr := .atom (.symbol mv)
              let consT : SExpr :=
                .cons (.atom (.symbol { name := "CONSP" })) (.cons mvT .nil)
              let endpT : SExpr :=
                .cons (.atom (.symbol { name := "ENDP" })) (.cons mvT .nil)
              let atomT : SExpr :=
                .cons (.atom (.symbol { name := "ATOM" })) (.cons mvT .nil)
              let xvE ← dpConcVar eV mv
              match facts.find? (fun f => f.test == consT && f.sign) with
              | some cf => do
                let neTy ← mkAppM ``Ne #[conspOf xvE, nilC]
                unless ← isDefEq (← inferType cf.signE) neTy do
                  throwError "replayInduction: the (consp {mv.name}) \
                              fact's value is not Logic.consp of the \
                              measured var's env value"
                let hNeCast ← mkExpectedTypeHint cf.signE neTy
                mkAppM ``toBool_true_of_ne_nil #[hNeCast]
              | none =>
              -- the case tree strips the leading `not`: the step case's
              -- fact is the POSITIVE recognizer with sign FALSE
              match facts.find? (fun f => f.test == endpT && !f.sign) with
              | some cf => do
                let eqTy ← mkEq (mkApp (mkConst ``Logic.endp) xvE) nilC
                unless ← isDefEq (← inferType cf.signE) eqTy do
                  throwError "replayInduction: the falsy (endp {mv.name}) \
                              fact's value is not Logic.endp of the \
                              measured var's env value"
                let hCast ← mkExpectedTypeHint cf.signE eqTy
                mkAppM ``consp_toBool_of_endp_nil #[hCast]
              | none =>
              match facts.find? (fun f => f.test == atomT && !f.sign) with
              | some cf => do
                -- direct falsy (atom v) — J4's INTERLEAVE shape
                let eqTy ← mkEq (mkApp (mkConst ``Logic.atom) xvE) nilC
                unless ← isDefEq (← inferType cf.signE) eqTy do
                  throwError "replayInduction: the falsy (atom {mv.name}) \
                              fact's value is not Logic.atom of the \
                              measured var's env value"
                let hCast ← mkExpectedTypeHint cf.signE eqTy
                mkAppM ``consp_toBool_of_atom_nil #[hCast]
              | none => do
                -- J3 (design I5): a COMPOUND or-form ruling test — ACL2's
                -- `(IF a a c)` or-normal form (ZIP2/ZIP3) — whose NIL fact
                -- or-contains the (ATOM mv) leaf. Invert along the EMITTED
                -- term's shape; any other shape hard-fails.
                let rec orContains (t : SExpr) : Bool :=
                  t == atomT ||
                    match t with
                    | .cons (.atom (.symbol ifS))
                        (.cons a (.cons a2 (.cons c .nil))) =>
                      ifS.name == "IF" && a == a2
                        && (orContains a || orContains c)
                    | _ => false
                let some cf := facts.find?
                    (fun f => !f.sign && orContains f.test)
                  | throwError "replayInduction: no in-scope truthy \
                      (consp {mv.name}) / falsy (endp/atom {mv.name}) \
                      fact, and no nil or-form ruling fact contains \
                      (ATOM {mv.name}) — IH decrease underivable \
                      (frontier)"
                let rec invert (t : SExpr) (hNil : Expr) : MetaM Expr := do
                  if t == atomT then
                    mkAppM ``consp_toBool_of_atom_nil #[hNil]
                  else match t with
                    | .cons (.atom (.symbol ifS))
                        (.cons a (.cons a2 (.cons c .nil))) => do
                      unless ifS.name == "IF" && a == a2 do
                        throwError "replayInduction: ruling test {repr t} \
                            is not or-form (J3 inversion frontier)"
                      let hpair ← mkAppM ``cond_or_nil_inv #[hNil]
                      if orContains a then
                        invert a (← mkAppM ``And.left #[hpair])
                      else
                        invert c (← mkAppM ``And.right #[hpair])
                    | _ =>
                      throwError "replayInduction: or-form inversion \
                          reached a non-if non-(ATOM {mv.name}) component \
                          {repr t} (frontier)"
                invert cf.test cf.signE
            -- DECREASE via the emitted-obligation prover (#37 rework,
            -- design I4; docs/plans/2026-07-18_decrease-prover-rework.md):
            -- locate the scheme fn's EMITTED termination clause for THIS
            -- substitution, verify its ruling literals against the case's
            -- facts, and discharge the strict count decrease by the Count
            -- walk. The covering-clause precondition (incl. the sound-
            -- induction distinct-variable condition) ran in
            -- checkCoveringClause; a decrease ACL2 did not emit is never
            -- proved.
            let .cons (.atom (.symbol schemeFn)) argSpine := ind.term
              | throwError "replayInduction: induction term {repr ind.term} \
                  is not an application (frontier)"
            let some schemeActuals := argSpine.toList?
              | throwError "replayInduction: induction term args not a list \
                  (frontier)"
            let some schemeFormals :=
                ((cfg.worldVal.defs.get? schemeFn).map (·.1)).orElse
                  (fun _ => (cfg.gzDefs.find? (·.1 == schemeFn)).map (·.2.1))
              | throwError "replayInduction: scheme fn {schemeFn.name} \
                  neither in the world nor a ground-zero snapshot (frontier)"
            let some just := cfg.justs.lookup schemeFn.name
              | throwError "replayInduction: no emitted justification for \
                  scheme fn {schemeFn.name} (emission gap — frontier)"
            let ctxNow := ctxD
            let kit : DecreaseKit := {
              cfg := cfg', envE := eV
              facts := facts.map (fun f => (f.test, f.sign))
              valOf := fun u => ctxValExpr cfg' ctxNow u
              convOf := fun u => ctxValProof cfg' ctxNow u
              conspTrueOf := fun b => match b with
                | .atom (.symbol mv) => conspToBoolOf mv
                | _ => throwFrontier m!"replayInduction: consp of non-var \
                    measured base {repr b} (frontier)"
              endpFalseOf := fun b => do
                -- a refuted (ENDP b) ruling fact, normalized to
                -- `toBool (endp (val b)) = false` (the falsy TestFact
                -- carries `endp (val b) = nil`)
                let endpT : SExpr :=
                  .cons (.atom (.symbol { name := "ENDP" })) (.cons b .nil)
                match facts.find? (fun f => f.test == endpT && !f.sign) with
                | some cf => do
                  let vB ← ctxValExpr cfg' ctxNow b
                  let eqTy ← mkEq (mkApp (mkConst ``Logic.endp) vB)
                    (mkConst ``SExpr.nil)
                  unless ← isDefEq (← inferType cf.signE) eqTy do
                    throwError "replayInduction: the falsy (endp {repr b}) \
                        fact's value is not Logic.endp of the term's value"
                  let hCast ← mkExpectedTypeHint cf.signE eqTy
                  mkAppM ``toBool_false_of_eq_nil #[hCast]
                | none => throwFrontier m!"replayInduction: registry \
                    decrease needs a refuted (ENDP {repr b}) ruling fact \
                    in scope (frontier)" }
            let hLtRaw ← dischargeDecrease just
              schemeFormals schemeActuals
              (alist.map (·.1)) (alist.map (·.2)) kit
            -- e' and the cast of the decrease to μ e' < μ e (defeq through
            -- the concrete bindArgsOver lookups)
            let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
            let valsList := vals.map (·.1)
            let valsE ← mkListLit (mkConst ``SExpr) valsList
            let argsE ← mkListLit (mkConst ``SExpr) (args.map reflectSExpr)
            let e' ← mkAppM ``bindArgsOver #[eV, formalsE, valsE]
            let ltTy ← mkAppM ``LT.lt
              #[(mkApp μE e').headBeta, (mkApp μE eV).headBeta]
            unless ← isDefEq (← inferType hLtRaw) ltTy do
              throwError "replayInduction: the decrease fact does not match \
                          μ's env-update reduction (internal)"
            let hLt ← mkExpectedTypeHint hLtRaw ltTy
            let pIH' := mkAppN sihV #[e', hLt]
            -- substN bridge: eval e (subst pushed) = eval e' pushed
            let hlenPf ← proveByDecide
              (← mkEq (← mkAppM ``List.length #[argsE])
                      (← mkAppM ``List.length #[valsE]))
              "substN arg/val lengths"
            let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
            let pFn ← withLocalDeclD `pr prodTy fun prV => do
              let fst ← mkAppM ``Prod.fst #[prV]
              let snd ← mkAppM ``Prod.snd #[prV]
              mkLambdaFVars #[prV] (← mkValConvPropEx w eV fst snd)
            let entries ← (args.zip valsList).mapM fun (a, vE) => do
              let pairE ← mkAppM ``Prod.mk #[reflectSExpr a, vE]
              pure pairE
            let proofs := vals.map (·.2)
            let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip proofs)
            let zipE ← mkAppM ``List.zip #[argsE, valsE]
            let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
              let mem ← mkAppM ``Membership.mem #[zipE, prV]
              mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
            let hargs ← mkExpectedTypeHint hargsRaw hargsTy
            let pBridge ← mkAppM ``evalOpt_substTerm_substN
              #[w, eV, formalsE, argsE, valsE, pushedE, hNoLet, hlenPf, hargs]
            return (ctxD, ← mkAppM ``evtrue_of_fuel_eq #[pBridge, pIH'])
          -- dispatch the decision tree; at each leaf replay the case child
          -- and peel ruling literals then IH literals (clause order)
          let rec go (t : CaseTree) (ctxD : ReplayCtx) (facts : List TestFact) :
              MetaM Expr := do
            match t with
            | .split test posT negT => do
              let ctxD ← pinTermOpaques cfg' eV ctxD test
              let vE ← ctxValExpr cfg' ctxD test
              let pV ← ctxValProof cfg' ctxD test
              let nilTy ← mkEq vE nilC
              let negL ← withLocalDeclD `hnil nilTy fun hNil => do
                let body ← go negT ctxD (facts ++
                  [{ test, valueE := vE, convE := pV, sign := false, signE := hNil }])
                mkLambdaFVars #[hNil] body
              let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vE, nilC]) fun hNe => do
                let body ← go posT ctxD (facts ++
                  [{ test, valueE := vE, convE := pV, sign := true, signE := hNe }])
                mkLambdaFVars #[hNe] body
              mkAppM ``Classical.byCases #[negL, posL]
            | .leaf i => do
              let some (_, c, _, _, _) := linked.find? (fun (j, _, _, _, _) => j == i)
                | throwError "replayInduction: internal — leaf {i} unlinked"
              -- replay the linked child for a SELECTION and peel it down to
              -- EvTrue(∨C): the leading negated ruling tests (nil by the
              -- branch facts), then the selection's ¬L_{jᵢ}σᵢ literals (nil
              -- by the walk's truthy facts)
              let dischargeChild (ctxD : ReplayCtx)
                  (chosen : List (List (Symbol × SExpr) × Nat × Expr)) :
                  MetaM Expr := do
                let key := chosen.map fun (al, j, _) => (al, j)
                let (p0, sel, ctxP) ← match linked.find?
                    (fun (ci, _, sel, _, _) =>
                      ci == i && sel.map (fun (al, j, _) => (al, j)) == key) with
                  | some (_, _, sel, _, child) => do
                    pure (← rec.clause cfg' ctxD child, sel, ctxD)
                  | none => do
                    -- a DROPPED (trivially-true) selection — ACL2's clean-up
                    -- removed its clause (recomputed by `isTaut` above; the
                    -- verdict is the clause's absence from the emitted
                    -- :SCHEME). Two drop classes:
                    let some (_, _, selD, clD) := dropped.find?
                        (fun (ci, _, sel, _) =>
                          ci == i && sel.map (fun (al, j, _) => (al, j)) == key)
                      | throwError "replayInduction: no child for case {i} \
                                    selection {repr (key.map (·.2))}"
                    -- (i) add-literal COMPLEMENT drop: some chosen IH
                    -- literal's σ-instance IS a goal literal, and this branch
                    -- holds its truthiness — direct.
                    for (al, j, hne) in chosen do
                      let some lj := pushedLits[j]?
                        | throwError "replayInduction: internal — selection \
                                      index {j} out of range"
                      let ljσ := ACL2.Replay.substTerm
                        (al.map (·.1)) (al.map (·.2)) lj
                      if let some m := pushedLits.findIdx? (· == ljσ) then
                        return ← evtrueOfLitTrue cfg' ctxD pushedLits m ljσ hne
                    -- (ii) `trivial-clause-p` if-tautology drop
                    -- (ORDEREDP-MEMB's merged base case): the dropped clause
                    -- is trivially TRUE — discharge the FULL clause by the
                    -- carve-out's closed-form check (ACL2 itself closed it by
                    -- `if-tautologyp`, verdict-only), then peel it down like
                    -- a linked child. GATED on the POSITIVE emitted record
                    -- (`:SCHEME-DROPPED`, audit 2026-07-22).
                    unless schemeDroppedClauses.contains clD do
                      throwError "replayInduction: dropped clause {repr clD} \
                                  has no emitted :SCHEME-DROPPED record \
                                  (emission gap)"
                    let ctxD ← pinTermOpaques cfg' eV ctxD (disjoinTerm clD)
                    pure (← replayDischargeNode cfg' ctxD (disjoinTerm clD),
                          selD, ctxD)
                let ctxD := ctxP
                let mut p := p0
                -- ruling-literal peels, clause order
                for t in c.tests do
                  let (litPos, fact) ← do
                    match t with
                    | .cons (.atom (.symbol ns)) (.cons u .nil) =>
                      if ns.name == "NOT" then
                        match facts.find? (fun f => f.test == u && !f.sign) with
                        | some f => pure (true, f)   -- literal = u, value nil
                        | none => throwError "replayInduction: no nil fact for \
                                              ruling test {repr u}"
                      else
                        match facts.find? (fun f => f.test == t && f.sign) with
                        | some f => pure (false, f)  -- literal = (not t), t truthy
                        | none => throwError "replayInduction: no truthy fact \
                                              for ruling test {repr t}"
                    | _ =>
                      match facts.find? (fun f => f.test == t && f.sign) with
                      | some f => pure (false, f)
                      | none => throwError "replayInduction: no truthy fact for \
                                            ruling test {repr t}"
                  let lit := dumbNegateLit t
                  if litPos then
                    -- literal value = fact value = nil
                    let pLit ← ctxValProof cfg' ctxD lit
                    let pLitNil ← mkAppM ``re_val_cast
                      #[w, eV, reflectSExpr lit, fact.valueE, nilC, pLit, fact.signE]
                    p ← mkAppM ``evtrue_extract_else #[pLitNil, p]
                  else
                    -- literal = (not t); Logic.not (truthy) = nil
                    let pLit ← ctxValProof cfg' ctxD lit
                    let hNotNil ← mkAppM ``not_nil_of_truthy #[fact.signE]
                    let pLitNil ← mkAppM ``re_val_cast
                      #[w, eV, reflectSExpr lit,
                        mkApp (mkConst ``Logic.not) fact.valueE, nilC, pLit, hNotNil]
                    p ← mkAppM ``evtrue_extract_else #[pLitNil, p]
                -- selection-literal peels, clause order: entry (alist, j, hne)
                -- with hne : v(L_jσ) ≠ nil; the clause literal is ¬L_jσ
                for ((al, j, negLit), (_, _, hne)) in sel.zip chosen do
                  let formals := al.map (·.1)
                  let args := al.map (·.2)
                  let some lj := pushedLits[j]?
                    | throwError "replayInduction: internal — selection index \
                                  {j} out of range"
                  let ljσ := ACL2.Replay.substTerm formals args lj
                  let vLjσ ← ctxValExpr cfg' ctxD ljσ
                  let pLit ← ctxValProof cfg' ctxD negLit
                  let pLitNil ←
                    if negLit == (.cons (.atom (.symbol { name := "NOT" }))
                        (.cons ljσ .nil)) then
                      -- L_j positive: ¬L_jσ = (not L_jσ), Logic.not (truthy) = nil
                      let hNil ← mkAppM ``not_nil_of_truthy #[hne]
                      mkAppM ``re_val_cast
                        #[w, eV, reflectSExpr negLit,
                          mkApp (mkConst ``Logic.not) vLjσ, nilC, pLit, hNil]
                    else do
                      -- L_j = (not U): L_jσ = (not Uσ), ¬L_jσ = Uσ; the truthy
                      -- Logic.not pins Uσ's value to nil (two-valued decode)
                      unless vLjσ.isAppOfArity ``Logic.not 1 do
                        throwError "replayInduction: negative pushed literal \
                                    {repr lj} has non-Logic.not value (frontier)"
                      let hNil ← mkAppM ``nil_of_logic_not_ne_nil #[hne]
                      mkAppM ``re_val_cast
                        #[w, eV, reflectSExpr negLit, vLjσ.appArg!, nilC, pLit, hNil]
                  p ← mkAppM ``evtrue_extract_else #[pLitNil, p]
                return p
              -- WALK one IH's σ-instance disjunction: nil literals peel off
              -- (evtrue_extract_else); the first truthy literal selects that
              -- branch's continuation. The LAST literal's EvTrue is its own
              -- truthy fact — the disjunction being true, no absurd case.
              let walkIH (ctxD : ReplayCtx) (pIH : Expr)
                  (litsσ : List SExpr)
                  (k : ReplayCtx → Nat → Expr → MetaM Expr) : MetaM Expr := do
                let rec goW (ctxD : ReplayCtx) (pCur : Expr) (j : Nat)
                    (rest : List SExpr) : MetaM Expr := do
                  match rest with
                  | [] => throwError "replayInduction: empty IH disjunction walk"
                  | [l] => do
                    let ctxD ← pinTermOpaques cfg' eV ctxD l
                    let pL ← ctxValProof cfg' ctxD l
                    -- pCur : EvTrue(l) — truthiness direct
                    let hne ← mkAppM ``ne_nil_of_evtrue_conv #[pCur, pL]
                    k ctxD j hne
                  | l :: restL => do
                    let ctxD ← pinTermOpaques cfg' eV ctxD l
                    let vL ← ctxValExpr cfg' ctxD l
                    let pL ← ctxValProof cfg' ctxD l
                    let negB ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
                      let pNil ← mkAppM ``re_val_cast
                        #[w, eV, reflectSExpr l, vL, nilC, pL, hNil]
                      let pRest ← mkAppM ``evtrue_extract_else #[pNil, pCur]
                      mkLambdaFVars #[hNil] (← goW ctxD pRest (j + 1) restL)
                    let posB ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
                      mkLambdaFVars #[hNe] (← k ctxD j hNe)
                    mkAppM ``Classical.byCases #[negB, posB]
                goW ctxD pIH 0 litsσ
              -- nest the walks over the case's IHs (clause order), then
              -- discharge the selected child
              let rec goIHs (ctxD : ReplayCtx)
                  (alists : List (List (Symbol × SExpr)))
                  (chosen : List (List (Symbol × SExpr) × Nat × Expr)) :
                  MetaM Expr := do
                match alists with
                | [] => dischargeChild ctxD chosen
                | alist :: restA => do
                  let (ctxD, pIH) ← ihDisjTruth ctxD facts alist
                  let litsσ := pushedLits.map
                    (ACL2.Replay.substTerm (alist.map (·.1)) (alist.map (·.2)))
                  walkIH ctxD pIH litsσ fun ctxD j hne =>
                    goIHs ctxD restA (chosen ++ [(alist, j, hne)])
              goIHs ctxD c.alists []
          let body ← go tree ctx0 []
          mkLambdaFVars #[sihV] body
    mkLambdaFVars #[eV] inner
  -- 6. apply the induction at the ambient env (env-level motive — no
  -- controller-value instantiation plumbing)
  let indP ← mkAppM ``measure_strong_induction #[μE, P, step]
  return (mkApp indP cfg.envExpr).headBeta

end ACL2.Replay.Driver
