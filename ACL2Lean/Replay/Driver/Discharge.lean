/-
  Driver/Discharge — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  Decision-procedure discharge leaves (c1+c2, the ratified carve-out) and
  the G3 Fragment A value-layer wiring.
-/
import ACL2Lean.Replay.Driver.NodeCore

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ## Decision-procedure discharge leaves (c1 + c2) — the ratified carve-out

A clause ACL2 closed by a verdict-only decision procedure (tau / type-set
forward-chain) carries an emitted DISCHARGE NODE `(disjoin clause) ⇒ t` with no
internal step record — ACL2 itself has only the verdict — so the replay
discharges the leaf's precisely-stated obligation with a kernel-checked decision
procedure (CLAUDE.md, ratified 2026-06-09): lift the clause to the Logic
primitives, prove the DP FACT by the fixed simp/split_ifs/omega tactic, and fold
it back through the clause spine. Opaque user-fn subterms take their values from
totality/TP hypotheses. Two entry points:
- `replayDischargeLeaf` — the STANDALONE (harness) form: quantifies the opaque
  values + hypotheses into a telescope; with `assumeFact` an unclosable DP fact
  becomes a further bound hypothesis (conditional proof, no `sorryAx`).
- `replayDischargeNode` — the COMPOSED form used inside `replayClause`/
  preprocess chains: opaque values come from the ambient `ReplayCtx` PINS, TP
  facts from the bound TP hypotheses; an unclosable fact is a frontier error. -/

/-- Discharge-node origins (the verdict-only sites instrumented in ACL2's
    preprocess; see the emission plan). -/
def dischargeOrigins : List String :=
  ["preprocess/tau", "preprocess/tau-contradiction", "preprocess/type-set-fc",
   "preprocess/trivial-clause", "preprocess/built-in-clause",
   -- S1.3 (2026-07-23): whole-clause verdict discharges at SIMPLIFY time —
   -- forward chaining over the negated literals reached a contradiction
   -- (simplify-clause1), or the literal's type-alist construction did
   -- (rewrite-clause). Both emit the preprocess/type-set-fc shape.
   "simplify-clause/fc-contradiction",
   "rewrite-clause/type-alist-contradiction"]


/-- Discharge-node occurrences in a clause item (the top-level verdict-only
    step nodes; single source — Runner and the conditional harness both
    consume this; audit F7 2026-07-26 killed a Runner-local shadow copy). -/
def itemDischargeOrigins : ClauseItem → List (String × SExpr)
  | .literal _ => []
  | .step (.node _ lhs _ _ prov) =>
      if dischargeOrigins.contains prov.origin then
        [(prov.origin, lhs)] else []
  | .clausify _ => []
  | .branch _ items => items.flatMap itemDischargeOrigins

/-- Per-theorem: the discharge nodes on PROVED leaves — `(clauseId, origin,
    the discharged clause)`. These leaves are emission-complete; their replay
    is the DP lift, or (unprovable) the harness's ASSUMED:dp-fact condition. -/
partial def theoremDischargeLeaves (cp : ClauseProof) : List (String × String × SExpr) :=
  let rec go (n : ClauseNode) : List (String × String × SExpr) :=
    let here :=
      if n.children.isEmpty && n.induction.isNone then
        (n.steps.flatMap (·.items.flatMap itemDischargeOrigins)).map
          (fun (o, lhs) => (n.idStr, o, lhs))
      else []
    here ++ n.children.flatMap go
  (cp.root.map go).getD []

/-- Split a disjoined clause's if-spine `(if l₁ 't (if l₂ 't … lₖ))` into
    `([l₁ … l_{k-1}], lₖ)`. A non-spine term is a singleton clause `([], l)`. -/
partial def dpSpine : SExpr → List SExpr × SExpr
  | t@(.cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil)))) =>
    if fs.name == "IF" && th == quoteT then
      let (lits, last) := dpSpine e
      (c :: lits, last)
    else ([], t)
  | t => ([], t)

/-- The fixed leaf-closing tactic of the carved-out decision procedure: `simp_all`
    with the Logic definitions, then `omega` on any arithmetic residue.

    `-Logic.toBool`: the def's global @[simp] eq_def unfolds `toBool X` on a
    SYMBOLIC recognizer application into a stuck raw `match` nothing can
    rewrite; erasing it lets the propositional bridges
    (`toBool_eq_true/false`) fire instead, and concrete arguments still
    reduce through them. `trueListp_ne_nil_iff` is recognizer booleanness —
    what tau itself knows about every recognizer (truthiness IS `= t`). -/
def dpLeafTactic : MetaM (TSyntax `tactic) :=
  `(tactic| first
      | (simp_all [-Logic.toBool, -Logic.endp, Logic.zp, Logic.lt, Logic.plus, Logic.equal,
                   Logic.not, Logic.integerp, Logic.consp, Logic.toRat,
                   Logic.toInt, Logic.mkNumber, Logic.car, Logic.cdr,
                   Logic.implies, Logic.iff, beq_iff_eq, Bool.cond_eq_ite,
                   SExpr.t, Logic.toBool_eq_true, Logic.toBool_eq_false,
                   Logic.trueListp_ne_nil_iff, logic_len_eq_lenNat,
                   logic_endp_eq_not_consp,
                   logic_car_of_consp_nil, logic_cdr_of_consp_nil] <;>
          omega)
      | (simp_all [-Logic.toBool, -Logic.endp, Logic.zp, Logic.lt, Logic.plus, Logic.equal,
                   Logic.not, Logic.integerp, Logic.consp, Logic.toRat,
                   Logic.toInt, Logic.mkNumber, Logic.car, Logic.cdr,
                   Logic.implies, Logic.iff, beq_iff_eq, Bool.cond_eq_ite,
                   SExpr.t, Logic.toBool_eq_true, Logic.toBool_eq_false,
                   Logic.trueListp_ne_nil_iff, logic_len_eq_lenNat,
                   logic_endp_eq_not_consp,
                   logic_car_of_consp_nil, logic_cdr_of_consp_nil] <;>
          -- `at *`: a HYPOTHESIS can be stuck on an if too (a `toBool`
          -- match over an unreduced decidable if — the plus-equation
          -- hypothesis shape), and goal-only splitting leaves omega
          -- without the arithmetic fact
          (try split_ifs at *) <;> simp_all [-Logic.toBool] <;> try omega)
      | omega)

/-- Collect the argument pairs of saturated `lexorder` applications in `e`
    (the DP order-theory scan). Pairs under binders (loose bvars) are skipped —
    the scan runs on post-`intros` hypothesis/target types, where `lexorder`
    occurs applied to closed subterms. -/
partial def lexorderAppPairs (e : Expr) : List (Expr × Expr) :=
  let here :=
    if e.isAppOfArity ``ACL2.lexorder 2 then
      let a := e.appFn!.appArg!
      let b := e.appArg!
      if a.hasLooseBVars || b.hasLooseBVars then [] else [(a, b)]
    else []
  let sub :=
    match e with
    | .app f a => lexorderAppPairs f ++ lexorderAppPairs a
    | .lam _ t b _ => lexorderAppPairs t ++ lexorderAppPairs b
    | .forallE _ t b _ => lexorderAppPairs t ++ lexorderAppPairs b
    | .letE _ t v b _ =>
      lexorderAppPairs t ++ lexorderAppPairs v ++ lexorderAppPairs b
    | .mdata _ b => lexorderAppPairs b
    | .proj _ _ b => lexorderAppPairs b
    | _ => []
  here ++ sub

/-- DP ORDER THEORY (S1, 2026-07-23): for every `lexorder` application pair in
    the goal, assert the kernel-proved built-in order facts —
    `lexorder_antisymm_ne` / `lexorder_total_ne` (EvalLemmas), ACL2's own
    LEXORDER-ANTI-SYMMETRIC / LEXORDER-TOTAL — as hypotheses. Tau closes
    clauses whose literal set is `lexorder`-contradictory using exactly these
    built-in theorems, so the carve-out's decision procedure must carry the
    same theory. The obligation STATEMENT is untouched (each hypothesis is
    backed by a kernel proof term); only the fixed tactic's context grows,
    keyed by the trusted-core primitive symbol, never by book. No-op on goals
    without `lexorder`. -/
def assertDpOrderFacts (g : MVarId) : MetaM MVarId := do
  let pairs ← g.withContext do
    let mut found : List (Expr × Expr) := []
    let mut scanned : List Expr := []
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        scanned := d.type :: scanned
    scanned := (← g.getType) :: scanned
    for e in scanned do
      for (a, b) in lexorderAppPairs (← instantiateMVars e) do
        -- dedupe as UNORDERED pairs — antisymm is symmetric and both total
        -- directions get asserted below
        unless found.any (fun (x, y) => (x == a && y == b) || (x == b && y == a)) do
          found := found ++ [(a, b)]
    pure found
  let mut g := g
  let mut i := 0
  for (a, b) in pairs do
    for (tag, prf) in [
        ("anti", mkApp2 (mkConst ``ACL2.Replay.lexorder_antisymm_ne) a b),
        ("tot", mkApp2 (mkConst ``ACL2.Replay.lexorder_total_ne) a b),
        ("tot'", mkApp2 (mkConst ``ACL2.Replay.lexorder_total_ne) b a)] do
      let ty ← g.withContext do inferType prf
      let (_, g') ← (← g.assert (Name.mkSimple s!"dpOrd_{tag}_{i}") ty prf).intro1P
      g := g'
    i := i + 1
  return g

/-- Recursively case-split every `Atom`/`Number` hypothesis (the components a
    value's one-level `SExpr` split introduced), then return the leaves. -/
partial def dpSplitAtoms (g : MVarId) : MetaM (List MVarId) := do
  let target? ← g.withContext do
    (← getLCtx).findDeclM? fun d => do
      if d.isImplementationDetail then return none
      let ty ← instantiateMVars d.type
      if ty.isConstOf ``Atom || ty.isConstOf ``Number then return some d.fvarId
      else return none
  match target? with
  | none => return [g]
  | some fv =>
    let subs ← g.cases fv
    subs.toList.flatMapM (dpSplitAtoms ·.mvarId)

/-- Case one level of each NAMED quantified value (`SExpr`: nil/atom/cons —
    cons components are NOT recursed into; only the listed `dpv{i}` binders
    are split), then split the atoms. -/
partial def dpSplitVars (g : MVarId) (names : List String) : MetaM (List MVarId) := do
  match names with
  | [] => dpSplitAtoms g
  | _ =>
    let target? ← g.withContext do
      (← getLCtx).findDeclM? fun d => do
        if d.isImplementationDetail then return none
        let ty ← instantiateMVars d.type
        -- intros may hygienize the binder name (`dpv3✝`) — compare on the
        -- macro-scope-erased name
        let nm := d.userName.eraseMacroScopes.toString
        if ty.isConstOf ``SExpr && names.contains nm then
          return some (d.fvarId, nm)
        else return none
    match target? with
    | none => throwError "dpSplitVars: expected values {names} to split"
    | some (fv, nm) =>
      let subs ← g.cases fv
      subs.toList.flatMapM (fun s => dpSplitVars s.mvarId (names.erase nm))

/-- The value indices (in the `dpv{i}` binder order, `vars ++ opaques`)
    OCCURRING in a literal, mirroring `dpValExpr`'s abstraction dispatch
    exactly: an opaque subterm matches FIRST (so its internal variables do
    NOT occur in the abstracted statement), quoted constants are inert,
    variables count only where the abstraction reads them. -/
partial def dpValueOccs (vars : List Symbol) (opaques : List SExpr) (t : SExpr) :
    List Nat :=
  if let some i := opaques.idxOf? t then [vars.length + i]
  else match t with
  | .atom (.symbol s) => (vars.idxOf? s).toList
  | .atom _ => []
  | .cons (.atom (.symbol fs)) args =>
    if fs.name == "QUOTE" then []
    else ((args.toList?).getD []).flatMap (dpValueOccs vars opaques)
  | _ => []

/-- The CONCLUSION's relevance cone: the values occurring in `last`, closed
    under "a hypothesis (test or TP corollary) mentions both a cone value and
    this value". A deterministic slice — used only to pick WHICH values the
    split fallback enumerates when the full value count exceeds the split
    bound; out-of-cone values and the hypotheses mentioning them are CLEARED
    at the split goal (see `proveDpFact` — audit 2026-07-21 doc fix). -/
def dpConeIndices (tests : List SExpr) (last : SExpr) (vars : List Symbol)
    (opaques : List SExpr) (tpCors : List SExpr) : List Nat := Id.run do
  let hyps := (tests ++ tpCors).map fun l => (dpValueOccs vars opaques l).eraseDups
  let mut cone := (dpValueOccs vars opaques last).eraseDups
  for _ in List.range (vars.length + opaques.length) do
    for h in hyps do
      if h.any cone.contains then
        for i in h do
          if !cone.contains i then
            cone := cone ++ [i]
  return cone

/-- Build the DP fact statement
    `∀ vars vops, tp₁ = t → … → v₁ = nil → … → v_{k-1} = nil → vₖ ≠ nil`
    — the discharged clause's truth over all variable AND opaque values, under the
    emitted type-prescription hypotheses. The conclusion is TRUTHINESS
    (sorting-completion-2 inc-4: the previous `= t` form over-strengthened
    bare-term final literals — ORDEREDP-MEMB's `(CAR A)` — making the leaf
    unprovable and, worse, an ASSUMED:dp-fact hypothesis FALSE/vacuous;
    `≠ nil` is exactly the clause's disjunctive semantics). -/
def dpFactStmt (tests : List SExpr) (last : SExpr) (vars : List Symbol)
    (opaques : List SExpr) (tpCors : List SExpr) : MetaM Expr := do
  let total := vars.length + opaques.length
  let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (Array.range total).map fun i =>
      (Name.mkSimple s!"dpv{i}", .default, fun _ => pure (mkConst ``SExpr))
  withLocalDecls decls fun fvars => do
    let varMap := vars.zip fvars.toList
    let opqMap := opaques.zip (fvars.toList.drop vars.length)
    let absVal := dpValExpr opqMap fun s =>
      match varMap.find? (fun (v, _) => v == s) with
      | some (_, fv) => pure fv
      | none => throwError "dpFactStmt: unmapped variable {s.name}"
    let tpTys ← tpCors.mapM fun c => do mkEq (← absVal c) (mkConst ``SExpr.t)
    let hypTys ← tests.mapM fun t => do mkEq (← absVal t) (mkConst ``SExpr.nil)
    let conclTy ← do mkAppM ``Ne #[← absVal last, mkConst ``SExpr.nil]
    let body ← (tpTys ++ hypTys).foldrM (fun h acc => mkArrow h acc) conclTy
    mkForallFVars fvars body

/-- Run `x` under a REAL heartbeat bound of `n` USER units (×1000 internal).
    `withOptions (maxHeartbeats := …)` is a NO-OP for this purpose —
    `Core.Context.maxHeartbeats` is fixed when the command context is created
    (perf profile P1); this is the toolchain's own idiom (cf. Grind/Canon). -/
def withRealMaxHeartbeats (n : Nat) (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := n * 1000 }) <|
    Core.withCurrHeartbeats x

/-- Raise the elaborator recursion limit for a sub-computation. Same gotcha as
    `withRealMaxHeartbeats`: `withOptions (maxRecDepth := …)` is a no-op here —
    `Core.Context.maxRecDepth` is fixed when the command context is created.
    Needed for DP-leaf discharge on large included worlds (qsort's arithmetic
    books), whose clause terms exceed the default depth (512) during lift and
    tactic elaboration. A pure engineering limit, not proof search. -/
def withRealMaxRecDepth (n : Nat) (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := n }) x

/-- Match the LIFTED nonneg-int TP hypothesis type
    `(bif toBool (integerp v) then not (lt v '0) else nil) = t` with `v` a
    local fvar; return it (see `dp_nonneg_int_of_tp`). -/
def nonnegIntTpFVar? (ty : Expr) : Option FVarId := do
  let some (_, lhs, rhs) := ty.eq? | none
  unless rhs.isConstOf ``SExpr.t do none
  unless lhs.isAppOfArity ``cond 4 do none
  let b := lhs.getArg! 1
  let thn := lhs.getArg! 2
  let els := lhs.getArg! 3
  unless els.isConstOf ``SExpr.nil do none
  unless b.isAppOfArity ``Logic.toBool 1 do none
  let ip := b.appArg!
  unless ip.isAppOfArity ``Logic.integerp 1 do none
  let v := ip.appArg!
  let .fvar vFv := v | none
  unless thn.isAppOfArity ``Logic.not 1 do none
  let ltE := thn.appArg!
  unless ltE.isAppOfArity ``Logic.lt 2 do none
  unless ltE.appFn!.appArg! == v do none
  unless ltE.appArg! == reflectSExpr (.atom (.number (.int 0))) do none
  return vFv

/-- INT-VIEW pre-pass (sorting arc 2026-07-28): each lifted nonneg-int TP
    hypothesis pins its value to a Nat-image integer atom
    (`dp_nonneg_int_of_tp`); obtain-and-subst each, so linear-arithmetic
    facts become PURE Int arithmetic and the bounded DIRECT tactic closes
    leaves the value-shape split could never reach (the 7-value admission
    leaves). The obligation STATEMENT is untouched — a context
    transformation by a trusted-core theorem, the `assertDpOrderFacts`
    pattern: deterministic (keyed on the lifted TP shape), never search.
    Terminates: each round substitutes away one distinct value fvar, after
    which its hypothesis no longer matches the view. -/
partial def introDpIntValues (g : MVarId) : MetaM MVarId := do
  let hit? ← g.withContext do
    let lctx ← getLCtx
    pure <| lctx.foldl (init := none) fun acc d =>
      if acc.isSome || d.isImplementationDetail then acc
      else match nonnegIntTpFVar? d.type with
        | some _ => some d.fvarId
        | none => acc
  match hit? with
  | none => return g
  | some hFv =>
    let prf ← g.withContext do mkAppM ``dp_nonneg_int_of_tp #[mkFVar hFv]
    let ty ← g.withContext do inferType prf
    let g ← g.assert `hDpInt ty prf
    let (exFv, g) ← g.intro1P
    let subs ← g.cases exFv
    let #[sub] := subs
      | throwError "introDpIntValues: cases on the ∃ gave {subs.size} goals"
    let heq := sub.fields[1]!
    let g ← Lean.Meta.subst sub.mvarId heq.fvarId!
    introDpIntValues g

/-- The direct attempt's budget where the COMPLETE split fallback exists
    (`total ≤` the split bound, so the enumeration runs over ALL values with
    every hypothesis intact): a pure LATENCY knob, free to tune — on timeout
    the split enumeration still proves everything provable, so this constant
    can never change an OUTCOME, only how fast a failing attempt gives up.
    (Premise, stated honestly: "the split path closes whatever the direct
    path closes" is empirically true for every corpus leaf — the
    pure-split-first run was golden-byte-identical — but not a theorem; the
    golden gate is the corpus tripwire, and for new books the failure mode
    is a LOUD conditional hypothesis, never a wrong verdict.)

    NOT applicable in CONE mode (`total >` the bound with a fitting cone):
    there the split is a SLICE that clears out-of-cone hypotheses, so a fact
    whose truth needs one (the lexorder-totality contradictions, S1) is
    provable ONLY by the full-context direct attempt — outcome-determining,
    hence `dpOnlyProverGuard` (found the hard way: the HOW-MANY-FILTER-1
    obligation timed out at 15000 and then failed loudly at a sliced leaf). -/
def dpDirectBudget : Nat := 15000

/-- The direct attempt's budget where it is the only FULL-CONTEXT prover
    (`total >` the split bound — whether the cone slice fits or not):
    OUTCOME-determining, so deliberately NOT a tuned constant — a generous
    runaway guard (~40 s, the same role as the harness's per-leaf guards).
    A true fact needing more than this from the fixed tactic is reported as
    an honest frontier; a corpus-calibrated bar here would silently gate
    FUTURE books' coverage on today's timings. -/
def dpOnlyProverGuard : Nat := 1000000

/-- Run `tac` on a CLONE of `l`, assigning on success — a failed attempt
    must not half-assign the mvar. On failure, the DEPTH-2 constructor-split
    fallback (sorting-completion-2 inc-4): a leaf stuck on a SECOND-level
    value match (the primitive unfolds destroy the conditional completion
    lemmas' targets — ORDEREDP-MEMB's `car(cdr v) = nil` under
    `consp(cdr v) = nil`) closes after one more constructor split of a
    remaining SExpr fvar. FIXED policy, bounded (fuel 2 → ≤ 9 sub-leaves
    per leaf), not search. -/
partial def dpSplitAndClose (tac : Lean.TSyntax `tactic) (l : Lean.MVarId)
    (fuel : Nat) : MetaM Bool := do
  let ok ← l.withContext do
    let m2 ← mkFreshExprMVar (← l.getType)
    let ok ← try
        let r ← Lean.Elab.runTactic m2.mvarId! tac
        pure r.1.isEmpty
      catch _ => pure false
    if ok then l.assign (← instantiateMVars m2)
    pure ok
  if ok then return true
  if fuel == 0 then return false
  let fv? ← l.withContext do
    let lctx ← Lean.getLCtx
    pure (lctx.foldl (init := (none : Option Lean.FVarId)) fun acc d =>
      if !d.isImplementationDetail && d.type.isConstOf ``ACL2.SExpr then
        some d.fvarId
      else acc)
  match fv? with
  | none => return false
  | some fv =>
    let subs ←
      try l.cases fv
      catch _ => return false
    for sg in subs do
      unless ← dpSplitAndClose tac sg.mvarId (fuel - 1) do return false
    return true

/-- PROVE the DP fact by the carved-out decision procedure: one BOUNDED run
    of the fixed tactic on the unsplit goal, else a one-level value split
    (policy-bounded) and the fixed tactic per leaf. Hard-fails if any case
    survives.

    `coneIdxs` (from `dpConeIndices`): when `total` exceeds the split bound,
    the split fallback may still run on the CONCLUSION-CONE values alone if
    the cone fits the bound — a deterministic relevance slice, not search.
    The PROVED statement is the same `stmt` (the metavariable's type is
    fixed); inside the tactic proof the out-of-cone values and the
    hypotheses mentioning them are CLEARED at the split goal (weakening the
    proof context, never the statement — audit 2026-07-21 doc fix).
    `total ≤ 3` keeps the original all-values split exactly. -/
def proveDpFact (stmt : Expr) (total : Nat) (coneIdxs : List Nat := []) : MetaM Expr := do
  -- PRISTINE-CONTEXT (perf profile P6): the fact statement is CLOSED
  -- (∀-quantified over its values), but the caller invokes this inside the
  -- vop/hconv/htp telescopes — and `simp_all` on EVERY split leaf re-churns
  -- those ambient hypotheses (whose types carry the reflected world):
  -- measured 23 s vs 1.7 s for the same statement. Run the whole proof in
  -- an empty local context when the statement is genuinely closed: no
  -- fvars AND no mvars (an unassigned mvar would carry the outer context —
  -- the audit's F2; instantiate first so assigned mvars don't trip it).
  let stmt ← instantiateMVars stmt
  if stmt.hasFVar || stmt.hasMVar then
    proveDpFactCore stmt total coneIdxs
  else
    Meta.withLCtx {} #[] do proveDpFactCore stmt total coneIdxs
where proveDpFactCore (stmt : Expr) (total : Nat) (coneIdxs : List Nat) : MetaM Expr := do
  let tac ← dpLeafTactic
  -- BOUNDED-DIRECT-FIRST (perf profile P5 + the 08-equality trade): the
  -- whole-goal simp_all is the fastest path when it works (sub-second on
  -- propositional/equality facts) and catastrophic when it fails UNBOUNDED
  -- (40–860 s measured) — so try it once under a REAL small budget, then
  -- fall back to the case-split enumeration (~30 ms per concrete leaf; a
  -- failing leaf aborts immediately). Splitting is sound case analysis and
  -- each leaf carries strictly more constructor information than the
  -- un-split goal. FIXED policy, not search: one bounded direct attempt;
  -- split ≤ 3 values (≈9 cases each — 9⁴ ≈ 6500 leaves is not a viable
  -- check); past the bound the bounded direct attempt is all there is.
  -- Each attempt uses a FRESH metavariable (a failed attempt may leave its
  -- mvar half-assigned).
  let splitIdxs := if total ≤ 3 then List.range total else coneIdxs.eraseDups
  let canSplit := splitIdxs.length ≤ 3
  let direct? ←
    withRealMaxHeartbeats (if total ≤ 3 then dpDirectBudget else dpOnlyProverGuard) <|
    tryCatchRuntimeEx
      (try
        let mv ← mkFreshExprMVar stmt
        let (_, g) ← mv.mvarId!.intros
        let g ← assertDpOrderFacts g
        let g ← introDpIntValues g
        let remaining ← Lean.Elab.runTactic g tac
        if remaining.1.isEmpty then pure (some (← instantiateMVars mv)) else pure none
      catch _ => pure none)
      (fun _ => pure none)
  if let some p := direct? then return p
  unless canSplit do
    throwError "proveDpFact: the bounded direct tactic failed, and both the \
                {total} quantified values and the {splitIdxs.length}-value \
                conclusion cone exceed the split bound (3) — DP-fact \
                frontier (fact: {stmt})"
  let mv ← mkFreshExprMVar stmt
  let (_, g) ← mv.mvarId!.intros
  -- CONE mode (total > 3): clear the out-of-cone values and every hypothesis
  -- mentioning them — the sliced route does not read them, and leaving them
  -- symbolic churns the leaf tactic (simp_all re-walks them at every leaf)
  -- and can starve omega. A fact whose truth NEEDS an out-of-cone hypothesis
  -- then fails LOUDLY at a leaf — an honest frontier, never a wrong verdict.
  let g ←
    if total ≤ 3 then pure g else
      g.withContext do
        let keep := splitIdxs.map (s!"dpv{·}")
        let lctx ← getLCtx
        let outVars := lctx.foldl (init := #[]) fun acc d =>
          let nm := d.userName.eraseMacroScopes.toString
          if !d.isImplementationDetail && d.type.isConstOf ``SExpr &&
             nm.startsWith "dpv" && !keep.contains nm
          then acc.push d.fvarId else acc
        let depHyps := lctx.foldl (init := #[]) fun acc d =>
          if !d.isImplementationDetail &&
             outVars.any (fun fv => d.type.containsFVar fv)
          then acc.push d.fvarId else acc
        let mut g' := g
        for fv in depHyps do g' ← g'.tryClear fv
        for fv in outVars.reverse do g' ← g'.tryClear fv
        pure g'
  -- order theory AFTER the cone clearing: pairs come from the surviving
  -- hypotheses only, so no asserted fact re-mentions a cleared value
  let g ← assertDpOrderFacts g
  let leaves ← dpSplitVars g (splitIdxs.map (s!"dpv{·}"))
  for leaf in leaves do
    -- surface WHICH leaf failed (the raw tactic error names the tactic but
    -- not the case) — rethrow with the leaf goal attached
    let leafGoal ← leaf.withContext do addMessageContextFull m!"{leaf}"
    unless ← dpSplitAndClose tac leaf 2 do
      throwError "proveDpFact: the DP leaf tactic FAILED \
                  on leaf {leafGoal} (incl. the depth-2 constructor-split \
                  fallback) — the discharged clause's lift is not closable \
                  by simp+omega (clause fact: {stmt})"
  instantiateMVars mv

/-! ## G3 Fragment A wiring — the consolidated value-layer proof

`DpLiftBundle` carries the REFLECTED `vars`/`opq` lists and the premises of
`dpLiftF_sound`; `dpLiftProof` then certifies any liftable term's
value-characterized convergence by ONE lemma instantiation, the
`dpLiftF … = some v` fact discharged by defeq (D-A5: concrete keys reduce;
symbolic values are carried opaquely). Replaces `dpValProof`'s per-node
proof chains in the discharge path. -/

/-- `∃ N, ∀ f ≥ N, evalOpt f w e t = some v`, term and value as `Expr`s
    (the per-entry premise shape of the bundle). -/
private def mkValConvPropE (w e tE vE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
      let ge ← mkAppM ``GE.ge #[fV, nV]
      let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, tE]
      let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
      mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nV] body]

/-- The reflected lists + premise proofs feeding `dpLiftF_sound`. -/
structure DpLiftBundle where
  varsE : Expr
  hvars : Expr
  opqE : Expr
  hopq : Expr
  hns : Expr

/-- Build the bundle: clause variables ↦ their `dpConcVar` values (premises
    by `re_val_var`), opaques ↦ their pinned values (premises supplied),
    no-shadow by one kernel `decide` on the world. -/
def mkDpLiftBundle (cfg : ReplayConfig) (envExpr : Expr)
    (vars : List Symbol) (opqMap opqP : List (SExpr × Expr)) :
    MetaM DpLiftBundle := do
  let symTy := mkConst ``Symbol
  let sexprTy := mkConst ``SExpr
  -- vars: pair + per-entry re_val_var proof
  let varPairTy ← mkAppM ``Prod #[symTy, sexprTy]
  let varEntries ← vars.mapM fun sym => do
    let vE ← dpConcVar envExpr sym
    let pairE ← mkAppM ``Prod.mk #[reflectSymbol sym, vE]
    let hNotT ← proveIsNamedFalse sym "T"
    let h ← mkAppM ``re_val_var #[cfg.worldExpr, envExpr, reflectSymbol sym, hNotT]
    return (pairE, h)
  let varP ← withLocalDeclD `q varPairTy fun qV => do
    let fst ← mkAppM ``Prod.fst #[qV]
    let snd ← mkAppM ``Prod.snd #[qV]
    let atomE ← mkAppM ``SExpr.atom #[← mkAppM ``Atom.symbol #[fst]]
    mkLambdaFVars #[qV] (← mkValConvPropE cfg.worldExpr envExpr atomE snd)
  let (varsE, hvars) ← mkForallMemProof varPairTy varP varEntries
  -- opq: pair + the supplied convergence proof (zipped by the opaque term)
  let opqPairTy ← mkAppM ``Prod #[sexprTy, sexprTy]
  let opqEntries ← opqMap.mapM fun (op, vE) => do
    let some (_, h) := opqP.find? (fun (o, _) => o == op)
      | throwError "mkDpLiftBundle: opaque {repr op} has a value but no proof"
    let pairE ← mkAppM ``Prod.mk #[reflectSExpr op, vE]
    return (pairE, h)
  let opqProp ← withLocalDeclD `p opqPairTy fun pV => do
    let fst ← mkAppM ``Prod.fst #[pV]
    let snd ← mkAppM ``Prod.snd #[pV]
    mkLambdaFVars #[pV] (← mkValConvPropE cfg.worldExpr envExpr fst snd)
  let (opqE, hopq) ← mkForallMemProof opqPairTy opqProp opqEntries
  -- no-shadow: one decide on the (concrete) world
  let hns ← mkDecideProof (mkApp (mkConst ``dpNoShadow) cfg.worldExpr)
  return { varsE, hvars, opqE, hopq, hns }

/-- Does the term contain a lambda application (a translated `let`) anywhere
    `dpLiftF` would walk? Quote bodies are DATA, not walked — a literal
    `LAMBDA` symbol inside them is not an application. -/
partial def containsLamApp : SExpr → Bool
  | .cons (.atom (.symbol q)) rest =>
      if q.isNamed "QUOTE" then false else containsLamApp rest
  | .cons a b =>
      (match a with
       | .cons (.atom (.symbol lam)) _ => lam.isNamed "LAMBDA"
       | _ => false)
      || containsLamApp a || containsLamApp b
  | _ => false

/-- Value-characterized convergence of `t` to `vE` by ONE `dpLiftF_sound`
    instantiation; `vE` must be the walker-computed value (`dpValExpr`), and
    the `dpLiftF … = some vE` fact must hold by REDUCTION — a mismatch is a
    hard error naming the term (the consolidated function and the walker
    disagreeing would be a defect, not a recoverable state). -/
def dpLiftProof (cfg : ReplayConfig) (envExpr : Expr) (b : DpLiftBundle)
    (t : SExpr) (vE : Expr) : MetaM Expr := do
  -- `dpLiftF` has NO lambda arm (a fuel/termination question the verified
  -- function has not taken on), while `dpValExpr` beta-reduces translated
  -- `let`s (S2). A lambda-bearing DP leaf is therefore a NAMED capability
  -- frontier of this consolidation — without this check it would surface as
  -- the misleading divergence error below (S2 audit F1, 2026-07-25).
  if containsLamApp t then
    throwFrontier m!"dpLiftProof: DP leaf contains a translated LET — \
                    dpLiftF has no lambda arm (frontier): {repr t}"
  let someV := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
  let liftApp := mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE (reflectSExpr t)
  unless ← isDefEq liftApp someV do
    throwError "dpLiftProof: dpLiftF does not reduce to the walker's value \
                for {repr t} (function/walker divergence — a defect)"
  let hfact ← mkExpectedTypeHint (← mkEqRefl someV) (← mkEq liftApp someV)
  mkAppM ``dpLiftF_sound
    #[cfg.worldExpr, envExpr, b.varsE, b.opqE, b.hvars, b.hopq, b.hns,
      reflectSExpr t, vE, hfact]

/-- Close the spine's last literal: cast its value-characterized convergence by
    the DP fact's conclusion `concVal(t) = SExpr.t`, entering `EvTrue` via the
    exact-t injection. -/
partial def dischargeClose (cfg : ReplayConfig) (b : DpLiftBundle)
    (opqMap : List (SExpr × Expr))
    (t : SExpr) (fPartial : Expr) : MetaM Expr := do
  let vt ← dpValExpr opqMap (dpConcVar cfg.envExpr) t
  let pt ← dpLiftProof cfg cfg.envExpr b t vt
  -- fPartial : vt ≠ nil (the truthiness conclusion, inc-4)
  mkAppM ``evtrue_of_conv_ne_nil #[pt, fPartial]

/-- Fold `evtrue_dp_if_split` over the discharge clause's spine, feeding
    nil-hypotheses to the partially-applied DP fact; result `EvTrue` of the
    spine (G2). The DP FACT itself stays value-level (`concVal = SExpr.t`) —
    only the clause boundary wraps. -/
partial def dischargeSpine (cfg : ReplayConfig) (b : DpLiftBundle)
    (opqMap : List (SExpr × Expr))
    (t : SExpr) (fPartial : Expr) : MetaM Expr := do
  match t with
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" && th == quoteT then
      let vc ← dpValExpr opqMap (dpConcVar cfg.envExpr) c
      let pc ← dpLiftProof cfg cfg.envExpr b c vc
      -- hthen : vc ≠ nil → EvTrue (quote t)
      let neTy ← mkAppM ``Ne #[vc, mkConst ``SExpr.nil]
      let hthen ← withLocalDeclD `h neTy fun h => do
        let _ := h
        mkLambdaFVars #[h] (← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg])
      -- helse : vc = nil → EvTrue e   (descend, feeding the hyp to F)
      let fTy ← whnf (← inferType fPartial)
      let .forallE _ dom _ _ := fTy
        | throwError "dischargeSpine: DP fact arity mismatch at {repr c}"
      let helse ← withLocalDeclD `h dom fun h => do
        let p ← dischargeSpine cfg b opqMap e (mkApp fPartial h)
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
          vc, pc, hthen, helse]
    else dischargeClose cfg b opqMap t fPartial
  | _ => dischargeClose cfg b opqMap t fPartial

end ACL2.Replay.Driver
