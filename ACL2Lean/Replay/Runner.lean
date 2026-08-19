/-
  The REPLAY RUNNER — the per-book replay harness, shared between the
  corpus coverage sweep (`Tests/DriverCoverage.lean`, the golden-gated
  build-time sweep) and the FOCUSED runtime CLI (`acl2lean-replay`,
  `ReplayMain.lean`) — the fast OODA loop (perf arc WP1, 2026-07-18).

  DELIBERATELY NOT imported by the root `ACL2Lean` module: the focused
  CLI's whole point is a minimal import cone (Driver + reconstruction, no
  `Imported/WaypointCatalog`, no `Tests`), so a driver edit rebuilds only
  this cone and a single book replays at runtime in seconds instead of a
  full-corpus re-elaboration.

  Report-line semantics here are the GOLDEN-COMPARED text: any change to a
  line format shows up as a coverage-golden diff. The focused run must
  print the same rows the sweep would, so results are directly comparable.
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.Replay.WorldTransport
import ACL2Lean.ProofLog
import ACL2Lean.ClauseTree
import Lean

open ACL2 ACL2.Replay.Driver Lean Lean.Elab Lean.Meta

namespace ACL2.Replay.Runner

/-- `replayed_theorem N := e` — a THEOREM-kind declaration whose TYPE is
    the MACHINE-computed type of the emitted proof `e` (ruled by Mike
    2026-08-19, toolchain-bump arc, for v4.33's `linter.defProp`).

    The replay pins (`def N := driver_replayed% …`, `acl2_replay% …`,
    `parametric_replayed% …`, …) are proofs of Props whose statements are
    deliberately NEVER hand-spelled — the machine-emitted type IS the
    record, and the hand statement pins are the adjacent `example`s.
    `theorem` syntax requires an explicit type, so the linter's own advice
    is unavailable; this command emits the theorem KIND with the inferred
    type — machine ascription, not hand ascription, so the pin design is
    intact and no linter is touched. Fail-closed: a residual metavariable
    or a non-Prop emission is a hard error.

    The `True`-typed gate-runner pins (`… : True := …_pins%`) use this
    command too, for a SECOND v4.33 reason: a plain `theorem`'s body now
    elaborates in an ASYNC task where `addDecl` is RESTRICTED to the
    theorem's own name prefix — the pin elaborators `addDecl` replay
    constants (`ReplayedStatements.*`) and registry entries, which that
    restriction rejects (measured: the pins report `replayed 0/N`). This
    command elaborates synchronously in the command context, where the
    macros' declarations land as they did under `def`. -/
elab dc:(Lean.Parser.Command.docComment)? "replayed_theorem " id:ident
    " := " t:term : command => do
  let name := (← Lean.Elab.Command.liftCoreM Lean.getCurrNamespace) ++ id.getId
  Lean.Elab.Command.liftTermElabM <| Lean.Elab.Term.withDeclName name do
    -- `withDeclName`: the replay macros register their replayed statement
    -- under the ENCLOSING DECLARATION NAME (`Term.getDeclName?`,
    -- Waypoints/Macro.lean) — without it registration silently skips and
    -- every registry-route consumer keeps its hypothesis.
    let e ← Lean.Elab.Term.elabTermAndSynthesize t none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar then
      throwError "replayed_theorem {id.getId}: the emitted proof has \
        residual metavariables (fail-closed)"
    let ty ← instantiateMVars (← inferType e)
    unless ← Meta.isProp ty do
      throwError "replayed_theorem {id.getId}: the emitted type is not a \
        Prop ({ty}) — this command is for proof pins only; use `def`"
    Lean.addDecl (.thmDecl { name, levelParams := [], type := ty, value := e })
    if let some d := dc then
      Lean.addDocStringCore name (← Lean.getDocStringText d)
    Lean.Elab.Term.addTermInfo' id (Lean.mkConst name) (isBinder := true)

/-- Defuns carrying a RECORDED termination proof whose decrease arguments
    are beyond the destructor-chain walk (the recorded-termination route's
    DEMAND filter, sorting arc 2026-07-28 — plain destructor admissions
    keep the fast path and pay nothing). -/
partial def recordedTerminationDefuns
    (justs : List (String × Justification)) :
    Development → List (String × ClauseProof)
  | .done => []
  | .bind ev rest =>
    (match ev with
     | .defun name _ _ _ (some tcp) =>
       match justs.lookup name with
       | some just => if needsRecorded just then [(name, tcp)] else []
       | none => []
     | _ => []) ++ recordedTerminationDefuns justs rest
where
  /-- some emitted decrease argument is beyond a cdr/car chain over a
      variable and not an EVENS/ODDS registry application — the exact
      precondition of `dischargeDecrease`'s frontier. A USER measure fn
      head (BNEXT-SIZE — the MDD-ratified admission-replay route; the
      μ-registry's interpretation covers only the trusted-core
      ACL2-COUNT/LEN family) always takes the recorded route. -/
  needsRecorded (just : Justification) : Bool :=
    just.terminationClauses.any fun c =>
      match c.toList? with
      | some lits => lits.any fun l =>
        match l with
        | .cons (.atom (.symbol olt))
            (.cons (.cons (.atom (.symbol cnt1)) (.cons d .nil)) _) =>
          olt.name == "O<" &&
            (if cnt1.name == "ACL2-COUNT" then !chainOk d else true)
        | _ => false
      | none => false
  chainOk (t : SExpr) : Bool := destructorChainOk false t

/-- Every rune NAME cited by any step of a clause proof — the DEMAND filter
    for the termination replay's rule offers (sorting arc 2026-07-29:
    offering the whole book's rule set builds a hypothesis telescope one
    nested binder frame per rule, deep enough to overflow the build-time
    elaborator's stack; the proof cites only a handful). Step-level `runes`
    are ACL2's aggregated ttree runes, a superset of every node's cites. -/
partial def citedRuneNames (cp : ClauseProof) : List String :=
  match cp.root with
  | none => []
  | some root => (go root).eraseDups
where
  go (n : ClauseNode) : List String :=
    n.steps.flatMap (fun s => s.runes.map (·.name))
    ++ n.children.flatMap go

/-- EVERY replay channel the conditional harness consumes, derived from the
    development in ONE place (sorting-absolute arc 1a). The sweep runner
    (`runBook`) and the `driver_replayed%` macro BOTH consume this
    structure — a channel added for one is automatically seen by the other.
    The bug class this closes is real: `fcRules`, the termination pre-pass,
    and `equivRefls` each hard-failed the macro AFTER the runner had them
    (the 2026-07-31 WAYPOINT program — that dated label said "mirror",
    which per docs/LEXICON.md now names the product layer), and the
    macro's hand-built config was
    missing `gzTps` outright when this builder landed. -/
structure BookChannels where
  /-- theorems in creation order, each with the rules created before it -/
  thms : List (ClauseProof × List ACL2.RuleSpec)
  /-- emitted TP corollaries (fn name ↦ corollary term) -/
  tps : List (String × SExpr)
  /-- dependency proof trees for `rule:`/`cong:` discharge (same-book
      first, then cross-book — 2a) -/
  depProofs : List (String × ClauseProof)
  /-- the SAME-BOOK trees only — the `cong:` OFFER source (audit F1) -/
  localTrees : List (String × ClauseProof)
  /-- equivalence-reflexivity evidence: this book's formulas + included ones -/
  equivRefls : List (String × SExpr)
  /-- prior books' STORED RULES (the cross-rules channel, P3) — offered in
      the telescope after the consumer's own; transitive citations in a
      dependency re-replay bind them and discharge from `depProofs` -/
  crossRules : List ACL2.RuleSpec := []

/-- One book's LOCAL theorem trees (proved or not — each is re-checked
    at the consumer), keyed by name — the CROSS-BOOK dependency offer
    (sorting-absolute 2a): a consumer book's included `rule:<thm>`
    hypotheses discharge by re-replaying the dependency book's tree at
    the CONSUMER's world (`dischargeRuleHyp`'s no-registry route),
    inside the shared telescope. Fail-closed at every layer: no tree
    (or a rootless one) → the hypothesis stays; a same-named tree with
    the wrong formula fails the stored-rule recompute-check; a replay
    wall in the tree is a kept-hyp frontier. -/
def bookTrees (dev : Development) : List (String × ClauseProof) :=
  (developmentTheoremsWithRules dev).map fun (c, _) => (c.name, c)

/-- One book's STORED RULES, deduped by rune key (cross-rules channel,
    P3: a dependency tree re-replayed at the consumer's world can cite
    rules the CONSUMER's log never re-emits — PERM-IS-AN-EQUIVALENCE's
    tree cites rule:PERM-SYMMETRIC, absent from the ordered-perms log.
    Offering the dep book's rules lets the transitive citation bind; its
    own tree in `crossTrees` then discharges it). The v1 gap (every
    `(:RULES …)` event after the last theorem event was in no snapshot)
    is CLOSED: this is now the direct walk over the development's rule
    events, ground-zero seed included. -/
private partial def allBookRulesGo : Development → List ACL2.RuleSpec
  | .bind (.rules specs) rest => specs ++ allBookRulesGo rest
  | .bind _ rest => allBookRulesGo rest
  | .done => []

def allBookRules (dev : Development) : List ACL2.RuleSpec :=
  -- machinery debt (close-out 2026-08-05): the DIRECT walk over the
  -- development's `.rules` events, closing the v1 gap above — rules
  -- created by the book's LAST theorem (and a theorem-less dep book's
  -- rules) are now included. Ground-zero seed first, then creation
  -- order — the same relative order the per-theorem snapshots gave.
  (dev.groundZeroRuleSpecs ++ allBookRulesGo dev).foldl
    (init := []) fun acc r =>
      if acc.any (fun o => o.runeKey == r.runeKey) then acc else acc ++ [r]

/-- Combine a theorem's own rule snapshot with the cross-book offers —
    OWN entries take precedence (same-book identity preserved; a
    same-keyed cross copy is the same re-emitted rule). -/
def combineRules (own cross : List ACL2.RuleSpec) : List ACL2.RuleSpec :=
  -- cross entries FIRST in list position (fold-back audit F3): cross rules
  -- are chronologically EARLIER (an included book precedes the consumer),
  -- and the discharge pass substitutes in REVERSE creation order under the
  -- topological premise — a same-book rule's discharge may introduce a
  -- cross rule's fvar, so the cross fvar must be discharged LATER, i.e.
  -- sit earlier in the list. OWN entries keep dedup precedence.
  -- SCOPE NOTE (audit F2): this widens the rule telescope O(corpus) —
  -- deliberately UNLIKE the cong-offer decision (same-book only); the
  -- widening is fail-closed (an offer is a hypothesis unless discharged,
  -- and the discharge recompute-checks the dep formula against the spec);
  -- an include-book provenance gate is queued in TODO.
  cross.filter (fun c => !own.any (fun o => o.runeKey == c.runeKey)) ++ own

/-- The channel set of a development — the single derivation site.
    `crossTrees`: prior books' theorem trees (2a); appended AFTER the
    same-book entries so same-book precedence is unchanged. -/
def bookChannels (dev : Development)
    (crossTrees : List (String × ClauseProof) := [])
    (crossRules : List ACL2.RuleSpec := []) : BookChannels :=
  let thms := developmentTheoremsWithRules dev
  { thms := thms
    tps := dev.typePrescriptions
    depProofs := (thms.map fun (c, _) => (c.name, c)) ++ crossTrees
    localTrees := thms.map fun (c, _) => (c.name, c)
    equivRefls := (thms.map fun (c, _) => (c.name, c.formula))
      ++ dev.includedTheorems
    crossRules := crossRules }

/-- The canonical `ReplayConfig` of a book replay — the ONE construction
    site for both the runner and the replayed-statement macro. `gzTps`: BUILTIN-named
    TP snapshots (world-defined fns get theirs as `tp:` hypotheses
    instead). -/
def mkBookConfig (dev : Development) (w : World) (wExpr envExpr : Expr)
    (termReplayed : List (String × Name × List String × List SExpr) := []) :
    ReplayConfig :=
  { worldExpr := wExpr, envExpr := envExpr, worldVal := w,
    gzDefs := dev.groundZeroSnapshotDefs, justs := dev.justifications,
    fcRules := dev.groundZeroFcRuleSpecs,
    linearRules := dev.groundZeroLinearRuleSpecs,
    termReplayed := termReplayed,
    gzTps := dev.typePrescriptions.filter fun (n, _) =>
      (w.defs.get? { name := n }).isNone
    gzTpBasicTs := dev.typePrescriptionBasicTs
    tpLeaves := dev.typePrescriptionLeaves
    tpAllTps := dev.typePrescriptionAllTps
    recogTuples := dev.groundZeroRecognizerTupleSpecs }

/-- Clause-ids of BLACK-BOX leaves under a clause node: a leaf clause (no child
    clauses, no induction) that ACL2 marks PROVED but for which NO replayable proof
    structure was emitted (every step's rewriter detail `items` is empty). These are
    `preprocess-clause` / type-set / evaluation / linear-arithmetic discharges that the
    instrumentation does not yet emit a sub-proof for — a known EMISSION gap (Track B;
    see docs/plans/2026-06-09_direct-proof-emission.md). There is nothing to mirror, so
    such a leaf must NOT be reported as handled. (A SIMPLIFY-CLAUSE-proved leaf carries
    `items`; a PUSH-CLAUSE-proved node carries an induction / child pool-root — neither
    is flagged.) -/
partial def blackBoxLeafIds (n : ClauseNode) : List String :=
  let isLeaf := n.children.isEmpty && n.induction.isNone
  let noDetail := n.steps.all (fun s => s.items.isEmpty)
  let here := if isLeaf && noDetail then [n.idStr] else []
  here ++ n.children.flatMap blackBoxLeafIds

/-- Black-box leaves of a whole theorem proof (empty if its root is unset). -/
def theoremBlackBoxLeaves (cp : ClauseProof) : List String :=
  (cp.root.map blackBoxLeafIds).getD []

-- `itemDischargeOrigins` / `theoremDischargeLeaves` live in Driver/Discharge
-- (the SINGLE source next to `dischargeOrigins` — audit F7 2026-07-26 killed a
-- Runner-local shadow; the conditional harness now consumes them too), and
-- ACL2.Replay.Driver is opened above.

/-- The transitive AXIOM set of a proof term: axioms among the constants of
    the expression and everything those constants' definitions depend on
    (`CollectAxioms` needs a declared constant, so walk the env manually). -/
def collectProofAxioms (e : Expr) : MetaM (List Name) := do
  let env ← Lean.getEnv
  let mut visited : Lean.NameSet := {}
  let mut axioms : List Name := []
  let mut work := e.getUsedConstants.toList
  while !work.isEmpty do
    let c :: rest := work | break
    work := rest
    if visited.contains c then continue
    visited := visited.insert c
    match env.find? c with
    | some (.axiomInfo _) => axioms := axioms ++ [c]
    | some ci =>
      -- v4.33 (4.30 #12973): theorems are opaque — `.value?` returns none
      -- without `allowOpaque`, which would silently DROP axioms reached
      -- through theorem proofs from this walk.
      if let some v := ci.value? (allowOpaque := true) then
        work := work ++ v.getUsedConstants.toList
    | none => pure ()
  return axioms.eraseDups

/-- Run the driver on one theorem over its derived world; return a one-line
    status, and — when `replayedName?` is given and the replay is green — the
    kept condition strings of the freshly `addDecl`'d D1 REPLAYED CONSTANT
    (design §D1, WP4: subsequent same-book consumers apply the constant via
    the `ReplayedRegistry` instead of re-replaying this theorem's tree). The
    world is PROJECTED from the development and REFLECTED concretely (P4);
    structural facts are DERIVED by the driver (P3). A message that is
    neither a `replayClause`/`replayNode`/`replayLiteral` frontier flags a
    real bug in the new code, not an expected frontier. -/
def tryReplay (dev : Development) (w : World) (wExpr : Expr)
    (cp : ClauseProof) (rules : List ACL2.RuleSpec := [])
    (replayed : ReplayedRegistry := [])
    (replayedName? : Option Name := none)
    (budget : Nat := 3000000)
    (termReplayed : List (String × Name × List String × List SExpr) := [])
    (crossTrees : List (String × ClauseProof) := [])
    (crossRules : List ACL2.RuleSpec := [])
    (usefiDischarge : Option (Development → ReplayConfig → ReplayCtx → UseFiSpec → MetaM Expr) := none) :
    TermElabM (String × Option (List String)) := do
  -- bounded per-theorem budget + runtime-exception capture, as for tryDischarge.
  -- REAL bound (P1): withOptions(maxHeartbeats) was a NO-OP — Core.Context
  -- pins it at command-context creation; a runaway guard with margin over
  -- the slowest legitimate replay. RECALIBRATED 3M (G1 inc-2c, same
  -- methodology): the p3-conj-mid-literal theorem — a 5-subgoal induction
  -- whose per-subgoal composition stacks the or-collapse bridge, taut-drop
  -- clausify bridges, and 3 DP leaves — legitimately costs ~1.9M units
  -- (~78 s measured); 3M is ~1.55x margin over that observed cost
  -- (audit N1 wording fix).
  -- `budget` override — NOT a tuning knob (sorting arc 2026-07-28): an
  -- ADMISSION (termination) proof contains several linear-arithmetic DP
  -- leaves, each individually entitled to the full `dpOnlyProverGuard`
  -- inner budget BY DESIGN, so the single-theorem guard is arithmetically
  -- too small for that class regardless of per-piece speed. The admission
  -- call site passes a guard set by the same methodology as this default:
  -- margin over the observed legitimate cost (qsort admission ≈ 4.7M
  -- units → 10M). Ordinary theorems keep the 1M default.
  withRealMaxHeartbeats budget <| withRealMaxRecDepth 8192 <| tryCatchRuntimeEx
    (try
      let p ← Meta.withLocalDeclD `env (mkConst ``ACL2.Env) fun envFV => do
        let ch := bookChannels dev crossTrees crossRules
        let cfg := mkBookConfig dev w wExpr envFV termReplayed
        let (prf, conds) ← replayProofConditional cfg ch.tps cp
          dev.justifications (combineRules rules ch.crossRules)
          ch.depProofs replayed
          (equivRefls := ch.equivRefls) termReplayed
          (congTrees := some ch.localTrees)
          (usefiDischarge := usefiDischarge.map (fun mk => mk dev cfg))
        return (← Meta.mkLambdaFVars #[envFV] prf, conds)
      Meta.check p.1
      -- ✓ must mean AXIOM-CLEAN, not just type-correct: Meta.check accepts
      -- sorryAx (audit 2026-07-06) — collect the proof's axioms and reject
      -- anything beyond the classical trio
      let axioms ← collectProofAxioms p.1
      let bad := axioms.filter (fun a =>
        a != ``propext && a != ``Classical.choice && a != ``Quot.sound)
      unless bad.isEmpty do
        return (s!"FAIL: replay produced a proof using axioms {bad} (sorryAx?)", none)
      -- ASSUMED-conditioned composed replays are NEVER ✓ and NEVER
      -- registered (consumer-queue audit 2026-08-05 S1/S2/S4): the assumed
      -- dp-fact hypothesis is stated over INDEPENDENTLY-quantified opaques
      -- and can be FALSE — the conditional is then
      -- vacuous. Render like `tryDischarge`'s ◌ (the legend's invariant:
      -- a composed row never carries an ASSUMED cond as ✓) and refuse
      -- registration at this single choke point so no consumer can ever
      -- resolve the condition to a hypothesis fvar.
      if p.2.contains assumedDpFactCond || p.2.contains assumedFiSelfCond then
        let condStr := s!" cond[{", ".intercalate p.2}]"
        return (s!"ASSUMED ◌{condStr}", none)
      -- D1: emit the replayed-statement constant (checked + axiom-clean above)
      let mut registered : Option (List String) := none
      if let some nm := replayedName? then
        -- name-collision guard (audit 2026-07-15): the sanitization
        -- (non-alphanumerics ↦ '_') is not injective across (book, theorem)
        -- pairs — name the collision instead of surfacing addDecl's
        -- "already declared" as a bare FAIL on a green replay
        if (← Lean.getEnv).contains nm then
          return (s!"FAIL: replayed-constant name collision: {nm} (sanitized \
                     book/theorem pair duplicates an earlier one)", none)
        let pv ← Lean.instantiateMVars p.1
        Lean.addDecl <| .thmDecl
          { name := nm, levelParams := [], type := ← Meta.inferType pv, value := pv }
        registered := some p.2
      let condStr := if p.2.isEmpty then "" else s!" cond[{", ".intercalate p.2}]"
      return (s!"REPLAYED ✓{condStr}", registered)
    catch e => return (s!"FAIL: {(← e.toMessageData.toString).replace "\n" " "}", none))
    (fun e =>
      return (s!"FAIL: (runtime: {(← e.toMessageData.toString).replace "\n" " "})", none))

/-- The recorded-admission replay of one defun — the TERMINATION PRE-PASS
    core shared by `runBook` and `driver_replayed%`'s `with_termination`
    (1a; cache handling and failure policy stay at the call sites). The
    rule offer is DEMAND-filtered to the proof's cited runes; the budget is
    the admission-class guard (see `tryReplay`'s budget doc). -/
def replayAdmission (dev : Development) (w : World) (wExpr : Expr)
    (tcp : ClauseProof) (mName : Name)
    (crossTrees : List (String × ClauseProof) := [])
    -- WP5: the D1 entries an admission's OWN dependency discharges may
    -- apply. The rule offer here is DEMAND-filtered to the admission's
    -- cited runes, so a dependency re-replayed INSIDE this telescope
    -- walls on the rules the filter dropped (`HOW-MANY-BAD-PAIRS-BNEXT`
    -- citing `HOW-MANY-SMALLER-BNEXT` is the measured case); with the
    -- dependency's own replayed constant registered, the discharge
    -- APPLIES it and the filter stops mattering.
    (replayed : ReplayedRegistry := [])
    (crossRules : List ACL2.RuleSpec := []) :
    TermElabM (String × Option (List String)) := do
  let thms := developmentTheoremsWithRules dev
  let cited := citedRuneNames tcp
  let termRules := ((thms.map (·.2)).flatten.filter
    (fun r => cited.contains r.name)).eraseDups
  tryReplay dev w wExpr tcp termRules
    (replayed := replayed)
    (replayedName? := some mName) (budget := 10000000)
    (crossTrees := crossTrees) (crossRules := crossRules)

/-- The termination-replay CIRCULARITY predicate (audit F3): an admission
    proof conditional on the defun's OWN totality/TP facts must be
    discarded — `thmAt` would resolve the condition to the consumer's
    hypothesis fvar and silently accept the circle. One predicate, both
    call sites (runner discards; the macro skips loudly). -/
def admissionCircular (fn : String) (conds : List String) : Bool :=
  conds.contains s!"total:{fn}" || conds.contains s!"tp:{fn}"

/-- WORLD INCLUSION (WP5, the cross-book transfer's fail-closed gate): every
    defun of `w1` is present in `w2` BYTE-IDENTICALLY (same formals, same
    body). This is the honest precondition for replaying a dependency
    book's recorded tree at the CONSUMER's world: the tree's unfoldings
    are exactly the ones its own book admitted. Any mismatch — a
    redefinition, a translation divergence between two captures of the
    same book — refuses the transfer; it never adjusts anything. -/
def worldIncludes (w1 w2 : World) : Bool :=
  w1.defs.entries.all fun (s, v) => w2.defs.get? s == some v

/-! ## The D2/D7 WORLD TRANSPORT (perf arc phase 2 item 1, 2026-08-17)

A dependency book's own module already holds a kernel-checked replayed
constant for each of its green theorems/admissions, stated over the
DEP's world. When that constant is IMPORTED (the coverage harness's
module DAG mirrors `covDeps`), re-replaying the dep's tree at the
consumer's world is redundant: `Replay.evtrue_transport`
(`WorldTransport.lean` — the proven `evalOpt_world_mono` behind two
per-pair decidable side conditions + finite per-new-name `callBuiltin`
facts) carries the SAME statement to the consumer's world by a single
kernel-checked lemma application.

Fail-closed at every layer, falling back to today's re-replay (never a
hard fail where today succeeds): a missing/foreign-named dep constant,
a CONDITIONAL dep constant (hypotheses are contravariant — they do not
transport), a statement mismatch (the dep constant's type must be
EXACTLY `∀ env, EvTrue w_dep env ⟦Φ⟧` for the formula the consumer
computed from the SAME log), a new consumer name shadowing a builtin,
or a failing side-condition check. The transported constant's type is
byte-identical to what the unconditional re-replay route would have
produced, so consumers (`thmAt`/the totality prover) see no
difference. -/

/-- The one shared name sanitizer of the registry constants. -/
private def xSan (s : String) : String :=
  String.map (fun c => if c.isAlphanum then c else '_') s

/-- Build (or reuse) the per-(consumer, dep) PAIR TRANSPORT constant
    `∀ env t, EvTrue w_dep env t → EvTrue w env t` — the two decidable
    side conditions kernel-checked ONCE per pair (design §4: per-pair
    constants, never per-theorem re-derivations), the `hnew` residue
    closed name-by-name by `rfl` on the concrete non-builtin new names
    (the P3c reconciliation — see `WorldTransport.lean`'s header).
    `none` = transport unavailable for this pair (fail-closed). -/
def tryBuildPairTransport (bookKey src : String) (dw w : World)
    (dwExpr wExpr : Expr) : TermElabM (Option Name) := do
  let pairName := Name.mkStr2 "CrossBookTransport" (xSan s!"pair_{bookKey}_{src}")
  if (← Lean.getEnv).contains pairName then return some pairName
  let news := w.defs.entries.filterMap fun kv =>
    if dw.defs.contains kv.1 then none else some kv.1
  -- a new name whose NAME STRING is a builtin would shadow `callBuiltin`
  -- dispatch — `hnew` is then genuinely unprovable (design §D2's audit-F6
  -- caveat); refuse the pair
  if news.any (fun s => builtinNames.contains s.name) then return none
  -- meta-level pre-check on the VALUES (compiled, cheap) before spending
  -- kernel time; a false check refuses the pair
  unless ACL2.Replay.worldExtendsCheck dw w
      && ACL2.Replay.newKeysCoverCheck dw w news do
    return none
  try
    let boolTrue := mkConst ``Bool.true
    let newsE ← Meta.mkListLit (mkConst ``ACL2.Symbol) (news.map reflectSymbol)
    let hinc ← Meta.mkDecideProof (← Meta.mkEq
      (← Meta.mkAppM ``ACL2.Replay.worldExtendsCheck #[dwExpr, wExpr]) boolTrue)
    let hcov ← Meta.mkDecideProof (← Meta.mkEq
      (← Meta.mkAppM ``ACL2.Replay.newKeysCoverCheck #[dwExpr, wExpr, newsE]) boolTrue)
    let hnb ← mkNoBuiltinsProof news
    let value ← Meta.mkAppM ``ACL2.Replay.evtrue_transport #[hinc, hcov, hnb]
    Lean.addDecl <| .thmDecl
      { name := pairName, levelParams := [],
        type := ← Meta.inferType value, value }
    return some pairName
  catch _ => return none
where
  /-- `NoBuiltins news`, each conjunct `∀ args, callBuiltin s.name args
      = none` closed by `rfl` — kernel whnf reduces the 55-arm match on
      a CONCRETE name with the args abstract; no equation lemma is
      involved. A name that fails the defeq check (a builtin — already
      excluded above, so this is belt) throws and refuses the pair. -/
  mkNoBuiltinsProof : List Symbol → MetaM Expr
    | [] => pure (mkConst ``ACL2.Replay.noBuiltins_nil)
    | s :: rest => do
      let sE := reflectSymbol s
      let listSExprTy := mkApp (mkConst ``List [.zero]) (mkConst ``ACL2.SExpr)
      let head ← Meta.withLocalDeclD `args listSExprTy fun argsFV => do
        let noneE := mkApp (mkConst ``Option.none [.zero]) (mkConst ``ACL2.SExpr)
        let lhs := mkApp2 (mkConst ``ACL2.callBuiltin)
          (mkApp (mkConst ``ACL2.Symbol.name) sE) argsFV
        let ty ← Meta.mkEq lhs noneE
        let pf ← Meta.mkEqRefl noneE
        -- force the defeq check NOW (fail-closed here, not at addDecl)
        unless ← Meta.isDefEq (← Meta.inferType pf) ty do
          throwError "mkNoBuiltinsProof: callBuiltin does not reduce to \
            none on {s.name} (builtin shadow?)"
        Meta.mkLambdaFVars #[argsFV] (← Meta.mkExpectedTypeHint pf ty)
      Meta.mkAppM ``ACL2.Replay.noBuiltins_cons
        #[head, ← mkNoBuiltinsProof rest]

/-- Transport ONE unconditional dep constant (type
    `∀ env, EvTrue w_dep env ⟦Φ⟧`, checked EXACTLY — statement-matched,
    fail-closed) to the consumer's world under `tgtName`. Returns
    `false` (caller falls back to re-replay) on any mismatch. -/
def tryTransportDepConst (pairName : Name) (dwExpr wExpr : Expr)
    (depDecl : Name) (formula : SExpr) (tgtName : Name) :
    TermElabM Bool := do
  let env ← Lean.getEnv
  let some ci := env.find? depDecl | return false
  if env.contains tgtName then return false
  try
    let φE := reflectSExpr formula
    let envTy := mkConst ``ACL2.Env
    let mkStmt (wE : Expr) : TermElabM Expr :=
      Meta.withLocalDeclD `env envTy fun envFV =>
        Meta.mkForallFVars #[envFV]
          (mkAppN (mkConst ``ACL2.Replay.EvTrue) #[wE, envFV, φE])
    let expectedDep ← mkStmt dwExpr
    unless ci.type == expectedDep do
      -- syntactic mismatch: allow a defeq match (same statement, different
      -- print) but nothing weaker — `isDefEq` here can only equate types,
      -- never change what is proved
      unless ← Meta.isDefEq ci.type expectedDep do return false
    let value ← Meta.withLocalDeclD `env envTy fun envFV =>
      Meta.mkLambdaFVars #[envFV]
        (mkAppN (mkConst pairName) #[envFV, φE, mkApp (mkConst depDecl) envFV])
    Lean.addDecl <| .thmDecl
      { name := tgtName, levelParams := [],
        type := ← mkStmt wExpr, value }
    return true
  catch _ => return false

/-- Transport-first recorded-admission reuse (phase 2 item 1c — the
    profile's QSORT-3x finding): when the dep book's OWN admission
    constant (`ReplayedTermination.term_<src>_<fn>`) is visible in the
    environment and the dep world is included in the consumer's, carry
    it to the consumer's world instead of re-replaying the admission
    waterfall. Shared by `crossBookRegistry`'s xterm pass and the
    coverage harness's usefi term pre-pass — ONE proof per (defun,
    world) per sweep. `false` = caller keeps today's re-replay. -/
def tryTransportDepAdmission (bookKey src : String) (dw w : World)
    (wExpr : Expr) (fn : String) (tcp : ClauseProof) (tgtName : Name) :
    TermElabM Bool := do
  let depDecl := Name.mkStr2 "ReplayedTermination" (xSan s!"term_{src}_{fn}")
  unless (← Lean.getEnv).contains depDecl do return false
  unless worldIncludes dw w do return false
  let dwE ← reflectWorld dw
  match ← tryBuildPairTransport bookKey src dw w dwE wExpr with
  | some pn =>
    tryTransportDepConst pn dwE wExpr depDecl
      (disjoinTerm ((tcp.root.map (·.inputClause)).getD [])) tgtName
  | none => return false

/-- Rune names cited ANYWHERE under a theorem's tree — the clause-level
    `WaterfallStep.runes` that `citedRuneNames` reads PLUS the rewriter
    detail's own per-step runes. The clause-level set is the ttree
    snapshot and is NOT a superset: `ORDERED-PERMS` consumes its book's
    `rule:TRUE-LISTP-RM` without the name appearing there. Used ONLY to
    size the cross-book pre-pass's demand — never to filter an offer, so
    it can only ever make the transfer reach further, never change what a
    replay is allowed to use. -/
partial def citedRuneNamesDeep (cp : ClauseProof) : List String :=
  match cp.root with
  | none => []
  | some root => (goNode root).eraseDups
where
  goNode (n : ClauseNode) : List String :=
    n.steps.flatMap (fun s =>
      s.runes.map (·.name) ++ goItems s.items)
    ++ n.children.flatMap goNode
  goItems (is : List ClauseItem) : List String :=
    is.flatMap fun i =>
      match i with
      | .literal lp => lp.nodes.flatMap goProof
      | .step nd => goProof nd
      | .branch _ sub => goItems sub
      | _ => []
  goProof : ProofNode → List String
    | .node rune _ _ children _ => rune.name :: children.flatMap goProof

/-- The names a book's proofs CITE — cited runes (deep) plus plain-`:use`
    citations, over every theorem of the development. The demand seed for
    the cross-book pre-pass. -/
def bookCitedNames (dev : Development) : List String :=
  ((developmentTheoremsWithRules dev).flatMap fun (cp, _) =>
    citedRuneNamesDeep cp
    ++ ACL2.Replay.Driver.theoremUseCitedNames cp).eraseDups

/-- The demand seed WIDENED with the consumer's OFFER surfaces (T1+2
    sprint P6; built and measured at P5a, adopted here once the post-sweep
    passes run to quiescence).

    A cited rune is not the only way a dependency theorem reaches a
    telescope: the consumer's own `(:RULES …)` / `(:GROUND-ZERO-LINEAR-RULES
    …)` snapshots OFFER stored rules whose names never appear in any tree's
    citations — `TRUE-LISTP-BNEXT` is cited by nothing at all, and
    `HOW-MANY-BAD-PAIRS-BNEXT` only inside `BSORT`'s ADMISSION waterfall —
    yet both arrive at `BSORT-IS-ISORT` as hypotheses (the recorded-admission
    totality proof maps the admission's own kept conditions onto the
    consumer's telescope). Without a registry entry the discharge falls to
    the re-replay route, which walls inside the consumer's telescope; with
    one it takes the transfer.

    The widening is DEMAND-SIDE ONLY: it can make the cross-book pre-pass
    replay more dependency theorems (each a full, deterministic,
    kernel-checked replay whose entry is matched by STATEMENT), never change
    what any replay is allowed to use. Measured cost at
    `sorting/sorts-equivalent`: the undemanded dep-theorem count drops
    13 → 1, i.e. 12 extra cross-book replays.

    P5a measured this widening ALONE as two conditions out, three in (the
    dependency's own `total:BNEXT`/`total:BNEXT-SIZE`/`tp:BNEXT-SIZE` arrive
    after the totality/TP passes) and reverted it under the movement rule.
    Its partner is `replayProofConditional`'s post-replay QUIESCENCE loop,
    which attempts those with a rebuilt `totalEnv`; the two land together. -/
def bookDemandSeed (dev : Development) : List String :=
  (bookCitedNames dev
    ++ (allBookRules dev).map (·.name)
    ++ dev.groundZeroLinearRuleSpecs.map (·.name)).eraseDups

/-- WP5 — THE CROSS-BOOK D1 TRANSFER. A dependency book's replayed
    statement lives over ITS OWN world, so the D1 registry (whose entries
    are Lean constants of type `∀ env, … → EvTrue w env Φ`) has always
    been per-book: a cross-book `rule:`/`use:`/`linear:` hypothesis fell
    through to the re-replay route, which replays the dependency's tree
    INSIDE THE CONSUMER'S TELESCOPE and frontiers whenever that telescope
    does not happen to offer what the dependency's own book did.

    The transfer replays each DEMANDED dependency theorem at the
    CONSUMER's world, in the DEPENDENCY BOOK's own channels — a full,
    deterministic, kernel-checked replay of the recorded tree, `addDecl`'d
    once and applied O(1) thereafter — and registers it. `depReplayedProofAt`
    then takes the registry route for cross-book dependencies exactly as
    it does for same-book ones.

    Fail-closed at every layer: a dependency world not INCLUDED in the
    consumer's (`worldIncludes`) is refused outright; an undemanded
    theorem is never replayed; a replay that walls leaves no entry (the
    consumer keeps its hypothesis); and the entry carries the
    dependency's translated Goal, so the consumer matches it by STATEMENT
    and not merely by name.

    `depDevs` must be in dependency order (a dep book's own cross-book
    citations resolve against the entries accumulated before it), which is
    the corpus order the sweep already uses. -/
def crossBookRegistry (bookKey : String) (w : World) (wExpr : Expr)
    (depDevs : List (String × Development)) (demandSeed : List String)
    -- PERF-ARC PHASE 1 instrumentation (2026-08-17, behavior-zero): the
    -- pre-pass was the profile's biggest UNTIMED gap (A5). `[t]` lines on
    -- stdout, gated on the focused CLI's timings flag; the sweep passes
    -- false and is untouched.
    (timings : Bool := false) :
    TermElabM (ReplayedRegistry
      × List (String × Name × List String × List SExpr)) := do
  let tXb0 ← IO.monoMsNow
  -- DEMAND (bounded), computed GLOBALLY and BEFORE any replay: the seed
  -- names closed over EVERY offered book's citations. Replaying a whole
  -- dependency corpus at each consumer world would be quadratic and
  -- pointless — only a CITED statement can ever be applied — but the
  -- closure must be global, because a later book's tree can demand an
  -- earlier book's theorem and the pre-pass itself runs in dependency
  -- order (registering the earlier one first).
  let cites : List (String × List String) :=
    depDevs.flatMap fun (_, d) =>
      (developmentTheoremsWithRules d).map fun (cp, _) =>
        (cp.name, citedRuneNamesDeep cp
          ++ ACL2.Replay.Driver.theoremUseCitedNames cp)
  let mut demand := demandSeed
  for _ in [0:cites.length] do
    let mut grew := false
    for (n, ns) in cites do
      if demand.contains n then
        for m in ns do
          unless demand.contains m do
            demand := demand ++ [m]
            grew := true
    unless grew do break
  let mut reg : ReplayedRegistry := []
  let mut xterm : List (String × Name × List String × List SExpr) := []
  let mut trees : List (String × ClauseProof) := []
  let mut earlierRules : List ACL2.RuleSpec := []
  let condsTy := mkApp (mkConst ``List [.zero]) (mkConst ``String)
  -- DIAGNOSTIC SINK for the pre-pass's SILENT drops (T1+2 sprint P5a, the
  -- J-P4b-g treatment applied here). P4b's item 2 could not answer why a
  -- demanded name produced NEITHER a registry entry NOR a failure line,
  -- because the two `continue`s below say nothing and the demand filter
  -- says nothing either. `ACL2LEAN_XBOOK_DIAG=1` prints one line per
  -- silent drop plus a closing census of demanded-but-unregistered names.
  -- stderr only, never a result line, never read by a gate; off by
  -- default. Do not harden it.
  let xdiag := (← IO.getEnv "ACL2LEAN_XBOOK_DIAG").isSome
  let mut offered : List String := []
  for (src, depDev) in depDevs do
    let dw := depDev.toWorld
    for (cp, _) in developmentTheoremsWithRules depDev do
      offered := offered ++ [s!"{src}/{cp.name}"]
    unless worldIncludes dw w do
      IO.println s!"    [cross-book {src}: world NOT included in \
        {bookKey} — transfer refused]"
      if xdiag then
        for (cp, _) in developmentTheoremsWithRules depDev do
          if demand.contains cp.name then
            IO.eprintln s!"[xbook-diag] {bookKey}: demanded {src}/{cp.name} \
              DROPPED — its book's world is not included"
      continue
    let thms := developmentTheoremsWithRules depDev
    let crossRules := earlierRules
    -- THE TRANSPORT prelude (phase 2 item 1): when the dep book's OWN
    -- module constants are visible (the coverage harness imports its
    -- covDeps — the module DAG), build the per-pair transport constant
    -- once; each demanded dep statement then transports instead of
    -- re-replaying. The focused CLI imports no coverage modules, so
    -- `anyDep` is false there and this costs nothing.
    let depThmDecl := fun (t : String) =>
      Name.mkStr2 "ReplayedStatements" (xSan s!"replayed_{src}_{t}")
    let depTermDecl := fun (fn : String) =>
      Name.mkStr2 "ReplayedTermination" (xSan s!"term_{src}_{fn}")
    let recTerms := recordedTerminationDefuns depDev.justifications depDev
    let envNow ← Lean.getEnv
    let anyDep := thms.any (fun (cp, _) => envNow.contains (depThmDecl cp.name))
      || recTerms.any (fun (fn, _) => envNow.contains (depTermDecl fn))
    let (pair?, dwExpr?) ←
      if anyDep then do
        let dwE ← reflectWorld dw
        pure (← tryBuildPairTransport bookKey src dw w dwE wExpr, some dwE)
      else pure (none, none)
    -- RECORDED ADMISSIONS of the dep book, at the CONSUMER's world. An
    -- :INCLUDE-BOOK'd defun carries no admission proof in the consumer's
    -- own log, so the consumer's totality prover walls on it and every
    -- dependency theorem whose replay needs that totality walls with it
    -- (`ORDEREDP-BSORT`/`HOW-MANY-QSORT` cross-replays, measured). The
    -- admission is the dep book's OWN recorded waterfall — replayed here
    -- exactly as its own book replays it, at the world that includes it.
    for (fn, tcp) in recTerms do
      if xterm.any (·.1 == fn) then continue
      let tBase := String.map (fun c => if c.isAlphanum then c else '_')
        s!"xterm_{bookKey}_{src}_{fn}"
      let tName := Name.mkStr2 "CrossBookTermination" tBase
      let tCondsName := Name.mkStr2 "CrossBookTermination" s!"{tBase}_conds"
      let tXa0 ← IO.monoMsNow  -- perf-arc phase 1 instrumentation
      let conds? ←
        if (← Lean.getEnv).contains tName then
          unless (← Lean.getEnv).contains tCondsName do
            throwError "crossBookRegistry: cached {tName} exists WITHOUT \
              its companion {tCondsName} (partial cache state or \
              sanitizer collision)"
          some <$> (unsafe Meta.evalExpr (List String) condsTy
            (mkConst tCondsName))
        else do
          -- THE TRANSPORT (phase 2 item 1c): the dep book's OWN
          -- recorded-admission constant, carried to this world by the
          -- pair transport — unconditional dep constants only,
          -- statement-matched, fail-closed to the re-replay below
          let transported ←
            match pair?, dwExpr? with
            | some pn, some dwE =>
              tryTransportDepConst pn dwE wExpr (depTermDecl fn)
                (disjoinTerm ((tcp.root.map (·.inputClause)).getD [])) tName
            | _, _ => pure false
          if transported then
            Lean.addAndCompile (.defnDecl {
              name := tCondsName, levelParams := [], type := condsTy,
              value := Lean.toExpr ([] : List String), hints := .opaque,
              safety := .safe })
            pure (some ([] : List String))
          else do
            let (status, r?) ← replayAdmission depDev w wExpr tcp tName
              (crossTrees := trees ++ bookTrees depDev)
              (replayed := reg) (crossRules := crossRules)
            match r? with
            | some cs =>
              Lean.addAndCompile (.defnDecl {
                name := tCondsName, levelParams := [], type := condsTy,
                value := Lean.toExpr cs, hints := .opaque, safety := .safe })
              pure (some cs)
            | none =>
              IO.println s!"    [cross-book termination {src}/{fn} @ \
                {bookKey}: {status}]"
              pure none
      if timings then  -- perf-arc phase 1 instrumentation
        IO.println s!"[t] xterm {src}/{fn}: {(← IO.monoMsNow) - tXa0} ms"
      if let some cs := conds? then
        -- the same circularity guard the in-book pre-pass uses
        unless admissionCircular fn cs do
          xterm := xterm ++
            [(fn, tName, cs, (tcp.root.map (·.inputClause)).getD [])]
    for (cp, rules) in thms do
      if !demand.contains cp.name then
        if xdiag then
          IO.eprintln s!"[xbook-diag] {bookKey}: {src}/{cp.name} not \
            DEMANDED (the seed's transitive closure does not reach it)"
        continue
      let some root := cp.root
        | if xdiag then
            IO.eprintln s!"[xbook-diag] {bookKey}: demanded {src}/{cp.name} \
              DROPPED — no reconstructed proof tree"
          continue
      let base := String.map (fun c => if c.isAlphanum then c else '_')
        s!"{bookKey}_{src}_{cp.name}"
      let mName := Name.mkStr2 "CrossBookReplayed" base
      let condsName := Name.mkStr2 "CrossBookReplayed" s!"{base}_conds"
      let formula := disjoinTerm root.inputClause
      -- CACHE (the `with_termination` pattern): a constant already
      -- declared for this (consumer world, dep book, theorem) is reused —
      -- the transfer is idempotent across the invocations of one module.
      -- The sanitizer is not injective, so a collision is possible; it is
      -- fail-closed (the constant is only ever APPLIED, and a type
      -- mismatch fails unification), but a partial cache state is named.
      if (← Lean.getEnv).contains mName then
        unless (← Lean.getEnv).contains condsName do
          throwError "crossBookRegistry: cached {mName} exists WITHOUT its \
            companion {condsName} (partial cache state or sanitizer \
            collision)"
        let conds ← unsafe Meta.evalExpr (List String) condsTy
          (mkConst condsName)
        reg := reg ++ [{ thm := cp.name, decl := mName, conds := conds,
                         formula := formula, crossBook := true }]
        continue
      -- THE TRANSPORT (phase 2 item 1b): the dep's OWN replayed
      -- constant, carried to this world by the pair transport —
      -- unconditional dep constants only, statement-matched,
      -- fail-closed to the re-replay below
      let transported ←
        match pair?, dwExpr? with
        | some pn, some dwE =>
          tryTransportDepConst pn dwE wExpr (depThmDecl cp.name)
            formula mName
        | _, _ => pure false
      if transported then
        Lean.addAndCompile (.defnDecl {
          name := condsName, levelParams := [], type := condsTy,
          value := Lean.toExpr ([] : List String), hints := .opaque,
          safety := .safe })
        reg := reg ++ [{ thm := cp.name, decl := mName, conds := [],
                         formula := formula, crossBook := true }]
        if timings then  -- perf-arc phase 2 instrumentation
          IO.println s!"[t] xthm {src}/{cp.name}: TRANSPORTED"
        continue
      let tXt0 ← IO.monoMsNow  -- perf-arc phase 1 instrumentation
      let (status, reg?) ← tryReplay depDev w wExpr cp rules
        (replayed := reg) (replayedName? := some mName)
        (termReplayed := xterm)
        (crossTrees := trees) (crossRules := crossRules)
      if timings then  -- perf-arc phase 1 instrumentation
        IO.println s!"[t] xthm {src}/{cp.name}: \
          {(← IO.monoMsNow) - tXt0} ms ({status})"
      match reg? with
      | some conds =>
        Lean.addAndCompile (.defnDecl {
          name := condsName, levelParams := [], type := condsTy,
          value := Lean.toExpr conds, hints := .opaque, safety := .safe })
        -- a CONDITIONAL cross entry is the one that can still frontier at
        -- the consumer (its kept conds must map onto the consumer's own
        -- telescope) — name it; unconditional entries stay silent.
        unless conds.isEmpty do
          IO.println s!"    [cross-book {src}/{cp.name} @ {bookKey}: \
            {status}]"
        reg := reg ++ [{ thm := cp.name, decl := mName, conds := conds,
                         formula := formula, crossBook := true }]
      | none =>
        IO.println s!"    [cross-book {src}/{cp.name} @ {bookKey}: \
          {status}]"
    -- the book's own trees/rules become OFFERS for the books after it —
    -- never for itself (a book's own rules reach its theorems through
    -- `rulesBefore`, which is creation-ordered; the whole-book set would
    -- offer a theorem its OWN stored rule, the self-premise the linear
    -- SELF-GATE documents)
    trees := trees ++ bookTrees depDev
    earlierRules := earlierRules ++ (allBookRules depDev).filter
      (fun r => !earlierRules.any (fun o => o.runeKey == r.runeKey))
  if timings then  -- perf-arc phase 1 instrumentation
    IO.println s!"[t] cross-book pre-pass total: \
      {(← IO.monoMsNow) - tXb0} ms ({xterm.length} admission(s), \
      {reg.length} registered theorem(s))"
  if xdiag then
    -- the closing census: what the seed demanded and the pre-pass never
    -- registered, and whether an offered book carries the name at all
    for n in demand do
      unless reg.any (·.thm == n) do
        let carriers := offered.filter (fun o => o.endsWith s!"/{n}")
        let carriedBy := if carriers.isEmpty then "NO dep book"
                         else String.intercalate ", " carriers
        IO.eprintln s!"[xbook-diag] {bookKey}: demanded {n} NOT registered \
          (offered by: {carriedBy})"
  return (reg, xterm)

/-- Attempt the DP-lift replay of one discharge leaf: prove the discharge node's
    claim `∃N∀f≥N, eval (disjoin clause) = some t` over a QUANTIFIED env (the
    obligation must hold for every environment), and kernel-check the proof. -/
def tryDischarge (w : World) (wExpr : Expr) (tps : List (String × SExpr))
    (totalEnv : List (String × Nat × Expr)) (id origin : String)
    (clause : SExpr) : TermElabM String := do
  -- fresh, BOUNDED heartbeat budget per leaf (the command itself runs unlimited;
  -- one pathological leaf must neither hang nor poison the rest), and runtime
  -- (timeout) exceptions report ✗ instead of failing the build. REAL bound
  -- (P1, see tryReplay): ~1M user units ≈ 40 s, margin over the slowest
  -- legitimate leaf (~17 s observed).
  withRealMaxHeartbeats 1000000 <| withRealMaxRecDepth 8192 <| tryCatchRuntimeEx
    (try
      let (p, conds) ← Meta.withLocalDeclD `env (mkConst ``ACL2.Env) fun envFV => do
        let cfg : ReplayConfig := { worldExpr := wExpr, envExpr := envFV, worldVal := w }
        let (prf, conds) ← replayDischargeLeaf cfg clause tps (assumeFact := true)
          (totalEnv := totalEnv)
        return (← Meta.mkLambdaFVars #[envFV] prf, conds)
      Meta.check p
      -- axiom filter (audit F8 residue, 2026-07-26): Meta.check accepts
      -- sorryAx, so the ✓ column was type-checked only. This probe's proof
      -- is never addDecl'd (the composed replayed-statement path is separately filtered
      -- at tryReplay), so this is REPORTING accuracy for the DP scoreboard,
      -- not a trust gate — but ✓ should mean what tryReplay's ✓ means.
      let axs ← collectProofAxioms p
      let bad := axs.filter (fun a =>
        a != ``propext && a != ``Classical.choice && a != ``Quot.sound)
      unless bad.isEmpty do
        throwError "discharge leaf uses forbidden axioms {bad}"
      -- An ASSUMED leaf (the DP fact is a bound hypothesis of the returned
      -- CONDITIONAL proof — its type states the missing obligation; no sorryAx;
      -- the lift/spine pipeline ran end-to-end) is reported as ◌, never as ✓.
      let assumed := conds.contains assumedDpFactCond
      let condStr := if conds.isEmpty then "" else s!" cond[{", ".intercalate conds}]"
      if assumed then return s!"{id}:{origin} ◌ assumed{condStr}"
      else return s!"{id}:{origin} ✓{condStr}"
    catch e =>
      return s!"{id}:{origin} ✗ ({(← e.toMessageData.toString).replace "\n" " "})")
    (fun e =>
      return s!"{id}:{origin} ✗ (runtime: {(← e.toMessageData.toString).replace "\n" " "})")

/-- Aggregated result of replaying one book — the sweep sums these across the
    corpus; the focused CLI prints one. `lines` is the golden-compared text. -/
structure BookResult where
  lines : Array String := #[]
  total : Nat := 0
  replayed : Nat := 0
  replayedCond : Nat := 0
  dpTotal : Nat := 0
  dpReplayed : Nat := 0
  dpAssumed : Nat := 0
  integrityFails : Array String := #[]
  emissionFrontiers : Array String := #[]

/-- Parse → reconstruct → replay every theorem of ONE book, in creation order,
    with the per-book D1 replayed registry — the exact sweep semantics (and the
    exact golden line text). `upTo`: stop AFTER the named theorem, and skip the
    (independent) DP-leaf attempts for the theorems before it — the focused
    CLI's target mode. Earlier theorems still REPLAY (never skipped): the
    replayed registry state at the target must be identical to the sweep's, so a
    focused row is directly comparable to the golden. -/
def runBook (name : String) (content : String) (upTo : Option String := none)
    (timings : Bool := false)
    (crossTrees : List (String × ClauseProof) := [])
    -- Include-DAG-gated offers (review-1 P1-8, fork-batch item 6's
    -- consumer, 2026-08-07): (source book key, its theorem trees) — the
    -- book's OWN emitted :INCLUDE-BOOK-EDGE set decides which sources'
    -- trees are offered (matched by path basename; a book with no edge
    -- to a source gets NOTHING from it). `crossTrees` remains the
    -- ungated channel for callers that pre-select (the pins).
    (crossTreesByBook : List (String × List (String × ClauseProof)) := [])
    -- WP5 CROSS-BOOK D1 TRANSFER: the dependency books' DEVELOPMENTS, in
    -- dependency order. Each demanded dependency theorem is replayed ONCE
    -- at THIS book's world, in its own book's channels, and registered
    -- (`crossBookRegistry`); the consumer's dependency discharges then
    -- apply the constant instead of re-replaying inside the consumer's
    -- telescope. Callers passing none keep the pre-WP5 route verbatim.
    (crossDevs : List (String × Development) := [])
    (crossRules : List ACL2.RuleSpec := [])
    -- R7b 2c (W4): the usefi: discharge composition, built by the CALLER
    -- (layering: it needs ParametricInstantiate, which sits above this
    -- module) and applied at each theorem's config; none = usefi conds
    -- stay kept verbatim (all pre-2c behavior).
    (usefiDischarge : Option (Development → ReplayConfig → ReplayCtx → UseFiSpec → MetaM Expr) := none) :
    TermElabM (BookResult × List (String × ClauseProof)
      × List ACL2.RuleSpec) := do
  let mut res : BookResult := {}
  let tParse0 ← IO.monoMsNow
  match ProofLog.parse content with
  | .error msg =>
    res := { res with lines := res.lines.push (s!"• {name}: PARSE-FAIL {msg}"),
                      integrityFails := res.integrityFails.push (s!"{name}: PARSE-FAIL {msg}") }
    return (res, [], [])
  | .ok log =>
    let tParse1 ← IO.monoMsNow
    if timings then IO.println s!"[t] parse: {tParse1 - tParse0} ms"
    match ClauseTree.buildDevelopment log with
    | .error msg =>
      res := { res with lines := res.lines.push (s!"• {name}: RECON-FAIL {msg}"),
                        integrityFails := res.integrityFails.push (s!"{name}: RECON-FAIL {msg}") }
      return (res, [], [])
    | .ok dev =>
      let tRecon ← IO.monoMsNow
      if timings then IO.println s!"[t] recon: {tRecon - tParse1} ms"
      let w := dev.toWorld
      -- the include-closure gate: every edge in this book's own log is in
      -- its transitive include set (nested includes fire during ld)
      let baseOf : String → String := fun p =>
        ((p.splitOn "/").getLast?.getD p).replace ".lisp" ""
      let includeBases := dev.includeEdges.map (fun (b, _) => baseOf b)
      let crossTrees := crossTrees ++
        (crossTreesByBook.filter (fun (src, _) =>
          includeBases.contains (baseOf src))).flatMap (·.2)
      -- per-FILE hoists (A3): the reflected world and the leaf harness's
      -- totality environment are env-independent — build each ONCE here
      -- instead of per theorem / per leaf
      let wExpr ← reflectWorld w
      let tW1 ← IO.monoMsNow
      if timings then IO.println s!"[t] toWorld+reflectWorld: {tW1 - tRecon} ms"
      -- LAZY per-book totality environment (perf WP1b, 2026-07-18): built on
      -- the FIRST DP-leaf attempt, then cached for the book (the A3
      -- once-per-file property preserved). Eager construction cost ~9 s on a
      -- 206-defun world before any theorem ran — pure waste for books/target
      -- runs that never reach a leaf. Same facts, same order — golden text
      -- unchanged.
      let mut leafTotalEnv? : Option (List (String × Nat × Expr)) := none
      let thms := developmentTheoremsWithRules dev
      let headerLine := s!"• {name}  (world: {w.defs.size} defun(s), {thms.length} theorem(s))"
      res := { res with lines := res.lines.push headerLine }
      if thms.isEmpty then
        let zeroLine := s!"{name}: 0 theorems reconstructed (failed/empty capture?)"
        res := { res with integrityFails := res.integrityFails.push zeroLine }
      -- D1 REPLAYED REGISTRY, per book (WP4): theorems are replayed in
      -- creation order (topological in the citation DAG), each green one
      -- addDecl'd as a replayed-statement constant that later SAME-BOOK consumers
      -- apply instead of re-replaying its tree. SEEDED (WP5) with the
      -- cross-book transfer's entries — dependency-book trees replayed at
      -- THIS book's world; the per-book reset otherwise stands, since a
      -- constant is only ever stated over the world it was replayed at.
      let (crossReg, crossTerm) ←
        if crossDevs.isEmpty then
          pure (([] : ReplayedRegistry),
                ([] : List (String × Name × List String × List SExpr)))
        else crossBookRegistry name w wExpr crossDevs (bookDemandSeed dev) (timings := timings)
      let mut replayed : ReplayedRegistry := crossReg
      -- RECORDED-TERMINATION replayed statements (sorting arc 2026-07-28): defuns whose
      -- admission decrease is beyond the destructor walk get their recorded
      -- admission waterfall replayed ONCE per book as a conditional replayed statement
      -- constant; the totality prover applies it at each consumer's
      -- telescope (the D1 replayed-constant pattern). A FAILED replay keeps the fn on
      -- the destructor route's honest frontier — no silent change. The
      -- budget is the admission-class guard (see tryReplay's budget doc).
      -- SEEDED (WP5) with the dependency books' admissions replayed at THIS
      -- world: an :INCLUDE-BOOK'd defun has no admission proof in this
      -- book's log, so its totality had no route at all — the transfer
      -- supplies the dep book's own recorded waterfall.
      let recTermDefuns := recordedTerminationDefuns dev.justifications dev
      let mut termReplayed : List (String × Name × List String × List SExpr)
        := crossTerm.filter fun (fn, _, _, _) =>
             !recTermDefuns.any (fun (g, _) => g == fn)
      -- PRE-TERMINATION D1 REGISTRY (WP5): the SAME-BOOK theorems a recorded
      -- admission cites, replayed BEFORE it and registered, so its
      -- dependency discharges APPLY the constant. `replayAdmission`'s rule
      -- offer is DEMAND-filtered to the admission's own cited runes, so a
      -- dependency re-replayed inside that telescope walls on the rules the
      -- filter dropped — HOW-MANY-BAD-PAIRS-BNEXT (bsort's `:LINEAR`
      -- source) walls exactly there, on `rule:HOW-MANY-SMALLER-BNEXT`.
      -- ACL2's own chronology is this order: it proves those theorems
      -- BEFORE it admits the defun. Distinct constant names from the main
      -- loop's, which replays and registers each theorem in its own right.
      -- CIRCULARITY: a pre-entry conditional on a pre-passed defun's own
      -- totality/TP is discarded (the `admissionCircular` rule, applied to
      -- every recorded-termination fn — the admission telescope would
      -- otherwise resolve it to its own hypothesis fvar).
      let termCited := (recTermDefuns.flatMap fun (_, tcp) =>
        citedRuneNamesDeep tcp).eraseDups
      for (cp, rules) in thms do
        if !termCited.contains cp.name then continue
        let pName := Name.mkStr2 "PreTermReplayed"
          (String.map (fun c => if c.isAlphanum then c else '_')
            s!"pre_{name}_{cp.name}")
        if (← Lean.getEnv).contains pName then continue
        let tPt0 ← IO.monoMsNow  -- perf-arc phase 1 instrumentation
        let (status, reg?) ← tryReplay dev w wExpr cp rules
          (replayed := replayed) (replayedName? := some pName)
          (crossTrees := crossTrees) (crossRules := crossRules)
        if timings then  -- perf-arc phase 1 instrumentation
          IO.println s!"[t] pre-term {cp.name}: \
            {(← IO.monoMsNow) - tPt0} ms"
        match reg? with
        | some conds =>
          if recTermDefuns.any (fun (fn, _) => admissionCircular fn conds) then
            IO.println s!"    [pre-termination {name}/{cp.name}: entry \
              DISCARDED — conditional on a pre-passed defun's own facts \
              (circularity guard)]"
          else
            replayed := replayed ++
              [{ thm := cp.name, decl := pName, conds := conds,
                 formula := disjoinTerm ((cp.root.map (·.inputClause)).getD []) }]
        | none =>
          IO.println s!"    [pre-termination {name}/{cp.name}: {status}]"
      for (fn, tcp) in recTermDefuns do
        let mName := Name.mkStr2 "ReplayedTermination"
          (String.map (fun c => if c.isAlphanum then c else '_')
            s!"term_{name}_{fn}")
        let tTm0 ← IO.monoMsNow
        let (status, reg?) ← replayAdmission dev w wExpr tcp mName
          (crossTrees := crossTrees) (replayed := replayed)
        let tTm1 ← IO.monoMsNow
        if timings then
          IO.println s!"[t] termination {fn}: {tTm1 - tTm0} ms ({status})"
        -- the termination replay's status is a ROW, not just a timing print
        -- (validator/lifter arc W1 item 6 — the survey found the class
        -- INVISIBLE to the golden: a termination replayed statement
        -- silently regressing to FAIL only showed up indirectly)
        let termRow := s!"    termination:{fn} → {status}"
        res := { res with lines := res.lines.push termRow }
        if let some conds := reg? then
          -- CIRCULARITY guard (audit F3): the admission proof precedes the
          -- defun — a replayed statement conditional on the defun's OWN totality/TP
          -- would let `thmAt` resolve the condition to the consumer's
          -- hypothesis fvar and silently accept the circle as an "honest
          -- condition". Chronology makes it near-impossible (admission-time
          -- runes only), but the guard is structural, not probabilistic.
          if admissionCircular fn conds then
            IO.println s!"    [termination {fn}: replayed statement DISCARDED — \
              conditional on its own {fn} facts (circularity guard)]"
          else
            let goalLits := (tcp.root.map (·.inputClause)).getD []
            termReplayed := termReplayed ++ [(fn, mName, conds, goalLits)]
      for (cp, rules) in thms do
        res := { res with total := res.total + 1 }
        -- EMISSION FRONTIER (Track B): a black-box PROVED leaf — ACL2 discharged
        -- the clause by preprocess/eval/type-set but emitted no replayable
        -- structure. Marked unhandled and HARD-FAILED by the sweep (not a silent green).
        let bb := theoremBlackBoxLeaves cp
        unless bb.isEmpty do
          let bbLine := s!"{name}/{cp.name}: black-box PROVED leaf(s) [{", ".intercalate bb}]"
          res := { res with emissionFrontiers := res.emissionFrontiers.push bbLine }
        -- Discharge leaves (decision-procedure nodes): emission-complete under the
        -- ratified carve-out; attempt the DP-lift replay (c1) per leaf.
        let dis := theoremDischargeLeaves cp
        let tps := dev.typePrescriptions
        let mName := Name.mkStr2 "ReplayedStatements"
          (String.map (fun c => if c.isAlphanum then c else '_')
            s!"replayed_{name}_{cp.name}")
        let tThm0 ← IO.monoMsNow
        -- FI-citing rows carry the applied usefi constants through the
        -- remaining passes — structurally larger by design, entitled to
        -- the admission-class window (same budget-methodology note as
        -- tryReplay's docstring)
        let rowBudget := if (ACL2.Replay.Driver.theoremFnInstanceCites
            cp).isEmpty then 3000000 else 10000000
        let (status, reg?) ← tryReplay dev w wExpr cp rules
          (replayed := replayed) (replayedName? := some mName)
          (termReplayed := termReplayed) (crossTrees := crossTrees)
          (crossRules := crossRules) (usefiDischarge := usefiDischarge)
          (budget := rowBudget)
        let tThm1 ← IO.monoMsNow
        if timings then IO.println s!"[t] theorem {cp.name}: {tThm1 - tThm0} ms"
        if let some conds := reg? then
          replayed := replayed ++
            [{ thm := cp.name, decl := mName, conds := conds,
               formula := disjoinTerm ((cp.root.map (·.inputClause)).getD []) }]
        if status.startsWith "REPLAYED ✓" then
          res := { res with replayed := res.replayed + 1 }
          -- CONDITIONAL replays (undischarged cond[…] hypotheses) counted
          -- separately: a rule:<thm>-conditional replay is NOT the same
          -- claim as an unconditional one (audit 2026-07-06, outside
          -- reviewer) — the summary must not blend them silently.
          if (status.splitOn " cond[").length > 1 then
            res := { res with replayedCond := res.replayedCond + 1 }
        let tag := if bb.isEmpty then "" else
          s!"  [EMISSION-FRONTIER: black-box leaf {", ".intercalate bb}]"
        -- target mode: DP leaves are theorem-independent — skip them for
        -- non-target theorems (their replays still ran, for the registry)
        let isTarget := upTo.map (· == cp.name) |>.getD true
        let mut disParts : List String := []
        if isTarget && !dis.isEmpty then
          let leafTotalEnv ← match leafTotalEnv? with
            | some te => pure te
            | none => do
              let tTE0 ← IO.monoMsNow
              let te ← Meta.withLocalDeclD `env (mkConst ``ACL2.Env) fun envFV => do
                -- gzDefs (T1+2 sprint P3b): the DP-probe totality sweep
                -- used the SAME prover as the main harness but from a
                -- config with no ground-zero snapshot — so a fn whose
                -- admission reads a builtin-EXCLUDED snapshot (`O-P`'s
                -- `EQL` ruler; `gzDefs` is the only place such a body
                -- lives) failed here while proving there. Same input,
                -- same answer.
                let cfg : ReplayConfig :=
                  { worldExpr := wExpr, envExpr := envFV, worldVal := w,
                    gzDefs := dev.groundZeroSnapshotDefs }
                -- same engineering limit as tryReplay/tryDischarge (the
                -- helper's docstring): the totality sweep over a large
                -- included world runs within ~1 frame of the default 512
                -- (final close-out, sorts-equivalent: warm meta caches from
                -- a preceding in-node DP discharge pushed one defeq path
                -- past it — a runtime-class throw no plain catch intercepts)
                ACL2.Replay.Driver.withRealMaxRecDepth 8192 <|
                  buildTotalEnv cfg dev.justifications
              let tTE1 ← IO.monoMsNow
              if timings then IO.println s!"[t] buildTotalEnv (lazy): {tTE1 - tTE0} ms"
              pure te
          leafTotalEnv? := some leafTotalEnv
          for (id, o, clause) in dis do
            res := { res with dpTotal := res.dpTotal + 1 }
            let tDp0 ← IO.monoMsNow  -- perf-arc phase 1 instrumentation
            let r ← tryDischarge w wExpr tps leafTotalEnv id o clause
            if timings then  -- perf-arc phase 1 instrumentation
              IO.println s!"[t] dp-leaf {cp.name} {id}:{o}: \
                {(← IO.monoMsNow) - tDp0} ms"
            if (r.splitOn "✓").length > 1 then
              res := { res with dpReplayed := res.dpReplayed + 1 }
            if (r.splitOn "◌").length > 1 then
              res := { res with dpAssumed := res.dpAssumed + 1 }
            disParts := disParts ++ [r]
        let disTag := if disParts.isEmpty then "" else
          s!"  [DISCHARGE: {", ".intercalate disParts}]"
        let row := s!"    {cp.name} → {status}{tag}{disTag}"
        res := { res with lines := res.lines.push row }
        if upTo == some cp.name then
          return (res, bookTrees dev, allBookRules dev)
      return (res, bookTrees dev, allBookRules dev)

end ACL2.Replay.Runner
