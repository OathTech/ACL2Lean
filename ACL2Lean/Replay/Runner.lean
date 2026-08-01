/-
  The REPLAY RUNNER — the per-book replay harness, shared between the
  corpus coverage sweep (`Tests/DriverCoverage.lean`, the golden-gated
  build-time sweep) and the FOCUSED runtime CLI (`acl2lean-replay`,
  `ReplayMain.lean`) — the fast OODA loop (perf arc WP1, 2026-07-18).

  DELIBERATELY NOT imported by the root `ACL2Lean` module: the focused
  CLI's whole point is a minimal import cone (Driver + reconstruction, no
  `Imported/NativeMirrors`, no `Tests`), so a driver edit rebuilds only
  this cone and a single book replays at runtime in seconds instead of a
  full-corpus re-elaboration.

  Report-line semantics here are the GOLDEN-COMPARED text: any change to a
  line format shows up as a coverage-golden diff. The focused run must
  print the same rows the sweep would, so results are directly comparable.
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.ProofLog
import ACL2Lean.ClauseTree
import Lean

open ACL2 ACL2.Replay.Driver Lean Lean.Elab Lean.Meta

namespace ACL2.Replay.Runner

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
      precondition of `dischargeDecrease`'s frontier. -/
  needsRecorded (just : Justification) : Bool :=
    just.terminationClauses.any fun c =>
      match c.toList? with
      | some lits => lits.any fun l =>
        match l with
        | .cons (.atom (.symbol olt))
            (.cons (.cons (.atom (.symbol cnt1)) (.cons d .nil)) _) =>
          olt.name == "O<" && cnt1.name == "ACL2-COUNT" && !chainOk d
        | _ => false
      | none => false
  chainOk : SExpr → Bool
    | .atom (.symbol _) => true
    | .cons (.atom (.symbol d)) (.cons u .nil) =>
      (d.name == "CDR" || d.name == "CAR" || d.name == "EVENS"
        || d.name == "ODDS") && chainOk u
    | _ => false

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
    (`runBook`) and the `driver_replayed%` mirror macro BOTH consume this
    structure — a channel added for one is automatically seen by the other.
    The bug class this closes is real: `fcRules`, the termination pre-pass,
    and `equivRefls` each hard-failed the macro AFTER the runner had them
    (mirror program 2026-07-31), and the macro's hand-built config was
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

/-- The channel set of a development — the single derivation site.
    `crossTrees`: prior books' theorem trees (2a); appended AFTER the
    same-book entries so same-book precedence is unchanged. -/
def bookChannels (dev : Development)
    (crossTrees : List (String × ClauseProof) := []) : BookChannels :=
  let thms := developmentTheoremsWithRules dev
  { thms := thms
    tps := dev.typePrescriptions
    depProofs := (thms.map fun (c, _) => (c.name, c)) ++ crossTrees
    localTrees := thms.map fun (c, _) => (c.name, c)
    equivRefls := (thms.map fun (c, _) => (c.name, c.formula))
      ++ dev.includedTheorems }

/-- The canonical `ReplayConfig` of a book replay — the ONE construction
    site for both the runner and the mirror macro. `gzTps`: BUILTIN-named
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
      (w.defs.get? { name := n }).isNone }

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
      if let some v := ci.value? then
        work := work ++ v.getUsedConstants.toList
    | none => pure ()
  return axioms.eraseDups

/-- Run the driver on one theorem over its derived world; return a one-line
    status, and — when `replayedName?` is given and the replay is green — the
    kept condition strings of the freshly `addDecl`'d D1 MIRROR CONSTANT
    (design §D1, WP4: subsequent same-book consumers apply the constant via
    the `ReplayedRegistry` instead of re-replaying this theorem's tree). The
    world is PROJECTED from the development and REFLECTED concretely (P4);
    structural facts are DERIVED by the driver (P3). A message that is
    neither a `replayClause`/`replayNode`/`replayLiteral` frontier flags a
    real bug in the new code, not an expected frontier. -/
def tryReplay (dev : Development) (w : World) (wExpr : Expr)
    (cp : ClauseProof) (rules : List ACL2.RuleSpec := [])
    (mirrors : ReplayedRegistry := [])
    (replayedName? : Option Name := none)
    (budget : Nat := 3000000)
    (termReplayed : List (String × Name × List String × List SExpr) := [])
    (crossTrees : List (String × ClauseProof) := []) :
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
        let ch := bookChannels dev crossTrees
        let cfg := mkBookConfig dev w wExpr envFV termReplayed
        let (prf, conds) ← replayProofConditional cfg ch.tps cp
          dev.justifications rules ch.depProofs mirrors
          (equivRefls := ch.equivRefls) termReplayed
          (congTrees := some ch.localTrees)
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
    (crossTrees : List (String × ClauseProof) := []) :
    TermElabM (String × Option (List String)) := do
  let thms := developmentTheoremsWithRules dev
  let cited := citedRuneNames tcp
  let termRules := ((thms.map (·.2)).flatten.filter
    (fun r => cited.contains r.name)).eraseDups
  tryReplay dev w wExpr tcp termRules
    (replayedName? := some mName) (budget := 10000000)
    (crossTrees := crossTrees)

/-- The termination-mirror CIRCULARITY predicate (audit F3): an admission
    proof conditional on the defun's OWN totality/TP facts must be
    discarded — `thmAt` would resolve the condition to the consumer's
    hypothesis fvar and silently accept the circle. One predicate, both
    call sites (runner discards; the macro skips loudly). -/
def admissionCircular (fn : String) (conds : List String) : Bool :=
  conds.contains s!"total:{fn}" || conds.contains s!"tp:{fn}"

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
      -- is never addDecl'd (the composed mirror path is separately filtered
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
      let assumed := conds.contains "ASSUMED:dp-fact"
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
    (crossTrees : List (String × ClauseProof) := []) :
    TermElabM (BookResult × List (String × ClauseProof)) := do
  let mut res : BookResult := {}
  let tParse0 ← IO.monoMsNow
  match ProofLog.parse content with
  | .error msg =>
    res := { res with lines := res.lines.push (s!"• {name}: PARSE-FAIL {msg}"),
                      integrityFails := res.integrityFails.push (s!"{name}: PARSE-FAIL {msg}") }
    return (res, [])
  | .ok log =>
    let tParse1 ← IO.monoMsNow
    if timings then IO.println s!"[t] parse: {tParse1 - tParse0} ms"
    match ClauseTree.buildDevelopment log with
    | .error msg =>
      res := { res with lines := res.lines.push (s!"• {name}: RECON-FAIL {msg}"),
                        integrityFails := res.integrityFails.push (s!"{name}: RECON-FAIL {msg}") }
      return (res, [])
    | .ok dev =>
      let tRecon ← IO.monoMsNow
      if timings then IO.println s!"[t] recon: {tRecon - tParse1} ms"
      let w := dev.toWorld
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
      -- D1 MIRROR REGISTRY, per book (WP4): theorems are replayed in
      -- creation order (topological in the citation DAG), each green one
      -- addDecl'd as a replayed-statement constant that later SAME-BOOK consumers
      -- apply instead of re-replaying its tree. Reset per book — the
      -- constants are stated over THIS book's world (cross-book reuse is
      -- WP5's transfer).
      let mut mirrors : ReplayedRegistry := []
      -- RECORDED-TERMINATION mirrors (sorting arc 2026-07-28): defuns whose
      -- admission decrease is beyond the destructor walk get their recorded
      -- admission waterfall replayed ONCE per book as a conditional replayed statement
      -- constant; the totality prover applies it at each consumer's
      -- telescope (the D1 mirror pattern). A FAILED replay keeps the fn on
      -- the destructor route's honest frontier — no silent change. The
      -- budget is the admission-class guard (see tryReplay's budget doc).
      let mut termReplayed : List (String × Name × List String × List SExpr) := []
      let recTermDefuns := recordedTerminationDefuns dev.justifications dev
      for (fn, tcp) in recTermDefuns do
        let mName := Name.mkStr2 "ReplayedTermination"
          (String.map (fun c => if c.isAlphanum then c else '_')
            s!"term_{name}_{fn}")
        let tTm0 ← IO.monoMsNow
        let (status, reg?) ← replayAdmission dev w wExpr tcp mName
          (crossTrees := crossTrees)
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
          -- defun — a mirror conditional on the defun's OWN totality/TP
          -- would let `thmAt` resolve the condition to the consumer's
          -- hypothesis fvar and silently accept the circle as an "honest
          -- condition". Chronology makes it near-impossible (admission-time
          -- runes only), but the guard is structural, not probabilistic.
          if admissionCircular fn conds then
            IO.println s!"    [termination {fn}: mirror DISCARDED — \
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
        let (status, reg?) ← tryReplay dev w wExpr cp rules
          (mirrors := mirrors) (replayedName? := some mName)
          (termReplayed := termReplayed) (crossTrees := crossTrees)
        let tThm1 ← IO.monoMsNow
        if timings then IO.println s!"[t] theorem {cp.name}: {tThm1 - tThm0} ms"
        if let some conds := reg? then
          mirrors := mirrors ++ [(cp.name, mName, conds)]
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
                let cfg : ReplayConfig :=
                  { worldExpr := wExpr, envExpr := envFV, worldVal := w }
                buildTotalEnv cfg dev.justifications
              let tTE1 ← IO.monoMsNow
              if timings then IO.println s!"[t] buildTotalEnv (lazy): {tTE1 - tTE0} ms"
              pure te
          leafTotalEnv? := some leafTotalEnv
          for (id, o, clause) in dis do
            res := { res with dpTotal := res.dpTotal + 1 }
            let r ← tryDischarge w wExpr tps leafTotalEnv id o clause
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
          return (res, bookTrees dev)
      return (res, bookTrees dev)

end ACL2.Replay.Runner
