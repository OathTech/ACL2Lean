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

/-- The emitted type-prescription corollaries of a development (fn name ↦
    corollary term) — the type facts the DP lift may consume as hypotheses. -/
partial def developmentTPs : Development → List (String × SExpr)
  | .bind (.typePrescription n cor _ _) rest => (n, cor) :: developmentTPs rest
  | .bind _ rest => developmentTPs rest
  | .done => []

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

/-- Origins of the DECISION-PROCEDURE DISCHARGE nodes (emitted at the discharge
    sites in `tau-clausep` / `built-in-clausep`): the top-level node recording that
    ACL2 closed the clause by a verdict-only decision procedure. Under the ratified
    carve-out (CLAUDE.md, 2026-06-09) such a leaf is EMISSION-complete — the replay
    obligation is to discharge the recorded clause by a kernel-checked decision
    procedure (omega / lean-smt) in the driver. -/
def dischargeOrigins : List String :=
  ["preprocess/tau", "preprocess/tau-contradiction", "preprocess/type-set-fc",
   "preprocess/trivial-clause", "preprocess/built-in-clause"]

private def itemDischargeOrigins : ClauseItem → List (String × SExpr)
  | .literal _ => []
  | .step (.node _ lhs _ _ prov) =>
      if dischargeOrigins.contains prov.origin then [(prov.origin, lhs)] else []
  | .clausify _ => []
  | .branch _ items => items.flatMap itemDischargeOrigins

/-- Per-theorem: the discharge nodes on PROVED leaves — `(clauseId, origin, the
    discharged clause)`. These leaves are emission-complete; their replay is the
    DP lift (`replayDischargeLeaf`), attempted below per leaf. -/
partial def theoremDischargeLeaves (cp : ClauseProof) : List (String × String × SExpr) :=
  let rec go (n : ClauseNode) : List (String × String × SExpr) :=
    let here :=
      if n.children.isEmpty && n.induction.isNone then
        (n.steps.flatMap (·.items.flatMap itemDischargeOrigins)).map
          (fun (o, lhs) => (n.idStr, o, lhs))
      else []
    here ++ n.children.flatMap go
  (cp.root.map go).getD []

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
    status, and — when `mirrorName?` is given and the replay is green — the
    kept condition strings of the freshly `addDecl`'d D1 MIRROR CONSTANT
    (design §D1, WP4: subsequent same-book consumers apply the constant via
    the `MirrorRegistry` instead of re-replaying this theorem's tree). The
    world is PROJECTED from the development and REFLECTED concretely (P4);
    structural facts are DERIVED by the driver (P3). A message that is
    neither a `replayClause`/`replayNode`/`replayLiteral` frontier flags a
    real bug in the new code, not an expected frontier. -/
def tryReplay (w : World) (wExpr : Expr) (tps : List (String × SExpr))
    (justs : List (String × ACL2.Justification)) (cp : ClauseProof)
    (rules : List ACL2.RuleSpec := [])
    (depProofs : List (String × ClauseProof) := [])
    (gzDefs : List (Symbol × List Symbol × SExpr) := [])
    (mirrors : MirrorRegistry := [])
    (mirrorName? : Option Name := none) :
    TermElabM (String × Option (List String)) := do
  -- bounded per-theorem budget + runtime-exception capture, as for tryDischarge.
  -- REAL bound (P1): withOptions(maxHeartbeats) was a NO-OP — Core.Context
  -- pins it at command-context creation; ~1M user units ≈ 40 s, a runaway
  -- guard with margin over the slowest legitimate replay (~9 s observed).
  withRealMaxHeartbeats 1000000 <| withRealMaxRecDepth 8192 <| tryCatchRuntimeEx
    (try
      let p ← Meta.withLocalDeclD `env (mkConst ``ACL2.Env) fun envFV => do
        let cfg : ReplayConfig := { worldExpr := wExpr, envExpr := envFV, worldVal := w,
                                    gzDefs := gzDefs, justs := justs }
        let (prf, conds) ← replayProofConditional cfg tps cp justs rules depProofs
          mirrors
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
      -- D1: emit the mirror constant (checked + axiom-clean above)
      let mut registered : Option (List String) := none
      if let some nm := mirrorName? then
        -- name-collision guard (audit 2026-07-15): the sanitization
        -- (non-alphanumerics ↦ '_') is not injective across (book, theorem)
        -- pairs — name the collision instead of surfacing addDecl's
        -- "already declared" as a bare FAIL on a green replay
        if (← Lean.getEnv).contains nm then
          return (s!"FAIL: mirror-constant name collision: {nm} (sanitized \
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
    with the per-book D1 mirror registry — the exact sweep semantics (and the
    exact golden line text). `upTo`: stop AFTER the named theorem, and skip the
    (independent) DP-leaf attempts for the theorems before it — the focused
    CLI's target mode. Earlier theorems still REPLAY (never skipped): the
    mirror registry state at the target must be identical to the sweep's, so a
    focused row is directly comparable to the golden. -/
def runBook (name : String) (content : String) (upTo : Option String := none)
    (timings : Bool := false) : TermElabM BookResult := do
  let mut res : BookResult := {}
  let tParse0 ← IO.monoMsNow
  match ProofLog.parse content with
  | .error msg =>
    res := { res with lines := res.lines.push (s!"• {name}: PARSE-FAIL {msg}"),
                      integrityFails := res.integrityFails.push (s!"{name}: PARSE-FAIL {msg}") }
    return res
  | .ok log =>
    let tParse1 ← IO.monoMsNow
    if timings then IO.println s!"[t] parse: {tParse1 - tParse0} ms"
    match ClauseTree.buildDevelopment log with
    | .error msg =>
      res := { res with lines := res.lines.push (s!"• {name}: RECON-FAIL {msg}"),
                        integrityFails := res.integrityFails.push (s!"{name}: RECON-FAIL {msg}") }
      return res
    | .ok dev =>
      let tRecon ← IO.monoMsNow
      if timings then IO.println s!"[t] recon: {tRecon - tParse1} ms"
      let w := dev.toWorld
      -- per-FILE hoists (A3): the reflected world and the leaf harness's
      -- totality environment are env-independent — build each ONCE here
      -- instead of per theorem / per leaf
      let tW0 ← IO.monoMsNow
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
      -- addDecl'd as a mirror constant that later SAME-BOOK consumers
      -- apply instead of re-replaying its tree. Reset per book — the
      -- constants are stated over THIS book's world (cross-book reuse is
      -- WP5's transfer).
      let mut mirrors : MirrorRegistry := []
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
        let tps := developmentTPs dev
        let mName := Name.mkStr2 "CoverageMirrors"
          (String.map (fun c => if c.isAlphanum then c else '_')
            s!"mirror_{name}_{cp.name}")
        let tThm0 ← IO.monoMsNow
        let (status, reg?) ← tryReplay w wExpr tps dev.justifications cp rules
          (thms.map fun (c, _) => (c.name, c))
          (gzDefs := dev.groundZeroSnapshotDefs)
          (mirrors := mirrors) (mirrorName? := some mName)
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
          return res
      return res

end ACL2.Replay.Runner
