/-
  Driver coverage harness over the whole sample corpus.

  For every `.proof-log` in the corpus, this parses → reconstructs → projects the World
  (`Development.toWorld`) → runs the replay driver on each local theorem, recording per
  theorem whether it REPLAYED (the driver emitted a kernel-valid proof Expr) or the exact
  failure message. Most theorems fail-closed at a frontier today (induction, type-set,
  multi-arg unfold, exec-counterpart, …) — those are EXPECTED clean failures; the value is
  (1) exercising the new derive-on-demand / `toWorld` / `reflectWorld` code across diverse
  worlds (incl. `simple.proof-log`, two defuns), surfacing any real bug as a non-frontier
  message, and (2) a live coverage table that fills in as node kinds / the induction
  scaffold land.

  ON DEMAND (not in the `just ci` aggregate — it runs the driver over the whole corpus):
      lake build Tests.DriverCoverage
  reads the table from the build output.

  NO SILENT SKIPS: each log is `include_str`'d, so (a) an ABSENT log is a HARD compile
  error naming the file (never silently skipped, never cached away), and (b) lake tracks
  the logs as dependencies and re-runs when they change. Logs are gitignored; regenerate
  the corpus with `scripts/capture-proof-log.sh` before building this.
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.ProofLog
import ACL2Lean.ClauseTree
import Lean

open ACL2 ACL2.Replay.Driver Lean Lean.Elab Lean.Elab.Command Lean.Meta

namespace ACL2.Tests.Coverage

/-- Every theorem (in file order) of a reconstructed development. -/
partial def developmentTheorems : Development → List ClauseProof
  | .bind (.theorem cp) rest => cp :: developmentTheorems rest
  | .bind _ rest => developmentTheorems rest
  | .done => []

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

/-- The corpus as `(name, log-content)` pairs. Each log is `include_str`'d (a missing one
    is a hard compile error here — no silent skip — and lake re-runs on change). -/
def corpus : List (String × String) :=
  [("simple",                  include_str "../acl2_samples/simple.proof-log"),
   ("00-direct",               include_str "../acl2_samples/recon-tests/00-direct.proof-log"),
   ("01-multi-theorem",        include_str "../acl2_samples/recon-tests/01-multi-theorem.proof-log"),
   ("02-rev",                  include_str "../acl2_samples/recon-tests/02-rev.proof-log"),
   ("03-linear",               include_str "../acl2_samples/recon-tests/03-linear.proof-log"),
   ("04-multi-case-induction", include_str "../acl2_samples/recon-tests/04-multi-case-induction.proof-log"),
   ("05-hints",                include_str "../acl2_samples/recon-tests/05-hints.proof-log"),
   ("06-measure",              include_str "../acl2_samples/recon-tests/06-measure.proof-log"),
   ("07-mutual-recursion",     include_str "../acl2_samples/recon-tests/07-mutual-recursion.proof-log"),
   ("08-equality-reasoning",   include_str "../acl2_samples/recon-tests/08-equality-reasoning.proof-log"),
   ("09-defn-unfold",          include_str "../acl2_samples/recon-tests/09-defn-unfold.proof-log"),
   ("10-tree-induction",       include_str "../acl2_samples/recon-tests/10-tree-induction.proof-log"),
   ("11-custom-measure",       include_str "../acl2_samples/recon-tests/11-custom-measure.proof-log"),
   ("12-multi-controller",     include_str "../acl2_samples/recon-tests/12-multi-controller.proof-log"),
   ("13-multi-measured-var",   include_str "../acl2_samples/recon-tests/13-multi-measured-var.proof-log"),
   ("14-accumulator",          include_str "../acl2_samples/recon-tests/14-accumulator.proof-log"),
   ("15-nested-induction",     include_str "../acl2_samples/recon-tests/15-nested-induction.proof-log"),
   ("16-three-way",            include_str "../acl2_samples/recon-tests/16-three-way.proof-log")]

/-- Run the driver on one theorem over its derived world; return a one-line status. The
    world is PROJECTED from the development and REFLECTED concretely (P4); structural facts
    are DERIVED by the driver (P3). A message that is neither a `replayClause`/`replayNode`/
    `replayLiteral` frontier flags a real bug in the new code, not an expected frontier. -/
def tryReplay (w : World) (tps : List (String × SExpr)) (cp : ClauseProof) :
    TermElabM String := do
  let wExpr ← reflectWorld w
  -- bounded per-theorem budget + runtime-exception capture, as for tryDischarge
  withOptions (fun o => o.set `maxHeartbeats (1000000 : Nat)) <|
    Core.withCurrHeartbeats <| tryCatchRuntimeEx
    (try
      let p ← Meta.withLocalDeclD `env (mkConst ``ACL2.Env) fun envFV => do
        let cfg : ReplayConfig := { worldExpr := wExpr, envExpr := envFV, worldVal := w }
        let (prf, conds) ← replayProofConditional cfg tps cp
        return (← Meta.mkLambdaFVars #[envFV] prf, conds)
      Meta.check p.1
      let condStr := if p.2.isEmpty then "" else s!" cond[{", ".intercalate p.2}]"
      return s!"REPLAYED ✓{condStr}"
    catch e => return s!"FAIL: {(← e.toMessageData.toString).replace "\n" " "}")
    (fun e =>
      return s!"FAIL: (runtime: {(← e.toMessageData.toString).replace "\n" " "})")

/-- Attempt the DP-lift replay of one discharge leaf: prove the discharge node's
    claim `∃N∀f≥N, eval (disjoin clause) = some t` over a QUANTIFIED env (the
    obligation must hold for every environment), and kernel-check the proof. -/
def tryDischarge (w : World) (tps : List (String × SExpr)) (id origin : String)
    (clause : SExpr) : TermElabM String := do
  let wExpr ← reflectWorld w
  -- fresh, BOUNDED heartbeat budget per leaf (the command itself runs unlimited;
  -- one pathological leaf must neither hang nor poison the rest), and runtime
  -- (timeout) exceptions report ✗ instead of failing the build.
  withOptions (fun o => o.set `maxHeartbeats (200000 : Nat)) <|
    Core.withCurrHeartbeats <| tryCatchRuntimeEx
    (try
      let (p, conds) ← Meta.withLocalDeclD `env (mkConst ``ACL2.Env) fun envFV => do
        let cfg : ReplayConfig := { worldExpr := wExpr, envExpr := envFV, worldVal := w }
        let (prf, conds) ← replayDischargeLeaf cfg clause tps (assumeFact := true)
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

elab "#driver_coverage" : command => do
  liftTermElabM do
    let mut lines : Array String := #[]
    let mut replayed := 0
    let mut total := 0
    -- Reconstruction-INTEGRITY failures (distinct from the expected driver-replay
    -- frontier): a parse-fail, a recon-fail, or a log that reconstructs to ZERO
    -- theorems (a failed/empty capture — every recon-test .lisp has ≥1 defthm). These
    -- HARD-FAIL the build below, so a broken/empty corpus log can't slip through as a
    -- silent "0 theorem(s)" line (as a header-only 00-direct capture once did). The
    -- per-theorem replay FAILs are NOT integrity failures — they are the expected frontier.
    let mut integrityFails : Array String := #[]
    -- EMISSION-FRONTIER failures: theorems containing a black-box PROVED leaf (Track B
    -- gap). Deliberately HARD-FAIL until the preprocess/eval/type-set emission lands.
    let mut emissionFrontiers : Array String := #[]
    -- DP-lift replay (c1/c2) tally over discharge leaves.
    let mut dpTotal := 0
    let mut dpReplayed := 0
    let mut dpAssumed := 0
    for (name, content) in corpus do
      match ProofLog.parse content with
      | .error msg =>
        lines := lines.push s!"• {name}: PARSE-FAIL {msg}"
        integrityFails := integrityFails.push s!"{name}: PARSE-FAIL {msg}"
      | .ok log =>
        match ClauseTree.buildDevelopment log with
        | .error msg =>
          lines := lines.push s!"• {name}: RECON-FAIL {msg}"
          integrityFails := integrityFails.push s!"{name}: RECON-FAIL {msg}"
        | .ok dev =>
          let w := dev.toWorld
          let thms := developmentTheorems dev
          lines := lines.push s!"• {name}  (world: {w.defs.size} defun(s), {thms.length} theorem(s))"
          if thms.isEmpty then
            integrityFails := integrityFails.push s!"{name}: 0 theorems reconstructed (failed/empty capture?)"
          for cp in thms do
            total := total + 1
            -- EMISSION FRONTIER (Track B): a black-box PROVED leaf — ACL2 discharged
            -- the clause by preprocess/eval/type-set but emitted no replayable
            -- structure. Marked unhandled and HARD-FAILED below (not a silent green).
            let bb := theoremBlackBoxLeaves cp
            unless bb.isEmpty do
              emissionFrontiers := emissionFrontiers.push s!"{name}/{cp.name}: black-box PROVED leaf(s) [{", ".intercalate bb}]"
            -- Discharge leaves (decision-procedure nodes): emission-complete under the
            -- ratified carve-out; attempt the DP-lift replay (c1) per leaf.
            let dis := theoremDischargeLeaves cp
            let tps := developmentTPs dev
            let status ← tryReplay w tps cp
            if status.startsWith "REPLAYED ✓" then replayed := replayed + 1
            let tag := if bb.isEmpty then "" else s!"  [EMISSION-FRONTIER: black-box leaf {", ".intercalate bb}]"
            let mut disParts : List String := []
            for (id, o, clause) in dis do
              dpTotal := dpTotal + 1
              let r ← tryDischarge w tps id o clause
              if (r.splitOn "✓").length > 1 then dpReplayed := dpReplayed + 1
              if (r.splitOn "◌").length > 1 then dpAssumed := dpAssumed + 1
              disParts := disParts ++ [r]
            let disTag := if disParts.isEmpty then "" else
              s!"  [DISCHARGE: {", ".intercalate disParts}]"
            lines := lines.push s!"    {cp.name} → {status}{tag}{disTag}"
    logInfo m!"Driver coverage — REPLAYED {replayed}/{total}; DP-discharge leaves ✓{dpReplayed} ◌{dpAssumed} ✗{dpTotal - dpReplayed - dpAssumed} of {dpTotal}:\n{"\n".intercalate lines.toList}"
    unless integrityFails.isEmpty do
      throwError m!"Reconstruction-integrity failures (not the replay frontier):\n{"\n".intercalate integrityFails.toList}"
    unless emissionFrontiers.isEmpty do
      -- HARD RED until the Track B emission lands (docs/plans/2026-06-09_direct-proof-emission.md).
      -- A black-box PROVED leaf has no emitted proof structure to replay; treating it as
      -- handled would be a fidelity lie. These FAIL the build deliberately.
      throwError m!"Unhandled EMISSION FRONTIER — {emissionFrontiers.size} theorem(s) discharged by an uninstrumented preprocess/eval/type-set path (black-box PROVED leaf, no replayable structure emitted). This is the Track B emission gap (docs/plans/2026-06-09_direct-proof-emission.md), deliberately failing until that instrumentation lands:\n{"\n".intercalate emissionFrontiers.toList}"

-- Unlimited at the command level: per-leaf budgets are enforced INSIDE
-- `tryDischarge` (withCurrHeartbeats + a 400k cap), so one expensive leaf cannot
-- poison the rest of the sweep.
set_option maxHeartbeats 0 in
#driver_coverage

end ACL2.Tests.Coverage




