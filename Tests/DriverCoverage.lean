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
def tryReplay (w : World) (cp : ClauseProof) : TermElabM String := do
  let wExpr ← reflectWorld w
  let emptyEnv ← Term.elabTerm (← `(({} : Env))) none
  let cfg : ReplayConfig := { worldExpr := wExpr, envExpr := emptyEnv, worldVal := w }
  try
    let _ ← replayProof cfg cp
    return "REPLAYED ✓"
  catch e => return s!"FAIL: {(← e.toMessageData.toString).replace "\n" " "}"

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
            let status ← tryReplay w cp
            if status == "REPLAYED ✓" then replayed := replayed + 1
            lines := lines.push s!"    {cp.name} → {status}"
    logInfo m!"Driver coverage — REPLAYED {replayed}/{total}:\n{"\n".intercalate lines.toList}"
    unless integrityFails.isEmpty do
      throwError m!"Reconstruction-integrity failures (not the replay frontier):\n{"\n".intercalate integrityFails.toList}"

#driver_coverage

end ACL2.Tests.Coverage
