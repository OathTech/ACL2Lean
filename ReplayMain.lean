/-
  `acl2lean-replay` — the FOCUSED replay CLI (perf arc WP1, 2026-07-18).

  Replays ONE book (optionally stopping after one named theorem) at RUNTIME
  against a `.proof-log` read from disk — the fast OODA loop for driver work:
  a driver edit rebuilds only the `Runner` import cone (no `Imported/`
  catalog, no `Tests` corpus elaboration, no `include_str` staleness), and a
  single book replays in seconds.

  Row text is IDENTICAL to the coverage sweep's (`Runner.runBook` is the
  shared harness), so a focused row is directly comparable to
  `Tests/driver-coverage.golden`. The full sweep remains the gate — this
  tool exists to iterate, not to certify.

  Usage (via the Justfile recipe, which supplies the Lean search path):
      just replay acl2_samples/sorting/msort.proof-log
      just replay acl2_samples/recon-tests/10-tree-induction.proof-log TRUE-LISTP-FLATTEN
-/
import ACL2Lean.Replay.Runner

open Lean ACL2.Replay.Runner

unsafe def main (args : List String) : IO Unit := do
  let usage := "usage: acl2lean-replay [--deps <log1,log2,…>] \
<file.proof-log> [THEOREM-NAME] | --dump <file.proof-log>"
  -- --dump: print the reconstructed tree WITHOUT the Imported/ catalog
  -- import cone (the CLI's dump-proof-tree is unusable mid-migration when
  -- WaypointCatalog's compile-time replays are red — path-emission Phase 1)
  match args.filter (· ≠ "") with
  | ["--dump", p] =>
    let contents ← IO.FS.readFile p
    match ACL2.ProofLog.parse contents with
    | .error e => throw (IO.userError s!"Parse error: {e}")
    | .ok log =>
      match ACL2.ClauseTree.buildDevelopment log with
      | .error e => throw (IO.userError s!"Reconstruction error: {e}")
      | .ok dev => ACL2.printDevelopment dev
    return
  | _ => pure ()
  -- --deps: comma-separated dependency logs whose theorem trees are offered
  -- for cross-book rule discharge (2a) — matching the sweep's prior-book
  -- accumulation for this book. WITHOUT it, a consumer book's cross-book
  -- rule: conds stay hypothesis-backed and its rows DIFFER from the sweep.
  let (depPaths, rest) ← match args.filter (· ≠ "") with
    | "--deps" :: ds :: rest => pure (ds.splitOn ",", rest)
    | rest => pure ([], rest)
  let (path, upTo?) ← match rest with
    | [p] => pure (p, (none : Option String))
    | [p, t] => pure (p, some t)
    | _ => throw <| IO.userError usage
  let mut crossTrees : List (String × ACL2.ClauseProof) := []
  let mut crossRules : List ACL2.RuleSpec := []
  -- WP5: the dep DEVELOPMENTS drive the cross-book D1 transfer pre-pass —
  -- without them a focused row would differ from the sweep's again (the
  -- exact parity property this CLI's docstring promises).
  let mut crossDevs : List (String × ACL2.Development) := []
  for dp in depPaths do
    let c ← IO.FS.readFile dp
    match ACL2.ProofLog.parse c with
    | .error e => throw (IO.userError s!"deps {dp}: parse error: {e}")
    | .ok log =>
      match ACL2.ClauseTree.buildDevelopment log with
      | .error e => throw (IO.userError s!"deps {dp}: recon error: {e}")
      | .ok ddev =>
        crossTrees := crossTrees ++ bookTrees ddev
        crossDevs := crossDevs ++ [(dp, ddev)]
        crossRules := crossRules ++ (allBookRules ddev).filter
          (fun r => !crossRules.any (fun o => o.runeKey == r.runeKey))
  let tR0 ← IO.monoMsNow
  let content ← IO.FS.readFile path
  let tR1 ← IO.monoMsNow
  IO.println s!"[t] readFile: {tR1 - tR0} ms"
  -- book display name = file stem, matching the sweep's corpus keys closely
  -- enough for eyeball comparison (the sweep prefixes sorting/ manually)
  let name := (System.FilePath.mk path).fileStem.getD path
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let tI0 ← IO.monoMsNow
  let env ← importModules #[{ module := `ACL2Lean.Replay.Runner }] {}
    (trustLevel := 0) (loadExts := true)
  let tI1 ← IO.monoMsNow
  IO.println s!"[t] importModules: {tI1 - tI0} ms"
  let coreCtx : Core.Context := {
    fileName := "<acl2lean-replay>", fileMap := default,
    -- per-theorem/per-leaf budgets are enforced INSIDE the harness
    -- (withRealMaxHeartbeats); unlimited at the top, as in the sweep
    maxHeartbeats := 0 }
  let t0 ← IO.monoMsNow
  let act : MetaM (BookResult × List (String × ACL2.ClauseProof)
      × List ACL2.RuleSpec) :=
    Elab.Term.TermElabM.run' (runBook name content upTo? (timings := true)
      (crossTrees := crossTrees) (crossDevs := crossDevs)
      (crossRules := crossRules))
  let ((res, _), _) ← (act.run' {} {}).toIO coreCtx { env }
  let t1 ← IO.monoMsNow
  for l in res.lines do IO.println l
  IO.println s!"— {res.replayed}/{res.total} replayed ({res.replayed - res.replayedCond} unconditional + {res.replayedCond} conditional); DP leaves ✓{res.dpReplayed} ◌{res.dpAssumed} ✗{res.dpTotal - res.dpReplayed - res.dpAssumed} of {res.dpTotal}; {t1 - t0} ms"
  unless res.emissionFrontiers.isEmpty do
    IO.eprintln s!"EMISSION FRONTIER (would fail the sweep):"
    for f in res.emissionFrontiers do IO.eprintln s!"  {f}"
  unless res.integrityFails.isEmpty do
    IO.eprintln "INTEGRITY FAILURES:"
    for f in res.integrityFails do IO.eprintln s!"  {f}"
    IO.Process.exit 1
