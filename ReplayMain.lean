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
  let usage := "usage: acl2lean-replay <file.proof-log> [THEOREM-NAME]"
  let (path, upTo?) ← match args.filter (· ≠ "") with
    | [p] => pure (p, (none : Option String))
    | [p, t] => pure (p, some t)
    | _ => throw <| IO.userError usage
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
  let act : MetaM BookResult :=
    Elab.Term.TermElabM.run' (runBook name content upTo? (timings := true))
  let (res, _) ← (act.run' {} {}).toIO coreCtx { env }
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
