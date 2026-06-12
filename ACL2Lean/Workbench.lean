import ACL2Lean.Import
import Init.System.FilePath
import Std

open ACL2

namespace ACL2

/-- Non-exhaustive list of ACL2 sample files for syntax probing. These live in
    the `acl2/` SUBMODULE (the canonical upstream copies — we no longer keep
    duplicates under `acl2_samples/`). -/
def sampleFiles : List System.FilePath :=
  [ "acl2/books/workshops/2009/cowles-gamboa-triangle-square/materials/log2.lisp"
  , "acl2/books/workshops/2009/cowles-gamboa-triangle-square/materials/tri-sq.lisp"
  , "acl2/books/projects/apply-model/apply.lisp"
  , "acl2/books/projects/apply-model/apply-prim.lisp"
  , "acl2/books/projects/die-hard-bottle-game/top.lisp"
  , "acl2/books/projects/die-hard-bottle-game/work.lisp"
  , "acl2/books/projects/concurrent-programs/bakery/programs.lisp"
  , "acl2/books/projects/concurrent-programs/bakery/inv-sufficient.lisp"
  , "acl2/books/projects/execloader/top.lisp"
  , "acl2/books/projects/gaussian-elim-solvers/big-a-and-b.lsp"
  , "acl2/books/projects/gaussian-elim-solvers/df-solver-v9.lisp"
  ]

/-- Render a hash map as a friendly string for debugging. -/
def prettyCounts (m : Std.HashMap String Nat) : String :=
  let entries := m.toList.map (fun (k, v) => s!"{k}: {v}")
  String.intercalate ", " entries

/-- Evaluate the parser+classifier against known ACL2 inputs. -/
def reportSamples : IO Unit := do
  for file in sampleFiles do
    let summary ← summarizeFile file
    match summary with
    | .error msg =>
        IO.println s!"[error] {file}: {msg}"
    | .ok counts =>
        IO.println s!"[ok] {file}: {prettyCounts counts}"

    -- Print skipped events for debugging
    let events ← loadEventsFromFile file
    match events with
    | .ok evs =>
        let skips := evs.filter fun
          | .skip _ => true
          | _ => false
        if ¬ skips.isEmpty then
          IO.println s!"  Skipped {skips.length} events in {file}:"
          for s in skips.take 5 do
            match s with
            | .skip raw => IO.println s!"    {repr raw}"
            | _ => pure ()
          if skips.length > 5 then
            IO.println "    ..."
    | _ => pure ()

end ACL2
