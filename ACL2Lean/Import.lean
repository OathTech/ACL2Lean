import ACL2Lean.Syntax
import ACL2Lean.Parser
import Std
import Init.System.IO

namespace ACL2

/-- Parse a raw ACL2 source file into events — fails closed on any form the
    classifier rejects. -/
def loadEventsFromFile (path : System.FilePath) : IO (Except String (List Event)) := do
  let contents ← IO.FS.readFile path
  pure <| do
    let raw ← Parse.parseAll contents
    raw.mapM Event.classify

/-- Count how often each event constructor appears. -/
def summarizeFile (path : System.FilePath) : IO (Except String (Std.HashMap String Nat)) := do
  let events ← loadEventsFromFile path
  pure <| events.map fun evs =>
    evs.foldl
      (fun acc ev =>
        let rec getTag : Event → String
          | .inPackage _ => "in-package"
          | .includeBook _ _ => "include-book"
          | .defun .. => "defun"
          | .defthm .. => "defthm"
          | .defmacro .. => "defmacro"
          | .local e => "local(" ++ getTag e ++ ")"
          | .inTheory _ => "in-theory"
          | .mutualRecursion _ => "mutual-recursion"
          | .encapsulate _ => "encapsulate"
          | .makeEvent _ => "make-event"
          | .defrec .. => "defrec"
          | .defconst .. => "defconst"
          | .defstobj .. => "defstobj"
          | .table .. => "table"
          | .skip _ => "skip"
        let tag := getTag ev
        let prev := (acc.get? tag).getD 0
        acc.insert tag (prev + 1))
      ({} : Std.HashMap String Nat)

end ACL2
