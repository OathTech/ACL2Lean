import ACL2Lean.ClauseTree

namespace ACL2.Replay.Driver.TsQueryCapture
open ACL2

/-- A strict view of a recorded plist. Unrecognized fields remain errors;
the caller declares exactly the schema it consumes. -/
def fields (s : SExpr) (allowed : List String) : Except String (List (String × SExpr)) := do
  let some xs := s.toList? | throw "FC basis: record is not a proper list"
  let rec go : List SExpr → List (String × SExpr) → Except String (List (String × SExpr))
    | [], acc => pure acc.reverse
    | .atom (.keyword k) :: v :: rest, acc => do
      unless allowed.contains k && !acc.any (fun (a, _) => a == k) do
        throw s!"FC basis: unexpected or repeated field {k}"
      go rest ((k, v) :: acc)
    | _, _ => throw "FC basis: malformed plist"
  go xs []

def required (fs : List (String × SExpr)) (key : String) : Except String SExpr :=
  match fs.lookup key with
  | some v => pure v
  | none => throw s!"FC basis: missing {key}"

def asList (s : SExpr) : Except String (List SExpr) :=
  match s.toList? with
  | some xs => pure xs
  | none => throw "FC basis: expected proper list"

def asInt : SExpr → Except String Int
  | .atom (.number (.int n)) => pure n
  | _ => throw "FC basis: expected integer"

/-- A snapshot is evidence about ACL2's lookup, never a collection of
assumed Lean facts. Each entry retains its term, mask, and provenance. -/
def typeAlist (s : SExpr) : Except String (List (SExpr × Int × SExpr)) := do
  (← asList s).mapM fun
    | .cons term (.cons mask tt) => do
      let _ ← asList tt
      pure (term, ← asInt mask, tt)
    | _ => throw "FC basis: malformed type-alist entry"

structure Query where
  term : SExpr
  result : Int
  lookup : SExpr
  route : SExpr
  comparison : SExpr
  recognizer : SExpr
  children : List SExpr
  ttree : SExpr
  inputTtree : SExpr
  dwp : SExpr

def query (s : SExpr) : Except String Query := do
  let fs ← fields s ["TERM", "RESULT", "TTREE", "INPUT-TTREE", "DWP", "LOOKUP", "ROUTE",
    "COMPARISON", "RECOGNIZER", "CHILDREN"]
  return {
    term := ← required fs "TERM", result := ← asInt (← required fs "RESULT"),
    lookup := ← required fs "LOOKUP", route := ← required fs "ROUTE",
    comparison := ← required fs "COMPARISON", recognizer := ← required fs "RECOGNIZER",
    children := ← asList (← required fs "CHILDREN"), ttree := ← required fs "TTREE",
    inputTtree := ← required fs "INPUT-TTREE", dwp := ← required fs "DWP" }

end ACL2.Replay.Driver.TsQueryCapture
