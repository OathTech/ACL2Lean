/-
  World generator: produces .lean files with World definitions and
  theorem statements from parsed ACL2 events.

  Output format:
  - SExpr constants for each defun body (as data, not Lean functions)
  - A World definition mapping function names to (formals, body) pairs
  - Theorem statements using `eval` with `sorry`
-/
import ACL2Lean.Syntax
import ACL2Lean.Translator

namespace ACL2

namespace WorldGen

/-- Extract a PascalCase module name from a file path.
    "acl2_samples/simple.lisp" → "Simple" -/
def bookNameFromPath (path : String) : String :=
  let base := match path.splitOn "/" with
    | [] => path
    | parts => parts.getLast!
  let base := base.replace ".lisp" ""
  let parts := base.splitOn "-"
  let capitalized := parts.map fun p =>
    if p.isEmpty then p
    else String.ofList (p.toList.head!.toUpper :: p.toList.tail!)
  String.intercalate "" capitalized

/-- Render a Symbol reference as `(sym "name")`. -/
private def renderSymbol (s : Symbol) : String :=
  s!"(sym \"{s.name}\")"

/-- Render a list of formals as `[sym "x", sym "y"]`. -/
private def renderFormals (formals : List Symbol) : String :=
  let items := formals.map fun s => s!"sym \"{s.name}\""
  s!"[{String.intercalate ", " items}]"

/-- Sanitized Lean identifier from an ACL2 name. -/
private def leanName (name : Symbol) : String :=
  Translator.sanitizeName (Translator.translateSymbol name)

/-- Generate the complete Lean source for a World + theorem statements. -/
def generateWorld (bookName : String) (events : List Event) : String := Id.run do
  let flat := Event.flattenList events
  let mut defuns : Array (Symbol × List Symbol × SExpr) := #[]
  let mut defthms : Array (Symbol × SExpr) := #[]

  for ev in flat do
    match ev with
    | .defun name formals _ _ body => defuns := defuns.push (name, formals, body)
    | .defthm name info => defthms := defthms.push (name, info.body)
    | _ => pure ()

  let mut lines : Array String := #[]

  -- Header
  lines := lines.push "import ACL2Lean.Eval"
  lines := lines.push ""
  lines := lines.push "open ACL2"
  lines := lines.push ""
  lines := lines.push s!"namespace ACL2.Worlds.{bookName}"
  lines := lines.push ""
  lines := lines.push "private def sym (name : String) : Symbol := ⟨\"ACL2\", name⟩"
  lines := lines.push ""

  -- Function bodies as SExpr data
  for entry in defuns do
    let name := entry.1
    let body := entry.2.2
    let ln := leanName name
    lines := lines.push s!"def {ln}Body : SExpr :="
    lines := lines.push s!"  {Translator.translateLiteral body}"
    lines := lines.push ""

  -- World definition
  if defuns.isEmpty then
    lines := lines.push "def world : World where"
    lines := lines.push "  defs := {}"
  else
    lines := lines.push "def world : World where"
    lines := lines.push "  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))"
    for entry in defuns do
      let name := entry.1
      let formals := entry.2.1
      let ln := leanName name
      lines := lines.push s!"    |>.insert {renderSymbol name} ({renderFormals formals}, {ln}Body)"
  lines := lines.push ""

  -- Default fuel for sorry'd theorems
  lines := lines.push "def defaultFuel : Nat := 1000000"
  lines := lines.push ""

  -- Theorem formulas and statements
  for entry in defthms do
    let name := entry.1
    let body := entry.2
    let ln := leanName name
    lines := lines.push s!"def {ln}Formula : SExpr :="
    lines := lines.push s!"  {Translator.translateLiteral body}"
    lines := lines.push ""
    lines := lines.push s!"theorem {ln} (env : Env) :"
    lines := lines.push s!"    eval defaultFuel world env {ln}Formula = SExpr.t := sorry"
    lines := lines.push ""

  -- Footer
  lines := lines.push s!"end ACL2.Worlds.{bookName}"
  lines := lines.push ""

  return "\n".intercalate lines.toList

end WorldGen

end ACL2
