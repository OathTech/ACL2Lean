/-
  World generator: produces .lean files with World definitions and
  theorem statements from parsed ACL2 events.

  Output format:
  - SExpr constants for each defun body (as data, not Lean functions)
  - A World definition mapping function names to (formals, body) pairs
  - Theorem statements using `evalOpt` with `sorry`
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
  s!"(sym \"{Translator.escapeStringLit s.name}\")"

/-- Render a list of formals as `[sym "x", sym "y"]`. -/
private def renderFormals (formals : List Symbol) : String :=
  let items := formals.map fun s => s!"sym \"{Translator.escapeStringLit s.name}\""
  s!"[{String.intercalate ", " items}]"

/-- Sanitized Lean identifier from an ACL2 name. -/
private def leanName (name : Symbol) : String :=
  Translator.sanitizeName (Translator.translateSymbol name)

/-- First symbol with a non-`ACL2` package in a term, if any. The generated
    world resolves symbol identity by full `Symbol` `BEq` while `sym`/the
    statement builder work in the `ACL2` package, and cross-package identity
    (a package's import list) is reader state we do not model — so ANY
    foreign-package symbol must hard-fail rather than silently alias or
    diverge (fail-closed audit 2026-07-06, N5). -/
private partial def findForeignSym : SExpr → Option Symbol
  | .atom (.symbol s) => if s.package == "ACL2" then none else some s
  | .cons a b => (findForeignSym a) <|> findForeignSym b
  | _ => none

private def checkSyms (ctx : String) (syms : List Symbol) (terms : List SExpr) :
    Except String Unit := do
  match syms.find? (fun s => s.package != "ACL2") with
  | some s => throw s!"gen-world: {ctx}: symbol {s.package}::{s.name} is not \
                       in the ACL2 package — cross-package identity (import \
                       lists) is not modeled (fail-closed audit N5)"
  | none => pure ()
  match terms.findSome? findForeignSym with
  | some s => throw s!"gen-world: {ctx}: term mentions {s.package}::{s.name} \
                       — non-ACL2 packages are not supported (fail-closed \
                       audit N5)"
  | none => pure ()

/-- Reject events the world generator cannot translate FAITHFULLY — fail
    closed (never silently skip; CLAUDE.md). Checked on the UNFLATTENED list:
    `Event.flattenList` unwraps `encapsulate` transparently, which is wrong
    for world semantics (constrained functions are an abstract interface, not
    global defuns), so the check must run first. `local`/`mutual-recursion`
    recurse; `in-theory` is explicitly world-irrelevant; `in-package` is
    accepted only for the ACL2 package, and defun/defthm contents are scanned
    for foreign-package symbols (fail-closed audit N5). -/
private partial def checkTranslatable (ev : Event) : Except String Unit :=
  match ev with
  | .inPackage pkg =>
      if pkg == "ACL2" then .ok ()
      else .error s!"gen-world: (in-package \"{pkg}\") is not supported — the \
                     translator works in the ACL2 package only; honoring a \
                     foreign package needs its import list (fail-closed \
                     audit N5)"
  | .defun name formals _ decls body =>
      checkSyms s!"defun {name.name}" (name :: formals) (body :: decls)
  | .defthm name info =>
      checkSyms s!"defthm {name.name}" [name] [info.body]
  | .inTheory _ => .ok ()
  | .local inner => checkTranslatable inner
  | .mutualRecursion evs => evs.forM checkTranslatable
  | .includeBook path _ =>
      .error s!"gen-world: include-book \"{path}\" is not supported yet — the \
                included book's world does not exist here, so the generated \
                world/statements would be silently WRONG (R2 of \
                docs/plans/2026-06-12_sorting-corpus-roadmap.md)"
  | .encapsulate _ =>
      .error "gen-world: encapsulate is not supported yet — constrained \
              functions are an abstract interface, not global defuns (R6 of \
              the sorting-corpus roadmap)"
  | .defmacro name .. => .error s!"gen-world: defmacro {name.name} is not supported"
  | .defconst name _ => .error s!"gen-world: defconst {name.name} is not supported"
  | .defrec name _ => .error s!"gen-world: defrec {name.name} is not supported"
  | .defstobj name _ => .error s!"gen-world: defstobj {name.name} is not supported"
  | .table name _ => .error s!"gen-world: table event {name.name} is not supported"
  | .makeEvent body =>
      .error s!"gen-world: unexpanded make-event is not supported: \
                {(body.headSymbol?.map (·.name)).getD "?"}"
  | .skip raw =>
      .error s!"gen-world: unrecognized/skipped top-level form (never silently \
                drop): {(raw.headSymbol?.map (·.name)).getD "?"}"

/-- Render the Lean source for a World + theorem statements from the
    flattened, pre-validated event list. -/
private def renderWorld (bookName : String) (flat : List Event) : String := Id.run do
  let mut defuns : Array (Symbol × List Symbol × SExpr) := #[]
  let mut defthms : Array (Symbol × SExpr) := #[]

  for ev in flat do
    match ev with
    | .defun name formals _ _ body => defuns := defuns.push (name, formals, body)
    | .defthm name info => defthms := defthms.push (name, info.body)
    | _ => pure ()

  let mut lines : Array String := #[]

  -- Header
  lines := lines.push "import ACL2Lean.EvalOpt"
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
    lines := lines.push "  defs := ({} : DefMap)"
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
    lines := lines.push
      s!"    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f world env {ln}Formula = some v ∧ v ≠ SExpr.nil := sorry"
    lines := lines.push ""

  -- Footer
  lines := lines.push s!"end ACL2.Worlds.{bookName}"
  lines := lines.push ""

  return "\n".intercalate lines.toList

/-- Generate the complete Lean source for a World + theorem statements.
    Fails closed on any event it cannot translate faithfully. -/
def generateWorld (bookName : String) (events : List Event) : Except String String := do
  events.forM checkTranslatable
  return renderWorld bookName (Event.flattenList events)

end WorldGen

end ACL2
