import Std.Data.HashMap
import Lean
import ACL2Lean.DSL.SyntaxCategories

open Lean

namespace ACL2

/-- Symbols cover ACL2 package-qualified names (e.g. `ACL2::CAR`). -/
structure Symbol where
  package : String := "ACL2"
  name : String
  deriving DecidableEq, BEq, Hashable, Inhabited

-- LawfulBEq for Symbol: derived BEq agrees with derived DecidableEq.
-- Needed for Std.HashMap.getElem?_insert lemma.
-- We override the derived BEq with one that uses DecidableEq directly.
instance : BEq Symbol where
  beq a b := decide (a = b)

instance : LawfulBEq Symbol where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

namespace Symbol

@[inline] def normalizedName (s : Symbol) : String :=
  s.name.map Char.toLower

/-- Compare a symbol's name against a target string.
    The symbol's name is already lowercased by the parser. The target
    `name` must also be lowercase for the comparison to work. We use
    direct string comparison which is kernel-reducible (unlike
    String.map Char.toLower which goes through @[irreducible]
    String.mapAux and blocks kernel reduction in proofs).
    All call sites in the codebase use lowercase target strings. -/
@[inline] def isNamed (s : Symbol) (name : String) : Bool :=
  s.name == name

end Symbol

instance : Repr Symbol where
  reprPrec s _ :=
    if s.package == "ACL2" then s.name else s.package ++ "::" ++ s.name

/-- Keywords are stored without the leading colon. -/
abbrev Keyword := String

/-- Numeric literals include integers and common decimal rationals. -/
inductive Number
  | int (value : Int)
  | rational (numerator : Int) (denominator : Nat)
  | decimal (mantissa : Int) (exponent : Int)
  deriving DecidableEq

instance : Repr Number where
  reprPrec n _ := match n with
    | .int v => repr v
    | .rational n d => s!"{n}/{d}"
    | .decimal m e => s!"{m}E{e}"

inductive Atom
  | symbol (value : Symbol)
  | keyword (value : Keyword)
  | string (value : String)
  | number (value : Number)
  deriving DecidableEq

instance : Repr Atom where
  reprPrec a _ := match a with
    | .symbol s => repr s
    | .keyword k => ":" ++ k
    | .string s => repr s
    | .number n => repr n

/-- Minimal s-expression structure to model ACL2 source. -/
inductive SExpr
  | nil
  | atom (a : Atom)
  | cons (car : SExpr) (cdr : SExpr)
  deriving DecidableEq, Inhabited

/-- ACL2 `t` — the canonical truthy value. -/
abbrev SExpr.t : SExpr := .atom (.symbol { name := "t" })

namespace SExpr

/-- Build a proper list. -/
@[simp] def ofList : List SExpr → SExpr
  | [] => SExpr.nil
  | a :: tl => SExpr.cons a (ofList tl)

/-- Attempt to view an s-expression as a proper list. -/
def toList? : SExpr → Option (List SExpr)
  | .nil => .some []
  | .atom _ => .none
  | .cons hd tl => do
      let rest ← toList? tl
      .some (hd :: rest)

/-- Return the first symbol for quick event classification. -/
def headSymbol? : SExpr → Option Symbol
  | .cons (.atom (.symbol s)) _ => some s
  | .cons (.atom (.keyword _)) _ => none
  | .cons (.atom _) _ => none
  | _ => none

end SExpr

partial def SExpr.toString : SExpr → String
  | .nil => "NIL"
  | .atom a => s!"{repr a}"
  | s@(.cons _ _) =>
    match s.toList? with
    | some l => "(" ++ " ".intercalate (l.map toString) ++ ")"
    | none => match s with
      | .cons car cdr => s!"({toString car} . {toString cdr})"
      | _ => ""

instance : ToString SExpr where
  toString := SExpr.toString

instance : Repr SExpr where
  reprPrec s _ := s.toString

structure TheoremOption where
  key : Keyword
  value : SExpr
  deriving DecidableEq, Inhabited, Repr

inductive TheoryExpr
  | enable (items : List SExpr)
  | disable (items : List SExpr)
  | e_d (enabled : List SExpr) (disabled : List SExpr)
  | raw (expr : SExpr)
  deriving DecidableEq, Inhabited, Repr

structure GoalHint where
  goal : String
  options : List TheoremOption := []
  deriving DecidableEq, Inhabited, Repr

inductive ProofInstruction
  | atom (name : String)
  | command (name : String) (args : List SExpr := [])
  | block (name : String) (steps : List ProofInstruction)
  | raw (expr : SExpr)
  deriving Inhabited, Repr

structure RuleClass where
  name : String
  options : List TheoremOption := []
  deriving DecidableEq, Inhabited, Repr

structure TheoremInfo where
  body : SExpr
  options : List TheoremOption := []
  deriving DecidableEq, Inhabited, Repr

namespace TheoremOption

@[inline] private def normalizeKey (key : Keyword) : Keyword :=
  key.map Char.toLower

def fromSExprs : List SExpr → List TheoremOption
  | .atom (.keyword key) :: value :: rest =>
      { key := normalizeKey key, value } :: fromSExprs rest
  | [] => []
  | [.atom (.keyword key)] => panic! s!"keyword without value in theorem options: :{key}"
  | item :: _ => panic! s!"expected keyword in theorem options, got: {repr item}"

def findValue? (options : List TheoremOption) (key : Keyword) : Option SExpr :=
  let key := normalizeKey key
  (options.find? fun option => option.key = key).map (·.value)

def render (option : TheoremOption) : String :=
  s!":{option.key} {option.value}"

end TheoremOption

namespace TheoryExpr

private def unpackItems (expr : SExpr) : List SExpr :=
  match expr.toList? with
  | some items => items
  | none => [expr]

def ofSExpr (expr : SExpr) : TheoryExpr :=
  match expr.toList? with
  | some (SExpr.atom (.symbol head) :: rest) =>
      if head.isNamed "enable" then
        .enable rest
      else if head.isNamed "disable" then
        .disable rest
      else if head.isNamed "e/d" then
        match rest with
        | [enabled, disabled] => .e_d (unpackItems enabled) (unpackItems disabled)
        | _ => .raw expr
      else
        .raw expr
  | _ => .raw expr

private def renderItems (items : List SExpr) : String :=
  String.intercalate ", " (items.map toString)

def summary : TheoryExpr → String
  | .enable items => s!"enable [{renderItems items}]"
  | .disable items => s!"disable [{renderItems items}]"
  | .e_d enabled disabled =>
      s!"e/d enable [{renderItems enabled}] disable [{renderItems disabled}]"
  | .raw expr => toString expr

end TheoryExpr

namespace GoalHint

private def renderGoal (expr : SExpr) : String :=
  match expr with
  | .atom (.string s) => s
  | .atom (.symbol s) => toString (SExpr.atom (.symbol s))
  | _ => toString expr

def ofSExpr? (expr : SExpr) : Option GoalHint := do
  let items ← expr.toList?
  match items with
  | goalExpr :: rest =>
      some { goal := renderGoal goalExpr, options := TheoremOption.fromSExprs rest }
  | [] => none

def findOption? (hint : GoalHint) (key : Keyword) : Option SExpr :=
  TheoremOption.findValue? hint.options key

def inTheory? (hint : GoalHint) : Option TheoryExpr :=
  hint.findOption? "in-theory" |>.map TheoryExpr.ofSExpr

def summary (hint : GoalHint) : String :=
  let basics :=
    [ hint.findOption? "use" |>.map (fun useExpr => s!"use {useExpr}")
    , hint.inTheory? |>.map (fun theoryExpr => s!"in-theory {theoryExpr.summary}")
    , hint.findOption? "induct" |>.map (fun inductExpr => s!"induct {inductExpr}")
    , hint.findOption? "expand" |>.map (fun expandExpr => s!"expand {expandExpr}")
    , hint.findOption? "do-not-induct" |>.map (fun dniExpr => s!"do-not-induct {dniExpr}")
    ].filterMap id
  let handled := ["use", "in-theory", "induct", "expand", "do-not-induct"]
  let extras :=
    hint.options
      |>.filter (fun option => !handled.contains option.key)
      |>.map TheoremOption.render
  let parts := basics ++ extras
  if parts.isEmpty then
    s!"hint {hint.goal}"
  else
    s!"hint {hint.goal}: {String.intercalate "; " parts}"

end GoalHint

namespace ProofInstruction

@[inline] private def renderIndent (indent : Nat) : String :=
  String.ofList (List.replicate indent ' ')

private def instructionName? : SExpr → Option String
  | .atom (.keyword key) => some key
  | .atom (.symbol sym) => some sym.normalizedName
  | _ => none

private def isQuotedName (name : String) : Bool :=
  name = "quote" || name = "quasiquote" || name = "unquote" || name = "unquote-splicing"

private def allowsNestedSteps (name : String) : Bool :=
  name = "quiet!" || name = "repeat"

private def looksLikeInstruction : SExpr → Bool
  | .atom (.keyword _) => true
  | .atom (.symbol _) => true
  | expr =>
      match expr.toList? with
      | some (head :: _) =>
          match instructionName? head with
          | some name => !isQuotedName name
          | none => false
      | _ => false

partial def ofSExpr : SExpr → ProofInstruction
  | .atom (.keyword key) => .atom key
  | .atom (.symbol sym) => .atom sym.normalizedName
  | expr =>
      match expr.toList? with
      | some (head :: rest) =>
          match instructionName? head with
          | some name =>
              if allowsNestedSteps name && rest.all looksLikeInstruction then
                .block name (rest.map ofSExpr)
              else
                .command name rest
          | none => .raw expr
      | _ => .raw expr

private def goalHintsFromExpr (expr : SExpr) : List GoalHint :=
  match GoalHint.ofSExpr? expr with
  | some hint => [hint]
  | none =>
      match expr.toList? with
      | some items => items.filterMap GoalHint.ofSExpr?
      | none => []

def goalHints : ProofInstruction → List GoalHint
  | .command "bash" args => (args.map goalHintsFromExpr).foldr List.append []
  | _ => []

def theoryExpr? : ProofInstruction → Option TheoryExpr
  | .command "in-theory" [expr] => some (TheoryExpr.ofSExpr expr)
  | _ => none

private def renderArgs (args : List SExpr) : String :=
  String.intercalate "; " (args.map toString)

partial def renderLines (indent : Nat := 0) : ProofInstruction → List String
  | .atom name => [s!"{renderIndent indent}{name}"]
  | .raw expr => [s!"{renderIndent indent}{expr}"]
  | .command "bash" args =>
      let hints := goalHints (.command "bash" args)
      if hints.isEmpty then
        [s!"{renderIndent indent}bash: {renderArgs args}"]
      else
        let header := s!"{renderIndent indent}bash:"
        let hintLines := hints.map (fun hint => s!"{renderIndent (indent + 2)}{hint.summary}")
        header :: hintLines
  | inst@(.command "in-theory" args) =>
      match inst.theoryExpr? with
      | some theoryExpr => [s!"{renderIndent indent}in-theory: {theoryExpr.summary}"]
      | none => [s!"{renderIndent indent}in-theory: {renderArgs args}"]
  | .command name args =>
      if args.isEmpty then
        [s!"{renderIndent indent}{name}"]
      else
        [s!"{renderIndent indent}{name}: {renderArgs args}"]
  | .block name steps =>
      let header := s!"{renderIndent indent}{name}"
      header :: (steps.map (renderLines (indent + 2))).foldr List.append []

end ProofInstruction

namespace RuleClass

def ofSExpr? : SExpr → Option RuleClass
  | .atom (.keyword key) => some { name := key.map Char.toLower }
  | expr => do
      let items ← expr.toList?
      match items with
      | .atom (.keyword key) :: rest =>
          some { name := key.map Char.toLower, options := TheoremOption.fromSExprs rest }
      | _ => none

def summary (ruleClass : RuleClass) : String :=
  let extraKeys := ruleClass.options.map (fun option => s!":{option.key}")
  if extraKeys.isEmpty then
    ruleClass.name
  else
    s!"{ruleClass.name} ({String.intercalate ", " extraKeys})"

end RuleClass

namespace TheoremInfo

def findOption? (info : TheoremInfo) (key : Keyword) : Option SExpr :=
  TheoremOption.findValue? info.options key

def hintGoals (info : TheoremInfo) : List GoalHint :=
  match info.findOption? "hints" with
  | some hints =>
      match hints.toList? with
      | some goals => goals.filterMap GoalHint.ofSExpr?
      | none => []
  | none => []

def ruleClasses (info : TheoremInfo) : List RuleClass :=
  match info.findOption? "rule-classes" with
  | some .nil => []
  | some (.atom (.keyword key)) => [{ name := key.map Char.toLower }]
  | some expr =>
      match expr.toList? with
      | some items => items.filterMap RuleClass.ofSExpr?
      | none => []
  | none => []

def extraOptions (info : TheoremInfo) : List TheoremOption :=
  info.options.filter (fun option =>
    option.key ≠ "hints" && option.key ≠ "rule-classes" && option.key ≠ "instructions")

def instructions (info : TheoremInfo) : List ProofInstruction :=
  match info.findOption? "instructions" with
  | some instructionsExpr =>
      match instructionsExpr.toList? with
      | some items => items.map ProofInstruction.ofSExpr
      | none => [ProofInstruction.ofSExpr instructionsExpr]
  | none => []

end TheoremInfo

-- DSL-like notation for S-expressions in Lean code
syntax "sexpr!{" acl2_sexpr "}" : term

/-- Capture the ACL2 package context for events. -/
structure PackageState where
  current : String := "ACL2"
  openImports : Std.HashMap String (List String) := {}
  deriving Inhabited, Repr

/-- Top-level ACL2 event skeleton. -/
inductive Event
  | inPackage (name : String)
  | includeBook (path : String) (dirs : List String := [])
  | defun (name : Symbol) (formals : List Symbol) (doc : Option String) (decls : List SExpr) (body : SExpr)
  | defthm (name : Symbol) (info : TheoremInfo)
  | defmacro (name : Symbol) (formals : List Symbol) (doc : Option String) (decls : List SExpr) (body : SExpr)
  | mutualRecursion (events : List Event)
  | local (event : Event)
  | inTheory (expr : SExpr)
  | encapsulate (events : List Event)
  | makeEvent (body : SExpr)
  | defrec (name : Symbol) (fields : List Symbol)
  | defconst (name : Symbol) (value : SExpr)
  | defstobj (name : Symbol) (fields : List SExpr)
  | table (name : Symbol) (args : List SExpr)
  | skip (raw : SExpr)
  deriving Repr, Inhabited

namespace Event

/-- Peel off docstrings and declarations from a function body list. -/
partial def parseDefunBody (doc : Option String) (decls : List SExpr) (rest : List SExpr) : (Option String × List SExpr × SExpr) :=
  match rest with
  | SExpr.atom (.string s) :: rest => parseDefunBody (some s) decls rest
  | (d@(SExpr.cons (SExpr.atom (.symbol sym)) _)) :: rest =>
      if sym.normalizedName = "declare" then
        parseDefunBody doc (d :: decls) rest
      else
        let body := match d :: rest with
          | [b] => b
          | many => SExpr.ofList many
        (doc, decls.reverse, body)
  | rest =>
        let body := match rest with
        | [b] => b
        | _ => SExpr.ofList rest
      (doc, decls.reverse, body)

/--
Best-effort recovery of a quasiquoted event skeleton.

This does not execute ACL2; it only peels away quasiquote syntax so that static
`make-event` expansions can still expose nested `defthm` / `defconst` forms.
-/
private partial def dequasiquote (depth : Nat) : SExpr → SExpr
  | expr@(.cons (.atom (.symbol sym)) (.cons inner .nil)) =>
      if sym.isNamed "quasiquote" then
        if depth = 0 then
          dequasiquote (depth + 1) inner
        else
          SExpr.ofList [SExpr.atom (.symbol sym), dequasiquote (depth + 1) inner]
      else if sym.isNamed "unquote" || sym.isNamed "unquote-splicing" then
        if depth = 1 then
          inner
        else
          SExpr.ofList [SExpr.atom (.symbol sym), dequasiquote (depth - 1) inner]
      else
        match expr with
        | .cons car cdr => .cons (dequasiquote depth car) (dequasiquote depth cdr)
        | _ => expr
  | .cons car cdr => .cons (dequasiquote depth car) (dequasiquote depth cdr)
  | expr => expr

/--
Peel lightweight wrappers that ACL2 commonly uses around generated events.

This stays syntactic: it does not attempt to evaluate arbitrary `let`/`cond`
terms produced inside `make-event`.
-/
private partial def unwrapGeneratedEventExpr (expr : SExpr) : SExpr :=
  let expr := dequasiquote 0 expr
  match expr.toList? with
  | some (.atom (.symbol sym) :: rest) =>
      if sym.isNamed "value" || sym.isNamed "value-triple" then
        match rest.reverse with
        | inner :: _ => unwrapGeneratedEventExpr inner
        | [] => expr
      else
        expr
  | _ => expr

/-- Classify an ACL2 event from its raw syntax. Panics on malformed or unrecognized forms. -/
partial def classify (sexpr : SExpr) : Event :=
  match sexpr with
  | .cons (.atom (.symbol sym)) rest =>
      match sym.normalizedName with
      | "in-package" =>
          match rest.toList? with
          | some [SExpr.atom (.string pkg)] => .inPackage pkg
          | some [SExpr.atom (.symbol pkg)] => .inPackage pkg.name
          | _ => panic! s!"malformed in-package: {repr sexpr}"
      | "include-book" =>
          match rest.toList? with
          | some (SExpr.atom (.string path) :: tail) =>
              -- include-book tail is keyword-value pairs; extract just the keywords
              let dirs := tail.filterMap fun
                | SExpr.atom (.keyword kw) => some kw
                | _ => none
              .includeBook path dirs
          | some (SExpr.atom (.symbol path) :: tail) =>
              let dirs := tail.filterMap fun
                | SExpr.atom (.keyword kw) => some kw
                | _ => none
              .includeBook path.name dirs
          | _ => panic! s!"malformed include-book: {repr sexpr}"
      | "defun" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: rest) =>
              let fmls :=
                match params.toList? with
                | some lst =>
                    lst.map
                      (fun
                        | SExpr.atom (.symbol s) => s
                        | other => panic! s!"non-symbol formal in defun: {repr other}")
                | none => panic! s!"non-list formals in defun: {repr params}"
              let (doc, decls, bodyExpr) := parseDefunBody none [] rest
              .defun name fmls doc decls bodyExpr
          | _ => panic! s!"malformed defun: {repr sexpr}"
      | "defthm" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: body :: options) =>
              .defthm name { body, options := TheoremOption.fromSExprs options }
          | _ => panic! s!"malformed defthm: {repr sexpr}"
      | "defmacro" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: rest) =>
              let fmls :=
                match params.toList? with
                | some lst =>
                    lst.map
                      (fun
                        | SExpr.atom (.symbol s) => s
                        | other => panic! s!"non-symbol formal in defmacro: {repr other}")
                | none => panic! s!"non-list formals in defmacro: {repr params}"
              let (doc, decls, bodyExpr) := parseDefunBody none [] rest
              .defmacro name fmls doc decls bodyExpr
          | _ => panic! s!"malformed defmacro: {repr sexpr}"
      | "local" =>
          match rest.toList? with
          | some [inner] => .local (classify inner)
          | _ => panic! s!"malformed local: {repr sexpr}"
      | "with-output" =>
          match rest.toList? with
          | some args =>
              match args.reverse with
              | inner :: _ => classify inner
              | [] => panic! s!"empty with-output: {repr sexpr}"
          | _ => panic! s!"malformed with-output: {repr sexpr}"
      | "in-theory" =>
          match rest.toList? with
          | some [expr] => .inTheory expr
          | _ => panic! s!"malformed in-theory: {repr sexpr}"
      | "mutual-recursion" =>
          match rest.toList? with
          | some lst => .mutualRecursion (lst.map classify)
          | _ => panic! s!"malformed mutual-recursion: {repr sexpr}"
      | "encapsulate" =>
          match rest.toList? with
          | some (_ :: events) => .encapsulate (events.map classify)
          | _ => panic! s!"malformed encapsulate: {repr sexpr}"
      | "make-event" => .makeEvent rest
      | "defrec" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: _) =>
              let fmls := match params.toList? with
                | some lst => lst.map (fun | SExpr.atom (.symbol s) => s
                                           | other => panic! s!"non-symbol field in defrec: {repr other}")
                | none => panic! s!"non-list fields in defrec: {repr params}"
              .defrec name fmls
          | _ => panic! s!"malformed defrec: {repr sexpr}"
      | "defconst" =>
          match rest.toList? with
          | some [SExpr.atom (.symbol name), val] => .defconst name val
          | _ => panic! s!"malformed defconst: {repr sexpr}"
      | "defstobj" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: fields) => .defstobj name fields
          | _ => panic! s!"malformed defstobj: {repr sexpr}"
      | "table" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: args) => .table name args
          | _ => panic! s!"malformed table: {repr sexpr}"
      -- Known no-ops: explicitly listed ACL2 forms we intentionally skip
      | "program" => .skip sexpr
      | "set-verify-guards-eagerness" => .skip sexpr
      | "defequiv" => .skip sexpr
      | "defcong" => .skip sexpr
      | "comp" => .skip sexpr
      | "verify-guards" => .skip sexpr
      | "verify-termination" => .skip sexpr
      | other => panic! s!"unrecognized ACL2 event: {other} in {repr sexpr}"
  | _ => panic! s!"expected event form (cons), got: {repr sexpr}"

/-- Recover statically visible nested events from a `make-event`. -/
def generatedEvents (body : SExpr) : List Event :=
  match body.toList? with
  | some [generatedExpr] =>
      let recovered := unwrapGeneratedEventExpr generatedExpr
      match classify recovered with
      | .skip _ => []
      | event => [event]
  | _ => []

/-- Flatten nested ACL2 event structure into replay order. -/
partial def flatten : Event → List Event
  | .local inner => flatten inner
  | .mutualRecursion events => events.foldr (fun ev acc => flatten ev ++ acc) []
  | .encapsulate events => events.foldr (fun ev acc => flatten ev ++ acc) []
  | .makeEvent body =>
      let generated := generatedEvents body
      if generated.isEmpty then
        [.makeEvent body]
      else
        generated.foldr (fun ev acc => flatten ev ++ acc) []
  | event => [event]

def flattenList (events : List Event) : List Event :=
  events.foldr (fun ev acc => flatten ev ++ acc) []

end Event

/-- Reduction-friendly finite map: function name → (formals, body). An association
    list that mirrors the `HashMap` interface the world used (`get?` / `insert` /
    `[k]?` / `contains` / `size` / `{}`), but whose lookups **reduce by `decide`/`rfl`
    on a concrete map**. This is what lets the replay driver *derive* the structural
    facts `w.defs.get? fn = some (formals, body)` / `= none` on the fly, instead of
    consuming hand-written `simp [World.empty]` theorems.

    `evalOpt` does one lookup per function call — O(n) on the assoc list vs O(1) on a
    `HashMap` — but the corpus has a handful of functions and `evalOpt` is fuel-bounded
    (proof/test use, not production execution), so this is immaterial. -/
structure DefMap where
  entries : List (Symbol × (List Symbol × SExpr)) := []
  deriving Repr, Inhabited, DecidableEq

namespace DefMap

/-- Lookup by key: the first matching entry. Since `insert` prepends and drops the
    prior binding, that is the latest insert. Reduces on a concrete map. -/
def get? (m : DefMap) (s : Symbol) : Option (List Symbol × SExpr) :=
  let rec go : List (Symbol × (List Symbol × SExpr)) → Option (List Symbol × SExpr)
    | [] => none
    | (k, v) :: rest => if k == s then some v else go rest
  go m.entries

/-- Insert/overwrite: drop any existing binding for `s`, then prepend. Matches
    `HashMap.insert` (latest wins) while keeping the list duplicate-free. -/
def insert (m : DefMap) (s : Symbol) (v : List Symbol × SExpr) : DefMap :=
  ⟨(s, v) :: m.entries.filter (fun kv => kv.1 != s)⟩

/-- Whether a key is bound. -/
def contains (m : DefMap) (s : Symbol) : Bool := (m.get? s).isSome

/-- Number of distinct bound keys (the assoc list is kept duplicate-free). -/
def size (m : DefMap) : Nat := m.entries.length

/-- `m[s]?` is `m.get? s` (and so also reduces on a concrete map). -/
instance : GetElem? DefMap Symbol (List Symbol × SExpr) (fun _ _ => True) where
  getElem m s _ := (m.get? s).getD default
  getElem? m s := m.get? s

/-- Bridge `[s]?` and `get?` for `simp` (they are definitionally equal). The `HashMap`
    repr had an analogous simp normal form; keep proofs that wrote `w.defs[s]?` working. -/
@[simp] theorem getElem?_eq_get? (m : DefMap) (s : Symbol) : m[s]? = m.get? s := rfl

end DefMap

/-- Semantics: interpret events into a growing environment. -/
structure World where
  package : PackageState := {}
  defs : DefMap := {}
  macros : Std.HashMap Symbol (List Symbol × SExpr) := {}
  theorems : Std.HashMap Symbol TheoremInfo := {}
  theories : List TheoryExpr := []
  consts : Std.HashMap Symbol SExpr := {}
  recs : Std.HashMap Symbol (List Symbol) := {}
  stobjs : Std.HashMap Symbol (List SExpr) := {}
  tables : Std.HashMap Symbol (List SExpr) := {}
  deriving Repr

instance : Inhabited World :=
  ⟨{ package := {}, defs := {}, macros := {} }⟩

namespace World

/-- Install an event, currently ignoring proof obligations. -/
partial def step (w : World) (event : Event) : World :=
  match event with
  | .inPackage name => { w with package := { w.package with current := name } }
  | .includeBook _ _ => w
  | .defun name formals _ _ body => { w with defs := w.defs.insert name (formals, body) }
  | .defthm name info => { w with theorems := w.theorems.insert name info }
  | .defmacro name formals _ _ body => { w with macros := w.macros.insert name (formals, body) }
  | .local e => step w e
  | .inTheory expr => { w with theories := w.theories ++ [TheoryExpr.ofSExpr expr] }
  | .mutualRecursion evs => evs.foldl step w
  | .encapsulate evs => evs.foldl step w
  | .makeEvent body =>
      match Event.generatedEvents body with
      | [] => w
      | generated => generated.foldl step w
  | .defrec name fields => { w with recs := w.recs.insert name fields }
  | .defconst name value => { w with consts := w.consts.insert name value }
  | .defstobj name fields => { w with stobjs := w.stobjs.insert name fields }
  | .table name args => { w with tables := w.tables.insert name args }
  | .skip _ => w

/-- Replay a script of events. -/
def empty : World := { package := {}, defs := {}, macros := {} }

/-- A world that is just its function map (all other fields default/empty). `evalOpt`
    reads only `defs`, so this is the world the replay reasons over — used as the concrete
    target when projecting a `World` from a reconstructed `Development` (the reflected form
    a generated world def takes). -/
def ofDefs (defs : DefMap) : World := { defs }

/-- Replay a script of events starting from an empty world. -/
def replay (events : List Event) : World :=
  events.foldl step empty

/-- Replay events extending an existing world. -/
def extend (w : World) (events : List Event) : World :=
  events.foldl step w

end World

/-- Environment maps variable symbols to their values. -/
abbrev Env := Std.HashMap Symbol SExpr

end ACL2
