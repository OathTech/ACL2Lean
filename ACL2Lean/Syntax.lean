import Std.Data.HashMap
import Lean

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
  /-- An ACL2 CHARACTER: the code points 0–255 exactly (ACL2's character
      domain — `char-code` is `< 256`). Stored as the raw code. A character is
      a DISTINCT object from the like-named symbol/string under `equal`. -/
  | char (value : UInt8)
  deriving DecidableEq

/-- Render a character the way ACL2's printer does (axioms.lisp:22537, kept in
    sync with the reader `acl2-read-character-string`): `#\` then, for the six
    named codes, the NAME; otherwise the raw character. See
    docs/notes/2026-07-08_acl2-character-semantics.md. -/
def reprChar (c : UInt8) : String :=
  "#\\" ++ match c.toNat with
    | 10  => "Newline"
    | 32  => "Space"
    | 12  => "Page"
    | 9   => "Tab"
    | 127 => "Rubout"
    | 13  => "Return"
    | n   => String.singleton (Char.ofNat n)

instance : Repr Atom where
  reprPrec a _ := match a with
    | .symbol s => repr s
    | .keyword k => ":" ++ k
    | .string s => repr s
    | .number n => repr n
    | .char c => reprChar c

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
    -- Render a cons like ACL2 (and standard Lisp): walk the list spine,
    -- printing successive CARs space-separated, and use the dot ONLY for a
    -- final non-nil atomic cdr — so `(1 . (2 . 3))` prints as `(1 2 . 3)` and
    -- a proper list `(1 2 3)` has no dot. (The old code special-cased only the
    -- fully-proper case and emitted nested dotted pairs otherwise, which ACL2
    -- never prints — a serialization-fidelity gap for the differential surface.)
    "(" ++ spine s ++ ")"
where
  /-- Render the elements of a (possibly improper) list without the enclosing
      parens: `a b c` for a proper list, `a b . tl` for an improper one. -/
  spine : SExpr → String
  | .cons car .nil => SExpr.toString car
  | .cons car (tl@(.cons _ _)) => SExpr.toString car ++ " " ++ spine tl
  | .cons car cdr => SExpr.toString car ++ " . " ++ SExpr.toString cdr
  | other => SExpr.toString other

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

/-- Parse a keyword/value plist into options — fails CLOSED on a malformed
    plist. (Was `panic!`, which in Lean prints and returns the `Inhabited`
    default `[]` rather than aborting — a loud default, not a hard fail;
    fail-closed audit 2026-07-06.) -/
def fromSExprs : List SExpr → Except String (List TheoremOption)
  | .atom (.keyword key) :: value :: rest => do
      pure ({ key := normalizeKey key, value } :: (← fromSExprs rest))
  | [] => .ok []
  | [.atom (.keyword key)] => .error s!"keyword without value in theorem options: :{key}"
  | item :: _ => .error s!"expected keyword in theorem options, got: {repr item}"

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
      -- display-metadata helper: a malformed plist joins this function's
      -- existing `none` arms (silent-drop inventory, deferred class — the
      -- load-bearing gate is `Event.classify`, which THROWS on it)
      some { goal := renderGoal goalExpr,
             options := ← (TheoremOption.fromSExprs rest).toOption }
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
          -- display-metadata helper: malformed plist → `none` like the arm
          -- below (deferred class; `Event.classify` is the throwing gate)
          some { name := key.map Char.toLower,
                 options := ← (TheoremOption.fromSExprs rest).toOption }
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

/-- Classify an ACL2 event from its raw syntax — fails CLOSED on malformed
    or unrecognized forms. (Was `panic!`, which in Lean prints to stderr and
    returns the `Inhabited` default — it does NOT abort, so a malformed form
    silently continued as a defaulted `Event` on the world/statement build
    path; fail-closed audit 2026-07-06.) -/
partial def classify (sexpr : SExpr) : Except String Event :=
  match sexpr with
  | .cons (.atom (.symbol sym)) rest =>
      match sym.normalizedName with
      | "in-package" =>
          match rest.toList? with
          | some [SExpr.atom (.string pkg)] => .ok (.inPackage pkg)
          | some [SExpr.atom (.symbol pkg)] => .ok (.inPackage pkg.name)
          | _ => .error s!"malformed in-package: {repr sexpr}"
      | "include-book" =>
          match rest.toList? with
          | some (SExpr.atom (.string path) :: tail) =>
              -- include-book tail is keyword-value pairs; extract just the keywords
              let dirs := tail.filterMap fun
                | SExpr.atom (.keyword kw) => some kw
                | _ => none
              .ok (.includeBook path dirs)
          | some (SExpr.atom (.symbol path) :: tail) =>
              let dirs := tail.filterMap fun
                | SExpr.atom (.keyword kw) => some kw
                | _ => none
              .ok (.includeBook path.name dirs)
          | _ => .error s!"malformed include-book: {repr sexpr}"
      | "defun" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: rest) => do
              let fmls ← match params.toList? with
                | some lst =>
                    lst.mapM fun
                      | SExpr.atom (.symbol s) => .ok s
                      | other => .error s!"non-symbol formal in defun: {repr other}"
                | none => .error s!"non-list formals in defun: {repr params}"
              let (doc, decls, bodyExpr) := parseDefunBody none [] rest
              pure (.defun name fmls doc decls bodyExpr)
          | _ => .error s!"malformed defun: {repr sexpr}"
      | "defthm" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: body :: options) => do
              pure (.defthm name { body, options := ← TheoremOption.fromSExprs options })
          | _ => .error s!"malformed defthm: {repr sexpr}"
      | "defmacro" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: rest) => do
              let fmls ← match params.toList? with
                | some lst =>
                    lst.mapM fun
                      | SExpr.atom (.symbol s) => .ok s
                      | other => .error s!"non-symbol formal in defmacro: {repr other}"
                | none => .error s!"non-list formals in defmacro: {repr params}"
              let (doc, decls, bodyExpr) := parseDefunBody none [] rest
              pure (.defmacro name fmls doc decls bodyExpr)
          | _ => .error s!"malformed defmacro: {repr sexpr}"
      | "local" =>
          match rest.toList? with
          | some [inner] => do pure (.local (← classify inner))
          | _ => .error s!"malformed local: {repr sexpr}"
      | "with-output" =>
          match rest.toList? with
          | some args =>
              match args.reverse with
              | inner :: _ => classify inner
              | [] => .error s!"empty with-output: {repr sexpr}"
          | _ => .error s!"malformed with-output: {repr sexpr}"
      | "in-theory" =>
          match rest.toList? with
          | some [expr] => .ok (.inTheory expr)
          | _ => .error s!"malformed in-theory: {repr sexpr}"
      | "mutual-recursion" =>
          match rest.toList? with
          | some lst => do pure (.mutualRecursion (← lst.mapM classify))
          | _ => .error s!"malformed mutual-recursion: {repr sexpr}"
      | "encapsulate" =>
          match rest.toList? with
          | some (_ :: events) => do pure (.encapsulate (← events.mapM classify))
          | _ => .error s!"malformed encapsulate: {repr sexpr}"
      | "make-event" => .ok (.makeEvent rest)
      | "defrec" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: _) => do
              let fmls ← match params.toList? with
                | some lst =>
                    lst.mapM fun
                      | SExpr.atom (.symbol s) => .ok s
                      | other => .error s!"non-symbol field in defrec: {repr other}"
                | none => .error s!"non-list fields in defrec: {repr params}"
              pure (.defrec name fmls)
          | _ => .error s!"malformed defrec: {repr sexpr}"
      | "defconst" =>
          match rest.toList? with
          | some [SExpr.atom (.symbol name), val] => .ok (.defconst name val)
          | _ => .error s!"malformed defconst: {repr sexpr}"
      | "defstobj" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: fields) => .ok (.defstobj name fields)
          | _ => .error s!"malformed defstobj: {repr sexpr}"
      | "table" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: args) => .ok (.table name args)
          | _ => .error s!"malformed table: {repr sexpr}"
      -- Known no-ops: explicitly listed ACL2 forms we intentionally skip
      | "program" => .ok (.skip sexpr)
      | "set-verify-guards-eagerness" => .ok (.skip sexpr)
      | "defequiv" => .ok (.skip sexpr)
      | "defcong" => .ok (.skip sexpr)
      | "comp" => .ok (.skip sexpr)
      | "verify-guards" => .ok (.skip sexpr)
      | "verify-termination" => .ok (.skip sexpr)
      | other => .error s!"unrecognized ACL2 event: {other} in {repr sexpr}"
  | _ => .error s!"expected event form (cons), got: {repr sexpr}"

/-- Recover statically visible nested events from a `make-event`. A
    classification FAILURE yields `[]` — fail-closed, not a default: the
    surrounding `.makeEvent` then survives `flatten` untouched and is
    hard-rejected downstream (`checkTranslatable`). -/
def generatedEvents (body : SExpr) : List Event :=
  match body.toList? with
  | some [generatedExpr] =>
      let recovered := unwrapGeneratedEventExpr generatedExpr
      match classify recovered with
      | .ok (.skip _) | .error _ => []
      | .ok event => [event]
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

/-- Environment maps variable symbols to their values. A minimal ASSOC LIST —
    deliberately NOT a hash map: the trusted core (Layer 1) must stay small and
    auditable, and the KERNEL must be able to REDUCE evaluation (the
    executable-counterpart replay re-checks ACL2's computations by reduction;
    `Std.HashMap`'s string hashing is opaque to the kernel). `insert` prepends,
    so `get?` (first match) sees the newest binding — observationally the
    hash-map `insert`/`get?` semantics. -/
structure Env where
  entries : List (Symbol × SExpr)
  deriving Repr

namespace Env

def get? (e : Env) (s : Symbol) : Option SExpr :=
  e.entries.lookup s

def insert (e : Env) (s : Symbol) (v : SExpr) : Env :=
  ⟨(s, v) :: e.entries⟩

instance : EmptyCollection Env := ⟨⟨[]⟩⟩
instance : Inhabited Env := ⟨{}⟩

@[simp] theorem get?_insert (e : Env) (s s' : Symbol) (v : SExpr) :
    (e.insert s v).get? s' = if s' == s then some v else e.get? s' := by
  cases h : s' == s <;> simp [get?, insert, List.lookup, h]

@[simp] theorem get?_empty (s : Symbol) : ({} : Env).get? s = none := rfl

end Env

end ACL2
