import ACL2Lean.Syntax

namespace ACL2.Parse

/-- Decoded token characters, with positions of unescaped package markers.
An escape, even an empty `||` run, makes the token symbolic rather than numeric. -/
structure ReaderToken where
  chars : List Char
  colons : List Nat
  lastEscape : Option Nat
  deriving Repr

def ReaderToken.escaped (t : ReaderToken) : Bool := t.lastEscape.isSome

def ReaderToken.text (t : ReaderToken) : String := String.ofList t.chars

/-- Read a CL token with multiple and single escapes. Only unescaped runs
receive readtable-case :upcase; only unescaped colons are package markers. -/
def readToken (isTokenChar : Char → Bool) (input : List Char) :
    Except String (ReaderToken × List Char) :=
  go [] [] 0 none false input
where
  go (acc : List Char) (colons : List Nat) (len : Nat)
      (lastEscape : Option Nat) (inBars : Bool) : List Char → Except String (ReaderToken × List Char)
    | [] =>
      if inBars then .error "unterminated escaped symbol"
      else if len == 0 && lastEscape.isNone then .error "empty token"
      else .ok (⟨acc.reverse, colons.reverse, lastEscape⟩, [])
    | '\\' :: rest =>
      match rest with
      | [] => .error "unterminated single-character symbol escape"
      | c :: tail => go (c :: acc) colons (len + 1) (some len) inBars tail
    | '|' :: rest => go acc colons len (some len) (!inBars) rest
    | c :: rest =>
      if !inBars && !isTokenChar c then
        if len == 0 && lastEscape.isNone then .error "empty token"
        else .ok (⟨acc.reverse, colons.reverse, lastEscape⟩, c :: rest)
      else
        let char := if inBars then c else c.toUpper
        let colons := if !inBars && c == ':' then len :: colons else colons
        go (char :: acc) colons (len + 1) lastEscape inBars rest

private def symbolAt (pkg name : String) : Except String SExpr := do
  if (pkg == "ACL2" || pkg == "COMMON-LISP") && name == "NIL" then return .nil
  if (pkg == "ACL2" || pkg == "COMMON-LISP") && name == "T" then return .t
  if pkg == "KEYWORD" then return .atom (.keyword name)
  if hc : canonSym pkg name = true then
    return .atom (.symbol { package := pkg, name, canon := hc })
  throw s!"non-canonical symbol identity: {pkg}::{name}"

/-- Resolve symbolic token syntax. `none` leaves an unescaped, unqualified
token for the numeric reader. Export-table-dependent single-colon access
remains an explicit frontier. -/
def ReaderToken.symbol? (t : ReaderToken) : Except String (Option SExpr) := do
  match t.colons with
  | [] =>
    if t.escaped || t.text == "NIL" || t.text == "T" then
      return some (← symbolAt "ACL2" t.text)
    return none
  | [0] =>
    let name := String.ofList (t.chars.drop 1)
    if name.isEmpty && t.lastEscape != some 1 then throw "empty keyword token"
    return some (.atom (.keyword name))
  | [a, b] =>
    unless a > 0 && b == a + 1 do
      throw s!"malformed package-qualified symbol: {t.text}"
    let pkg := String.ofList (t.chars.take a)
    let name := String.ofList (t.chars.drop (b + 1))
    if pkg.isEmpty || (name.isEmpty && t.lastEscape != some (b + 1)) then
      throw s!"malformed package-qualified symbol: {t.text}"
    return some (← symbolAt pkg name)
  | _ => throw s!"single-colon or malformed package marker unsupported \
      (external-symbol access needs export tables; frontier, BUG-015): {t.text}"

end ACL2.Parse
