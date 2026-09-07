import ACL2Lean.ProofLogTypes

/-! Shared proof-log field readers and the retained linear insertion record.
The main event parser imports these without duplicating rune or plist parsing. -/
namespace ACL2.ProofLog

/-- Look up a keyword in a plist-style s-expression list.
    Given `[:key1, val1, :key2, val2, ...]`, returns `val` for the matching key. -/
def lookupKeyword (kw : String) : List SExpr → Option SExpr
  | .atom (.keyword k) :: v :: rest =>
    if k == kw then some v else lookupKeyword kw rest
  | _ :: rest => lookupKeyword kw rest
  | [] => none

/-- All (keyword, value) pairs of a plist whose key is NOT in `known` — used to
    capture unmodeled fields verbatim rather than silently dropping them. -/
def plistExtras (known : List String) : List SExpr → List (String × SExpr)
  | .atom (.keyword k) :: v :: rest =>
    -- keyword names are stored upcased (readtable :upcase); the extra-field
    -- KEYS are internal dispatch tags looked up with lowercase literals
    -- (`.lookup "poolname"` etc.), so canonicalize to lowercase here.
    let k := k.map Char.toLower
    if known.contains k then plistExtras known rest
    else (k, v) :: plistExtras known rest
  | _ :: rest => plistExtras known rest
  | [] => []

/-- Extract a string from a symbol or string atom. -/
def atomString? : SExpr → Option String
  | .atom (.symbol s) => some s.name
  | .atom (.string s) => some s
  | .atom (.keyword k) => some k
  | _ => none

/-- Parse a single rune like `(:REWRITE CAR-CONS)` — or the multi-rule shape
    `(:REWRITE FLOOR-ZERO . 3)` (J7) — into a `Rune`.
    The rune TYPE (`:REWRITE`/`:DEFINITION`/…) is a fixed keyword-vocabulary
    dispatch tag — we canonicalize it to LOWERCASE at the boundary (analogous
    to `normalizeKey` for theorem-option keys). The rune NAME is an ACL2
    SYMBOL IDENTITY (a theorem/function name — `car-cons`, `perm-symmetric`,
    `my-app`) that must match the same symbol as it is stored elsewhere
    (World keys, theorem names, dependency-proof keys), so it stays UPCASED
    (readtable :upcase) exactly as the parser produced it. A dotted tail that
    is not a nonnegative integer is malformed (fail-closed at the callers). -/
def parseRune? : SExpr → Option Rune
  | .cons (.atom (.keyword runeType)) (.cons nameExpr tail) =>
    let ty := runeType.map Char.toLower
    let name := match atomString? nameExpr with
      | some name => name
      | none => toString (repr nameExpr)
    match tail with
    | .nil => some { ty, name }
    | .atom (.number (.int k)) =>
      if k ≥ 0 then some { ty, name, idx := some k.toNat } else none
    | _ => none
  | _ => none

/-- Parse a rune list like `((:REWRITE FOO) (:DEFINITION BAR))`. Hard-fails on a
    malformed rune or a non-list (no silent drop). -/
def parseRunes (s : SExpr) : Except String (List Rune) :=
  match s.toList? with
  | some items => items.mapM fun r => match parseRune? r with
    | some rune => pure rune
    | none => throw s!"bad rune in rune list: {repr r}"
  | none => throw s!"rune list is not a list: {repr s}"

/-- Parse the same cons-term fold record in hypothesis relief and USE instances. -/
def parseSubstitutionFolds (label : String) (folds : SExpr) :
    Except String (List SubstitutionFold) := do
  let some rows := folds.toList? | throw s!"{label}: :SUBST-FOLDS is not a list"
  let folds ← rows.mapM fun row => do
    let some fields := row.toList? | throw s!"{label}: substitution fold is not a plist"
    let rec validate : List SExpr → List String → Except String Unit
      | [], seen => unless seen.length == 3 do
          throw s!"{label}: substitution fold requires :PATH, :LHS and :RHS"
      | .atom (.keyword key) :: _ :: rest, seen => do
        unless ["PATH", "LHS", "RHS"].contains key && !seen.contains key do
          throw s!"{label}: unknown or repeated substitution fold field"
        validate rest (key :: seen)
      | _, _ => throw s!"{label}: malformed substitution fold plist"
    validate fields []
    let some path := lookupKeyword "PATH" fields | throw s!"{label}: fold path absent"
    let some parts := path.toList? | throw s!"{label}: fold path is not a list"
    let path ← parts.mapM fun part => match part with
      | .atom (.number (.int i)) =>
        if i ≥ 0 then pure i.toNat else throw s!"{label}: negative fold path index"
      | _ => throw s!"{label}: fold path index is not an integer"
    let some lhs := lookupKeyword "LHS" fields | throw s!"{label}: fold lhs absent"
    let some rhs := lookupKeyword "RHS" fields | throw s!"{label}: fold rhs absent"
    return ({ path, lhs, rhs } : SubstitutionFold)
  return folds

/-- Preserve the paired substitution fields; reject malformed fold records. -/
def parseHypSubstitutionBasis (input folds : Option SExpr) :
    Except String (Option HypSubstitutionBasis) := do
  match input, folds with
  | none, none => return none
  | some input, some folds =>
    return some { input, folds := ← parseSubstitutionFolds "HYP-RELIEF" folds }
  | _, _ => throw "HYP-RELIEF: :UNFOLDED-HYP and :SUBST-FOLDS must occur together"

/-- USE folds align with the actual hypothesis/LMI order. Absent is the old format. -/
def parseUseInstanceFolds (value : Option SExpr) (count : Nat) :
    Except String (Option (List (List SubstitutionFold))) := do
  let some value := value | return none
  let some rows := value.toList? | throw "USE-HINT: :INSTANCE-FOLDS is not a list"
  unless rows.length == count do throw "USE-HINT: :INSTANCE-FOLDS must align with :HYPS"
  return some (← rows.mapM (parseSubstitutionFolds "USE-HINT"))

/-- Preserve the selected root comparison route and its returned mask. -/
def parseHypComparisonBasis (value : Option SExpr) :
    Except String (Option HypComparisonBasis) := do
  let some value := value | return none
  if value == .nil then return none
  let some [.atom (.keyword "RESULT"), .atom (.number (.int resultTs)),
      .atom (.keyword "ROUTE"), route] := value.toList?
    | throw "HYP-RELIEF: malformed :COMPARISON-BASIS"
  return some { resultTs, route }

/-- Decode the actual PROCESS-EQUATIONAL-POLYS insertion. Its payload is
provenance, never a proof of the inserted equation. -/
def parseLinearEquation (rest : List SExpr) : Except String TraceEvent := do
  let rec validate : List SExpr → List String → Except String Unit
    | [], _ => pure ()
    | .atom (.keyword key) :: _ :: rest, seen => do
      if seen.contains key then throw s!"LINEAR-EQUATION: duplicate :{key}"
      validate rest (key :: seen)
    | _, _ => throw "LINEAR-EQUATION: malformed property list"
  validate rest []
  let required (key : String) : Except String SExpr :=
    (lookupKeyword key rest).elim (throw s!"LINEAR-EQUATION: missing :{key}") pure
  let readList (key : String) : Except String (List SExpr) := do
    let value ← required key
    value.toList?.elim (throw s!"LINEAR-EQUATION: :{key} is not a list") pure
  let origin ← required "ORIGIN"
  unless origin == .atom (.symbol { name := "PROCESS-EQUATIONAL-POLYS/INSERT" }) do
    throw "LINEAR-EQUATION: unsupported origin"
  unless (plistExtras ["origin", "parent-clause", "input-clause", "new-literal", "output-clause",
      "numeric-flags", "numeric-basis", "poly-pairs", "assumptions", "runes"] rest).isEmpty do
    throw "LINEAR-EQUATION: unrecognized fields"
  let flags ← (← readList "NUMERIC-FLAGS").mapM fun flag => do
    let .atom (.keyword key) := flag | throw "LINEAR-EQUATION: numeric flag is not a keyword"
    unless ["KNOWN-TRUE", "KNOWN-FALSE", "ADDED", "FAILED"].contains key do
      throw "LINEAR-EQUATION: unrecognized numeric flag"
    pure key
  unless flags.length == 2 do throw "LINEAR-EQUATION: expected two numeric flags"
  pure (.linearEquation {
    parentClause := ← readList "PARENT-CLAUSE",
    inputClause := ← readList "INPUT-CLAUSE", newLiteral := ← required "NEW-LITERAL",
    outputClause := ← readList "OUTPUT-CLAUSE", numericFlags := flags,
    numericBasis := lookupKeyword "NUMERIC-BASIS" rest,
    polyPairs := ← readList "POLY-PAIRS", assumptions := ← readList "ASSUMPTIONS",
    runes := ← parseRunes (← required "RUNES") })

end ACL2.ProofLog
