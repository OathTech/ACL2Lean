import ACL2Lean.Syntax
import ACL2Lean.Logic

namespace ACL2

namespace Parse

abbrev Stream := List Char

-- ACL2 reads unescaped symbol tokens with readtable-case :upcase
-- (*acl2-readtable* = (copy-readtable nil), acl2.lisp:2026), so a bare token's
-- name is UPCASED; `|bar|`-escaped tokens are read verbatim (handled on the
-- `|` path, which does NOT call this). Symbol identity is exact (name,package)
-- string equality (symbol-equality, axioms.lisp:16884). See
-- docs/notes/2026-07-08_symbol-case-semantics.md.
private def normalizeSymbolName (name : String) : String :=
  name.map Char.toUpper

private def normalizePackageName (name : String) : String :=
  name.map Char.toUpper

private def dropWhile (p : Char → Bool) : Stream → Stream
  | [] => []
  | c :: cs => if p c then dropWhile p cs else c :: cs

private def span (p : Char → Bool) : Stream → (List Char × Stream)
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (taken, rest) := span p cs
        (c :: taken, rest)
      else
        ([], c :: cs)

partial def skipWS : Stream → Stream
  | [] => []
  | c :: cs =>
      if c = ';' then
        skipWS (dropWhile (fun d => d ≠ '\n') cs)
      else if c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '\r' then
        skipWS cs
      else if c = '#' then
        match cs with
        | '|' :: rest =>
            let rec skipBlock : Nat → Stream → Stream
              | 0, r => skipWS r
              | _, [] => panic! "unterminated block comment"
              | d, '#' :: '|' :: r => skipBlock (d + 1) r
              | d, '|' :: '#' :: r => skipBlock (d - 1) r
              | d, _ :: r => skipBlock d r
            skipBlock 1 rest
        | _ => c :: cs
      else
        c :: cs

private def readString : Stream → Except String (String × Stream)
  | [] => .error "unterminated string"
  | c :: cs =>
      if c = '"' then
        let rec go : List Char → Stream → Except String (String × Stream)
          | _, [] => .error "unterminated string"
          | acc, '"' :: rest => .ok (String.ofList (acc.reverse), rest)
          | acc, '\\' :: rest =>
              match rest with
              | [] => .error "unterminated escape"
              | h :: tl => go (h :: acc) tl
          | acc, h :: rest => go (h :: acc) rest
        go [] cs
      else
        .error "string literal must start with quote"

private def isAtomChar (c : Char) : Bool :=
  ¬ (c = '(' ∨ c = ')' ∨ c = ' ' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t')

/-- Chars that CONTINUE a `#\` character token: anything that is not one of
    ACL2's `*acl2-read-character-terminators*` (acl2.lisp:1871):
    Tab, Newline, Page, Space, `"`, `'`, `(`, `)`, `;`, backtick, `,`. -/
private def isCharTokChar (c : Char) : Bool :=
  ¬ (c = '\t' ∨ c = '\n' ∨ c = '\x0c' ∨ c = ' ' ∨ c = '"' ∨ c = '\'' ∨
     c = '(' ∨ c = ')' ∨ c = ';' ∨ c = '`' ∨ c = ',')

private def readAtom (cs : Stream) : (String × Stream) :=
  let (tok, rest) := span isAtomChar cs
  (String.ofList tok, rest)

/-- Digit value of `c` in `base` (2–36), or `none` if not a digit in that base.
    Case-insensitive for the letter digits (a–z / A–Z), matching Common Lisp's
    radix reader. -/
private def digitInBase (base : Nat) (c : Char) : Option Nat :=
  let v :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat + 10)
    else none
  match v with
  | some d => if d < base then some d else none
  | none => none

/-- Read a radix integer literal body — `[sign] digit+` in `base` — from the
    token `readAtom` delimits. ACL2 uses the standard CL radix reader
    (`#x`/`#b`/`#o`/`#Nr`), so a missing/ill-formed body is a reader error
    (fail-closed, no silent default). Returns the integer and the rest stream. -/
private def readRadixInt (base : Nat) (cs : Stream) : Except String (Int × Stream) :=
  let (tok, rest) := readAtom cs
  let chars := tok.toList
  let (neg, digits) := match chars with
    | '-' :: ds => (true, ds)
    | '+' :: ds => (false, ds)
    | ds => (false, ds)
  if digits.isEmpty then
    .error s!"radix literal (base {base}): no digits in {tok}"
  else
    let rec go : List Char → Nat → Option Nat
      | [], acc => some acc
      | c :: cs, acc => match digitInBase base c with
        | some d => go cs (acc * base + d)
        | none => none
    match go digits 0 with
    | some n => .ok ((if neg then -(Int.ofNat n) else Int.ofNat n), rest)
    | none => .error s!"radix literal (base {base}): bad digit in {tok}"

/-- Read an ACL2 `#f<float>` literal body (acl2-fns.lisp `sharp-f-read`:1469),
    which RATIONALIZES float syntax into an EXACT rational (ACL2 has no host
    floats). Grammar (already past the `#f`): an optional `x`/`X` selects base
    16 (mantissa base 16, exponent base 2, exponent marker `p`/`P`); otherwise
    base 10 (exponent marker `e`/`E`). Then `[sign] digits [. digits] [expmark
    [sign] digits]`. The value is `± (before + after / mantBase^|after|) *
    expBase^exp`. Returns the value (via `Logic.mkNumber`, so it reduces to an
    integer when the denominator is 1) and the rest stream. Malformed → error
    (fail-closed). Consumes exactly the delimited token (`readAtom`). -/
private def readSharpF (cs : Stream) : Except String (SExpr × Stream) :=
  let (tok, rest) := readAtom cs
  let chars0 := tok.toList
  -- optional hex selector
  let (base16, chars1) := match chars0 with
    | 'x' :: cs | 'X' :: cs => (true, cs)
    | cs => (false, cs)
  let mantBase : Nat := if base16 then 16 else 10
  let expBase : Int := if base16 then 2 else 10
  let isExpMark := fun c => if base16 then (c = 'p' ∨ c = 'P') else (c = 'e' ∨ c = 'E')
  -- sign
  let (neg, chars2) := match chars1 with
    | '-' :: cs => (true, cs)
    | '+' :: cs => (false, cs)
    | cs => (false, cs)
  -- accumulate a run of base-`b` digits, DISCARDING `_` separators (ACL2
  -- `read-digits` skips #\_ in every run) → (value, digit-count, rest).
  let rec digsB : Nat → List Char → Int → Nat → (Int × Nat × List Char)
    | b, c :: cs, acc, cnt =>
      if c = '_' then digsB b cs acc cnt
      else match digitInBase b c with
        | some d => digsB b cs (acc * (Int.ofNat b) + Int.ofNat d) (cnt + 1)
        | none => (acc, cnt, c :: cs)
    | _, [], acc, cnt => (acc, cnt, [])
  -- mantissa/fraction use base `mantBase`; the EXPONENT is ALWAYS base 10
  -- (ACL2 read-exp calls read-digits with base-16-p = nil — only the mantissa
  -- is hex; the p/P exponent's DIGITS are decimal, the exponent BASE is 2).
  let digs := digsB mantBase
  let (before, _, afterDot0) := digs chars2 0 0
  -- fractional part (optional)
  let (numer, denomExp, afterFrac) := match afterDot0 with
    | '.' :: cs =>
      let (afterVal, afterCnt, r) := digs cs 0 0
      -- significand = before + after / mantBase^afterCnt  = (before*mantBase^cnt + after) / mantBase^cnt
      (before * (Int.ofNat mantBase) ^ afterCnt + afterVal, afterCnt, r)
    | cs => (before, 0, cs)
  -- exponent (optional) — digits in BASE 10 regardless of mantBase
  let expE : Except String (Int × List Char) := match afterFrac with
    | c :: cs =>
      if isExpMark c then
        let (esign, cs1) := match cs with
          | '-' :: t => (true, t) | '+' :: t => (false, t) | t => (false, t)
        let (eval, ecnt, r) := digsB 10 cs1 0 0
        if ecnt == 0 then .error s!"#f literal: empty exponent in {tok}"
        else .ok ((if esign then -eval else eval), r)
      else .error s!"#f literal: unexpected '{c}' in {tok}"
    | [] => .ok (0, [])
  match expE with
  | .error e => .error e
  | .ok (exp, leftover) =>
    -- (ACL2 `read-digits` returns 0 for an empty run, so a digitless `#f`/`#fx`
    -- / `#f.` is 0 — not an error. We follow suit; `beforeCnt`/`denomExp` may
    -- both be 0.)
    if !leftover.isEmpty then .error s!"#f literal: trailing chars in {tok}"
    else
      -- value = ± numer / mantBase^denomExp * expBase^exp
      let signedNum := if neg then -numer else numer
      -- fold the exponent into numerator/denominator (exact)
      let num0 : Int := signedNum * (if exp ≥ 0 then expBase ^ exp.toNat else 1)
      let den0 : Int := (Int.ofNat mantBase) ^ denomExp * (if exp < 0 then expBase ^ (-exp).toNat else 1)
      -- Logic.mkNumber reduces gcd + collapses denom 1 → integer
      .ok (Logic.mkNumber num0 den0.natAbs, rest)

/-- `[sign] digit+ '.'` — a trailing-dot DECIMAL INTEGER (CL: the dot forces
    base 10). Returns the integer, or `none` if the (already-upcased) token is
    not this shape. E.g. `1.`→1, `-5.`→-5, `10.`→10; `1.5`/`1`/`.5`→none. -/
private def trailingDotInteger? (tok : String) : Option Int :=
  let chars := tok.toList
  let (neg, body) := match chars with
    | '-' :: cs => (true, cs)
    | '+' :: cs => (false, cs)
    | cs => (false, cs)
  match body.reverse with
  | '.' :: revInit =>
    let init := revInit.reverse
    if !init.isEmpty ∧ init.all (fun c => '0' ≤ c ∧ c ≤ '9') then
      match (String.ofList init).toNat? with
      | some n => some (if neg then -(Int.ofNat n) else Int.ofNat n)
      | none => none
    else none
  | _ => none

/-- Does the (already-upcased) token match Common Lisp FLOAT syntax? ACL2 has no
    float type, so its reader REFUSES these (BUG-004). CL float at base 10 is
    `[sign] {d}* '.' {d}+ [exp]` or `[sign] {d}+ ['.' {d}*] exp`, where the
    exponent marker is one of E/S/F/D/L (case-insensitive; upcased here) followed
    by `[sign] {d}+`. A trailing-dot integer (`1.`) is NOT a float — it is handled
    by `trailingDotInteger?`. -/
private def numericTokenIsFloat (tok : String) : Bool :=
  let chars := tok.toList
  let body := match chars with
    | '-' :: cs => cs
    | '+' :: cs => cs
    | cs => cs
  let isDigit := fun c => decide ('0' ≤ c ∧ c ≤ '9')
  let isExp := fun c => c == 'E' || c == 'S' || c == 'F' || c == 'D' || c == 'L'
  -- split off an optional exponent: mantissa [exp-marker sign? digit+]
  let rec splitExp : List Char → Option (List Char × List Char)
    | [] => none
    | c :: cs => if isExp c then some ([], cs) else
        match splitExp cs with
        | some (m, e) => some (c :: m, e)
        | none => none
  match splitExp body with
  | some (mant, exp) =>
    -- with an exponent: mantissa is digits with at most one '.', ≥1 digit;
    -- exponent is [sign] digit+ or digit+. (`1E3` is a float too.)
    let mantOk := mant.any isDigit && mant.all (fun c => isDigit c || c == '.') &&
                  (mant.filter (· == '.')).length ≤ 1
    let expOk := match exp with
      | s :: ds => (s == '-' || s == '+') && !ds.isEmpty && ds.all isDigit
      | [] => false
    mantOk && (expOk || (!exp.isEmpty && exp.all isDigit))
  | none =>
    -- no exponent: a float needs a '.' with a fractional DIGIT after it. Only
    -- digits and a single '.', ≥1 digit, and NOT trailing-dot (`1.5`/`.5` are
    -- floats; `1.` is a trailing-dot integer, handled elsewhere).
    let hasDot := body.contains '.'
    let onlyNumChars := body.all (fun c => isDigit c || c == '.')
    let oneDot := (body.filter (· == '.')).length ≤ 1
    let notTrailingDot := match body.reverse with
      | '.' :: _ => false
      | _ => true
    hasDot && onlyNumChars && oneDot && body.any isDigit && notTrailingDot

mutual
  partial def parseList (cs : Stream) (acc : List SExpr := [])
      : Except String (SExpr × Stream) :=
    let cs := skipWS cs
    match cs with
    | [] => .error "unterminated list"
    | ')' :: rest => .ok (SExpr.ofList acc.reverse, rest)
    | '.' :: rest =>
        -- A lone `.` (followed by a delimiter/EOF) with a head already read is the
        -- dotted-cdr separator: `(a … z . tl)` ⇒ the improper list with final cdr
        -- `tl`. (A bare `.` is never a legal Lisp symbol, so this is unambiguous; a
        -- `.` that begins an atom — e.g. `.5` — is followed by an atom char and is
        -- parsed normally below.)
        let lone := match rest with | [] => true | c :: _ => !isAtomChar c
        if lone && !acc.isEmpty then
          match parseSExpr rest with
          | .error e => .error e
          | .ok (tl, rest2) =>
              match skipWS rest2 with
              | ')' :: rest3 => .ok (acc.reverse.foldr SExpr.cons tl, rest3)
              | _ => .error "malformed dotted list: expected ) after dotted cdr"
        else
          match parseSExpr cs with
          | .error e => .error e
          | .ok (sx, rest') => parseList rest' (sx :: acc)
    | _ =>
        match parseSExpr cs with
        | .error e => .error e
        | .ok (sx, rest) => parseList rest (sx :: acc)

  partial def parseQuote (tag : String) (cs : Stream)
      : Except String (SExpr × Stream) :=
    match parseSExpr cs with
    | .error e => .error e
    | .ok (sx, rest) =>
        let sym := SExpr.atom (.symbol { name := tag })
        let quoted := SExpr.ofList [sym, sx]
        .ok (quoted, rest)

  partial def parseSExpr (input : Stream) : Except String (SExpr × Stream) :=
    let cs := skipWS input
    match cs with
    | [] => .error "unexpected end of file"
    | '(' :: rest => parseList rest
    | ')' :: _ => .error "unexpected )"
    -- Reader-constructed head symbols use ACL2's uppercase names (`'x` reads as
    -- `(QUOTE x)`; the symbol is QUOTE, not quote).
    | '\'' :: rest => parseQuote "QUOTE" rest
    | '`' :: rest => parseQuote "QUASIQUOTE" rest
    | ',' :: '@' :: rest =>
        match parseSExpr rest with
        | .error e => .error e
        | .ok (sx, tail) =>
            let sym := SExpr.atom (.symbol { name := "UNQUOTE-SPLICING" })
            .ok (SExpr.ofList [sym, sx], tail)
    | ',' :: rest => parseQuote "UNQUOTE" rest
    | '"' :: _ =>
        match readString cs with
        | .error e => .error e
        | .ok (str, rest) =>
            .ok (SExpr.atom (.string str), rest)
    | '|' :: rest =>
        let rec go : List Char → Stream → Except String (String × Stream)
          | _, [] => .error "unterminated escaped symbol"
          | acc, '|' :: rest => .ok (String.ofList acc.reverse, rest)
          | acc, h :: rest => go (h :: acc) rest
        match go [] rest with
        | .error e => .error e
        -- `|bar|` is read VERBATIM (no case change). But nil/t are ordinary
        -- symbols named "NIL"/"T", so `|NIL|` IS nil and `|T|` IS t (confirmed:
        -- (equal '|NIL| nil) = T in ACL2), while `|nil|` (name "nil") is a
        -- distinct symbol. Map the verbatim name to the canonical constructors.
        | .ok (str, rest) =>
            -- FAIL-CLOSED if the closing `|` is followed by more token chars
            -- (`|ABC|xyz`): that is the mixed-escaping case (per-run escaping
            -- unimplemented, BUG-010) — reading only `ABC` and leaving `xyz`
            -- would mis-parse. A proper delimiter/EOF is fine.
            match rest with
            | c :: _ =>
              if isAtomChar c then
                .error s!"escaped symbol |…| followed by more token chars \
                          (mixed per-run escaping unsupported; frontier — \
                          fail-closed, see BUG-010): |{str}|{c}…"
              else if str = "NIL" then .ok (SExpr.nil, rest)
              else if str = "T" then .ok (SExpr.t, rest)
              else .ok (SExpr.atom (.symbol { name := str }), rest)
            | [] =>
              if str = "NIL" then .ok (SExpr.nil, rest)
              else if str = "T" then .ok (SExpr.t, rest)
              else .ok (SExpr.atom (.symbol { name := str }), rest)
    | '#' :: '\\' :: rest =>
        -- ACL2 character syntax (acl2-fns.lisp `acl2-read-character-string`,
        -- researched in docs/notes/2026-07-08_acl2-character-semantics.md):
        -- the FIRST char after `#\` is taken literally (even if it is itself a
        -- terminator, e.g. `#\(`), then further chars are read up to a
        -- character terminator. A single char → that character; a multi-char
        -- token → case-insensitive match against the six names Space/Tab/
        -- Newline/Page/Rubout/Return (their codes); any other multi-char token
        -- is a reader ERROR (fail-closed, matching ACL2).
        match rest with
        | [] => .error "unexpected end of input after #\\"
        | c0 :: rest' =>
            let (more, tail) := span isCharTokChar rest'
            if more.isEmpty then
              -- single character: its code point (ACL2 chars are 0–255; a
              -- literal outside that range cannot arise from a byte source).
              .ok (SExpr.atom (.char (UInt8.ofNat c0.toNat)), tail)
            else
              let name := (String.ofList (c0 :: more)).toUpper
              match name with
              | "SPACE"   => .ok (SExpr.atom (.char 32), tail)
              | "TAB"     => .ok (SExpr.atom (.char 9), tail)
              | "NEWLINE" => .ok (SExpr.atom (.char 10), tail)
              | "PAGE"    => .ok (SExpr.atom (.char 12), tail)
              | "RUBOUT"  => .ok (SExpr.atom (.char 127), tail)
              | "RETURN"  => .ok (SExpr.atom (.char 13), tail)
              | _ => .error s!"invalid character name #\\{String.ofList (c0 :: more)} \
                              (expected a single char or one of Space, Tab, \
                              Newline, Page, Rubout, Return)"
    -- Reader conditionals: the old implementation ignored the feature test
    -- (`#+` always dropped the guarded form, `#-` always kept it — both
    -- backwards from Common Lisp for a present feature). Evaluating feature
    -- expressions honestly needs a *features* model we don't have, so
    -- hard-fail instead of silently mistranslating source (fail-closed
    -- audit N4; no `#+`/`#-` in the current corpus).
    | '#' :: '+' :: _ =>
        .error "reader conditional #+ unsupported — the translator has no \
                *features* model (fail-closed; see 2026-07-06 audit N4)"
    | '#' :: '-' :: _ =>
        .error "reader conditional #- unsupported — the translator has no \
                *features* model (fail-closed; see 2026-07-06 audit N4)"
    -- Radix integer literals (standard CL reader; *acl2-readtable* leaves these
    -- to the default reader). `#x`/`#X` hex, `#b`/`#B` binary, `#o`/`#O` octal,
    -- and `#Nr`/`#NR` arbitrary radix 2–36. Digits and prefix are
    -- case-insensitive; a sign is allowed; the value is the INTEGER (BUG-005).
    | '#' :: c :: rest =>
        let mkInt : Except String (Int × Stream) → Except String (SExpr × Stream) := fun r =>
          match r with
          | .error e => .error e
          | .ok (n, rest') => .ok (SExpr.atom (.number (.int n)), rest')
        if c = 'x' ∨ c = 'X' then mkInt (readRadixInt 16 rest)
        else if c = 'b' ∨ c = 'B' then mkInt (readRadixInt 2 rest)
        else if c = 'o' ∨ c = 'O' then mkInt (readRadixInt 8 rest)
        else if c = 'f' ∨ c = 'F' then
          -- `#f<float>` — ACL2's exact-rational float reader (BUG-011).
          readSharpF rest
        else if c = 'u' ∨ c = 'U' then
          -- `#u<numeral>` — ACL2's underscore-separated numeral (acl2-fns.lisp
          -- sharp-u-read:1416): read the following token, DISCARD every `_`, and
          -- parse the result as a number. A leading B/O/X (case-insensitive)
          -- makes it a radix literal (as if `#`-prefixed); otherwise it is a
          -- base-10 integer (BUG-011). Floats/rationals in `#u` are not modeled
          -- (fail-closed).
          let (rawTok, rest') := readAtom rest
          let stripped := (rawTok.toList.filter (· ≠ '_'))
          match stripped with
          | [] => .error "reader macro #u: no numeral"
          | d :: ds =>
            let bodyStr := String.ofList ds
            let parseIntStr : String → Except String (SExpr × Stream) := fun s =>
              match s.toInt? with
              | some n => .ok (SExpr.atom (.number (.int n)), rest')
              | none => .error s!"reader macro #u: {String.ofList stripped} is not a numeral"
            if d = 'x' ∨ d = 'X' then mkInt (readRadixInt 16 (bodyStr.toList ++ [' ']))
            else if d = 'b' ∨ d = 'B' then mkInt (readRadixInt 2 (bodyStr.toList ++ [' ']))
            else if d = 'o' ∨ d = 'O' then mkInt (readRadixInt 8 (bodyStr.toList ++ [' ']))
            else parseIntStr (String.ofList stripped)
        else if '0' ≤ c ∧ c ≤ '9' then
          -- `#Nr<digits>` — read the radix N (base-10, may be >1 digit), then
          -- `r`/`R`, then the digits in base N.
          let (radixDigits, afterRadix) := span (fun c => '0' ≤ c ∧ c ≤ '9') rest
          let radixStr := String.ofList (c :: radixDigits)
          match radixStr.toNat?, afterRadix with
          | some base, rc :: body =>
              if rc ≠ 'r' ∧ rc ≠ 'R' then
                .error s!"unrecognized reader macro: #{radixStr}… (expected #Nr radix)"
              else if base < 2 ∨ base > 36 then
                .error s!"radix literal #{radixStr}r: base must be 2–36"
              else mkInt (readRadixInt base body)
          | _, _ =>
              .error s!"unrecognized reader macro: #{radixStr}… (expected #Nr radix)"
        else .error s!"unrecognized reader macro: #{String.ofList [c]}"
    | '#' :: [] => .error "unexpected # at end of input"
    | ':' :: '|' :: rest =>
        -- `:|...|` — a keyword whose name is read VERBATIM from the escaped
        -- token (same rule as the top-level `|bar|` symbol path: no case
        -- change). ACL2 makes `:|ABC|` and `:abc` the SAME keyword (both name
        -- "ABC"), and `:|abc|` a DISTINCT one (name "abc").
        let rec goKw : List Char → Stream → Except String (String × Stream)
          | _, [] => .error "unterminated escaped keyword"
          | acc, '|' :: rest => .ok (String.ofList acc.reverse, rest)
          | acc, h :: rest => goKw (h :: acc) rest
        match goKw [] rest with
        | .error e => .error e
        | .ok (str, rest) =>
            -- FAIL-CLOSED on trailing token chars (mixed escaping, BUG-010).
            match rest with
            | c :: _ =>
              if isAtomChar c then
                .error s!"escaped keyword :|…| followed by more token chars \
                          (mixed per-run escaping unsupported; frontier — \
                          fail-closed, see BUG-010): :|{str}|{c}…"
              else .ok (SExpr.atom (.keyword str), rest)
            | [] => .ok (SExpr.atom (.keyword str), rest)
    | ':' :: _ =>
        let (tok, rest) := readAtom cs
        -- Bare keywords obey the same :upcase rule (name upcased); the KEYWORD
        -- package is implicit.
        let kw := ((tok.drop 1).toString).map Char.toUpper
        .ok (SExpr.atom (.keyword kw), rest)
    | _ =>
        let (rawTok, rest) := readAtom cs
        -- FAIL-CLOSED on mixed/partial escaping within a token (BUG-010).
        -- `readAtom` treats `|` and `\` as ordinary atom chars, so a token
        -- with an interior/leading escaped RUN (`a|B|c`, `foo\Bar`) is NOT
        -- handled by the whole-token `|bar|` branch above — ACL2 upcases the
        -- UNESCAPED runs and keeps escaped runs verbatim within one token,
        -- which we do not implement. Rather than silently upcase wholesale
        -- (a wrong symbol name), hard-fail: this is a frontier, not a value.
        if rawTok.contains '|' || rawTok.contains '\\' then
          .error s!"symbol token with interior '|' or '\\' escape unsupported \
                    (per-run readtable escaping not implemented; frontier — \
                    fail-closed, see BUG-010): {rawTok}"
        else
        let tok := normalizeSymbolName rawTok
        -- nil/t recognition against the UPCASED token (ACL2 names "NIL"/"T").
        if tok = "NIL" then .ok (SExpr.nil, rest)
        else if tok = "T" then .ok (SExpr.t, rest)
        else if rawTok.contains ':' then
          -- PACKAGE-QUALIFIED token (BUG-013/014/015). In the CL reader an
          -- unescaped colon is ALWAYS a package marker; leading-colon keywords
          -- (`:foo`) and `|…|`-escaped tokens were handled by the branches
          -- above, so a colon-bearing token HERE is a package reference and
          -- NEVER a number or dotted symbol. Only the double-colon form
          -- `pkg::name` (INTERNAL-symbol access) is supported. Single-colon
          -- `pkg:name` is EXTERNAL-symbol access — `keyword:foo` IS `:foo`,
          -- `common-lisp:car` IS `common-lisp::car`, `acl2:car` is a reader
          -- ERROR — which needs per-package export tables (the BUG-013
          -- import-table surface); until then we fail closed (BUG-015 interim:
          -- over-strict where ACL2 accepts, never a silent wrong value). Any
          -- other colon shape (`a:::b`, `a::b::c`, `foo::`, `a:b::c`) is
          -- malformed. Splitting on "::" cleanly separates the two: a valid
          -- form yields exactly two nonempty parts with no residual colon.
          match rawTok.splitOn "::" with
          | [pkg, name] =>
              if pkg.isEmpty || name.isEmpty || pkg.contains ':' || name.contains ':' then
                .error s!"malformed package-qualified symbol: {rawTok}"
              else
                let p := normalizePackageName pkg
                let n := normalizeSymbolName name
                -- BUG-013 (minimal fix): the ACL2 package IMPORTS NIL and T
                -- from COMMON-LISP, so `common-lisp::nil` / `acl2::nil` ARE
                -- nil (same for T) — verified vs running ACL2 2026-07-11.
                -- Map the resolved identities to the canonical values; the
                -- COMMON-LISP spellings are unrepresentable as Symbols
                -- (canonSym). Other packages' NIL/T-named symbols are
                -- genuinely distinct objects and pass through.
                if (p == "COMMON-LISP" || p == "ACL2") && n == "NIL" then
                  .ok (SExpr.nil, rest)
                else if (p == "COMMON-LISP" || p == "ACL2") && n == "T" then
                  .ok (SExpr.t, rest)
                -- BUG-014: `keyword::foo` IS the keyword `:foo` (the KEYWORD
                -- package is the keywords' home package; verified vs running
                -- ACL2 2026-07-12: `(equal :foo 'keyword::foo)` = T). Map to
                -- the canonical `.keyword` representation; KEYWORD-package
                -- Symbols are unrepresentable (canonSym).
                else if p == "KEYWORD" then
                  .ok (SExpr.atom (.keyword n), rest)
                else if hc : canonSym p n then
                  .ok (SExpr.atom (.symbol { package := p, name := n, canon := hc }), rest)
                else
                  -- unreachable (only COMMON-LISP::NIL/T and KEYWORD::* fail
                  -- canonSym and all are mapped above) — fail closed all the same
                  .error s!"non-canonical symbol identity: {rawTok}"
          | _ =>
              -- zero `::` (single-colon `pkg:name`) or more than one (`a::b::c`)
              .error s!"single-colon or malformed package marker unsupported \
                        (external-symbol access `pkg:name` needs per-package \
                        export tables; frontier — fail-closed, see BUG-015): \
                        {rawTok}"
        else
          match tok.toInt? with
          | some n => .ok (SExpr.atom (.number (.int n)), rest)
          | none =>
            if tok.contains '/' then
              let parts := tok.splitOn "/"
              match parts with
              | [numStr, denStr] =>
                  match numStr.toInt?, denStr.toNat? with
                  -- Route through `Logic.mkNumber` so the literal is normalized
                  -- exactly as ACL2's reader does: gcd-reduce, and collapse a
                  -- denominator-1 rational to the integer (so `4/2` reads as the
                  -- integer 2 and `2/4` as `1/2`). Building `.rational n d` raw
                  -- here was the number-normalization divergence the
                  -- differential suite pinned (5/1 ≠ 5, 2/4 ≠ 1/2).
                  | some n, some d => .ok (Logic.mkNumber n d, rest)
                  | _, _ => .ok (SExpr.atom (.symbol { name := tok }), rest)
              | _ => .ok (SExpr.atom (.symbol { name := tok }), rest)
            else if numericTokenIsFloat tok then
              -- BUG-004: ACL2 uses the standard CL reader at *read-base* = 10
              -- (acl2.lisp:2026 / axioms.lisp:21116). A token matching CL FLOAT
              -- syntax (a fractional digit after '.', or an exponent marker) is
              -- a float, which ACL2 has no type for — its reader REFUSES it.
              .error s!"float literal unsupported — ACL2 has no floating-point \
                        type (its reader refuses '{tok}'); fail-closed (BUG-004)"
            else if trailingDotInteger? tok |>.isSome then
              -- [sign] digit+ '.' (trailing dot, no fractional digit) is a
              -- DECIMAL INTEGER in CL (the dot forces base 10): 1.=1, -5.=-5.
              .ok (SExpr.atom (.number (.int (trailingDotInteger? tok).get!)), rest)
            else if tok.contains '.' then
              -- a '.'-bearing token that is neither a float nor a trailing-dot
              -- integer (e.g. FOO.BAR) is an ordinary symbol.
              .ok (SExpr.atom (.symbol { name := tok }), rest)
            else
              -- colon-free, dot-free, non-numeric: a plain ACL2-package symbol.
              .ok (SExpr.atom (.symbol { name := tok }), rest)
end

/-- Parse all s-expressions from a string. -/
partial def parseAll : String → Except String (List SExpr)
  | str =>
    let rec loop : Stream → List SExpr → Except String (List SExpr)
      | cs, acc =>
        let cs := skipWS cs
        match cs with
        | [] => .ok acc.reverse
        | ')' :: _ => .error "extra )"
        | _ =>
            match parseSExpr cs with
            | .error e => .error e
            | .ok (sx, rest) => loop rest (sx :: acc)
    loop str.toList []

private def parseOne (input : String) : Except String SExpr := do
  let (sx, rest) ← parseSExpr input.toList
  let rest := skipWS rest
  if rest.isEmpty then
    pure sx
  else
    throw s!"unexpected trailing input: {String.ofList rest}"

private def parsedUppercaseDefunLooksRight : Bool :=
  match parseOne "(DEFUN FOO (X) (DECLARE (XARGS :GUARD (INTEGERP X))) (IF T X NIL))" with
  | .ok sx =>
      match Event.classify sx with
      | .ok (.defun { name := "FOO", .. } [{ name := "X", .. }] _ decls body) =>
          decls.length = 1 && body.headSymbol? = some { name := "IF" }
      | _ => false
  | .error _ => false

private def parsedQualifiedBuiltinLooksRight : Bool :=
  match parseOne "ACL2::CAR" with
  | .ok (SExpr.atom (.symbol { package := "ACL2", name := "CAR" })) => true
  | _ => false

private def parsedUppercaseKeywordLooksRight : Bool :=
  match parseOne ":SYSTEM" with
  | .ok (SExpr.atom (.keyword "SYSTEM")) => true
  | _ => false

private def parsedDefthmMetadataLooksRight : Bool :=
  match parseOne "(DEFTHM FOO (EQUAL X X) :RULE-CLASSES (:LINEAR :REWRITE) :HINTS ((\"Goal\" :USE BAR :IN-THEORY (DISABLE BAZ))))" with
  | .ok sx =>
      match Event.classify sx with
      | .ok (.defthm { name := "FOO", .. } info) =>
          info.ruleClasses.map (·.name) = ["linear", "rewrite"] &&
            match info.hintGoals with
            | [hint] =>
                hint.goal = "Goal" &&
                hint.findOption? "use" = some (.atom (.symbol { name := "BAR" })) &&
                hint.inTheory? = some (.disable [.atom (.symbol { name := "BAZ" })])
            | _ => false
      | _ => false
  | .error _ => false

private def parsedTopLevelInTheoryLooksRight : Bool :=
  match parseOne "(IN-THEORY (E/D (COMMUTATIVITY-OF-+)
                                 (ASSOCIATIVITY-OF-+)))" with
  | .ok sx =>
      match Event.classify sx with
      | .ok (.inTheory expr) =>
          TheoryExpr.ofSExpr expr =
            .e_d
              [.atom (.symbol { name := "COMMUTATIVITY-OF-+" })]
              [.atom (.symbol { name := "ASSOCIATIVITY-OF-+" })]
      | _ => false
  | .error _ => false

private def parsedWithOutputWrappedDefthmLooksRight : Bool :=
  match parseOne "(WITH-OUTPUT :OFF :ALL (DEFTHM WRAPPED (EQUAL X X)))" with
  | .ok sx =>
      match Event.classify sx with
      | .ok (.defthm { name := "WRAPPED", .. } info) =>
          info.body = SExpr.ofList
            [ .atom (.symbol { name := "EQUAL" })
            , .atom (.symbol { name := "X" })
            , .atom (.symbol { name := "X" })
            ]
      | _ => false
  | .error _ => false

private def parsedMakeEventEncapsulateLooksRight : Bool :=
  match parseOne "(MAKE-EVENT `(ENCAPSULATE NIL
                                 (LOCAL
                                  (DEFTHM CHECK-IT!-WORKS
                                    (EQUAL X X)
                                    :RULE-CLASSES NIL))
                                 (DEFTHM BADGE-PRIM-TYPE
                                   (EQUAL X X)
                                   :HINTS ((\"Goal\"
                                            :IN-THEORY (DISABLE CHECK-IT! HONS-GET))))))" with
  | .ok sx =>
      match Event.classify sx with
      | .error _ => false
      | .ok ev =>
      match Event.flattenList [ev] with
      | [ .defthm { name := "CHECK-IT!-WORKS", .. } checkInfo
        , .defthm { name := "BADGE-PRIM-TYPE", .. } badgeInfo
        ] =>
          checkInfo.ruleClasses = [] &&
            match badgeInfo.hintGoals with
            | [hint] =>
                hint.goal = "Goal" &&
                hint.inTheory? =
                  some (.disable
                    [ .atom (.symbol { name := "CHECK-IT!" })
                    , .atom (.symbol { name := "HONS-GET" })
                    ])
            | _ => false
      | _ => false
  | .error _ => false

private def parsedProofBuilderInstructionsLookRight : Bool :=
  match parseOne "(DEFTHM APPLY$-PRIM-META-FN-CORRECT
                     (EQUAL (APPLY$-PRIM-META-FN-EV TERM ALIST)
                            (APPLY$-PRIM-META-FN-EV (META-APPLY$-PRIM TERM) ALIST))
                     :INSTRUCTIONS
                     ((QUIET!
                       (:BASH (\"Goal\"
                               :IN-THEORY '((:DEFINITION HONS-ASSOC-EQUAL)
                                            (:DEFINITION HONS-EQUAL))))
                       (:IN-THEORY (UNION-THEORIES
                                    '((:DEFINITION APPLY$-PRIM))
                                    (CURRENT-THEORY :HERE)))
                       (:REPEAT :PROVE)))
                     :RULE-CLASSES ((:META :TRIGGER-FNS (APPLY$-PRIM))))" with
  | .ok sx =>
      match Event.classify sx with
      | .ok (.defthm { name := "APPLY$-PRIM-META-FN-CORRECT", .. } info) =>
          match info.instructions with
          | [ .block "quiet!" [bashInst, theoryInst, .block "repeat" [.atom "prove"]] ] =>
              let bashOk :=
                match bashInst.goalHints with
                | [hint] =>
                    hint.goal = "Goal" &&
                      hint.inTheory?.isSome
                | _ => false
              let theoryOk :=
                match theoryInst.theoryExpr? with
                | some (.raw expr) =>
                    match expr.toList? with
                    | some (.atom (.symbol head) :: _) => head.isNamed "UNION-THEORIES"
                    | _ => false
                | _ => false
              bashOk && theoryOk
          | _ => false
      | _ => false
  | .error _ => false

#guard parsedQualifiedBuiltinLooksRight
#guard parsedUppercaseKeywordLooksRight
#guard parsedUppercaseDefunLooksRight
#guard parsedDefthmMetadataLooksRight
#guard parsedTopLevelInTheoryLooksRight
#guard parsedWithOutputWrappedDefthmLooksRight
#guard parsedMakeEventEncapsulateLooksRight
#guard parsedProofBuilderInstructionsLookRight

end Parse

end ACL2
