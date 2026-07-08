# ACL2 character semantics — researched from the ACL2 source

Date: 2026-07-08. Purpose: ground the Lean character-type implementation
(fixing the `#\a`-is-a-symbol differential known-bug) in ACL2's ACTUAL reader,
printer, and axioms — not black-box guesses. All citations are to the checked-in
`acl2/` submodule.

## The character domain

- Characters are the code points **0–255** (`char-code-linear`, axioms.lisp:9139:
  `(< (char-code x) 256)`; `type-set-char-code` gives `(integerp (char-code x))`
  and `(<= 0 (char-code x))`). So ACL2's character type is exactly the 256 bytes
  — hence the Lean model uses `UInt8`.
- `characterp` is an axiomatic primitive recognizer.

## `char-code` / `code-char` (axioms.lisp)

- `char-code`: char → its code 0–255. Completion (25463 `completion-of-char-code`):
  **`(char-code x) = 0` when `x` is not a character.**
- `code-char`: code → char. Completion (25475 `completion-of-code-char`):
  out of domain (non-integer, `< 0`, or `>= 256`) → `*null-char*` = `(code-char 0)`
  (axioms.lisp:2490). NOT the like-named symbol.
- Mutual inverses on the valid range (9152 `code-char-char-code-is-identity`,
  9156 `char-code-code-char-is-identity`).

## The READER — `#\` syntax (acl2-fns.lisp:1246 `acl2-read-character-string`)

After `#\`, read chars until an `*acl2-read-character-terminators*` char
(acl2.lisp:1871): **Tab Newline Page Space `"` `'` `(` `)` `;` `` ` `` `,`**.
Then:
- **single char** → that character (case-significant: `#\A` ≠ `#\a`).
- **multi-char token** → case-INSENSITIVE (`string-equal`) match against EXACTLY:
  - `Space` → 32
  - `Tab` → 9
  - `Newline` → 10
  - `Page` → 12
  - `Rubout` → 127
  - `Return` → 13
  (`Null`, `Linefeed` are `#+clisp` / `#+(and cmu18 solaris)` build-conditional —
  NOT in the standard/SBCL reader; `#\Null` is a reader error there.)
- **any other multi-char token** → **reader ERROR** ("x must either be a single
  character or one of Space, Tab, Newline, Page, Rubout, or Return").

## The PRINTER (axioms.lisp:22537, kept "in sync with acl2-read-character-string")

Print `#\` then:
- for codes 10/32/12/9/127/13 → the NAME (`Newline`/`Space`/`Page`/`Tab`/
  `Rubout`/`Return`);
- otherwise → the raw character (so `#\A`, `#\a`, `#\0`; a non-printing control
  char prints as `#\` + the raw byte).

## `coerce` (string ↔ char-list) — completion-of-coerce (axioms.lisp)

- `(coerce str 'list)` → list of the string's characters; non-string → `nil`.
- `(coerce x 'string)` → `(coerce (make-character-list x) 'string)`;
  `make-character-list` replaces each non-character element with `*null-char*`
  (code 0) — so coercion to string is total.

## Implications for the Lean model

- `Atom.char (UInt8)` — exact 0–255 domain, `DecidableEq` derivable.
- Parser `#\`: single char → `.char c.toUInt8`; the 6 named tokens
  (case-insensitive) → their codes; any other multi-char token → parse error
  (matches ACL2's reader error / the `refuse` differential class).
- `Logic.characterp` → recognizes `.char`; `char-code` (`.char` → its Nat code,
  else 0); `code-char` (0–255 int → `.char`, else code-0 char).
- Printer: `.char` → `#\` + name for the 6, else the raw char.
- A character is DISTINCT from the like-named symbol/string under `equal`
  (different `Atom` constructors) — matches ACL2.
- A character is NOT a symbol (`symbolp` stays false on `.char`).
