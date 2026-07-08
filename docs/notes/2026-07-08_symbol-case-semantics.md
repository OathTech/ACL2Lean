# ACL2 symbol case & identity — semantics, grounding, and the required change

Date: 2026-07-08. Purpose: specify EXACTLY how ACL2 treats symbol case/identity,
grounded in the ACL2 logical core (source citations) and confirmed by
differential tests against the running ACL2, so our Lean model can match it with
**zero** semantic difference. This is the design basis for fixing BUG-002.

The end state: for symbol reading, identity (`equal`), and every operation that
observes a symbol, there is NO semantic difference between our Lean ACL2 and the
original ACL2 — none, for any reason.

## 1. What a symbol IS in ACL2's logical core

A symbol's identity is its (symbol-name, symbol-package-name) string pair.

- **`symbol-equality`** (axioms.lisp:16884, a theorem over the axioms):
  ```
  (implies (and (or (symbolp s1) (symbolp s2))
                (equal (symbol-name s1) (symbol-name s2))
                (equal (symbol-package-name s1) (symbol-package-name s2)))
           (equal s1 s2))
  ```
  So two symbols are `equal` iff their name-strings and package-name-strings are
  `equal`. Symbol identity is thus fully determined by those two strings.
- **`intern-in-package-of-symbol-symbol-name`** (axioms.lisp:5665): interning a
  name-string back yields the same symbol. `intern`/`symbol-name` are inverse on
  the name string. So "the name is the string" is an axiomatic fact, independent
  of any reader or printer.

This means: to model a symbol faithfully we store exactly its name string and
package-name string, and compare by string equality. There is no separate
"display" notion — `symbol-name` returns THE string that defines identity.

## 2. What string the READER produces (the case rule)

ACL2 reads source with `*acl2-readtable*`, defined as **`(copy-readtable nil)`**
(acl2.lisp:2026) — a copy of the STANDARD Common Lisp readtable. Per the CL
spec, the standard readtable has `readtable-case = :upcase`. ACL2 customizes only
`#.`, backquote, `#\`, and a few `#`-dispatch chars (acl2.lisp:2026-2030 and
following); it does **not** change `readtable-case` for normal reading.

- `set-acl2-readtable-case :preserve` EXISTS (axioms.lisp:19000) but is
  `#-acl2-loop-only` (raw Lisp, not the logic) and is used ONLY inside
  `read-object-with-case` (axioms.lisp:20670-20691) — an explicit opt-in reader.
  That function's own code shows the DEFAULT is `:upcase`: line 20685,
  `((eq mode :upcase) (read-object channel state))` is the "optimization" that
  just calls the ordinary reader; only a non-`:upcase` mode installs `:preserve`.
  Ordinary term/source reading (`read-object`) is therefore `:upcase`.

Consequently, under `:upcase`:
- An **unescaped** token is upcased: `abc`, `ABC`, `aBc` all read as the symbol
  whose name is `"ABC"`.
- A **`|bar|`-escaped** token is verbatim: `|abc|` → name `"abc"`, `|AbC|` →
  `"AbC"`.
- Keywords follow the same case rule: `:foo`, `:FOO` → name `"FOO"`;
  `:|foo|` → `"foo"`.

## 3. Differential confirmation (semantic, not display)

Run against the real ACL2 (`acl2/saved_acl2`, `(set-guard-checking nil)`),
using `equal` / `intern` / `member-equal` — logical operations, NOT `symbol-name`
display, NOT our proof-log (which is our own instrumentation and is not
evidence):

| form | ACL2 |
|---|---|
| `(equal 'abc '|ABC|)` | `T` |
| `(equal 'abc '|abc|)` | `NIL` |
| `(equal (intern-in-package-of-symbol "ABC" 'x) 'abc)` | `T` |
| `(equal (intern-in-package-of-symbol "abc" 'x) 'abc)` | `NIL` |
| `(member-equal 'abc '(|ABC|))` | `(ABC)` (found) |
| `(member-equal 'abc '(|abc|))` | `NIL` |
| `(symbol-name 'abc)` / `(symbol-name '|abc|)` | `"ABC"` / `"abc"` |
| `(symbol-name :foo)` / `(symbol-package-name :foo)` | `"FOO"` / `"KEYWORD"` |

The bare symbol `abc` is `equal` to the symbol named `"ABC"` and NOT `equal` to
the one named `"abc"`; interning `"ABC"` reproduces it. This is ACL2's reasoning
core (`equal`/`intern`), confirming §1–§2. These are added to the differential
corpus (Tests/differential/corpus/symbols-keywords.lisp) as the acceptance gate.

## 3a. Discriminating experiments — ruling out rival theories

Confirming a theory is weak if the same tests pass under wrong theories too. The
tests in §3 (e.g. `(equal 'abc 'ABC)=T`) are consistent with SEVERAL theories.
Here are the rival theories of symbol case and the experiments that UNIQUELY
distinguish the correct one (all confirmed against real ACL2, using `equal` /
`symbol-name` / `assoc` — semantics, not display):

- **T0 (correct):** unescaped → UPCASE; `|bar|` → verbatim; identity = exact
  (name, pkg) string equality.
- **T1:** identity is case-INSENSITIVE (fold both sides before comparing).
- **T2:** unescaped → DOWNCASE; `|bar|` verbatim (this is our CURRENT model).
- **T3:** case-PRESERVING, no normalization (`abc`≠`ABC`).
- **T4:** CL `:invert` readtable-case.

| experiment | T0 | T1 | T2 | T3 | T4 | ACL2 (actual) |
|---|---|---|---|---|---|---|
| `(equal 'abc 'ABC)`     | T   | T | T   | **NIL** | T | **T** → kills T3 |
| `(equal 'abc '|ABC|)`   | T   | T | **NIL** | NIL | T | **T** → kills T2 (our model!) |
| `(equal '|abc| '|ABC|)` | NIL | **T** | NIL | NIL | NIL | **NIL** → kills T1 |
| `(symbol-name 'aBc)`    | "ABC" | — | "abc" | "aBc" | **"AbC"** | **"ABC"** → kills T4, T2, T3 |
| `(equal 'abc '|abc|)`   | NIL | T | T | NIL | NIL | **NIL** → kills T1, T2 |

The decisive payoffs:
- **UPCASE vs DOWNCASE (T0 vs T2, our current bug):** `(equal 'abc '|ABC|)` = T
  in ACL2. Under downcase, `abc`→"abc" ≠ "ABC" → NIL. Only upcase makes it T.
- **String identity vs case-insensitive (T0 vs T1):** `(equal '|abc| '|ABC|)` =
  NIL. Case-insensitive identity would make them equal.
- **Normalization happens (kills T3):** `(equal 'abc 'ABC)` = T and
  `(equal 'aBc 'AbC)` = T — distinct spellings collapse.
- **It is upcase, not invert (kills T4):** `(symbol-name 'aBc)` = "ABC" (invert
  would preserve the mixed case as "AbC").

**Where the semantics "pays off" (is observable):** anywhere a symbol is used as
DATA, not only in direct `(equal ...)`. Confirmed via computation:
`(cdr (assoc-equal 'abc '((|ABC| . hit))))` = `HIT` but
`(cdr (assoc-equal 'abc '((|abc| . hit))))` = `NIL`. So the case rule is visible
through alist lookup, `member`, `case` dispatch, and any function that branches
on symbol identity — i.e. it affects real evaluation, not just a `symbol-name`
readout. This is why matching it exactly matters: a wrong case theory silently
changes the VALUE of ordinary ACL2 computations over symbol data.

All of these are added to the differential corpus as the acceptance gate — the
suite must reproduce every ACL2 column above, which is only possible under T0.

## 3b. Corner cases where the case rule interacts with other reader paths

Symbol case "pays off" not just in isolation but where it crosses our parser's
special-case paths. Confirmed against real ACL2:

- **`nil` / `t` via bar-escape (identity of NIL/T as symbols).** In ACL2 `nil`
  and `t` are ORDINARY symbols (names "NIL"/"T"). So:
  - `(equal '|NIL| nil)` = **T** — `|NIL|` reads as the symbol named "NIL", which
    IS `nil`.
  - `(equal '|nil| nil)` = **NIL**, `(symbolp '|nil|)` = **T**,
    `(if '|nil| 'truthy 'falsy)` = **TRUTHY** — `|nil|` (name "nil") is a
    distinct, non-nil symbol.
  - `(equal '|T| t)` = **T**; `(equal '|t| t)` = **NIL**.
  This exposes a REPRESENTATION issue in our model beyond case:
  `SExpr.nil`/`SExpr.t` are a distinct constructor / a specific
  `{name:="t"}` symbol, but ACL2 treats NIL/T as ordinary symbols. So a
  faithful parser's `|bar|` path must map verbatim name "NIL" → `SExpr.nil`
  and "T" → `SExpr.t` (and the token path's `nil`/`t` recognition compares the
  UPCASED token to "NIL"/"T"). Our current model already gets
  `(equal '|NIL| 'nil)` wrong (NIL; should be T) — latent today, and the case
  fix must resolve it, not worsen it.
- **number vs symbol via bar-escape.** `(symbolp '|5|)` = **T**,
  `(acl2-numberp '|5|)` = **NIL**, `(equal '|5| '5)` = **NIL** — `|5|` is the
  symbol named "5", NOT the number. `(symbolp '5)` = NIL. Our bar path already
  yields `symbol{name:="5"}`; the number path only fires on bare tokens — so
  this is faithful, but pin it (a naive "does the token look like a number?"
  check applied to bar-escaped tokens would break it).
- **keywords obey the same case rule.** `(equal ':abc ':ABC)` = **T**,
  `(equal ':abc ':|abc|)` = **NIL**, `(equal ':abc ':|ABC|)` = **T**.
- **`case` dispatch / alist keys pay off.** `(case 'abc (ABC 'x)(t 'no))` and
  `(case 'abc (abc 'y)(t 'no))` both MATCH (keys `ABC` and `abc` both read as
  "ABC", same as the upcased `'abc`). And the `assoc` payoff from §3a shows the
  rule changing a computed VALUE, not just an `equal`.

These corner cases are added to the corpus too; the nil/t-as-symbol
representation point is called out as part of the fix (not deferred), since
`(equal '|NIL| 'nil)` must become T.

## 4. Packages (scope note)

`symbol-equality` also requires equal package-name. Built-in CL symbols read in
the ACL2 package but are imported from COMMON-LISP, so e.g. `(equal 'car
'acl2::car)` = T and `(equal 'list 'common-lisp::list)` = T (confirmed). On the
corpus/differential surface all user symbols are package "ACL2" (the translator
already hard-fails on other packages, WorldGen.lean:56), and equality works. The
COMMON-LISP-vs-ACL2 package DISPLAY (via `symbol-package-name`) matters only for
`symbol-package-name`/`symbol<` tiebreaks; it does not affect symbol EQUALITY on
this surface. Fully faithful package interning is out of scope for BUG-002 and
tracked separately (it interacts with `symbol<` / BUG-008 and complex packages).

## 5. Our current model — the divergence (BUG-002)

`ACL2Lean/Parser.lean` `normalizeSymbolName` LOWERCASES unescaped tokens
(`name.map Char.toLower`); the keyword path lowercases; `|bar|` is already
verbatim (Parser.lean ~139-146). So our stored names are lowercase for bare
symbols but verbatim for `|bar|` — the OPPOSITE collapse point from ACL2:
- ACL2: `|ABC|` = `abc` = `ABC` (all name "ABC"); `|abc|` differs.
- Ours:  `abc`/`ABC`/`aBc` → "abc"; `|ABC|` stays "ABC"; so `(equal '|ABC| 'abc)`
  = NIL here but T in ACL2, and `(equal '|abc| 'ABC)` = t here but NIL in ACL2.

`SExpr.t` is `{name := "t"}` (Syntax.lean) — should be `"T"`. `SExpr.nil` is a
distinct constructor (fine for equality; its symbol identity as COMMON-LISP::NIL
matters only for lexorder — see below).

## 6. The required change (exactly ACL2, no double representation, no shims)

Store the name EXACTLY as ACL2's `symbol-name` returns it — uppercase for
unescaped tokens, verbatim for `|bar|` — and compare by string `==` (which is
what `symbol-equality` says identity is):

1. **Parser**: `normalizeSymbolName` UPCASES (`Char.toUpper`); keyword path
   upcases; `|bar|` stays verbatim (already). The `nil`/`t` recognition compares
   the upcased token to `"NIL"`/`"T"`.
2. **`SExpr.t`** → `{name := "T"}`.
3. **All name literals become uppercase**: `Symbol.isNamed` targets (`"QUOTE"`,
   `"IF"`, `"CAR"`, …), `callBuiltin` dispatch keys (`"CONS"`, `"BINARY-+"`, …),
   every `{name := "..."}` and `.name == "..."`. `isNamed` KEEPS its direct `==`
   (kernel-reducible — verified that `String.map Char.toLower` does NOT reduce by
   `decide`/`rfl`, so a case-folding comparator would break the EvalLemmas
   reduction proofs; a direct `==` against the true uppercase name reduces
   fine). `normalizedName` (a lowercase canonical form) stays only where used
   off the proof path (event classification) and its targets stay lowercase.
   This is NOT a shim — it compares against the real stored (uppercase) name.

No two-representation scheme, no bridging lemmas: one field, holding ACL2's
actual name string, compared by equality — which is precisely ACL2's
`symbol-equality`.

## 7. Downstream: lexorder / nil (depends on this fix)

ACL2's `lexorder`/`alphorder` orders symbols by `symbol<` on the NAME string;
`nil` and `t` are COMMON-LISP symbols (names "NIL"/"T"). Confirmed: `(lexorder
nil 5)` = NIL (5 is a number, number < symbol, so nil > 5) — our current
"nil is smallest" is wrong. With names stored faithfully (uppercase), the
symbol-class comparison in `lexorder` matches ACL2, and `nil`/`t` sort as the
symbols "NIL"/"T". Wiring `lexorder` into `callBuiltin` and validating it
differentially is the follow-up that this fix unblocks (BUG-006/007/008 proofs +
the nil-as-symbol correction).
