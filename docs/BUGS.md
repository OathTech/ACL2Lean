# Fidelity bug backlog — canonical index

This is the SINGLE canonical list of known fidelity bugs: places where the Lean
interpreter / trusted core diverges from real ACL2. Total faithfulness to ACL2
is the goal, so every mismatch is definitionally a bug and belongs here.

**Robustness contract (enforced by `scripts/check-bugs.sh`, run in `just ci`):**
every `open` bug that is `Pinned-by: differential` MUST have at least one live
`;@ known-bug bug:BUG-NNN …` entry in the differential corpus, and every
`bug:BUG-NNN` tag in the corpus MUST reference an `open` bug here. This keeps
the prose index and the self-enforcing differential ratchet in sync — a bug
cannot be silently fixed-and-forgotten (the ratchet FAILs when behavior
changes) nor silently dropped from the index (the cross-check FAILs). Bugs that
CANNOT yet be pinned in the differential (e.g. a builtin not wired into
`callBuiltin`) are `Pinned-by: none (<reason>)` and listed all the same.

Entry format (keep machine-parseable — the checker reads the `BUG-NNN`,
`Status:`, and `Pinned-by:` fields):

```
## BUG-NNN — one-line summary
Status: open | fixed
Pinned-by: differential | none (<reason>)
<prose: what diverges, ACL2's behavior, root cause, fix notes>
```

---

## BUG-001 — no character type: `#\a` is modeled as a symbol
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2 has a character type (code points 0–255). Our `Atom` had no character
variant, so `#\a` parsed as a symbol named `#\a`. Consequences: `(equal #\a #\b)`
= t (distinct ACL2 characters collapse) and `(symbolp #\a)` = t (a char is not a
symbol). FIXED 2026-07-08: added `Atom.char (UInt8)` + faithful `#\` parser
(single char + the 6 named chars, error otherwise) + ACL2-faithful printer +
`characterp`/`char-code`/`code-char` (with completion corners). The
differential ratchet flipped the two known-bug entries and five now-modeled
char ops in characters.lisp; all reclassified to `match`. See
docs/notes/2026-07-08_acl2-character-semantics.md. (Residual: `char-upcase`/
`char-downcase`/`char<=`/`coerce` char ops remain `unsupported`.)

## BUG-002 — symbol case: parser lowercases bare symbols
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2's reader UPCASES bare symbols and PRESERVES the case of `|bar|`-escaped
symbols; our parser used to LOWERCASE bare symbols, so the case at which two
spellings collapse differed from ACL2. FIXED 2026-07-08 by adopting ACL2's
readtable-case :upcase exactly (docs/notes/2026-07-08_symbol-case-semantics.md):
the parser now upcases bare symbols AND bare keywords and reads `|bar|` (incl.
`:|bar|`) verbatim; `|NIL|`/`|T|` map to the nil/t constructors (they ARE those
symbols). Symbol NAMES are stored uppercase everywhere on the identity path
(`SExpr.t`, `isNamed` literals, `callBuiltin` keys, world/theorem/rune names);
internal DISPATCH TAGS that happen to arrive as symbols/keywords (rune TYPE,
equiv, processor, origin, clausify outcome/verdict/how/kind, extraField keys)
are lowercased at the ProofLog parse boundary — they are not symbol identities.
The differential ratchet flipped all 12 BUG-002 known-bug entries (across
symbol-identity/symbols-keywords/printing.lisp) to `match`, and surfaced a
latent gap the fix also closed: `:|bar|` keywords were not read verbatim
(`:|ABC|` now equals `:abc`, `:|abc|` stays distinct).

## BUG-003 — printer does not abbreviate `(quote x)` as `'x`
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2's printer renders a 2-element list whose car is the symbol `QUOTE` as
`'x`, recursively at any nesting depth; the exact 2-element form only (`(quote)`,
`(quote a b)`, improper `(1 quote a)` print literally). FIXED 2026-07-08 in
`SExpr.toString` (Syntax.lean) with a case matching `.cons (QUOTE) (.cons x nil)`
→ `"'" ++ toString x`; the recursive call re-enters the case so nesting is free.
Regression guards in printing.lisp (all now `match`).

## BUG-004 — the '.'-token reader path (floats + trailing-dot integers)
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to match/refuse)
Grounded in the ACL2 source: `*acl2-readtable* = (copy-readtable nil)` is the
standard Common Lisp reader, and ACL2 binds `*read-base* = 10` always
(axioms.lisp:21116). So a `.`-bearing token follows CL base-10 number syntax.
FIXED 2026-07-08 in Parser.lean (`numericTokenIsFloat` / `trailingDotInteger?`):
(A) FLOATS refused — a fractional digit after the dot (`5.0`/`1.5`/`.5`) or an
    exponent marker (`5e3`/`1d0`; markers E/S/F/D/L) is a FLOAT; ACL2 has no
    float type and its reader refuses, so we fail-closed (`<refused>`).
(B) TRAILING-DOT INTEGERS read as integers — `[sign] digits+ .` with no
    fractional digit is a DECIMAL INTEGER (`1.`=1, `10.`=10, `-5.`=-5,
    `(integerp '10.)`=T).
Dot-free numbers (`100`/`2/3`) and dotted non-numbers (`foo.bar`) are unchanged.
Regression guards in boundary.lisp (floats `refuse`, trailing-dot `match`).

## BUG-005 — radix integer literals rejected (ACL2 accepts them)
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2 accepts Common-Lisp radix literals: `#xFF`=255, `#b101`=5, `#o17`=15,
`#Nr…`=radix N. FIXED 2026-07-08 in Parser.lean (`readRadixInt`/`digitInBase`
+ `#`-dispatch cases for `#x/#X`, `#b/#B`, `#o/#O`, `#Nr/#NR`): case-insensitive
prefix+digits, signed, value is the integer, radix 2–36. Regression guards in
boundary.lisp (all now `match`).

## BUG-006 — lexorder atomKind: keyword has its own order class
Status: fixed
Pinned-by: differential (Tests/differential/corpus/target-ordering.lisp)
ACL2 `alphorder` (axioms.lisp:26995): keywords ARE symbols and sort within the
symbol class by `symbol<`. FIXED 2026-07-08 in the `lexorder`/`atomKind`
FUNCTION (keyword folded into the symbol kind); lexorder was then WIRED into
callBuiltin (Task #7, 2026-07-08) and is now differentially pinned vs real ACL2.
NOTE: the order-property PROOFS (refl/antisym/trans/total) are DONE
(2026-07-12, LexorderOrder.lean — kernel-checked against the corrected
lexorder, enabled by the BUG-012/013/014 canonicity fixes).

## BUG-007 — lexorder atomKind: no character class
Status: fixed
Pinned-by: differential (Tests/differential/corpus/target-ordering.lisp)
`alphorder` orders characters between rationals and strings (by `char-code`).
FIXED 2026-07-08 in the function (character kind added between number and
string, compared by char-code), alongside BUG-001's character type; wired +
differentially pinned 2026-07-08. Proofs commented out pending re-proof.

## BUG-008 — lexorder symbol comparison is not `symbol<`
Status: fixed
Pinned-by: differential (Tests/differential/corpus/target-ordering.lisp)
`Lexorder.lean` compared symbols by `name` then `package`; ACL2's `symbol<`
compares symbol-name via `string<`, tie-break by package-name via `string<`.
FIXED 2026-07-08 with a faithful `symbolLe` (name via `String.<`, tie-break
package) covering both symbols and keywords; wired + differentially pinned
2026-07-08 (`:abc` vs `'abc`, `acl2::foo` vs `common-lisp::foo` confirmed).
Proofs commented out pending re-proof. Residual fidelity question: Lean
`String.<` vs ACL2 `string<` char-ordering — validate when lexorder is wired +
differentially
tested.

## BUG-009 — no complex-rational class (numbers/lexorder)
Status: open
Pinned-by: none (complex numbers not modeled; `unsupported` in the differential
— Tests/differential/corpus/complex-and-packages.lisp)
`alphorder` places complex/complex-rationals between rationals and characters.
We do not model complex numbers at all.
Dependency note (2026-07-20, STRINGP-lift audit): `Logic.rationalp` coincides
with `Logic.acl2Numberp` ON THE MODEL (both true exactly on `.atom (.number _)`)
precisely because of this bug — and the DP-lift registry now consumes
`RATIONALP` through that coincidence. If complex numbers are ever modeled,
`Logic.rationalp` must diverge from `acl2Numberp` (nil on complex) and the
DP-lift discharge of RATIONALP leaves must be revisited alongside.

## BUG-010 — mixed/partial escaping within a symbol token not implemented
Status: open
Pinned-by: differential
ACL2's reader applies readtable-case :upcase to the UNESCAPED runs of a token
and keeps `|…|`/`\`-escaped runs VERBATIM, WITHIN a single token — so `a|B|c`
reads as the symbol named `ABC`, `foo\Bar` as `FOOBAR`, `|ABC|xyz` as `ABCXYZ`.
Our parser only recognizes `|bar|` when it spans the WHOLE token and never
treats `\` as an escape. Found in the BUG-002 audit (2026-07-08). The fix (this
commit) makes the parser FAIL CLOSED — a loud parse error (`<refused>`) — on any
symbol/keyword token with an interior/leading escaped run or a backslash, rather
than silently upcasing wholesale (which had returned a WRONG symbol name, e.g.
`(equal 'a|B|c 'ABC)`=NIL vs ACL2 T) or fuel-looping on trailing chars. Latent
on the current corpus (no such tokens in acl2_samples/ or the corpus). Proper
per-run escaping in the tokenizer is the real fix (deferred); until then the
refusal is faithful-at-the-frontier (never a wrong value). Pinned as
`known-bug bug:BUG-010 lean <refused>` in symbol-identity.lisp.

## BUG-013 — package-IMPORT symbol identity not modeled (nil/t/car duplicates)
Status: open
Pinned-by: differential
(MINIMAL fix landed 2026-07-11; the full import table remains — hence open.)
ACL2's ACL2 package IMPORTS ~977 symbols from COMMON-LISP
(`*common-lisp-symbols-from-main-lisp-package*`): `COMMON-LISP::NIL` IS
`nil`, `ACL2::NIL` resolves to it by import, and `'car` IS
`COMMON-LISP::CAR` (`symbol-package-name 'car` = "COMMON-LISP"). The parser
originally stored the literal source-text (package, name) pair UNRESOLVED,
so these were DISTINCT symbols — live wrong VALUES (the dangerous class):
`(equal 'common-lisp::nil nil)` = NIL vs ACL2 T; `(if 'common-lisp::nil
'truthy 'falsy)` = TRUTHY vs ACL2 FALSY; `(equal 'acl2::nil nil)` = NIL vs
T; `(equal 'car 'common-lisp::car)` = NIL vs T. Found during the lexorder
order-proof work: the nil/t duplicates are ALSO a second instance of the
BUG-012 pattern — two SExpr representations of one ACL2 value that
`lexorder`'s view collapses but `equal` distinguishes — falsifying
lexorder antisymmetry/transitivity over SExpr.
MINIMAL FIX LANDED 2026-07-11 (MDD-ratified option (i)): the parser maps
the import-resolved NIL/T spellings to the canonical `SExpr.nil`/`SExpr.t`,
and the COMMON-LISP::NIL/T identities are UNREPRESENTABLE as `Symbol`s
(`canonSym`, Syntax.lean) — restoring equal/if faithfulness for nil/t and
the view-injectivity the order proofs rest on (LexorderOrder.lean).
Regression guards + the still-open `car` row in complex-and-packages.lisp
(verified vs running ACL2 2026-07-11).
STILL OPEN — full import-table modeling (the fixed ~977 list; changes
builtin identities' packages and printing — e.g. `(equal 'car
'common-lisp::car)` and `symbol-package-name 'car`); options (ii)/(iii) in
the design doc §D5 addendum #2. Related frontier noted at BUG-002 §4 and
the lexorder note's representation section.

## BUG-014 — KEYWORD-package symbols duplicate keywords
Status: fixed
Pinned-by: none (fixed 2026-07-12 — regression guards `match` in
complex-and-packages.lisp)
`keyword::foo` IS `:foo` in ACL2 — KEYWORD is the keywords' HOME package
(not an import; verified vs running ACL2 2026-07-12: `(equal :foo
'keyword::foo)` = T, `(symbol-package-name 'keyword::foo)` = "KEYWORD").
Our parser built `Symbol {package := "KEYWORD", name := "FOO"}` for it — a
SECOND representation of the keyword `.keyword "FOO"` (the BUG-012/013
duplication pattern, third instance): a live wrong value (`(equal :foo
'keyword::foo)` = NIL vs T) and a falsifier of lexorder ANTISYMMETRY (both
representations have the same lexorder view `(name . "KEYWORD")`, so
lexorder held both ways between distinct values). Found during the
lexorder order-proof work — exactly where the memory of the pattern said
to look (the remaining duplicate-representation class after numbers and
nil/t). FIXED 2026-07-12: `canonSym` (Syntax.lean) additionally forbids
package "KEYWORD" (the `.keyword` constructor is the unique
representation), and the parser maps KEYWORD-package tokens to it
(Parser.lean). This completed `lexView?` injectivity, on which the order
proofs (LexorderOrder.lean) rest.

## BUG-015 — single-colon package markers not fully modeled
Status: open
Pinned-by: differential
(Interim fail-closed fix landed 2026-07-12; full external-set modeling
remains — hence still open.)
The CL reader (ACL2's reader) treats `pkg:name` (ONE colon) as
EXTERNAL-symbol access: `keyword:foo` IS `:foo` (the KEYWORD package
exports everything), `common-lisp:car` IS `common-lisp::car` (the standard
symbols are external), and `acl2:car` is a READER ERROR ("The symbol CAR
is not external in the ACL2 package" — the ACL2 package exports nothing).
All verified vs running ACL2 2026-07-12 (found while fidelity-checking the
BUG-014 fix). Our tokenizer originally split package markers on `::` ONLY,
so a single-colon token silently parsed as an ordinary ACL2-package symbol
with the colon IN ITS NAME (`'keyword:foo` → symbol "KEYWORD:FOO") — silent
wrong values (the dangerous class): `(equal :foo 'keyword:foo)` = NIL vs T,
`(equal 'common-lisp:car 'common-lisp::car)` = NIL vs T.
INTERIM FIX LANDED 2026-07-12 (Parser.lean): an unescaped colon is ALWAYS a
package marker (leading-colon keywords and `|…|`-escaped tokens are handled
earlier), so a colon-bearing token is intercepted up front and ONLY the
double-colon `pkg::name` form is accepted; single-colon `pkg:name` and every
other colon shape (`a:::b`, `a::b::c`, `foo::`, `pkg::name.x`) FAIL CLOSED
(parse error). Over-strict where ACL2 accepts external access, but never a
silent wrong value. Pinned in boundary.lisp (isolate path — a parse error
aborts the batched Lean stream, so these live with the other `<refused>`
boundary forms; 2 `known-bug lean <refused>` + control-guards
(`acl2::foo`/`keyword::foo`/`foo.bar` `match`, `|a:b|` under BUG-016) so
the fix cannot over-reject double-colon/dotted/escaped forms). The
`acl2:car` error case is not corpus-pinnable — the raw-Lisp abort emits no
value line. STILL OPEN — the faithful resolution needs external-ness per
package: trivial for KEYWORD (all external → map to `.keyword` like
BUG-014) and ACL2 (none → reader error), but COMMON-LISP's external set is
exactly the standard-symbol list — the BUG-013 import-table surface. Fold
into the BUG-013 full fix.

## BUG-016 — printer does not escape non-standard symbol names with `|…|`
Status: open
Pinned-by: differential
ACL2's printer wraps a symbol NAME in `|…|` bars whenever the name is not a
plain readtable-`:upcase` token — i.e. when it contains a colon, whitespace,
lowercase, or other special chars — so the printed form reads back as the
same symbol: `|a:b|` prints `|a:b|`, `|a b|` prints `|a b|`, `|abc|` (name
"abc", lowercase) prints `|abc|`, while `|FOO|` (name "FOO") prints bare
`FOO` (all verified vs running ACL2 2026-07-12). Our `Repr Symbol`
(Syntax.lean:79-81) renders the name VERBATIM (`a:b`, `a b`, `abc`), so the
printed form is not read-faithful for such names. Distinct from the
reader-side BUG-014/015 — parsing is CORRECT (`(equal '|a:b| '|a:b|)` = T,
`(symbol-name '|a:b|)` = "a:b"); only OUTPUT diverges. Surfaced 2026-07-12
by the BUG-015 control-guard round-trip. Pinned `known-bug bug:BUG-016 lean
a:b` on `'|a:b|` in boundary.lisp. Fix: teach the printer ACL2's
`needs-slashes`/`may-need-slashes` logic (axioms.lisp print path) — escape a
name that is not a bare uppercase token. Keyword printing (`:foo`) and the
plain-uppercase common case are already faithful; this is the escaped-name
tail.

## BUG-019 — `local` witnesses entered the World: mirrors stated about the witness
Status: fixed
Pinned-by: none (pattern-corpus pin: cov-encapsulate's log carries
`:SOURCE :LOCAL-WITNESS` — sig-gated by check-pattern-map — and its
reconstruction hard-fails with the named message; a differential form
cannot express a replay-layer statement bug)
Every `.defun` event entered the World unconditionally
(ClauseTree.lean), and the fork emitted an encapsulate/defstub/
defevaluator LOCAL witness's admission as a plain `(:DEFUN …)` — so the
World bound the constrained function to its DISCARDED witness body, and
every mirror statement (and every `total:`/`tp:` hypothesis) was about
the witness instead of the constrained function. cov-encapsulate
reported 2/2 REPLAYED, unconditional and axiom-clean, about `λx. 0` —
while the same world validated `(EQUAL (CF X) '0)`, which real ACL2
refuses as a theorem (surfaced by the 2026-07-26 full-pipeline audit,
F1/CONFIRMED; the mechanism was known as a design note since
2026-07-20 — what the audit established is that it failed GREEN).
Nothing false was kernel-certified (each mirror is a true statement
about the witness world); the defect is STATEMENT SUBSTITUTION.
Fix (2026-07-26): the fork emits explicit provenance on every
world-entering `:DEFUN` (`:ADMITTED` / `:INCLUDE-BOOK` /
`:GROUND-ZERO` / `:LOCAL-WITNESS` — detected via `in-local-flg`, the
`local` macro's own binding), and the parser HARD-FAILS on
`:LOCAL-WITNESS` (and on missing/unknown provenance) with the named
frontier. Encapsulate SUPPORT (stating mirrors over the exported
:CONSTRAINT list) remains an unbuilt frontier; the four S2b probe
books were rewritten from defstubs to disabled real defuns (their
green rows had been witness-substituted too). Known ADJACENT surface,
out of this fix's scope: local defTHMs' rules (ordered-perms) are
recorded in `(:RULES …)` without locality provenance — rule-provenance
is the same invariant one layer up.

## BUG-018 — duplicate `let`/lambda bindings: ACL2 refuses, we bind (inconsistently)
Status: open
Pinned-by: differential
Real ACL2's translate REJECTS a duplicate bound variable — `(let ((x '1)
(x '2)) x)` and its translated form `((lambda (x x) x) '1 '2)` both give
"improper let expression because it attempts to bind X, which occurs more
than once in the list" (verified against `acl2/saved_acl2`, 2026-07-25).
Our interpreter evaluates both, and — worse — the two spellings of what
ACL2 regards as ONE construct disagree with each other: the surface `LET`
arm's binding fold is last-binding-wins (`(let ((x '1) (x '2)) x)` ⇒ `2`),
while the LAMBDA arm's `bindArgsOver` is first-formal-wins
(`((lambda (x x) x) '1 '2)` ⇒ `1`). Surfaced by the S2 scoping audit
(2026-07-25; the LET side is pre-S2, the lambda side widened it). Fix
direction: refuse duplicate bound variables in both arms (`none`), matching
translate — a well-formedness check, not a semantics choice.

## BUG-017 — builtin dispatch keys on symbol NAME only, dropping the package
Status: open
Pinned-by: none (packages are only partially modeled — BUG-013/015 interim
fail-closed handling refuses the multi-package forms that would express a
divergence, so no differential form currently reaches the dispatch with a
same-name/foreign-package symbol)
`evalOpt` resolves an application head world-first, then falls to
`callBuiltin s.name` (EvalOpt.lean) — the builtin table is keyed by the
symbol's NAME with the package DROPPED. In real ACL2, `MYPKG::CONSP` (a
fresh symbol in a package that does NOT import `COMMON-LISP::CONSP`) is an
undefined function, not the builtin; our interpreter would silently give it
builtin semantics — the dangerous silent-wrong-value class. Not triggered
by the current corpus (single-package; the BUG-015 interim parser refuses
most multi-package forms fail-closed). Surfaced by the 2026-07-18 pre-merge
audit of the induction-generality arc (inherited, not introduced, by it).
SCOPE WIDENED by S2 (audit 2026-07-25): the same name-only `isNamed`
dispatch now also selects the SPECIAL FORMS — `QUOTE`/`IF`/`LET`/`LET*` and
the new `LAMBDA` application head — so a foreign-package `MYPKG::LAMBDA`
gets binder semantics the same way `MYPKG::CONSP` gets builtin semantics.
Same fix (full symbol identity), one more surface.
Fix direction: key the builtin table by full symbol identity (the canonical
COMMON-LISP/ACL2 homes), which is the same import-table surface as the
BUG-013 full fix — fold into it.

## BUG-012 — SExpr admits non-canonical numbers outside ACL2's value space
Status: fixed
Pinned-by: none (fixed 2026-07-11; the junk values were UNREACHABLE from
the ACL2-visible surface, so no differential form could exhibit them — the
divergence lived in the ∀-env quantification of mirror statements, and the
fix makes them UNREPRESENTABLE)
`Number` formerly admitted `.rational 2 4`, `.rational 1 1`, `.decimal …` —
multiple representations of one rational value — while ACL2's value space
has exactly one (reduced ratio, or integer). Recognizers accepted the junk,
arithmetic normalized it (`(* 1 x)` canonicalizes), and `equal`/`==` are
structural — so VALUE-equal junk representations were distinguishable.
Consequences (found by the external-knowledge WP3 spike, 2026-07-11,
countermodel EXECUTED):
(a) `lexorder` transitivity was FALSE over all SExpr — x=((2/4) . 5),
    y=((1/2) . nil), z=((2/4) . 3) gave lexorder x y = T, y z = T,
    x z = NIL (the cons branch's structural `==` vs value-compare on cars);
(b) mirrors of canonicity-sensitive ACL2 theorems were FALSE as ∀-env
    statements — verified `(equal (* 1 q) q)` = NIL for q = `.rational 2 4`,
    so e.g. `(implies (rationalp x) (equal (* 1 x) x))` (a true ACL2
    theorem) had a false mirror.
NOT a proof-of-false-statement unsoundness (a false hypothesis can never be
discharged — fail-closed), but a statement-meaning divergence of the
trust-note class, blocking the external-knowledge D5/WP3 order proofs.
FIXED 2026-07-11 (MDD-ratified Option A — mirror ACL2's value-space
restriction at the type level; docs/notes/2026-07-11_canonical-number-
design.md): `Number.rational` carries a decidable canonicity invariant
(`canonRat`: denominator ≥ 2, reduced), the unreachable `.decimal`
constructor is DELETED, and `Logic.mkNumber` is the proving smart
constructor (the sole construction route). Junk is unrepresentable; the
lexorder order proofs (LexorderOrder.lean) rest on the injectivity this
buys. Gates green with behavior byte-identical (the values were already
canonicalized dynamically).

## BUG-011 — ACL2's own numeric reader macros `#f` / `#d` / `#u`
Status: open
Pinned-by: differential
`*acl2-readtable*` redefines several `#` dispatch chars via
`modify-acl2-readtable` (acl2.lisp) → `define-sharp-f`/`-d`/`-u`; the source is
acl2-fns.lisp (`sharp-f-read`:1469, `sharp-d-read`:1531, `sharp-u-read`:1416,
`read-digits`:1444). These read into EXACT ACL2 numbers, not host floats.
`#f` and `#u` FIXED 2026-07-09 (Parser.lean `readSharpF` + the `#u` case):
`#f<float>` rationalizes decimal/hex float syntax to an exact rational (verified
vs real ACL2: `#f1.5`=3/2, `#f2.0`=2, `#f-1.5`=-3/2, `#fx1.8`=3/2, `#fx1p4`=16,
`#f1e3`=1000, `#f1.5e-2`=3/200); `#u<num>` discards `_` separators, with a
B/O/X prefix taken as radix (`#u1_000`=1000, `#ux1F`=31, `#ub1_0_1`=5).
REMAINING (still open): `#d` (double-float / the `df` feature) — no double-float
type is modeled, so it stays fail-closed (`<refused>`), pinned
`known-bug bug:BUG-011 lean <refused>` in sharp-numeric.lisp; needs the df type
first (a modeling decision, deferred). Distinct from BUG-004 (bare `.`-token
floats, no `#`) and BUG-005 (radix `#x/#b/#o/#Nr`, the standard CL reader).
