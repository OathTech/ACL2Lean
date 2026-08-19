# Fidelity bug backlog — canonical index

This is the SINGLE canonical list of known fidelity bugs: places where the Lean
interpreter / trusted core diverges from real ACL2. Total faithfulness to ACL2
is the goal, so every mismatch is definitionally a bug and belongs here.

Terminology per `docs/LEXICON.md` (canonical): *replayed statement* /
*waypoint* / *mirror* are three distinct things — entries below use them
in that sense.

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

**Dependency note (2026-07-29, sorting arc):** `Logic.complexRationalp`
is now a trusted-core builtin defined CONSTANTLY nil (with
`realpart`/`imagpart` on the complex-free space), differentially pinned
(numerator-denominator.lisp), and LOAD-BEARING in two vacuous-branch
discharges: the totality walk (`Totality.lean`, the definitionally-nil
truthy branch — ACL2-COUNT's complex admission case) and the induction
walk (`Waterfall/Induction.lean`, same pattern). Both close ACL2's
complex case by absurdity — a DOMAIN RESTRICTION of the model (SExpr
admits no complex values), not a statement weakening, and fail-closed
under a future fix here (the `isDefEq _ nil` guards stop matching and
those proofs stop elaborating, loudly).

**Dependency note (2026-08-15, T1+2 sprint P4b) — THIRD SITE, the
TYPE-SET comparison.** `ACL2Lean/Replay/Driver/TsFacts.lean`'s
`tsAcl2MaskOk`, consumed by `recogVerdictFromTs`
(`Replay/Driver/NodeCore/TypeSetWalk.lean`). ACL2 encodes basic type
INDEX 6 as `*ts-complex-rational*`; `tsIndex`
(`Replay/Lemmas/TsAlgebra.lean`) never returns 6, so `InTs m v` and
`InTs (m ∪ {6}) v` are the SAME proposition on this model and a derived
mask can never carry that bit. ACL2's `<` DOES order complex rationals,
so `(< N '0)` true is emitted with `:TYPESET 112` where the model
derives `48` — 112 = 48 ∪ {bit 6} exactly. The cross-check "ACL2's
emitted mask must be inside the one we derived" therefore demanded the
impossible and refused a strictly-STRONGER derivation (`CD2-BOUND`'s
`Subgoal 1`, recorded as charter J-P4a-g). The comparison now discounts
index 6 AND NOTHING ELSE — any other bit ACL2 has and we do not still
fails, closed. The verdict is unchanged (still ACL2's) and the proof
still runs on OUR mask and OUR `InTs` fact; this is the same domain
restriction as the two sites above, applied at one more place. Fail
direction under a future fix: index 6 becomes inhabited and the discount
becomes unsound to keep, so `tsAcl2MaskOk` must be DELETED (reverting to
`tsSubsumedM`) alongside any fix here — its docstring says so at the
site.

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

## BUG-021 — four unwired `Logic.lean` primitives diverge from ACL2, were documented as faithful
Status: fixed
Pinned-by: differential (`evenp-expt-string.lisp`, 21 match entries incl.
the corner oracles `(expt 0 -1)`=0, `(expt 5 'b)`=1, `(evenp nil)`=T —
fixed to guard-off semantics AND wired into `callBuiltin`/`builtinNames`
2026-07-26, pin-first per H3; two LogicTest #guards that had pinned the
divergent behavior updated to the oracle values)
`Logic.evenp`/`Logic.oddp` match only `.atom (.number (.int n))` and give
nil otherwise; real guard-off ACL2 gives `(evenp nil)`=T, `(evenp 'abc)`=T,
`(oddp 3/2)`=T. `Logic.expt` funnels both args through `toInt`, truncating
rational bases (`(expt 1/2 2)`=1/4 in ACL2). `Logic.string_append` returns
`""` unless both args are strings (`(string-append "ab" 'c)`="ab" in
ACL2). All four oracle values verified against `acl2/saved_acl2` by the
2026-07-26 full-pipeline audit (F6). Latent — but `builtinNames` makes
wiring a one-line change, and the definitions claimed faithfulness. The
tier-1 paperwork commit first marked the definition sites ⚠
NOT-YET-FAITHFUL; the fix then replaced the marks with the guard-off
definitions, whose docstrings cite this entry.

## BUG-023 — the congruence-license lookup was a shape inference; :DEFTHM emits no rule-classes
Status: Lean-side consumption FIXED (2026-07-30, the perm-lane pre-merge
audit's convergent finding — the (fn, pos, R) registry match is now
ANCHORED to the step-cited `(:CONGRUENCE <name>)` rune in the processor's
:RUNES; a collapse whose matched spec is not step-cited hard-fails);
fork-side emission refinements OPEN
Pinned-by: none (proof-log consumption/emission, not interpreter
behavior; the Lean-side guard is the citation anchoring itself, which
fail-closes any uncited license)

Found by the perm-lane pre-merge audit (both reviewers independently,
2026-07-30). G2 rung 2's congruence registry (`congSpecOfFormula?` +
`replayCongCollapse`) shape-parses every strictly-earlier single-literal
local theorem and selected the license by (fn, arg-position, relation)
alone. Two defects in that:
1. INFERENCE where ACL2 emits the answer: the enclosing `:STEP`'s
   `:RUNES` names the licensing rule (`(:CONGRUENCE
   PERM-IMPLIES-EQUAL-ALL-REL-2)` at qsort *1/3.2) and
   `geneqv-refinementp` returns the exact `cr-rune` at the fork's push
   site (acl2/induct.lisp:102-114) — neither was consumed. FIXED
   Lean-side: the registry match must be step-cited.
2. The registry could not distinguish a theorem STORED as :congruence
   from a congruence-SHAPED :rewrite theorem, because the emitted
   `:DEFTHM` event carried only :FORMULA and :SOURCE — no rule-classes.
   With the citation anchoring this can no longer select a wrong
   license (the cited name gates it).
   **HALF LANDED (verified 2026-08-13):** the rule-classes ARE now
   emitted — `:DEFTHM` events carry a `:CLASSES` field (e.g.
   `acl2_samples/sorting/qsort.proof-log:39`:
   `(:DEFTHM PERM-IS-AN-EQUIVALENCE … :CLASSES (:EQUIVALENCE) …)`; also
   `:CLASSES (:REWRITE)`, `:CLASSES :TYPE-PRESCRIPTION`, `:CLASSES NIL`).
   STILL OPEN (fork): emit `:cong-rune` on abbreviation-expansion steps
   (one line at acl2/induct.lisp:158-177) — the per-step congruence
   rune is the remaining emission gap.
   **RT2 LANDING (2026-08-15, T1+2 sprint fork round-trip 2; acl2 @
   `e8d78e513d`).** Ask 3 SHIPPED the OTHER half of defect 1's
   emission: `:CR-RUNE` at the solidify site — the licensing rune the
   fork's `geneqv-refinementp` returns is now emitted, 361 records
   corpus-wide, and PERM-TLFIX's G1 replay reads the exact predicted
   rune. Two things this did NOT do, stated so no reader infers them:
   (a) the `acl2/induct.lisp` abbreviation-expansion site above is a
   DIFFERENT site and remains open — the Status line stands; (b) it did
   NOT fix class D's anchor (`cov-cong-consume`) — that step is a
   STORED-RULE rewrite, not a solidify site, so the push `:CR-RUNE`
   rides on never runs there, and its step-level `:RUNES` still carry
   only `((:DEFINITION SYNP))`.
Related (same audit, tracked in the design note, not bugs): the
:EQUIVALENCE-rule implicit self-congruences and :REFINEMENT rules are
licensing mechanisms with no emitted defthm shape at all — rung-3 work.

## BUG-024 — proof-log emission const-folded instantiated fields (`:UNREWRITTEN-TEST`, `:hyp`, induction `:MEASURE`)
Status: fixed
Pinned-by: none (proof-log emission, not interpreter behavior — no value
stream to diff; verified by the fold-back audit's corpus detector:
529 folded records before the fix, 0 after)

Found by the path-emission fold-back audit (reviewer A + default-refute
verifier, 2026-07-31, V1/A-F1). Seven emission sites instantiated recorded
terms with `sublis-var`, which builds through `cons-term` and CONST-FOLDS
ground primitive calls (even with an empty substitution, via
`cons-term1-mv2`) — the same mechanism as the 2026-07-26 F3 class, whose
fix moved `:LHS`/`:RHS` to `structured-sublis-var-plain` but missed these:
the three `:UNREWRITTEN-TEST` sites (`if-finish/if-test`,
`if-finish/begin-if`, `rewrite-if/constant-if-test` — all 529 corpus hits
came from the last), the three `:hyp-relief` sites
(`relieve-hyp/type-alist`, `/ground-unit`, `/ground-unit-search`), and the
induction `:MEASURE` instantiation (induct.lisp). Witness class: a
recognizer step `(CONSP 'NIL) → 'NIL` followed by `:IF-TEST-FALSE
:UNREWRITTEN-TEST 'NIL` — the field re-performed the collapse instead of
recording the term. FIXED (acl2 9f12ded573): all seven sites use
`structured-sublis-var-plain`, now loop-visible (program-mode
mutual-recursion) so the loop-mode induct.lisp site can call it. Blast
radius at fix time was zero (the parser stored, and the tree builder
dropped, all three `ifTest*` events; nothing read `:hyp`/`:MEASURE`
foldings on the gated corpus) — fixed at the source per "emission is dumb
logging".

## BUG-025 — `IF-FINISH/COMBINED` `:LHS` spliced rule-formal branches (uninstantiated + folded); guard emitted spurious no-op steps
Status: fixed
Pinned-by: none (proof-log emission — the Lean guard is the combined
recipe's running-term ground truth + the final `== rhs` gate, which
fail-close on any misuse; verified by the fold-back audit's detector:
547 hard formal leaks before the fix, 0 after; record count 729 → 138)

Found by the path-emission fold-back audit (reviewer C + verifier,
2026-07-31, V2/C-F1) — BUG-022's "related latency" gone live: the combined
step's `:lhs (mcons-term* 'if test left right)` used the UNREWRITTEN
formal-level branches under a non-nil rewrite alist, leaking rule formals
(`X`, `J`, `I`, `E`, …) into 547 of 729 corpus records — an `:LHS` that
was not a subterm of any running term (witness: FIX's body emitted
`:LHS (IF (ACL2-NUMBERP A) X '0)` for a step ACL2 never took). It also
silently disabled `bridgeIfNegTestSwap`'s target case (`swapped == lhs`
can never match a formal-leaking record) — fail-closed but a coverage
suppressor. FIXED (acl2 9f12ded573): `:lhs` is the ACTUAL input to
`rewrite-if1` — `(list 'if test rewritten-left rewritten-right)`, raw
cons — i.e. exactly the running subterm after the branch windows apply,
and the emit guard compares against the same shape, so a combined step is
emitted exactly when `rewrite-if1` changed the term (this dropped ~591
spurious no-op records the old folded guard let through).

## BUG-026 — the rewrite-if branch swap was UNRECORDED (`:SWAPPED-P`)
Status: fixed
Pinned-by: none (proof-log emission; verified by the fold-back audit's
exact detector — 19 swap occurrences across 7 corpus books, 0 `:SWAPPED-P`
keys before the fix, emitted after)

Found by the path-emission fold-back audit (reviewers A/C + verifier,
2026-07-31, V3). `rewrite-if` normalizes a rewritten test of the negation
shape `(if x nil t)` by stripping it and EXCHANGING the branches
(`rewrite.lisp` mv-let, scoping over all six if-window sites and both
`rewrite-if-finish` calls; `rewrite-if-avoid-swap` is attached to
`constant-nil-function-arity-0`, so `if-call` never un-swaps). The swap
was silent: window KINDs and if-record orientations were post-swap with
nothing marking it, so the replay worked only because two UNRECORDED
normalizations cancelled (the driver's kind↦branch binding vs its
`normalizeSwapsToward`/`bridgeIfNegTestSwap` re-derivation inventory,
~190 lines). FIXED (acl2 9f12ded573): `:swapped-p` is emitted on the six
if-left/if-right window begins, both if-test events, the combined record,
and the constant-test record. Consumed (2026-07-31): the tree carries
`swapped`/`innerSwapped`; the if-finish partition hard-checks window flags
against the combined record's; the inline-window anchoring uses the flag
for pre-swap branch naming. REMAINING (parent-arc epicycle item): the
`if1/if11` record family still lacks the field, so the shape-directed
swap-bridge inventory is validated-but-not-yet-retired — retiring it
(record-directed swap replay) is tracked in TODO.md.

## BUG-027 — truthy-equal edges widened the J6 solidify equation closure without ratification
Status: open — DECISION RECORDED (MDD 2026-08-02): NARROW via emission.
Emit the type-alist equation-edge justifications from the fork (ACL2
consulted those facts and has them) and gate the truthy-equal edges on
the emitted provenance. Open until that emission lands.
Pinned-by: none (replay-side derivation scope, not a differential-visible
divergence — no value stream to diff)

Raised by the fold-back audit (reviewer B, B-F7, 2026-07-31). The
solidify/type-alist recipe's clause-context equation closure
(`inScopeEquations`/`eqChain?`/`composeEqChain`) gained TRUTHY-EQUAL edges
(a TRUE `(equal a b)` branch fact decodes to `a = b` via
`Logic.eq_of_equal_ne_nil`) during the sorting-completion-2 arc. This
widens what the J6 verdict-class carve-out (ratified 2026-06-09) lets the
replay re-derive for a verdict-only type-alist step: the closure now
composes equalities ACL2 justified by its type-alist machinery from MORE
in-scope sources. Each edge is kernel-checked and fail-closed (the
composition must reach the node's emitted `:EQUIV-TERM` target), so this
is a carve-out SCOPE question, not a soundness hole: either ratify the
widened closure as part of the J6 verdict class (it re-derives only from
clause-context facts ACL2 itself consulted) or narrow it behind emitted
justifications. Decide at the parent-arc merge review.

## BUG-022 — the proof-log `:EQUIV` mislabel class: iff-only steps emitted `:EQUIV EQUAL`
Status: fixed (emission sites); one emission-GAP sibling documented open
Pinned-by: none (proof-log emission, not interpreter behavior — no value
stream to diff; the guard is the Lean replay's R-typed chain barrier,
which fail-closes on any mislabeled step it meets: an iff-only fact
consumed as an eval-equality cannot elaborate)

Found by the equiv-lane pre-merge audit (outside reviewer, 2026-07-30).
Four sites in the fork share ACL2's or-shape collapse guard
`(and unrewritten-test (geneqv-refinementp 'iff geneqv wrld)
(equal unrewritten-test left))` or an explicit `*geneqv-iff*` guard, under
which the step is IFF-only (the produced 'T agrees with the value only in
truthiness); the emissions labeled them `:equiv 'equal`:

1. `rewrite.lisp` rewrite-if-finish combined step — FIXED (acl2
   2265010346, equiv-lane inc-2a): `:equiv` recomputes the guard.
2. `rewrite.lisp` rewrite-if quotep-test arm — FIXED (this entry's
   commit): when the truthy-constant test's collapse guard fires, ACL2
   returns `*t*`, not the rewrite of `left` — the record's `:rhs` ALSO
   diverged (said `(subst left)`); now `:rhs *t*` + `:equiv 'iff` under
   the recomputed guard.
3. `rewrite.lisp` rewrite-if11 type-alist-disjoint arm — FIXED (this
   entry's commit): explicitly `*geneqv-iff*`-guarded, `term => 'T`
   IFF-only; was `:equiv 'equal`, now `'iff`. No corpus occurrence yet.
4. `rewrite.lisp` rewrite-if-finish must-be-true arm — OPEN (an emission
   GAP, not a mislabel): the collapse returns `*t*` with NO rewrite-step
   emitted at all. A consumer meeting it fails closed on the chain
   mismatch (the recorded next step's lhs will not occur). Emit when a
   record demands it.

Related latency (same audit): the site-1 combined step's `:lhs`
`(mcons-term* 'if test left right)` splices the REWRITTEN test with
UNSUBSTITUTED left/right — only well-formed when the rewrite alist is
nil; no corpus record exercises a non-nil alist there yet. Fix by
substituting left/right when a record demands it. [This latency went
LIVE and is fixed — see BUG-025.]

## BUG-020 — reader ignores CL's terminating macro characters (fail-OPEN)
Status: fixed
Pinned-by: differential (`reader-terminators.lisp`, 4 match entries —
fixed 2026-07-26 by giving `isAtomChar` the same terminator set as
`isCharTokChar` / `*acl2-read-character-terminators*`; `;` cannot be
pinned in the corpus format and backquote/comma are unmodeled forms —
they now TERMINATE tokens, and a backquote form fails parse loudly)
`Parser.lean`'s `isAtomChar` USED TO end tokens on only
`( ) space \n \r \t` — CL's terminating macro characters
`"` `'` `` ` `` `,` `;` did NOT end a token, while `isCharTokChar` (the
`#\` path) already carried ACL2's real terminator list: an internal
inconsistency. Verified head-to-head (audit F5): ACL2 reads
`(A B;C D)` as `(A B D)`, `(A'B)` as `(A 'B)`, `(A"b")` as `(A "b")`;
the old reader took `B;C`, `A'B`, `A"B"` as single tokens — SILENTLY.
Unlike BUG-010/BUG-015, which hard-fail, this WAS the reader's one
fail-open gap, and it WOULD HAVE BECOME a live soundness hole the
moment gen-world output was wired into the certified pipeline (TODO's
frontend-replacement item) — which is why it was closed as a
prerequisite for that wiring rather than left open.
Fix (2026-07-26): `isAtomChar` was given the same terminator set as
`isCharTokChar` (`*acl2-read-character-terminators*`), and the family
was differential-pinned (the `Pinned-by` line above records what could
and could not be pinned in the corpus format).

## BUG-019 — `local` witnesses entered the World: replayed statements stated about the witness
Status: fixed
Pinned-by: none (pattern-corpus pin: cov-encapsulate's log carries
`:SOURCE :LOCAL-WITNESS` — sig-gated by check-pattern-map; a
differential form cannot express a replay-layer statement bug).
Fix EVOLUTION (2026-08-04, Phase 4's witness scoping — the ratified
tag+scope resolution): the interim fail-closed PARSE REFUSAL is
replaced by structural exclusion — a `:LOCAL-WITNESS` defun is
recorded as a SCOPED `witnessDefun` event (hard-fail outside any
encapsulate bracket) and `Development.toWorld` excludes it BY
CONSTRUCTION, so the certified world never contains a witness body
and the false-green statement substitution is unreachable
(cov-encapsulate now reconstructs and replays honestly red — the
constrained fn is opaque; equisort reconstructs end-to-end).
Every `.defun` event entered the World unconditionally
(ClauseTree.lean), and the fork emitted an encapsulate/defstub/
defevaluator LOCAL witness's admission as a plain `(:DEFUN …)` — so the
World bound the constrained function to its DISCARDED witness body, and
every replayed statement (and every `total:`/`tp:` hypothesis) was about
the witness instead of the constrained function. cov-encapsulate
reported 2/2 REPLAYED, unconditional and axiom-clean, about `λx. 0` —
while the same world validated `(EQUAL (CF X) '0)`, which real ACL2
refuses as a theorem (surfaced by the 2026-07-26 full-pipeline audit,
F1/CONFIRMED; the mechanism was known as a design note since
2026-07-20 — what the audit established is that it failed GREEN).
Nothing false was kernel-certified (each replayed statement is a true statement
about the witness world); the defect is STATEMENT SUBSTITUTION.
Fix (2026-07-26): the fork emits explicit provenance on every
world-entering `:DEFUN` (`:ADMITTED` / `:INCLUDE-BOOK` /
`:GROUND-ZERO` / `:LOCAL-WITNESS` — detected via `in-local-flg`, the
`local` macro's own binding), and the parser HARD-FAILS on
`:LOCAL-WITNESS` (and on missing/unknown provenance) with the named
frontier. Encapsulate SUPPORT (stating replayed statements over the exported
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
divergence lived in the ∀-env quantification of replayed statements, and the
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
(b) replayed statements of canonicity-sensitive ACL2 theorems were FALSE as ∀-env
    statements — verified `(equal (* 1 q) q)` = NIL for q = `.rational 2 4`,
    so e.g. `(implies (rationalp x) (equal (* 1 x) x))` (a true ACL2
    theorem) had a false replayed statement.
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
