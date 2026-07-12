;@isolate
; Differential corpus: BOUNDARY / ill-formed forms — run in PER-FORM ISOLATION
; (the `;@isolate` directive above). These cannot share a batched session: a
; float literal HALTS the ACL2 session and a radix literal ABORTS the Lean
; parse stream, so each form gets its own ACL2 session and its own Lean
; invocation. A read/translate/parse error maps to the `<refused>` outcome.
; Each test is ONE single-line form preceded by one `;@` line.
;
; Classes here:
;   refuse                 — BOTH interpreters reject (fidelity: our fail-closed
;                            matches ACL2's translate-time refusal).
;   known-bug lean <val>   — ACL2 refuses but Lean returns a value (too permissive).
;   known-bug lean <refused> — ACL2 has a value but Lean's parser rejects (too strict).

; ── refuse: ill-formed forms BOTH reject (ACL2 Error [Translate]; Lean stuck) ──
;@ refuse
(car '1 '2)
;@ refuse
(cons)
;@ refuse
(if '1 '2 '3 '4)
;@ refuse
(quote a b)
;@ refuse
(foobar '1)
;@ refuse
(let ((x)) x)
; (when …)/(unless …) macroexpand to a form ACL2 refuses at top level (the
; value context is unbound/ignored); Lean's evaluator also declines.
;@ refuse
(when 't '5)
;@ refuse
(unless 'nil '5)

; ── BUG-004 FIXED 2026-07-08 — the '.'-token reader path. GROUNDED in the ACL2
; source: *acl2-readtable* = (copy-readtable nil) — the STANDARD Common Lisp
; reader — and ACL2 binds *read-base* = 10 always (axioms.lisp:21116). Parser.lean
; now implements the CL base-10 rule (numericTokenIsFloat / trailingDotInteger?):
;
; (A) FLOATS are refused. A token with a fractional DIGIT after the dot
;     (`N.N`, `.N`, `N.Ne M`) or an exponent marker (E/S/F/D/L) is a FLOAT —
;     ACL2 has no float type, its reader REFUSES, and so do we (<refused>).
;@ refuse
'5.0
;@ refuse
'1.5
;@ refuse
'.5
;@ refuse
'5e3
;@ refuse
'5.0e3
;@ refuse
'-1.5
;@ refuse
'1d0
;
; (B) TRAILING-DOT INTEGERS. `[sign] digits+ .` with NO fractional digit is a
;     DECIMAL INTEGER (the trailing dot forces base 10): `1.`=1, `10.`=10,
;     `-5.`=-5, `(integerp '10.)`=T. Now match.
;@ match
'1.
;@ match
'10.
;@ match
'-5.
;@ match
'0.
;
; CONTROLS — dot-free numbers ACL2 accepts and we already get right; they must
; STAY accepted (guard against over-rejection).
;@ match
'100
;@ match
'2/3

; ── RADIX literals (BUG-005 FIXED 2026-07-08) — the standard CL radix reader,
; now implemented in Parser.lean: prefix + digits are CASE-INSENSITIVE (#x/#X,
; hex a-f/A-F), the value is the INTEGER (#xFF = 255), signs are allowed
; (#x-1A = -26), and #Nr / #NR is arbitrary radix 2-36 (#2r101 = 5,
; #16rFF = 255). Now match; regression guards. ──
;@ match
'#xFF
;@ match
'#xff
;@ match
'#XA
;@ match
'#x-1A
;@ match
'#b101
;@ match
'#o17
;@ match
'#2r101
;@ match
'#16rFF

; ── BUG-015 (single-colon package markers) — INTERIM FAIL-CLOSED FIX
; (2026-07-12). In the CL reader an unescaped colon is ALWAYS a package
; marker; `pkg:name` (one colon) is EXTERNAL-symbol access — `keyword:foo`
; IS `:foo`, `common-lisp:car` IS `common-lisp::car`, and `acl2:car` is a
; reader ERROR (nothing external in the ACL2 package). A faithful resolution
; needs per-package export tables (the BUG-013 import-table surface); until
; then the parser fail-CLOSES on any single-colon (and otherwise malformed)
; package token — over-strict where ACL2 accepts, but never a silent wrong
; value. Pinned here (isolate) because a parse error aborts the batched Lean
; stream; `known-bug lean <refused>` = ACL2 has a value, Lean's parser
; rejects (too strict). ──
;@ known-bug bug:BUG-015 lean <refused>
'keyword:foo
;@ known-bug bug:BUG-015 lean <refused>
'common-lisp:car
; CONTROLS — the forms the fix must NOT over-reject (must stay accepted):
; double-colon internal access and dotted symbols.
;@ match
'acl2::foo
;@ match
'keyword::foo
;@ match
'foo.bar
; A colon INSIDE a |…| escape is a genuine colon-in-name symbol (NOT a
; package marker — the whole-token escape branch handles it before the
; colon-refusal path, so the parser accepts it correctly: `(equal '|a:b|
; '|a:b|)` = T). It is pinned `known-bug`, not `match`, only because our
; PRINTER does not escape the name on output (renders `a:b`, ACL2 renders
; `|a:b|`) — a separate printer-faithfulness gap, BUG-016. The pin still
; guards parser over-rejection: if the colon-refusal fix wrongly swallowed
; this, Lean would go `<refused>` and the pin would FAIL.
;@ known-bug bug:BUG-016 lean a:b
'|a:b|
