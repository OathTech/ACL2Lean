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

; ── BUG-004 — the '.'-token reader path. GROUNDED in the ACL2 source
; (surveyed 2026-07-08): *acl2-readtable* = (copy-readtable nil) — the STANDARD
; Common Lisp reader — and ACL2 binds *read-base* = 10 always (axioms.lisp:21116
; "ACL2 never sets the read-base to other than 10"). So token→number is the CL
; number syntax at base 10, which splits into TWO opposite-direction bugs in our
; single `tok.contains '.'` → symbol branch (Parser.lean):
;
; (A) TOO PERMISSIVE on real FLOATS. A token with a fractional DIGIT after the
;     dot (`N.N`, `.N`, `N.Ne M`) or an exponent marker (e/E/d/D) is a FLOAT —
;     ACL2 has no float type, so its reader REFUSES (<refused>). We wrongly build
;     a decimal Number.
;@ known-bug bug:BUG-004 lean 5.0
'5.0
;@ known-bug bug:BUG-004 lean 1.5
'1.5
;@ known-bug bug:BUG-004 lean .5
'.5
;@ known-bug bug:BUG-004 lean 5E3
'5e3
;@ known-bug bug:BUG-004 lean 5.0E3
'5.0e3
;@ known-bug bug:BUG-004 lean -1.5
'-1.5
;@ known-bug bug:BUG-004 lean 1D0
'1d0
;
; (B) WRONG VALUE on TRAILING-DOT INTEGERS. In CL a `[sign] digits+ .` token
;     with NO fractional digit is a DECIMAL INTEGER (the trailing dot forces
;     base 10) — so ACL2 reads `1.`=1, `10.`=10, `-5.`=-5, and `(integerp '10.)`
;     =T. We instead make the SYMBOL `1.`/`10.`/… (integerp NIL). So the fix
;     must not merely reject dotted tokens (that would still be wrong for these
;     — and turn `1.` from a symbol into <refused>); it must read them as
;     integers. Recorded Lean outcome is the current (wrong) symbol.
;@ known-bug bug:BUG-004 lean 1.
'1.
;@ known-bug bug:BUG-004 lean 10.
'10.
;@ known-bug bug:BUG-004 lean -5.
'-5.
;@ known-bug bug:BUG-004 lean 0.
'0.
;
; CONTROLS — dot-free numbers ACL2 accepts and we already get right; they must
; STAY accepted through the BUG-004 fix (guard against over-rejection).
;@ match
'100
;@ match
'2/3

; ── known-bug: RADIX literals — ACL2 accepts #x/#b/#o/#Nr integers; our parser
; errors ("unrecognized reader macro"), so Lean is <refused>. Lean too strict.
; (ACL2 has a value; recorded Lean outcome is <refused>.) Surveyed 2026-07-08
; against real ACL2: prefix + digits are CASE-INSENSITIVE (#x/#X, hex a-f/A-F),
; the value is the INTEGER (#xFF = 255), signs are allowed (#x-1A = -26), and
; #Nr / #NR is arbitrary radix 2-36 (#2r101 = 5, #16rFF = 255). ──
;@ known-bug bug:BUG-005 lean <refused>
'#xFF
;@ known-bug bug:BUG-005 lean <refused>
'#xff
;@ known-bug bug:BUG-005 lean <refused>
'#XA
;@ known-bug bug:BUG-005 lean <refused>
'#x-1A
;@ known-bug bug:BUG-005 lean <refused>
'#b101
;@ known-bug bug:BUG-005 lean <refused>
'#o17
;@ known-bug bug:BUG-005 lean <refused>
'#2r101
;@ known-bug bug:BUG-005 lean <refused>
'#16rFF
