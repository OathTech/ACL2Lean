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

; ── known-bug: FLOAT literals — ACL2's reader REJECTS floats (it has no floats,
; suggests the #d prefix); our parser accepts them as a decimal Number. Lean too
; permissive. (ACL2 side is <refused>; recorded Lean value is the float.)
; Surveyed 2026-07-08 against real ACL2: the float SHAPES are `N.N`, `.N`,
; `N.`? NO — `1.` is the INTEGER 1 (see controls below) — so only a token with
; a fractional DIGIT after the dot, or an exponent marker (e/E/d/D), is a float
; ACL2 rejects. All rejected forms below map to <refused>; the CONTROLS at the
; end must still be ACCEPTED (guarding against over-rejection when BUG-004 is
; fixed by tightening the number reader). ──
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
; CONTROLS — these are NOT floats; ACL2 accepts them, and so must we (both
; before and after the BUG-004 fix). `1.` is the integer 1 (trailing dot,
; no fractional digit); `2/3` a rational; `100` an integer.
;@ match
'100
;@ match
'2/3
;@ known-bug bug:BUG-004 lean 1.
'1.

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
