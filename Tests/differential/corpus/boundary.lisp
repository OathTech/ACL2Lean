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

; ── known-bug: FLOAT literals — ACL2's reader REJECTS floats (it has no floats,
; suggests the #d prefix); our parser accepts them as a decimal Number. Lean too
; permissive. (ACL2 side is <refused>; recorded Lean value is the float.) ──
;@ known-bug lean 5.0
'5.0
;@ known-bug lean 1.5
'1.5

; ── known-bug: RADIX literals — ACL2 accepts #x/#b/#o integers; our parser
; errors ("unrecognized reader macro"), so Lean is <refused>. Lean too strict.
; (ACL2 has a value; recorded Lean outcome is <refused>.) ──
;@ known-bug lean <refused>
'#xFF
;@ known-bug lean <refused>
'#b101
;@ known-bug lean <refused>
'#o17
