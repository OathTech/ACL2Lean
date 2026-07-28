; Differential corpus: COERCE (sorting arc 2026-07-28) — an AXIOMATIC
; primitive (no defun body) demanded by LENGTH's emitted ground-zero body
; ((len (coerce x 'list))), which the ACL2-COUNT sim (the recorded-
; termination-proof consumer) must evaluate on every value. Guard-off
; oracle semantics: 'LIST explodes a string into character atoms
; (non-string -> nil, the completion axiom); any other second argument is
; the 'STRING route via make-character-list (non-character elements
; complete to the null char; non-list x -> ""). All entries verified
; against acl2/saved_acl2 by the harness.

;@ match
(coerce "abc" 'list)
;@ match
(coerce "" 'list)
;@ match
(coerce 'abc 'list)
;@ match
(coerce '5 'list)
;@ match
(coerce nil 'list)
;@ match
(coerce '(#\a #\b) 'string)
;@ match
(coerce nil 'string)
;@ match
(coerce "ab" 'string)
;@ match
(coerce '(#\a) 'foo)
;@ match
(coerce '(#\a . #\b) 'string)
; LENGTH itself is NOT a builtin — it has an emitted ground-zero defun body
; (world-entering in replay contexts); the bare interpreter has no world, so
; these stay unsupported here and pin the oracle values for the sim work.
;@ unsupported
(length "abc")
;@ unsupported
(length "")
;@ unsupported
(length '(1 2 3))
;@ unsupported
(length nil)
