; Differential corpus: value PRINTING / symbol representation fidelity. The
; interpreter's serializer is part of the masquerade surface (the manager
; compares printed values). These are eval-level (they run cleanly); the
; divergence is in how the RESULT is rendered or how symbols are cased.

; BUG-003 FIXED 2026-07-08: ACL2's printer abbreviates a 2-element list whose
; CAR is the symbol QUOTE, `(quote X)`, as `'X`, RECURSIVELY and at ANY nesting
; depth. It fires ONLY for the exact 2-element form: `(quote)` (1 elem),
; `(quote a b)` (3 elems), and an improper/dotted `(1 quote a)` all print
; LITERALLY. Implemented in SExpr.toString; these are now regression guards.
;@ match
(quote (quote a))
;@ match
(list 'quote 'quote)
; recursion / nesting: the abbreviation applies inside other lists too.
;@ match
(list '1 (list 'quote 'a) '3)
;@ match
(list 'a (list 'quote 'b))
; EDGE — NOT abbreviated (must print literally): wrong arity and improper shape.
;@ match
(list 'quote 'a 'b)
;@ match
(list 'quote)
; the VALUE is right (these AGREE — proving BUG-003 is display-only):
;@ match
(car (quote (quote a)))
;@ match
(cdr (quote (quote a)))
;@ match
(equal (quote (quote a)) (list 'quote 'a))

; SYMBOL CASE (BUG-002 fixed — regression guard): ACL2 upcases unbarred symbols
; but PRESERVES the case of |bar|-escaped symbols, so |abc| (verbatim lower)
; differs from abc (which reads as ABC) → NIL. Our parser now matches.
;@ match
(equal '|abc| 'abc)

; symbol behavior that AGREES (control): a |bar|-symbol is still a symbol; a
; quoted quote's car is the symbol QUOTE
;@ match
(symbolp '|foo bar|)
;@ match
(car '(quote a))
;@ match
(equal '|abc| '|abc|)
