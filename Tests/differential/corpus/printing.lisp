; Differential corpus: value PRINTING / symbol representation fidelity. The
; interpreter's serializer is part of the masquerade surface (the manager
; compares printed values). These are eval-level (they run cleanly); the
; divergence is in how the RESULT is rendered or how symbols are cased.

; KNOWN BUG (DISPLAY ONLY): ACL2's printer abbreviates (quote x) as 'x on
; output; ours prints the literal list (quote x). So (quote (quote a)) renders
; 'A in ACL2 but (quote a) here. This is purely a PRINTER divergence — the VALUE
; is structurally identical: the controls below show car/cdr/equal all agree
; that (quote (quote a)) IS the list (quote a). So BUG-003 is a serializer bug,
; not a semantic one. (The comparator case-folds, so the residual difference is
; the quote-abbreviation, not the case.)
; Surveyed 2026-07-08 against real ACL2 — the abbreviation rule is precise:
; a 2-element list whose CAR is the symbol QUOTE, `(quote X)`, prints as `'X`,
; RECURSIVELY and at ANY nesting depth. It fires ONLY for the exact 2-element
; form: `(quote)` (1 elem), `(quote a b)` (3 elems), and an improper/dotted
; `(1 quote a)` all print LITERALLY. These discriminators pin the rule so a
; future BUG-003 fix can't over- or under-abbreviate.
;@ known-bug bug:BUG-003 lean (quote a)
(quote (quote a))
;@ known-bug bug:BUG-003 lean (quote quote)
(list 'quote 'quote)
; recursion / nesting: the abbreviation applies inside other lists too.
;@ known-bug bug:BUG-003 lean (1 (quote a) 3)
(list '1 (list 'quote 'a) '3)
;@ known-bug bug:BUG-003 lean (a (quote b))
(list 'a (list 'quote 'b))
; EDGE — NOT abbreviated (these must print literally, both sides): wrong arity
; and improper shape. `(quote a b)` (3 elems) and `(quote)` (1 elem) print as
; the literal list; ACL2 and ours already AGREE here (the abbreviation must not
; fire).
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
