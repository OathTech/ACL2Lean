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
;@ known-bug bug:BUG-003 lean (quote a)
(quote (quote a))
;@ known-bug bug:BUG-003 lean (quote quote)
(list 'quote 'quote)
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
