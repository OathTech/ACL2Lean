; Differential corpus: value PRINTING / symbol representation fidelity. The
; interpreter's serializer is part of the masquerade surface (the manager
; compares printed values). These are eval-level (they run cleanly); the
; divergence is in how the RESULT is rendered or how symbols are cased.

; KNOWN BUG: ACL2's printer abbreviates (quote x) as 'x on output; ours prints
; it as the literal list (quote x). So (quote (quote a)) renders 'A in ACL2 but
; (quote a) here. (The comparator case-folds, so the residual difference is the
; quote-abbreviation, not the case.)
;@ known-bug lean (quote a)
(quote (quote a))
;@ known-bug lean (quote quote)
(list 'quote 'quote)

; KNOWN BUG (symbol case — the pending masquerade item): ACL2 upcases unbarred
; symbols but PRESERVES the case of |bar|-escaped symbols, so |abc| (lowercase)
; differs from abc (which reads as ABC) → NIL. Our parser lowercases ALL
; symbols, collapsing |abc| and abc → t.
;@ known-bug lean t
(equal '|abc| 'abc)

; symbol behavior that AGREES (control): a |bar|-symbol is still a symbol; a
; quoted quote's car is the symbol QUOTE
;@ match
(symbolp '|foo bar|)
;@ match
(car '(quote a))
;@ match
(equal '|abc| '|abc|)
