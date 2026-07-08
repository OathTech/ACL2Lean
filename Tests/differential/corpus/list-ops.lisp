; Differential corpus: list operations. TARGET SURFACE — evalOpt does not model
; these yet (all `unsupported`); the sorting corpus reaches them, so they pin what a
; faithful model must later compute. The manager shows ACL2's value. When a
; builtin is wired into callBuiltin, its entry starts producing a value and the
; `unsupported` verdict FAILS on purpose — reclassify it to `match`.

;@ unsupported
(append '(1 2) '(3 4))
;@ unsupported
(append 'nil '(1 2))
;@ unsupported
(append '(1) (append '(2) '(3)))
;@ unsupported
(revappend '(1 2 3) '(4 5))
;@ unsupported
(reverse '(1 2 3))
;@ unsupported
(nth '1 '(a b c))
;@ unsupported
(nth '5 '(a b c))
;@ unsupported
(nthcdr '2 '(a b c d))
;@ unsupported
(member-equal '2 '(1 2 3))
;@ unsupported
(member-equal '9 '(1 2 3))
;@ unsupported
(last '(1 2 3))
;@ unsupported
(update-nth '1 'x '(a b c))
;@ unsupported
(list* '1 '2 '(3 4))
;@ unsupported
(first '(1 2 3))
;@ unsupported
(rest '(1 2 3))
;@ unsupported
(second '(1 2 3))
;@ unsupported
(take '2 '(1 2 3 4))
;@ unsupported
(binary-append '(1) '(2))

; TOTAL-SEMANTICS edge cases (non-obvious ACL2 answers a faithful model must
; match): negative/out-of-bounds indices, padding, improper-list inputs.
;@ unsupported
(nth '-1 '(a b c))       ; negative index nfixes to 0 → A
;@ unsupported
(nthcdr '-1 '(a b))      ; negative → whole list (A B)
;@ unsupported
(nthcdr '5 '(a b))       ; past end → NIL
;@ unsupported
(take '5 '(a b))         ; pads past end with nil → (A B NIL NIL NIL)
;@ unsupported
(take '0 '(a b))         ; → NIL
;@ unsupported
(last 'x)                ; last of an atom is the atom → X
;@ unsupported
(append '(1 . 2) '(3))   ; append walks the proper structure → (1 3)
;@ unsupported
(revappend '(1 2) '3)    ; improper base preserved → (2 1 . 3)
;@ unsupported
(nth '0 'x)              ; nth into an atom → NIL

; alists
;@ unsupported
(acons 'k 'v 'nil)
;@ unsupported
(pairlis$ '(a b) '(1 2))
;@ unsupported
(assoc 'b '((a . 1) (b . 2)))
;@ unsupported
(strip-cars '((1 . 2) (3 . 4)))

; list-structure corners that AGREE (control — cons/car/cdr/len/true-listp are
; modeled and faithful on improper lists and nesting)
;@ match
(cons 'a (cons 'b 'c))
;@ match
(list 'a (list 'b 'c) 'd)
;@ match
(len (cons '1 '2))
;@ match
(true-listp (cons '1 '2))
;@ match
(car (car '((1 2) 3)))
;@ match
(cons '1 '())
;@ match
(equal (cons '1 'nil) (list '1))
