; Differential corpus: sequence search/membership functions — TARGET SURFACE
; (all unsupported in our model). Values pinned from real ACL2. Note the
; non-boolean return shapes a faithful model must reproduce:
;   member[-equal] returns the TAIL from the match (not t/nil);
;   position returns the INDEX (nil if absent);
;   assoc returns the matching PAIR (nil if absent).

;@ unsupported
(member '2 '(1 2 3))
;@ unsupported
(member-equal '9 '(1 2 3))
;@ unsupported
(assoc '2 '((1 . a) (2 . b)))
;@ unsupported
(assoc '9 '((1 . a)))
;@ unsupported
(position '2 '(1 2 3))
;@ unsupported
(position '9 '(1 2 3))
;@ unsupported
(subsetp '(1 2) '(1 2 3))
;@ unsupported
(subsetp '(1 9) '(1 2 3))
;@ unsupported
(no-duplicatesp '(1 2 3))
;@ unsupported
(no-duplicatesp '(1 2 2))
;@ unsupported
(remove-equal '2 '(1 2 2 3))
;@ unsupported
(count '2 '(1 2 2 3))
