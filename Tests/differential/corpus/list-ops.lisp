; Differential corpus: list operations. TARGET SURFACE — evalOpt does not model
; these yet (all `stuck`); the sorting corpus reaches them, so they pin what a
; faithful model must later compute. The manager shows ACL2's value. When a
; builtin is wired into callBuiltin, its entry starts producing a value and the
; `stuck` verdict FAILS on purpose — reclassify it to `match`.

;@ stuck
(append '(1 2) '(3 4))
;@ stuck
(append 'nil '(1 2))
;@ stuck
(append '(1) (append '(2) '(3)))
;@ stuck
(revappend '(1 2 3) '(4 5))
;@ stuck
(reverse '(1 2 3))
;@ stuck
(nth '1 '(a b c))
;@ stuck
(nth '5 '(a b c))
;@ stuck
(nthcdr '2 '(a b c d))
;@ stuck
(member-equal '2 '(1 2 3))
;@ stuck
(member-equal '9 '(1 2 3))
;@ stuck
(last '(1 2 3))
;@ stuck
(update-nth '1 'x '(a b c))
