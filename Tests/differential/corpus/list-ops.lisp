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
