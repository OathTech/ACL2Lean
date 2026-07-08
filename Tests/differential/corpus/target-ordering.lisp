; Differential corpus: TARGET SURFACE — ACL2's total order primitives, not
; modeled yet (all `unsupported`). lexorder is the current R2 (isort) wall — insert's
; comparator — built from alphorder over the atom classes. These pin exactly
; what a faithful Logic.lexorder must produce, per input kind.

;@ unsupported
(lexorder '1 '2)
;@ unsupported
(lexorder '2 '1)
;@ unsupported
(lexorder 'a 'b)
;@ unsupported
(lexorder '(1) '(2))
;@ unsupported
(lexorder '(1 2) '(1 3))
;@ unsupported
(alphorder '1 '2)
;@ unsupported
(alphorder 'a 'b)
;@ unsupported
(symbol-name 'abc)
