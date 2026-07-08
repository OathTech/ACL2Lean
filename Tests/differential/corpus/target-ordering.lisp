; Differential corpus: TARGET SURFACE — ACL2's total order primitives, not
; modeled yet (all `stuck`). lexorder is the current R2 (isort) wall — insert's
; comparator — built from alphorder over the atom classes. These pin exactly
; what a faithful Logic.lexorder must produce, per input kind.

;@ stuck
(lexorder '1 '2)
;@ stuck
(lexorder '2 '1)
;@ stuck
(lexorder 'a 'b)
;@ stuck
(lexorder '(1) '(2))
;@ stuck
(lexorder '(1 2) '(1 3))
;@ stuck
(alphorder '1 '2)
;@ stuck
(alphorder 'a 'b)
;@ stuck
(symbol-name 'abc)
