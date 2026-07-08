; Differential corpus: TARGET SURFACE — integer division/rounding and related
; arithmetic not modeled by evalOpt yet (all `stuck`). qsort-era / arithmetic-3
; territory. ACL2 values shown by the manager pin what a faithful model must
; produce when these are wired.

;@ stuck
(floor '7 '2)
;@ stuck
(mod '7 '3)
;@ stuck
(truncate '-7 '2)
;@ stuck
(abs '-5)
;@ stuck
(max '3 '7)
;@ stuck
(min '3 '7)
;@ stuck
(expt '2 '10)
;@ stuck
(zerop '0)
;@ stuck
(evenp '4)
;@ stuck
(oddp '4)
