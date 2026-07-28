; Differential corpus: TARGET SURFACE — integer division/rounding and related
; arithmetic not modeled by evalOpt yet (all `unsupported`). qsort-era / arithmetic-3
; territory. ACL2 values shown by the manager pin what a faithful model must
; produce when these are wired.

;@ unsupported
(floor '7 '2)
;@ unsupported
(mod '7 '3)
;@ unsupported
(truncate '-7 '2)
;@ unsupported
(abs '-5)
;@ unsupported
(max '3 '7)
;@ unsupported
(min '3 '7)
;@ match ; reclassified 2026-07-26 (BUG-021 fix wired evenp/oddp/expt/string-append)
(expt '2 '10)
;@ unsupported
(zerop '0)
;@ unsupported
(zerop '5)
;@ match ; reclassified 2026-07-26 (BUG-021 fix wired evenp/oddp/expt/string-append)
(evenp '4)
;@ match ; reclassified 2026-07-26 (BUG-021 fix wired evenp/oddp/expt/string-append)
(oddp '4)

; comparison operators beyond `<` — VERY common in real ACL2 (esp. <=), all
; unmodeled today. High-priority target surface.
;@ unsupported
(<= '2 '3)
;@ unsupported
(<= '3 '3)
;@ unsupported
(> '3 '2)
;@ unsupported
(>= '3 '3)
;@ unsupported
(= '3 '3)
;@ unsupported
(= '3 '4)

; rational accessors (also needed to state lexorder/arith lemmas)
;@ match ; reclassified 2026-07-28 (sorting arc wired numerator/denominator)
(numerator '1/2)
;@ match ; reclassified 2026-07-28 (sorting arc wired numerator/denominator)
(denominator '1/2)
;@ match ; reclassified 2026-07-28 (sorting arc wired numerator/denominator)
(numerator '3)
;@ match ; reclassified 2026-07-28 (sorting arc wired numerator/denominator)
(denominator '3)
;@ unsupported
(signum '-5)
;@ unsupported
(signum '0)

; 2-arg division (1-arg unary-/ IS modeled; the 2-arg / macro is not)
;@ unsupported
(/ '1 '0)
;@ unsupported
(/ '6 '3)
;@ unsupported
(/ '5)

; division/rounding with NEGATIVE operands (floor rounds toward -inf; mod
; follows the divisor's sign — the corners arithmetic books lean on)
;@ unsupported
(mod '-7 '3)
;@ unsupported
(floor '-7 '3)
;@ unsupported
(rem '7 '3)
;@ unsupported
(nonnegative-integer-quotient '7 '2)
;@ unsupported
(integer-length '255)

; expt corners (negative exponent → rational; 0^0 = 1)
;@ match ; reclassified 2026-07-26 (BUG-021 fix wired evenp/oddp/expt/string-append)
(expt '2 '-1)
;@ match ; reclassified 2026-07-26 (BUG-021 fix wired evenp/oddp/expt/string-append)
(expt '0 '0)
;@ match ; reclassified 2026-07-26 (BUG-021 fix wired evenp/oddp/expt/string-append)
(expt '2 '0)

; rational accessors on negatives / reduced forms
;@ match ; reclassified 2026-07-28 (sorting arc wired numerator/denominator)
(numerator '-6/4)
;@ match ; reclassified 2026-07-28 (sorting arc wired numerator/denominator)
(denominator '-6/4)
;@ unsupported
(abs '3/2)

; zip (distinct from the modeled zp), realpart/imagpart on reals
;@ unsupported
(zip '0)
;@ unsupported
(zip 'nil)
;@ match ; reclassified 2026-07-28 (sorting arc wired realpart/imagpart)
(realpart '5)
;@ match ; reclassified 2026-07-28 (sorting arc wired realpart/imagpart)
(imagpart '5)
