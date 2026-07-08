; Differential corpus: NUMBER NORMALIZATION — a systematic KNOWN DIVERGENCE
; found by this harness (2026-07-07). ACL2's READER normalizes rational literals
; (gcd-reduce, collapse denominator-1 to an integer), so 2/4 IS 1/2 and 4/2 IS
; the integer 2. Our parser (Parser.lean ~175) builds the rational literal
; DIRECTLY, bypassing Logic.mkNumber's reduction — so equal/integerp on
; unreduced literals mismatch. Root cause is one line; the fix (route the parser
; through mkNumber) is a trusted-core change, out of scope for the testing
; sprint. NOTE the bug is PARSE-TIME only: arithmetic RESULTS normalize
; correctly (see (binary-+ '2/4 '0) below and rat-arith.lisp), because
; Logic.plus/times route through mkNumber. Recorded so the fix is DETECTED
; (each `known-bug` entry FAILS when Lean's value changes → reclassify to `match`).

; -- reduce-to-integer: literal has denominator dividing the numerator --
;@ known-bug lean NIL
(equal '3/1 '3)
;@ known-bug lean NIL
(equal '4/2 '2)
;@ known-bug lean NIL
(integerp '4/2)
;@ known-bug lean NIL
(integerp '6/3)
;@ known-bug lean NIL
(equal '0/5 '0)
; -- reduce-to-lower-terms: gcd(num,den) > 1 --
;@ known-bug lean NIL
(equal '2/4 '1/2)
;@ known-bug lean NIL
(equal '10/20 '1/2)

; -- CONTROL: arithmetic through mkNumber normalizes correctly (NOT divergent) --
;@ match
(binary-+ '2/4 '0)
;@ match
(binary-* '3 '1/6)
;@ match
(rationalp '4/2)
; -- negative-denominator literals: agree (both keep them unequal / as-read) --
;@ match
(equal '1/-2 '-1/2)
; -- integer literal quirks that DO agree --
;@ match
(equal '-0 '0)
;@ match
(equal '00 '0)
