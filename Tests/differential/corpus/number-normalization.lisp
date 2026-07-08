; Differential corpus: NUMBER NORMALIZATION. ACL2's READER normalizes rational
; literals (gcd-reduce, collapse denominator-1 to an integer), so 2/4 IS 1/2 and
; 4/2 IS the integer 2. This was a KNOWN DIVERGENCE (the parser built the
; rational literal directly, bypassing Logic.mkNumber) — FIXED 2026-07-07 by
; routing the parser's rational construction through Logic.mkNumber. These
; entries were `known-bug` and are now `match` (the differential ratchet caught
; the fix and forced the reclassification).

; -- reduce-to-integer: literal has denominator dividing the numerator --
;@ match
(equal '3/1 '3)
;@ match
(equal '4/2 '2)
;@ match
(integerp '4/2)
;@ match
(integerp '6/3)
;@ match
(equal '0/5 '0)
; -- reduce-to-lower-terms: gcd(num,den) > 1 --
;@ match
(equal '2/4 '1/2)
;@ match
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
