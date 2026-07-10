;@isolate
; Differential corpus (ISOLATED — a `#`-macro parse error aborts a batched Lean
; stream, like the radix literals in boundary.lisp): ACL2's OWN numeric reader
; macros. *acl2-readtable* redefines several `#` dispatch chars (acl2.lisp
; modify-acl2-readtable → define-sharp-f / -d / -u); the source is acl2-fns.lisp
; sharp-f-read:1469, sharp-d-read:1531, sharp-u-read:1416, read-digits:1444.
; These read into EXACT ACL2 numbers, not host floats.
;
; #f<float> and #u<num> are MODELED (BUG-011 fixed 2026-07-09, Parser.lean
; readSharpF + the #u case): #f rationalizes decimal/hex float syntax to an
; exact rational; #u discards `_` digit separators. #d (double-float, the `df`
; feature) is NOT modeled — no double-float type — and stays a frontier
; (fail-closed <refused>).

; ── #f — exact-rational float reader (now match) ──
;@ match
'#f1.5
;@ match
(equal '#f1.5 '3/2)
;@ match
'#f2.0
;@ match
'#f-1.5
;@ match
'#f10
; hex float: mantissa base 16, exponent (p/P) base 2
;@ match
'#fx1.8
;@ match
'#fx1p4
; exponents (e/E, base 10), incl. negative
;@ match
'#f1e3
;@ match
'#f1.5e2
;@ match
'#f1.5e-2

; ── #u — underscore-separated numeral (now match); B/O/X prefix = radix ──
;@ match
'#u1_000
;@ match
'#u1_000_000
;@ match
'#u42
;@ match
'#ux1F
;@ match
'#ub1_0_1
;@ match
'#uo17

; ── #d — double-float syntax, NOT modeled (frontier; ACL2 has a value) ──
;@ known-bug bug:BUG-011 lean <refused>
'#d1.5
