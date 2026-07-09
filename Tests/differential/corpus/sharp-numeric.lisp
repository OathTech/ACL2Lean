;@isolate
; Differential corpus (ISOLATED — a `#`-macro parse error aborts a batched Lean
; stream, like the radix literals in boundary.lisp): ACL2's OWN numeric reader
; macros (BUG-011). *acl2-readtable* redefines several `#` dispatch chars
; (acl2.lisp modify-acl2-readtable → define-sharp-f / -d / -u); the source is
; acl2-fns.lisp sharp-f-read:1469, sharp-d-read:1531, sharp-u-read:1416,
; read-digits:1444. These read into EXACT ACL2 numbers, not host floats:
;
;   #f<float>  — reads decimal/hex float syntax and RATIONALIZES it: #f1.5 = 3/2,
;                #f2.0 = 2, #f-1.5 = -3/2, #fx1.8 = 3/2 (hex float), #f10 = 10.
;   #u<num>    — a numeral with `_` digit separators discarded: #u1_000 = 1000.
;   #d<num>    — double-float syntax (df feature).
;
; Our parser has none of these (`#` → "unrecognized reader macro"), so it FAILS
; CLOSED (<refused>) while ACL2 has a value. Surveyed 2026-07-08 against real
; ACL2. Pinned known-bug (lean <refused>) as the target surface — fail-closed is
; correct-at-the-frontier. See docs/BUGS.md BUG-011.

;@ known-bug bug:BUG-011 lean <refused>
'#f1.5
;@ known-bug bug:BUG-011 lean <refused>
(equal '#f1.5 '3/2)
;@ known-bug bug:BUG-011 lean <refused>
'#f2.0
;@ known-bug bug:BUG-011 lean <refused>
'#f-1.5
;@ known-bug bug:BUG-011 lean <refused>
'#fx1.8
;@ known-bug bug:BUG-011 lean <refused>
'#u1_000
;@ known-bug bug:BUG-011 lean <refused>
'#u1_000_000
