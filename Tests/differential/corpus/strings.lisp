; Differential corpus: STRING operations. String literals parse and string
; equality is faithful (control cases); the operations are unmodeled target
; surface. Values pinned from real ACL2.

; string behavior that AGREES (control)
;@ match
(stringp "")
;@ match
(stringp "hello")
;@ match
(equal "" "")
;@ match
(equal "abc" "abc")
;@ match
(equal "abc" "abd")
;@ match
(equal "a" "A")
;@ match
(consp "abc")
;@ match
(atom "abc")

; TARGET SURFACE — string operations not modeled. Note (string< "abc" "abd")
; returns a POSITION (2), not a boolean, in ACL2.
;@ match ; reclassified 2026-07-28 (sorting arc wired coerce)
(coerce "abc" 'list)
;@ match ; reclassified 2026-07-28 (sorting arc wired coerce)
(coerce '(#\a #\b) 'string)
; coerce COMPLETION semantics (completion-of-coerce, axioms.lisp): a type-flag
; that isn't 'list defaults to the 'string branch; (coerce x 'string) uses
; make-character-list so non-character elements become the null char; nil→"".
;@ match ; reclassified 2026-07-28 (sorting arc wired coerce)
(coerce "abc" 'foo)
;@ match ; reclassified 2026-07-28 (sorting arc wired coerce)
(coerce 'nil 'string)
;@ match ; reclassified 2026-07-28 (sorting arc wired coerce)
(coerce '(#\a #\1 #\Space) 'string)
;@ match ; reclassified 2026-07-28 (sorting arc wired coerce)
(coerce "" 'list)
; length works on strings AND lists
;@ unsupported
(length "hello")
;@ unsupported
(length '(a b c))
;@ unsupported
(char "hello" '0)
;@ unsupported
(subseq "hello" '1 '3)
;@ match ; reclassified 2026-07-26 (BUG-021 fix wired evenp/oddp/expt/string-append)
(string-append "ab" "cd")
;@ unsupported
(concatenate 'string "ab" "cd")
;@ unsupported
(string-upcase "abc")
;@ unsupported
(string-downcase "ABC")
;@ unsupported
(string< "abc" "abd")
;@ unsupported
(symbol-name 'foo)
;@ unsupported
(symbol-package-name 'foo)
