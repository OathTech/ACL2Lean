; Differential corpus: CHARACTERS. ACL2 has a character type (#\a etc.); our
; Atom model does NOT (only symbol/keyword/string/number), so #\a is parsed as a
; symbol named "#\a". This produces real divergences, pinned here.

; KNOWN BUG: distinct characters compare EQUAL. ACL2: #\a and #\b are different
; character objects → NIL. Ours: both are symbols, and the parser collapses the
; token so they end up equal → t. (Serious: two distinct ACL2 objects identified.)
;@ known-bug bug:BUG-001 lean t
(equal #\a #\b)

; KNOWN BUG: a character is not a symbol in ACL2 → NIL; ours models #\a as a
; symbol → t.
;@ known-bug bug:BUG-001 lean t
(symbolp #\a)

; behavior that AGREES (control — a char is an atom, not a cons/number/string,
; and is self-equal / distinct from the like-named symbol and string)
;@ match
(atom #\a)
;@ match
(consp #\a)
;@ match
(stringp #\a)
;@ match
(acl2-numberp #\a)
;@ match
(equal #\a #\a)
;@ match
(equal #\a 'a)
;@ match
(equal #\a "a")
; chars coerce to 0 in arithmetic (both agree — fix semantics)
;@ match
(binary-+ #\a '1)
;@ match
(binary-+ #\a #\b)

; TARGET SURFACE — character operations not modeled
;@ unsupported
(characterp #\a)
;@ unsupported
(characterp 'a)
;@ unsupported
(char-code #\A)
;@ unsupported
(char-code #\0)
;@ unsupported
(code-char '65)
;@ unsupported
(char-upcase #\a)
;@ unsupported
(char-downcase #\A)
;@ unsupported
(char<= #\a #\b)
