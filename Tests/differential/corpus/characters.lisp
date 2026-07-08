; Differential corpus: CHARACTERS. ACL2 has a character type (#\a etc., codes
; 0–255). This was BUG-001 (no character Atom, so #\a parsed as a symbol);
; FIXED 2026-07-08 by adding Atom.char (UInt8) + faithful parser/printer +
; characterp/char-code/code-char. A character is now a distinct, self-equal
; object that is not a symbol/string/number, matching ACL2.

; Was the BUG-001 divergences (distinct chars compared equal; char was a
; symbol) — now correct.
;@ match
(equal #\a #\b)
;@ match
(symbolp #\a)

; a char is an atom, not a cons/number/string; self-equal; distinct from the
; like-named symbol and string
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
; chars coerce to 0 in arithmetic (fix semantics)
;@ match
(binary-+ #\a '1)
;@ match
(binary-+ #\a #\b)

; character primitives — now modeled (characterp / char-code / code-char),
; incl. the completion corners (char-code of a non-char = 0; code-char out of
; [0,256) = the null char). char-code / code-char are mutual inverses on 0–255.
;@ match
(characterp #\a)
;@ match
(characterp 'a)
;@ match
(char-code #\A)
;@ match
(char-code #\0)
;@ match
(char-code 'a)
;@ match
(code-char '65)
;@ match
(code-char '32)
;@ match
(code-char '256)
;@ match
(char-code (code-char '97))

; TARGET SURFACE — character operations still not modeled
;@ unsupported
(char-upcase #\a)
;@ unsupported
(char-downcase #\A)
;@ unsupported
(char<= #\a #\b)
