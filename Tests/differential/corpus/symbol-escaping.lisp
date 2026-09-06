;@isolate
; Mixed and qualified CL token escapes (BUG-010).
; Only unescaped runs are uppercased; unescaped colons mark package syntax.
; FLOOR's actual snapshot contains ACL2::|(CAR REMAINDER)|.

; interior escaped run
;@ match
(equal 'a|B|c 'ABC)
; backslash single-char escape
;@ match
(equal 'foo\Bar 'FOOBAR)
; leading escaped run then bare chars
;@ match
(equal '|ABC|xyz 'ABCXYZ)

; qualified escaped name with delimiters, as encountered in FLOOR
;@ match
(equal 'ACL2::|(CAR REMAINDER)| '|(CAR REMAINDER)|)
; lowercase run is preserved (compare a boolean, not normalized output case)
;@ match
(equal 'a|b|c '|AbC|)
; single escape outside and inside multiple escapes
;@ match
(equal 'foo\bar '|FOObAR|)
;@ match
(equal '|A\|B\\C| 'A\|B\\C)
; escaped colon is name data, including after a package marker
;@ match
(equal 'a\:b '|A:B|)
;@ match
(equal 'ACL2::a|:|b '|A:B|)
; escapes in the package component
;@ match
(equal 'a|CL|2::n|I|l nil)
; canonical NIL/T and keyword representations
;@ match
(equal '|NIL| nil)
;@ match
(equal '|nil| nil)
;@ match
(equal :a|b|c :|AbC|)
;@ match
(equal 'KEYWORD::|abc| :|abc|)
; an escape forces numeric-looking syntax to be a symbol
;@ match
(equal '|1/0| '1\/0)
;@ match
(equal '1|| '|1|)
; explicitly empty symbol names
;@ match
(equal 'ACL2::|| '||)
;@ match
(equal :|| 'KEYWORD::||)
; package-only escapes must not license a missing name
;@ refuse
(equal '|ACL2|:: 'x)
;@ refuse
(equal 'ACL2:::X 'x)
;@ refuse
(equal : 'x)
; malformed escapes (isolated so a reader error cannot consume another test)
;@ refuse
(equal 'a|unterminated 'x)
;@ refuse
(equal 'abc\

; a lowercase escape differs from the ordinary uppercase symbol
;@ match
(equal 'a|b|c 'ABC)
; escaped numeric tokens are not numbers
;@ match
(equal '1|| 1)
