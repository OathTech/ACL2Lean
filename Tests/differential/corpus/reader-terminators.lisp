; Differential corpus: READER TERMINATING MACRO CHARACTERS (BUG-020,
; fixed 2026-07-26). CL's terminating macro chars (" ' ` , ;) end a token;
; our isAtomChar previously terminated only on parens+whitespace, silently
; reading A'B / A"B" as single tokens — the reader's one fail-open
; divergence. Pins the fixed tokenization. (`;` cannot be pinned here — it
; comments THIS corpus format; backquote/comma are not yet modeled forms.)

;@ match
(cons 'a'b)

;@ match
(car (cons 'x'y))

;@ match
(cons 'a"b")

;@ match
(equal "x"'x)
