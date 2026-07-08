; Differential corpus: TARGET SURFACE — bitwise ops and string/char primitives,
; not modeled yet (all `stuck`).
;
; NOTE: several bitwise ops already HAVE a Logic.* definition (intLogand,
; intLogor, intLogxor, lognot, ash) but are not wired into callBuiltin — so
; wiring is a one-line callBuiltin arm each, and this differential will confirm
; the existing def matches ACL2 the moment it is wired. The string/char ops are
; needed by lexorder's alphorder over strings and characters.

; bitwise
;@ stuck
(logand '12 '10)
;@ stuck
(logior '12 '10)
;@ stuck
(logxor '12 '10)
;@ stuck
(lognot '5)
;@ stuck
(ash '1 '4)

; string / char
;@ stuck
(char-code #\a)
;@ stuck
(string-append "ab" "cd")
;@ stuck
(length "abc")
;@ stuck
(coerce "ab" 'list)
