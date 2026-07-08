; Differential corpus: TARGET SURFACE — bitwise ops and string/char primitives,
; not modeled yet (all `unsupported`).
;
; NOTE: several bitwise ops already HAVE a Logic.* definition (intLogand,
; intLogor, intLogxor, lognot, ash) but are not wired into callBuiltin — so
; wiring is a one-line callBuiltin arm each, and this differential will confirm
; the existing def matches ACL2 the moment it is wired. The string/char ops are
; needed by lexorder's alphorder over strings and characters.

; bitwise
;@ unsupported
(logand '12 '10)
;@ unsupported
(logior '12 '10)
;@ unsupported
(logxor '12 '10)
;@ unsupported
(lognot '5)
;@ unsupported
(ash '1 '4)

; string / char
;@ unsupported
(char-code #\a)
;@ unsupported
(string-append "ab" "cd")
;@ unsupported
(length "abc")
;@ unsupported
(coerce "ab" 'list)
