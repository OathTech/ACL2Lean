; Differential corpus: TARGET SURFACE — control/binding forms and equality
; variants not modeled by evalOpt's callBuiltin/special-form set yet.
;
; NOTE: `and`/`or` are ACL2 MACROS; in real proof bodies they are macroexpanded
; to `if` before the log is emitted, so the replay path never sees them. But a
; faithful stream interpreter (the masquerade goal) must handle them as written.
; Likewise a direct ((lambda …) …) application. `eq` is a function (like eql/
; equal) that is simply unmodeled. These pin what full ACL2-parity requires.

; macros: and / or (expand to if; value is the last/ first-true operand)
;@ unsupported
(and '1 '2)
;@ unsupported
(and '1 'nil)
;@ unsupported
(or 'nil '3)
;@ unsupported
(or 'nil 'nil)

; direct lambda application
;@ unsupported
((lambda (x) (binary-+ x x)) '5)

; eq (equality function — modeled cousins eql/equal ARE handled)
;@ unsupported
(eq 'a 'a)
;@ unsupported
(eq 'a 'b)
;@ unsupported
(eq '1 '1)
