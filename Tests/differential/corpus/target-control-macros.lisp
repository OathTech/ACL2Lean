; Differential corpus: TARGET SURFACE — ACL2 control/binding MACROS and forms
; not modeled by evalOpt's special-form set. These are pervasive in real books
; (cond/case especially). In the REPLAY path they arrive macroexpanded to `if`,
; so this is a stream-interpreter (masquerade) gap, not a replay gap — but a
; faithful interpreter must handle them as written. Values pinned from ACL2.

; conditionals
;@ unsupported
(cond ('nil '1) ('t '2))
;@ unsupported
(cond ('nil '1))
;@ unsupported
(case '2 (1 'a) (2 'b) (t 'c))
; NOTE: (when …)/(unless …) are NOT here — ACL2 refuses them at top level
; (they are refuse-class, both interpreters decline); see boundary.lisp.

; sequencing / typing / exec-control (logical value is what a model computes)
;@ unsupported
(prog2$ '1 '2)
;@ unsupported
(the integer '5)
;@ unsupported
(ec-call (car '(1 2)))
;@ unsupported
(mbe :logic '1 :exec '2)

; multiple values
;@ unsupported
(mv '1 '2)
;@ unsupported
(mv-let (a b) (mv '1 '2) (cons a b))

; n-ary arithmetic MACROS: + * < expand to the binary-* / binary-+ / if forms.
; Only the binary-* primitives are modeled; the n-ary surface macros are not.
;@ unsupported
(+ '1 '2 '3)
;@ unsupported
(+ '1)
;@ unsupported
(* '2 '3 '4)

; boolean MACROS and / or (expand to if; value is the last / first-true operand)
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
