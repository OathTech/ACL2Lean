; Differential corpus: the remaining ACL2 AXIOMATIC PRIMITIVES not modeled by
; evalOpt (all `unsupported`) — complex numbers and package/symbol primitives.
; These complete the enumeration of ACL2's *primitive-formals-and-guards*
; (basis-b.lisp) in the corpus: exotic but part of the axiomatic core, so pinned
; here as a coverage record. Values are ACL2's; the completion values (a
; primitive on an out-of-domain arg) are pinned too.

; complex numbers (complex/complex-rationalp/realpart/imagpart). Note ACL2
; normalizes a zero-imaginary complex to the real: (complex 1 0) = 1.
;@ unsupported
(complex '1 '2)
;@ unsupported
(complex '1 '0)
;@ unsupported
(complex-rationalp (complex '1 '2))
;@ unsupported
(complex-rationalp '5)
;@ unsupported
(realpart (complex '3 '4))
;@ unsupported
(imagpart (complex '3 '4))
;@ unsupported
(< (complex '1 '2) (complex '1 '3))
; completion values on out-of-domain args (realpart/imagpart of non-number = 0)
;@ unsupported
(realpart 'abc)
;@ unsupported
(imagpart 'abc)
;@ unsupported
(denominator 'abc)
;@ unsupported
(numerator 'abc)

; package / symbol primitives. symbol-package-name of a Common-Lisp symbol is
; "COMMON-LISP", not "ACL2" — a subtlety worth pinning.
;@ unsupported
(intern-in-package-of-symbol "CAR" 'foo)
;@ unsupported
(pkg-witness "ACL2")
;@ unsupported
(symbol-package-name 'foo)
;@ unsupported
(symbol-package-name 'car)
;@ unsupported
(symbol-name '5)
;@ unsupported
(char-code 'abc)
;@ unsupported
(code-char '256)
;@ unsupported
(intern-in-package-of-symbol "NIL" 'foo)

; bad-atom<= : the total order on "bad atoms" (the axiomatic fallback in
; alphorder for non-standard atoms); on ordinary atoms it is nil.
;@ unsupported
(bad-atom<= 'a 'b)
