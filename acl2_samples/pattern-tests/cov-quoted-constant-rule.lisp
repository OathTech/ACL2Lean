(in-package "ACL2")

; COVERAGE/:rewrite-quoted-constant (gap audit A3 — one of the two
; rule-class tokens missing from the frame; defthm.lisp:11232). Form-2
; shape: a normalizer over quoted constants.

(defun qnorm (x)
  (if (integerp x) x 0))

(defthm qnorm-idempotent
  (equal (qnorm (qnorm x)) (qnorm x)))

(defthm qnorm-norms
  (equal (qnorm x) (if (integerp x) x 0))
  :rule-classes :rewrite-quoted-constant)
