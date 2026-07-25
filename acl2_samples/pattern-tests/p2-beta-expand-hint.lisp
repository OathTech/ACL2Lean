(in-package "ACL2")

; PROBE/beta-expand-hint (S2b, 2026-07-25): the :expand (:lambdas) hint —
; beta site 4. The permission check in rewrite-with-lemmas PREEMPTS
; rewrite-fncall's default lambda handling, so this book's beta goes through
; the expand-hint path (origin EXPAND-HINT/LAMBDA-BODY), not site 1. The
; duplicated formal keeps preprocess from opening the lambda (fails
; abbreviationp), and the non-quoted actual keeps the all-quoted arms out.

(defun fsq3 (x)
  (let ((y (+ x 1)))
    (* y y)))

(defthm fsq3-unfolds
  (equal (fsq3 a) (* (+ a 1) (+ a 1)))
  :hints (("Goal" :expand (:lambdas)))
  :rule-classes nil)
