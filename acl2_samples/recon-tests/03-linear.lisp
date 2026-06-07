(in-package "ACL2")

;; FEATURE: linear arithmetic + type reasoning.
;; These proofs lean on the linear-arithmetic and type-set processors rather
;; than the rewriter, so they probe whether reconstruction captures (or
;; silently drops) non-rewriter waterfall steps.

(defun len2 (x)
  (if (consp x)
      (+ 1 (len2 (cdr x)))
    0))

;; (1) length is non-negative — type-prescription / linear.
(defthm len2-nonneg
  (<= 0 (len2 x)))

;; (2) length of a cdr is strictly smaller — linear arithmetic over the IH.
(defthm len2-cdr-smaller
  (implies (consp x)
           (< (len2 (cdr x)) (len2 x))))

;; (3) a pure linear-arithmetic goal with no functions at all.
(defthm linear-chain
  (implies (and (<= a b) (<= b c) (integerp a) (integerp b) (integerp c))
           (<= a c)))
