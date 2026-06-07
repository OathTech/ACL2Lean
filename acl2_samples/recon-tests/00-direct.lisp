(in-package "ACL2")

;; FEATURE: direct proof, NO induction.
;; Ground / first-order goals dispatched by simplification + evaluation only.
;; Stresses the "Goal"-clause handling in reconstruction: the whole proof
;; lives under "Goal", which buildAllTheoremProofs currently filters out.

;; Pure ground arithmetic — evaluated, no waterfall reasoning.
(defthm ground-arith
  (equal (+ 1 2 3) 6))

;; A defun unfolded on a constant, then evaluated. No induction.
(defun sq (n) (* n n))

(defthm sq-of-3
  (equal (sq 3) 9))

;; A non-ground but non-inductive simplification: unfold once, equal-self.
(defthm sq-rewrites
  (equal (sq n) (* n n)))
