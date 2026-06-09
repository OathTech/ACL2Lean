(in-package "ACL2")

;; FEATURE: direct proof, NO induction.
;; Ground / first-order goals dispatched by simplification + evaluation only.
;; Stresses the "Goal"-clause handling in reconstruction: the whole proof
;; lives under "Goal".
;; NOTE: all theorems use :rule-classes nil. A ground equality like
;; (equal (+ 1 2 3) 6) is proved fine but is an ILLEGAL :rewrite rule (it
;; rewrites 'T to itself), so storing it FAILS and halts `ld` — leaving an empty
;; (header-only) proof log. :rule-classes nil avoids rule storage entirely.

;; Pure ground arithmetic — evaluated, no waterfall reasoning.
(defthm ground-arith
  (equal (+ 1 2 3) 6)
  :rule-classes nil)

;; A defun unfolded on a constant, then evaluated. No induction.
(defun sq (n) (* n n))

(defthm sq-of-3
  (equal (sq 3) 9)
  :rule-classes nil)

;; A non-ground but non-inductive simplification: unfold once, equal-self.
(defthm sq-rewrites
  (equal (sq n) (* n n))
  :rule-classes nil)
