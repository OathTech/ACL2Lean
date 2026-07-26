(in-package "ACL2")

; PROBE/beta-hide (S2b re-audit F2, reviewer artifact probe-hide):
; HIDE inside a let body — expand-abbreviations' HIDE arm substitutes
; with sublis-var, whose cons-term folds INSIDE the hide with no
; recursion and hence no per-fold steps; after the plain-substitution
; fix the beta reduct (HIDE (BINARY-* '3 '3)) jumped to (HIDE '9) with
; nothing recorded. Pins the (:hide-normalize nil) step.
; emission records the PLAIN substitution.  Chain coherence?
(defstub h (x) t)
(defthm probe-hide
  (equal (h (let ((y 3)) (hide (* y y)))) (h (hide 9)))
  :rule-classes nil)
