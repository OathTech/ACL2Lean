(in-package "ACL2")

; PROBE/beta-hide (S2b re-audit F2, reviewer artifact probe-hide):
; HIDE inside a let body — expand-abbreviations' HIDE arm substitutes
; with sublis-var, whose cons-term folds INSIDE the hide with no
; recursion and hence no per-fold steps; after the plain-substitution
; fix the beta reduct (HIDE (BINARY-* '3 '3)) jumped to (HIDE '9) with
; nothing recorded. Pins the (:hide-normalize nil) step.
; emission records the PLAIN substitution.  Chain coherence?
; h must stay OPAQUE (the probe needs (h ...) unopened) but must NOT be a
; defstub: defstub's LOCAL witness would enter the World and every mirror
; would be about the witness (BUG-019 — this book's original 2/2 green was
; exactly that). A DISABLED real defun is opaque to the rewriter and
; honestly in the world.
(defun h (x) (cons x x))
(in-theory (disable h (:executable-counterpart h)))
(defthm probe-hide
  (equal (h (let ((y 3)) (hide (* y y)))) (h (hide 9)))
  :rule-classes nil)
