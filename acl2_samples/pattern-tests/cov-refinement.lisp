(in-package "ACL2")

; COVERAGE/:refinement (rule classes — UNCOVERED): an equivalence that
; REFINES equal. Pins the defrefinement obligation's emitted shape.

(defun same-thing (x y) (equal x y))

(defequiv same-thing)

(defrefinement same-thing equal)
