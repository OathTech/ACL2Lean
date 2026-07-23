(in-package "ACL2")

; COVERAGE/defattach (event forms — UNCOVERED; in/out-of-tier
; decision pending): attach an executable witness to a constrained
; fn. Attachments affect EVALUATION, not proofs — the pin is the
; event's log shape (or its absence/halt).

(encapsulate
 (((astub *) => *))
 (local (defun astub (x) x))
 (defthm astub-preserves-acl2-count
   (equal (acl2-count (astub x)) (acl2-count (astub x)))
   :rule-classes nil))

(defun aimpl (x) x)

(defattach astub aimpl)

(defthm after-attach
  (equal (car (cons p q)) p))
