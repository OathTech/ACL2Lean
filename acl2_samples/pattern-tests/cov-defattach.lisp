(in-package "ACL2")

; COVERAGE/defattach (event forms). S1 CORRECTION (2026-07-23): the
; "halt at the event" was ACL2 requiring GUARD-VERIFIED attachments,
; error inhibited. With :guard t verified, the event's log shape gets
; pinned for real.

(encapsulate
 (((astub *) => *))
 (local (defun astub (x) x))
 (defthm astub-preserves-acl2-count
   (equal (acl2-count (astub x)) (acl2-count (astub x)))
   :rule-classes nil))

(defun aimpl (x)
  (declare (xargs :guard t))
  x)

(defattach astub aimpl)

(defthm after-attach
  (equal (car (cons p q)) p)
  :rule-classes nil)
