(in-package "ACL2")

; COVERAGE/:type-set-inverter (rule classes). S1 CORRECTION iteration 3
; (2026-07-23): :TYPE-SET 3 is *ts-zero*|*ts-one* = {0,1} in this
; ACL2's encoding (the unsuppressed error names the required standard
; expression), predicate on the LEFT. Iterations 1-2 were rejected
; with the errors inhibited — iteration 2's failure is the first
; (:EVENT-FAILED ...) the new emitter recorded.

(defun my-bitp (x)
  (or (equal x 0) (equal x 1)))

(defthm my-bitp-inverts
  (equal (my-bitp x)
         (or (equal x 0) (equal x 1)))
  :rule-classes ((:type-set-inverter :type-set 3)))
