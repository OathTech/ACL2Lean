(in-package "ACL2")

; COVERAGE/:do-not and :do-not-induct hints (gap audit A2-top):
; disabling waterfall processors — proof-structure-affecting hints
; absent from every sample.

(defun fz (x) (if (consp x) (fz (cdr x)) 0))

(defthm fz-zero
  (equal (fz x) 0)
  :hints (("Goal" :do-not '(generalize fertilize))))

(defthm fz-cons
  (equal (fz (cons a x)) (fz x))
  :hints (("Goal" :do-not-induct t)))
