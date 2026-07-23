(in-package "ACL2")

; COVERAGE/:expand hint (map frame: hints — UNCOVERED): pins the
; emitted structure of a hint-directed expansion.

(defun sz2 (x)
  (if (consp x) (+ 1 (sz2 (cdr x))) 0))

(defthm sz2-singleton
  (equal (sz2 (cons a nil)) 1)
  :hints (("Goal" :expand ((sz2 (cons a nil))))))
