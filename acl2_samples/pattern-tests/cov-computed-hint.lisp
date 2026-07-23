(in-package "ACL2")

; COVERAGE/computed hints (hints — UNCOVERED): a computed hint (a form
; evaluating to a hint keyword list). Pins how computed-hint firing
; appears in the log.

(defun szc (x)
  (if (consp x) (+ 1 (szc (cdr x))) 0))

(defthm szc-cons
  (equal (szc (cons a x)) (+ 1 (szc x)))
  :hints ((if stable-under-simplificationp
              '(:expand ((szc (cons a x))))
            nil)))
