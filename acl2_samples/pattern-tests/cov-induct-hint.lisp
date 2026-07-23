(in-package "ACL2")

; COVERAGE/:induct hint with an EXPLICIT foreign scheme (gap audit B —
; the frame's ":induct recon-05?" uncertainty gets a dedicated book):
; induct on cd's scheme to prove a cd2 fact.

(defun cd (x) (if (consp x) (cd (cdr x)) nil))
(defun cd2 (x) (if (consp x) (cd2 (cdr x)) 0))

(defthm cd2-zero
  (equal (cd2 x) 0)
  :hints (("Goal" :induct (cd x))))
