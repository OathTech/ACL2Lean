(in-package "ACL2")

; COVERAGE/eliminate-irrelevance dedicated book (gap audit B — the
; frame's own "thin" admission): a hypothesis about y in a goal about
; x — judged irrelevant and dropped by the processor before induction.

(defun anyf (x) (if (consp x) (anyf (cdr x)) 0))

(defthm irrelevant-hyp
  (implies (true-listp y) (equal (anyf x) 0)))
