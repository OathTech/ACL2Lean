(in-package "ACL2")

; COVERAGE/quirk backlog — minimal :SCHEME-DROPPED trigger (the
; ORDEREDP-MEMB merged-base-case shape, minimized): an induction whose
; (consp ∧ e=car) case clause is a propositional tautology via the
; concl's (not (equal e (car x))) hypothesis — remove-trivial-clauses
; deletes it; the fork emits it in :SCHEME-DROPPED.

(defun memq2 (e x)
  (if (consp x)
      (if (equal e (car x)) t (memq2 e (cdr x)))
    nil))

(defthm memq2-skip
  (implies (and (not (equal e (car x))) (memq2 e x))
           (memq2 e (cdr x))))
