(in-package "ACL2")

; COVERAGE/quirk backlog — :SCHEME-DROPPED retry via the *1-REVERT
; route (iteration 2; iteration 1 proved without induction and its
; flattened shape lands in the complement-fold class). This is the
; ORDEREDP-MEMB structure minimized STANDALONE: a 3-hyp implies that
; survives simplification, REVERTS at push, and inducts with the
; IMPLIES literal whole — the (consp ∧ e=car) case clause is then an
; if-tautology and should appear in :SCHEME-DROPPED.

(defun ordp (x)
  (if (consp x)
      (if (consp (cdr x))
          (and (lexorder (car x) (cadr x)) (ordp (cdr x)))
        t)
    t))

(defun memq3 (e x)
  (if (consp x)
      (if (equal e (car x)) t (memq3 e (cdr x)))
    nil))

(defthm ordp-memq3
  (implies (and (ordp x)
                (not (equal e (car x)))
                (lexorder e (car x)))
           (not (memq3 e x))))
