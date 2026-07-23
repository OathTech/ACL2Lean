(in-package "ACL2")

; COVERAGE/rewrite-cache effects (rewriter situations): iteration 2 —
; the first version's constant-valued fn was closed by its own
; :TYPE-PRESCRIPTION with no rewriting at all (probe finding — the
; third TP-defeats-probe instance; see the map's probe-craft note).
; Non-degenerate counter: does the REPEATED subterm's unfold appear
; once (cache) or per occurrence?

(defun rc2 (x) (if (consp x) (+ 1 (rc2 (cdr x))) 0))

(defthm rc2-of-cons-twice
  (equal (+ (rc2 (cons a x)) (rc2 (cons a x)))
         (+ 2 (* 2 (rc2 x)))))
