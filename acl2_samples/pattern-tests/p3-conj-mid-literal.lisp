; (certify-book "p3-conj-mid-literal")
(in-package "ACL2")

; The ORDEREDP-ISORT wild anchor, literal-POSITION axis varied: the
; AND-shape-splitting literal must sit MID-clause (a junk disjunct after
; it) so the conjunction composer's CONTINUATION arm is exercised.
(defun ordd (x)
  (cond ((endp x) t)
        ((endp (cdr x)) t)
        ((lexorder (car x) (car (cdr x))) (ordd (cdr x)))
        (t nil)))

(defun ins (e x)
  (cond ((endp x) (cons e x))
        ((lexorder e (car x)) (cons e x))
        (t (cons (car x) (ins e (cdr x))))))

(defthm ordd-ins-mid
  (implies (and (consp it)
                (not (lexorder x1 (car it)))
                (ordd (cdr it))
                (ordd it))
           (or (ordd (ins x1 it))
               (equal it 'junk)))
  :rule-classes nil)
