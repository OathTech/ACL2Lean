; p5-or-shape-flipped — the or-collapse bridge's DECORRELATED validation
; book (equiv-lane arc, rung 1). Wild anchor: the same ORDEREDP-ISORT /
; ORDD-INS-MID or-shape family, with the DISJUNCT-ORDER axis varied: the
; junk disjunct comes FIRST, so rewrite-if's or-shape collapse fires with
; the surviving conjunct in the ELSE position (p3 exercised the THEN
; position), and the collapsing test is an EQUAL application rather than a
; recursive-recognizer application. Function family deliberately fresh
; (dupp/rep over EQL-counting) vs qsort (orderedp/insert), p3 (ordd/ins),
; and p4 (snoc/has-e).
(in-package "ACL2")

(defun rep (n e)
  (if (zp n)
      nil
    (cons e (rep (1- n) e))))

(defun dupp (x)
  (cond ((endp x) t)
        ((endp (cdr x)) t)
        ((equal (car x) (car (cdr x))) (dupp (cdr x)))
        (t nil)))

(defthm dupp-rep-mid
  (implies (and (consp x)
                (equal (car x) e)
                (dupp x))
           (or (equal x 'junk)
               (dupp (cons e x))))
  :rule-classes nil)
