; p5-or-shape-flipped — an IFF-LANE validation book (equiv-lane arc,
; rung 1). Wild anchor: the ORDEREDP-ISORT / ORDD-INS-MID or-shape family
; with the DISJUNCT-ORDER axis varied (the junk disjunct FIRST).
; OBSERVED BEHAVIOR (pre-merge audit correction, 2026-07-30): the
; or-collapse does NOT fire here — type-set kills the leading test
; ((EQUAL X 'JUNK) => 'NIL via EQUAL/TYPE-SET-NIL), so rewrite-if takes
; the CONSTANT-TEST path and the or survives clausify intact as one
; literal; there are ZERO IF-FINISH/COMBINED records. What the book DOES
; validate, 1/1 unconditional: the iff preprocess lane (PREPROCESS/IF-IFF
; + an FNCALL/ABBREVIATION step under :EQUIV IFF) on a fresh function
; family (dupp/rep) — NOT the or-collapse bridge.
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
