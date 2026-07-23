(in-package "ACL2")

; P1/joint (pattern map 2026-07-22): a (NOT (EQUAL ...)) test INSIDE a
; defun body — its NOT unfold makes the enclosing if's test
; negation-shaped between the recorded children and the recorded rhs,
; so ACL2 swaps at the if-finish JOINT (the normalizeSwapsToward case).
; Anchor: ORDEREDP-MEMB (ordered-perms).

(defun cntne (e x)
  (if (atom x)
      0
    (if (not (equal e (car x)))
        (cntne e (cdr x))
      (+ 1 (cntne e (cdr x))))))

(defthm cntne-cons
  (equal (cntne e (cons a x))
         (if (equal e a)
             (+ 1 (cntne e x))
           (cntne e x))))
