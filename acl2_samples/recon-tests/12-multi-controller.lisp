(in-package "ACL2")

;; FEATURE: simultaneous recursion on TWO arguments → the induction has multiple
;; CONTROLLERS (x and y) and the step IH substitutes BOTH (x:=(cdr x), y:=(cdr y)).
;; Exercises :CONTROLLERS with >1 var and a multi-variable IH substitution alist.
;; The property is a length bound (not a type fact), forcing induction on zip2.

(defun zip2 (x y)
  (if (or (atom x) (atom y))
      nil
    (cons (cons (car x) (car y))
          (zip2 (cdr x) (cdr y)))))

;; inducts on zip2's scheme: controllers (x y); step IH x:=(cdr x), y:=(cdr y).
(defthm len-zip2
  (<= (len (zip2 x y)) (len x))
  :rule-classes nil)
