(in-package "ACL2")

;; FEATURE: binary-tree recursion → an induction STEP case with TWO induction
;; hypotheses (one per recursive call, on (car x) and (cdr x)).  Exercises the
;; measure emission's multi-IH-per-case path: :CASES should show one step case
;; with two :ALISTS (x:=(car x) and x:=(cdr x)).

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun flatten (x)
  (if (consp x)
      (app (flatten (car x)) (flatten (cdr x)))
    (cons x nil)))

;; consumed (as a :rewrite rule) by the flatten proof
(defthm true-listp-app
  (implies (true-listp y)
           (true-listp (app x y))))

;; inducts on flatten's scheme: step case (consp x) with IHs on (car x) AND (cdr x).
(defthm true-listp-flatten
  (true-listp (flatten x))
  :rule-classes nil)
