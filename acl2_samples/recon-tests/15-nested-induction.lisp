(in-package "ACL2")

;; FEATURE: TWO inductions inside ONE theorem — a nested/sequential induction with
;; a synthesized *1.k pool-root.  Proving a conjunction whose conjuncts need
;; DIFFERENT recursion schemes makes ACL2 induct on the first (app, on x), then —
;; inside a subgoal where the first conjunct is discharged — induct AGAIN on the
;; second (dup, on z), giving a pool root like *1.1 nested under *1/2''.  Exercises
;; the proof-tree reconstruction's push->induct adjacency for a SECOND induction
;; (every prior recon-test has exactly one induction per theorem).

(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))

(defun dup (x) (if (consp x) (cons (car x) (cons (car x) (dup (cdr x)))) nil))

;; conjunction: conjunct 1 inducts on app's scheme (x); conjunct 2 on dup's (z).
(defthm nested-induction
  (and (equal (len (app x y)) (+ (len x) (len y)))
       (equal (len (dup z)) (+ (len z) (len z))))
  :rule-classes nil)
