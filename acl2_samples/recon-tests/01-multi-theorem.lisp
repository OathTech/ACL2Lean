(in-package "ACL2")

;; FEATURE: several theorems in ONE file.
;; Confirms reconstruction separates theorems (each defthm closes the prior
;; one) and that the dump renders each independently. Mix of inductive and
;; non-inductive so the boundary handling is exercised.

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun len2 (x)
  (if (consp x)
      (+ 1 (len2 (cdr x)))
    0))

;; (1) non-inductive: rewrites by definition of app on a cons literal.
(defthm app-cons-car
  (equal (car (app (cons a b) y)) a))

;; (2) inductive: append a nil onto a true-list is identity.
(defthm app-nil
  (implies (true-listp x)
           (equal (app x nil) x)))

;; (3) inductive: length distributes over append (same shape as my-len-my-app).
(defthm len2-app
  (equal (len2 (app x y))
         (+ (len2 x) (len2 y))))
