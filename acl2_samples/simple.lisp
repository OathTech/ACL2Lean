(in-package "ACL2")

(defun my-len (x)
  (if (consp x)
      (+ 1 (my-len (cdr x)))
    0))

(defun my-app (x y)
  (if (consp x)
      (cons (car x) (my-app (cdr x) y))
    y))

(defthm my-len-my-app
  (equal (my-len (my-app x y))
         (+ (my-len x) (my-len y))))
