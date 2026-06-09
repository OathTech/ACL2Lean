(in-package "ACL2")

;; FEATURE: a measure over TWO variables — (+ (acl2-count x) (acl2-count y)) — so
;; the measured subset / :CONTROLLERS is {x, y} (both), AND the step IH SWAPS the
;; variables (x:=y, y:=(cdr x)).  Unlike 12-multi-controller (subset {x}, simple
;; cdr/cdr), here neither variable alone is a measure and the substitution is not a
;; uniform descent — exercises a compound (binary-+) measure term over a 2-element
;; subset with a non-trivial IH alist.

(defun interleave (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (atom x)
      y
    (cons (car x) (interleave y (cdr x)))))

;; (len (interleave x y)) = (len x) + (len y); forces induction on interleave's
;; scheme (step IH x:=y, y:=(cdr x); measured subset {x, y}).
(defthm len-interleave
  (equal (len (interleave x y))
         (+ (len x) (len y)))
  :rule-classes nil)
