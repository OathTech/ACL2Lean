(in-package "ACL2")

;; FEATURE: an induction scheme with MORE THAN TWO cases / a step that peels
;; two constructors at once (recursion on (cddr x)). The induction has a base
;; case, a one-element near-base case, and a two-element step, so the dump's
;; "induction scheme (each case is a clause)" rendering is exercised with >2
;; subgoals.

(defun evenlen (x)
  (if (consp x)
      (if (consp (cdr x))
          (evenlen (cddr x))
        nil)
    t))

;; evenlen always returns a Boolean — proved by the cddr induction.
(defthm evenlen-booleanp
  (booleanp (evenlen x)))

;; A nested case split inside one clause: three-way classification.
(defun classify (n)
  (cond ((not (integerp n)) 'not-int)
        ((< n 0) 'neg)
        ((equal n 0) 'zero)
        (t 'pos)))

(defthm classify-pos
  (implies (and (integerp n) (< 0 n))
           (equal (classify n) 'pos)))
