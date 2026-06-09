(in-package "ACL2")

;; FEATURE: THREE-way simultaneous recursion → a 3-element IH-substitution alist
;; (x:=(cdr x), y:=(cdr y), z:=(cdr z)) and a 3-disjunct governing test.  Extends
;; 12-multi-controller (2-way) / 13-multi-measured-var (2-way) to confirm the
;; multi-variable IH alist and case-test reconstruction scale past two variables.

(defun zip3 (x y z)
  (if (or (atom x) (atom y) (atom z))
      nil
    (cons (list (car x) (car y) (car z))
          (zip3 (cdr x) (cdr y) (cdr z)))))

;; length bound forces induction on zip3's scheme (step IH on all three vars).
(defthm len-zip3
  (<= (len (zip3 x y z)) (len x))
  :rule-classes nil)
