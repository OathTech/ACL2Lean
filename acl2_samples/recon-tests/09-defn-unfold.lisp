(in-package "ACL2")
;; FEATURE: non-inductive definition unfold then close. The driver target for the
;; def-unfold rune (real ACL2 tree, no induction). :rule-classes nil so the trivial
;; equalities aren't rejected at rule storage.
(defun sq (n) (* n n))
(defthm sq-rewrites (equal (sq n) (* n n)) :rule-classes nil)
(defun idf (x) x)
(defthm idf-rewrites (equal (idf x) x) :rule-classes nil)
