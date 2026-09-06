; BUG-042's wild anchor is arithmetic-3/pass1/basic-arithmetic-helper:
; FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT substitutes (* X Y) and
; (* X (- Y)) into a named theorem. Exercise those same source macros
; in a small proof whose only consumer step is the recorded USE instance.
(in-package "ACL2")

(defthm ns1-use-head
  (equal (car (cons x y)) x)
  :rule-classes nil)

(defthm ns1-use-macro-product
  (equal (car (cons (* x (- y)) z)) (* x (- y)))
  :hints (("Goal"
           :use ((:instance ns1-use-head (x (* x (- y))) (y z)))
           :in-theory nil)))
