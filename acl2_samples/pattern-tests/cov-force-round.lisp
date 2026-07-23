(in-package "ACL2")

; COVERAGE/forcing ROUND (rewriter situations): iteration 2. The first
; version's forced rule was defeated by g2's own :TYPE-PRESCRIPTION
; ((EQUAL (G2 X) '0) — type-set closed the goal with no rule
; application at all; probe finding catalogued). Here the conclusion
; value (CONS '0 X) is not TP-derivable, the definition is disabled,
; and the forced hyp needs INDUCTION — unrelievable at use time,
; provable in the round.

(defun tlp2 (x) (if (consp x) (tlp2 (cdr x)) (equal x nil)))

(defun app2 (x y) (if (consp x) (cons (car x) (app2 (cdr x) y)) y))

(defun g2 (x) (cons 0 x))

(defthm g2-rule
  (implies (force (tlp2 x)) (equal (g2 x) (cons 0 x))))

(in-theory (disable g2))

(defthm g2-app2
  (implies (tlp2 b) (equal (g2 (app2 a b)) (cons 0 (app2 a b)))))
