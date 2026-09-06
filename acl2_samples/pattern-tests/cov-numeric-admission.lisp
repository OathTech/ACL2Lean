(in-package "ACL2")

; Real definitions whose convergence needs the ground-zero arithmetic chain:
; FLOOR's translated LETs call the recursive quotient; MOD calls FLOOR.
(defun numeric-floor (x y) (floor x y))
(defthm numeric-floor-opener
  (equal (numeric-floor x y) (floor x y)))

(defun numeric-mod (x y) (mod x y))
(defthm numeric-mod-opener
  (equal (numeric-mod x y) (mod x y)))
