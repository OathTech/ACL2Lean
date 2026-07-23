(in-package "ACL2")

; COVERAGE/LET-lambda (gap audit A1 — the map's biggest blind spot:
; ZERO let/mv usage in the whole sample tree, yet let is the commonest
; binding construct and translates to ((LAMBDA ...) actuals)). Should
; reproduce the LAMBDA-frame parse frontier standalone, decoupled from
; defevaluator.

(defun fsq (x)
  (let ((y (+ x 1)))
    (* y y)))

(defthm fsq-unfolds
  (equal (fsq a) (* (+ a 1) (+ a 1))))
