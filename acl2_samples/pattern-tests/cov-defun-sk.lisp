(in-package "ACL2")

; COVERAGE/defun-sk (map frame: event forms — UNCOVERED): existential
; quantification + the -suff rule via :use. Pins the emitted shape of
; defun-sk's constraint machinery and a witness instantiation.

(defun-sk exists-double (n)
  (exists m (equal n (* 2 m))))

(defthm four-has-double
  (exists-double 4)
  :hints (("Goal" :use (:instance exists-double-suff (n 4) (m 2)))))
