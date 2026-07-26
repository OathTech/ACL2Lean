(in-package "ACL2")

; PROBE/beta-preprocess (S2 audit 2026-07-25, reviewer artifact site2b):
; preprocess expand-abbreviations beta-reduces the lambda (site 3 —
; ground actual / abbreviation body; induct.lisp 317-441) with NO
; emission at all, not even BEGIN/END markers: the log shows the
; abbreviation-expansion to the lambda application and the const-folds,
; with the beta step absent in between.

; h must stay OPAQUE (the probe needs (h ...) unopened) but must NOT be a
; defstub: defstub's LOCAL witness would enter the World and every mirror
; would be about the witness (BUG-019 — this book's original 2/2 green was
; exactly that). A DISABLED real defun is opaque to the rewriter and
; honestly in the world.
(defun h (x) (cons x x))
(in-theory (disable h (:executable-counterpart h)))

(defthm site2-probe-a
  (equal (h (let ((y (+ 1 2))) (* y y))) (h 9))
  :rule-classes nil)

(defun g (n) (let ((y (+ n 1))) (* y y)))

(in-theory (disable (:executable-counterpart g)))

(defthm site2-probe-b
  (equal (h (g 2)) (h 9))
  :rule-classes nil)
