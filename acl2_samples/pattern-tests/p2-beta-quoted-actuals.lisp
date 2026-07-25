(in-package "ACL2")

; PROBE/beta-site2 (S2 audit 2026-07-25, reviewer artifact site2c):
; reaches rewrite.lisp's ALL-QUOTEPS lambda fast path (site 2 of the
; four-site beta table in the pattern map) — the actual (k a) only
; becomes quoted INSIDE the rewriter (via k-is-3), so the beta happens
; at rewrite's lambda case, not rewrite-fncall's. PINS the emission gap:
; a LAMBDA-BODY inner block with NO adopting beta step, which the tree
; builder silently mis-parents onto the next chain step.

(defstub k (x) t)

(defaxiom k-is-3
  (implies (integerp a) (equal (k a) 3)))

(defun f (a)
  (let ((y (k a)))
    (if (< y 5) (+ y 1) (+ y 2))))

(defthm probe-site2
  (implies (integerp a) (equal (f a) 4))
  :rule-classes nil)
