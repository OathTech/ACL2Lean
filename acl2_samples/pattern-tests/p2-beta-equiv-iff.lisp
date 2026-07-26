(in-package "ACL2")

; PROBE/beta-equiv (S2b re-audit; REWRITTEN at the F1/BUG-019 fix — the
; original used defstubs + a defaxiom, and a defstub's LOCAL witness enters
; the World): a lambda application in an IF TEST, whose body rewrites via a
; genuinely-IFF rule — pins the beta step's geneqv-derived :EQUIV IFF.
; foo/bar are opaque-but-real (disabled); bar's body is boolean-valued so
; its type-prescription CANNOT resolve the test (a truthy TP would let
; type-set close the IF before any iff rewriting happens — the failure mode
; of the first rewrite of this book); bar-iff is an honest, provable IFF
; rule that fires only under an iff geneqv.

(defun foo (x) (cons x x))
(defun bar (x) (not (not x)))
(in-theory (disable foo bar
                    (:executable-counterpart foo)
                    (:executable-counterpart bar)))

(defthm bar-iff (iff (bar x) x)
  :hints (("Goal" :in-theory (enable bar))))

(defun p (a)
  (if (let ((y (foo a)))
        (if (consp y) (bar y) (bar y)))
      'yes 'no))

(defthm probe-iff
  (equal (p a) 'yes)
  :rule-classes nil)
