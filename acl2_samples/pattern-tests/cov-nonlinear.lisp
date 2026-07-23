(in-package "ACL2")

; COVERAGE/nonlinear arithmetic (gap audit A5): :nonlinearp t — the
; nonlinear extension of the linear pot list, a distinct mechanism
; from cov-linear-pot's.

(defthm square-nonneg-nl
  (implies (rationalp x) (<= 0 (* x x)))
  :hints (("Goal" :nonlinearp t)))
