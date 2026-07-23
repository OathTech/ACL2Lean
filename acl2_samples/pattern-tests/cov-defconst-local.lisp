(in-package "ACL2")

; COVERAGE/defconst + local (event forms — UNCOVERED): a defconst
; consumed by a theorem, and a LOCAL helper event. Pins both event
; forms' log shapes.

(defconst *k* 42)

(local (defthm local-helper
  (equal (+ *k* 0) *k*)
  :rule-classes nil))

(defthm k-fixed
  (equal (* *k* 1) 42))
