(in-package "ACL2")

; COVERAGE/reader literals (value surface). S1 CORRECTION (2026-07-23):
; the "halt" was the illegal-ground-rewrite-rule failure, hidden by
; structured-mode error inhibition. :rule-classes nil throughout.

(defthm neg-ratio
  (equal (+ -1/2 1/2) 0)
  :rule-classes nil)

(defthm hex-lit
  (equal #x10 16)
  :rule-classes nil)

(defthm bin-lit
  (equal #b101 5)
  :rule-classes nil)

(defthm oct-lit
  (equal #o17 15)
  :rule-classes nil)
