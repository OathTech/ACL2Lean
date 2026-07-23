(in-package "ACL2")

; COVERAGE/defconst + local (event forms). S1 CORRECTION (2026-07-23):
; the "session halt after the local event" was K-FIXED's ground
; equality being rejected as a rewrite rule, error inhibited. Top-level
; LOCAL is fine (logs with :SOURCE :LOCAL).

(defconst *k* 42)

(local (defthm local-helper
  (equal (+ *k* 0) *k*)
  :rule-classes nil))

(defthm k-fixed
  (equal (* *k* 1) 42)
  :rule-classes nil)
