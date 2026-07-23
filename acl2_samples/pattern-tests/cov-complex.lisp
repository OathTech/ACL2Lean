(in-package "ACL2")

; COVERAGE/complex numbers (value surface). S1 CORRECTION (2026-07-23):
; the original "capture halt" was ACL2 REJECTING the ground equalities
; as rewrite rules ('T rewrites to itself) with the error INHIBITED by
; structured mode — not an instrumentation limit. :rule-classes nil
; fixes the events; this book now pins how #c literals flow through
; capture/parse in formulas and proofs.

(defthm complex-add
  (equal (+ #c(1 2) #c(3 4)) #c(4 6))
  :rule-classes nil)

(defthm complex-parts
  (and (equal (realpart #c(5 7)) 5)
       (equal (imagpart #c(5 7)) 7))
  :rule-classes nil)
