(in-package "ACL2")

; COVERAGE/:by hint (hints — UNCOVERED): a theorem discharged :by an
; earlier one (instance subsumption). Pins the :by event shape.

(defthm app-assoc-orig
  (equal (append (append x y) z) (append x (append y z))))

(defthm app-assoc-again
  (equal (append (append a b) c) (append a (append b c)))
  :hints (("Goal" :by app-assoc-orig)))
