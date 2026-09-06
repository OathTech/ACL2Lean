; Ordinary imported definition under an outer LOCAL, as in BVCHOP's
; local arithmetic includes. It is not a constrained-function witness.
(in-package "ACL2")
(local (include-book "cov-local-include-helper"))
(defthm ns1-local-include-result
  (equal (car (ns1-included-fn x)) x))
