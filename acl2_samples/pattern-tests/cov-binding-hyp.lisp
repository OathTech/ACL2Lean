; Probe of relieve-hyp's binding-hyp-p arm, observed in Kestrel bvchop.
; Y is first bound by rewriting hypothesis 2's RHS; no hand-made trace.
(in-package "ACL2")

(defun bind-probe (x) x)

(defthm bind-probe-rule
  (implies (and (integerp x)
                (equal y (cdr (cons 0 x))))
           (equal (bind-probe x) y)))

(in-theory (disable bind-probe))

(defthm bind-probe-result
  (implies (integerp x)
           (equal (bind-probe x) x))
  :hints (("Goal" :in-theory '(bind-probe-rule car-cons cdr-cons))))
