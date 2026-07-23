(in-package "ACL2")

; COVERAGE/:meta (rule classes — UNCOVERED): a defevaluator + a
; (trivial, identity) metafunction admitted as a :meta rule, then a
; theorem whose rewriting passes through the trigger fn. Pins the
; emitted shape of defevaluator's generated events, the :meta
; correctness obligation, and metafunction application (if any) in
; the log.

(defevaluator mev mev-lst
  ((binary-+ x y) (fix x)))

(defun keep-term (term) term)

(defthm keep-term-meta
  (equal (mev term a) (mev (keep-term term) a))
  :rule-classes ((:meta :trigger-fns (binary-+))))

(defthm plus-fix
  (equal (+ 0 (fix x)) (fix x)))
