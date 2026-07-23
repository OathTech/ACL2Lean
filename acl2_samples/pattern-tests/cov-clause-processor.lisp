(in-package "ACL2")

; COVERAGE/:clause-processor (rule classes — UNCOVERED): a verified
; identity clause-processor + a theorem using it via a :clause-processor
; hint. Pins the correctness obligation and the hint's log shape.

(defevaluator cpev cpev-lst
  ((if x y z) (not x)))

(defun id-cp (cl) (list cl))

(defthm id-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (cpev (conjoin-clauses (id-cp cl)) a))
           (cpev (disjoin cl) a))
  :rule-classes :clause-processor)

(defthm use-id-cp
  (equal (car (cons u v)) u)
  :hints (("Goal" :clause-processor (id-cp clause))))
