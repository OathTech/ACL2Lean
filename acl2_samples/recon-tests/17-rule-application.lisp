(in-package "ACL2")

;; FEATURE: theorem-dependency (rule:<thm>) — a proof citing a PREVIOUSLY
;; proven theorem as a :REWRITE rule (with-lemma application), the minimal
;; exemplar of docs/plans/2026-07-05_theorem-dependency-hypotheses.md
;; independent of the big sorting/perm book. Exercises: the (:RULES …)
;; stored-rule emission, the emitted :SUBST instantiation, and CONDITIONAL
;; rule application with the hyp relieved silently from the clause context
;; (a :HYP-RELIEF marker, no rewrite chain).

;; true-listp, structurally (avoid the built-in to keep the world small).
(defun tlp (x)
  (if (consp x) (tlp (cdr x)) (equal x nil)))

;; append, locally.
(defun app (x y)
  (if (consp x) (cons (car x) (app (cdr x) y)) y))

;; The DEPENDENCY: proven by induction, stored as a conditional rewrite rule
;; (hyp (tlp x), lhs (app x nil), rhs x — implies-flattened).
(defthm tlp-app-nil
  (implies (tlp x) (equal (app x nil) x)))

;; The CITING theorem: no induction of its own — the proof rewrites with the
;; stored TLP-APP-NIL rule (twice: the inner redex, then the outer), each
;; application's hyp (tlp x) relieved from the clause's own (not (tlp x))
;; literal via the type-alist.
(defthm tlp-app-nil-twice
  (implies (tlp x) (equal (app (app x nil) nil) x))
  :rule-classes nil)
