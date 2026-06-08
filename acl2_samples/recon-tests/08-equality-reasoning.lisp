;; Equality reasoning: stepping stones toward transitivity, to see what proof-tree
;; logic the driver must support next. (Generated tree inspected, not committed as a
;; trust anchor — see recon-tests/README.md.)
;;
;; NOTE: `:rule-classes nil` — these are proved as THEOREMS only, not stored as
;; :REWRITE rules. Without it, ACL2 rejects e.g. `(equal y x)` at RULE STORAGE
;; ("rewrites the variable symbol Y") and `ld` halts before proving anything — the
;; defthm fails for a form reason, unrelated to provability or our instrumentation.

;; (S3 candidate) one with-lemma rewrite (cdr-cons) then close, no hypotheses.
(defthm cdr-cons-refl (equal (cdr (cons x y)) y) :rule-classes nil)

;; one hypothesis equality used to rewrite the conclusion (solidify w/ a clause hyp).
(defthm equal-symm (implies (equal x y) (equal y x)) :rule-classes nil)

;; the transitivity target: two hypothesis equalities + conclusion.
(defthm equal-trans (implies (and (equal x y) (equal y z)) (equal x z)) :rule-classes nil)
