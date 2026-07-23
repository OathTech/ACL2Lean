(in-package "ACL2")

; COVERAGE/user-geneqv consumption (rewriter situations — UNCOVERED;
; quirk backlog "congruence-consumption"): a rewrite rule stated under
; a user equivalence, applied INSIDE a congruence-blessed context —
; geneqv = same-len2 at the argument of len. Pins the user-geneqv
; rewriting shape (the L2 lane's core situation).
;
; Probe finding (2026-07-22, first version): a HYP-FREE version of
; cons-norm-same-len2 loops ACL2's PREPROCESSOR (call-depth hard
; error) — preprocess classes it as a "simple" abbreviation rule and
; ignores loop-stoppers. The syntaxp guard below both stops the loop
; and routes the rule through the full rewriter.

(defun same-len2 (x y) (equal (len x) (len y)))

(defequiv same-len2)

(defcong same-len2 equal (len x) 1)

(defthm cons-norm-same-len2
  (implies (syntaxp (not (quotep a)))
           (same-len2 (cons a x) (cons 0 x))))

(defthm len-cons-under-cong
  (equal (len (cons a x)) (len (cons 0 x)))
  :rule-classes nil)
