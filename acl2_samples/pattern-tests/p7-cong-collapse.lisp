; p7-cong-collapse — rung 2's DECORRELATED validation book (perm-lane arc,
; G2). Wild anchor: books/sorting/qsort.lisp's ORDEREDP-QSORT — a theorem
; whose preprocess applies a hyp-free rewrite rule stored under a USER
; equivalence (:EQUIV PERM, PERM-QSORT) at a defcong-licensed argument
; position (ALL-REL arg 2), collapsing to an eval-equality of the parent
; applications. Axes drawn from the anchor, all varied: (1) the relation —
; SAME-LN (length equivalence) instead of PERM; (2) the function family —
; ln/dub instead of qsort/all-rel/rm; (3) the congruence position — an
; ARITY-1 fn's arg 1 instead of an arity-3 fn's arg 2; (4) the defcong
; formula is the TRIVIAL instance (hyp = conclusion), so the license's
; consumption is isolated from any auxiliary lemma. The equivalence and
; congruence proofs need no induction; SAME-LN-DUB is the book's one
; inductive theorem (the PERM-QSORT analogue, hyp-free — the abbreviation
; class).
(in-package "ACL2")

(defun ln (x)
  (if (endp x)
      0
    (+ 1 (ln (cdr x)))))

(defun same-ln (x y)
  (equal (ln x) (ln y)))

(defthm same-ln-is-an-equivalence
  (and (booleanp (same-ln x y))
       (same-ln x x)
       (implies (same-ln x y) (same-ln y x))
       (implies (and (same-ln x y) (same-ln y z))
                (same-ln x z)))
  :rule-classes :equivalence)

(defcong same-ln equal (ln x) 1)

(defun dub (x)
  (if (endp x)
      nil
    (cons 0 (dub (cdr x)))))

(defthm same-ln-dub
  (same-ln (dub x) x))

(defthm p7-target
  (equal (ln (dub x)) (ln x)))
