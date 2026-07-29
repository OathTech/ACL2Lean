; p4-iff-or-shape — the iff rung's DECORRELATED validation book (equiv-lane
; arc, G1 inc-2c). Wild anchor: books/sorting/qsort.lisp's ORDEREDP-APPEND —
; an IFF-stated defthm whose preprocess expands the IFF definition and
; normalizes under *geneqv-iff*, with an OR (translated (IF a a b)) inside
; the biconditional driving rewrite-if's or-shape collapse. Axes drawn from
; the anchor: (1) the IFF statement head; (2) the OR-shaped right side;
; (3) an inductive membership-style recursion — deliberately a DIFFERENT
; function family (snoc/has-e over raw equality) from both the qsort book
; (orderedp/all-rel over lexorder) and p3-conj-mid-literal (ordd/ins).
(in-package "ACL2")

(defun snoc (x e)
  (if (endp x)
      (cons e nil)
    (cons (car x) (snoc (cdr x) e))))

(defun has-e (x e)
  (if (endp x)
      nil
    (if (equal (car x) e)
        t
      (has-e (cdr x) e))))

(defthm has-e-snoc
  (iff (has-e (snoc x d) e)
       (or (has-e x e) (equal d e))))
