(in-package "ACL2")

;; FEATURE: explicit MEASURE / termination proofs.
;; Admitting each defun below generates a measure (termination) conjecture
;; that ACL2 proves through the waterfall. Reconstruction currently records a
;; defun as only (name formals body) — no :measure, no well-founded relation,
;; and the admission-time proof is not attached to the defun. These probe what
;; the log emits for termination.

;; (1) simple measure: recursion that needs (nfix n) to terminate.
(defun count-down (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons n (count-down (- n 1)))))

;; (2) summed measure: recursion that shrinks *either* argument, so ACL2 cannot
;;     guess a single decreasing formal — the (+ ...) measure must be declared.
;;     (A true lexicographic measure needs llist / l< from the ordinals book,
;;     which base ACL2 does not have; deferred until we test include-book.)
(defun zip-lists (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((consp x) (cons (car x) (zip-lists (cdr x) y)))
        ((consp y) (cons (car y) (zip-lists x (cdr y))))
        (t nil)))

;; (3) measure over a structural argument: recursion on the cdr.
(defun my-len (x)
  (declare (xargs :measure (acl2-count x)))
  (if (consp x)
      (+ 1 (my-len (cdr x)))
    0))

;; A trivial theorem so the file also produces an ordinary defthm proof.
(defthm count-down-zero
  (equal (count-down 0) nil))
