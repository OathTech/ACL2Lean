(in-package "ACL2")

;; FEATURE: chained proofs that consume PRIOR user lemmas as :REWRITE rules,
;; plus cross-fertilization (using an equality hypothesis / the IH).
;; rev-rev is the classic example: it only goes through once app-assoc and
;; rev-app are available as enabled rewrite rules.

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun rev (x)
  (if (consp x)
      (app (rev (cdr x)) (cons (car x) nil))
    nil))

;; (1) associativity of append — induction + fertilization.
(defthm app-assoc
  (equal (app (app a b) c)
         (app a (app b c))))

;; (2) rev always produces a true-list — type lemma, consumed below.
(defthm true-listp-rev
  (true-listp (rev x)))

;; (3) appending nil onto a true-list is identity — consumed by rev-app/rev-rev.
(defthm app-nil
  (implies (true-listp x)
           (equal (app x nil) x)))

;; (4) rev distributes over append — induction; consumes app-assoc, app-nil,
;;     and true-listp-rev as :REWRITE runes.
(defthm rev-app
  (equal (rev (app a b))
         (app (rev b) (rev a))))

;; (5) rev is an involution on true-lists — consumes rev-app + the rules above.
(defthm rev-rev
  (implies (true-listp x)
           (equal (rev (rev x)) x)))
