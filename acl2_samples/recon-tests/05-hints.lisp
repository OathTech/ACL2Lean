(in-package "ACL2")

;; FEATURE: explicit :hints. The hint machinery changes the waterfall: :use
;; adds a hypothesis (a separate clause), :induct forces a named scheme, and
;; :in-theory enables/disables rules. None of this provenance is currently
;; captured by reconstruction — these probe whether hints leave any trace.

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun len2 (x)
  (if (consp x)
      (+ 1 (len2 (cdr x)))
    0))

;; A standalone lemma we will :use below.
(defthm len2-app-helper
  (equal (len2 (app x y))
         (+ (len2 x) (len2 y))))

;; (1) :use — instantiate the helper lemma explicitly.
(defthm len2-app-via-use
  (equal (len2 (app (cons a b) y))
         (+ 1 (len2 b) (len2 y)))
  :hints (("Goal" :use (:instance len2-app-helper (x (cons a b))))))

;; (2) :induct — force induction on a specific term.
(defthm len2-app-via-induct
  (equal (len2 (app x y))
         (+ (len2 x) (len2 y)))
  :hints (("Goal" :induct (app x y))))

;; (3) :in-theory — disable the helper so it must reprove from scratch.
(defthm len2-app-no-helper
  (equal (len2 (app x y))
         (+ (len2 x) (len2 y)))
  :hints (("Goal" :in-theory (disable len2-app-helper))))
