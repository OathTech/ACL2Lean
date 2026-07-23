(in-package "ACL2")

; P1/or-optimization PROBE (pattern map 2026-07-22): (OR p q) in a
; HYPOTHESIS position rewrites under IFF geneqv as (IF p p q) with
; unrewritten-test == left — ACL2's "do not rewrite x more than once"
; optimization (rewrite.lisp, directly below the swapped-p site)
; replaces the then-branch by *T*. No corpus row exhibits it; this
; book probes what the log records so the replay side can be built
; against the real shape (or the axis recorded unreachable).

(defun firstc (x y)
  (if (consp x)
      (car x)
    (car y)))

(defthm firstc-or-hyp
  (implies (or (consp x) (consp y))
           (equal (firstc x y)
                  (if (consp x) (car x) (car y)))))
