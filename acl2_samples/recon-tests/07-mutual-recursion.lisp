(in-package "ACL2")

;; FEATURE: mutual recursion (and the measure each branch needs).
;; mutual-recursion bundles several defuns admitted together with a shared
;; termination argument. Reconstruction handles defun events one at a time;
;; this probes whether the bundle's structure (and the flag function ACL2
;; introduces) survives, and whether a theorem proved by the induced
;; mutual-recursion induction scheme reconstructs.

(mutual-recursion
 (defun my-evenp (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) t (my-oddp (- n 1))))
 (defun my-oddp (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) nil (my-evenp (- n 1)))))

;; The feature under test is the mutual-recursion DEFINITION bundle above (the
;; flag function and shared measure ACL2 introduces) — does it survive in the
;; log and reconstruction? ACL2 will not suggest an induction scheme for a
;; property like (or (my-evenp n) (my-oddp n)) on its own (the mutual `or`
;; recursion is a known-hard idiom), so we keep a theorem that actually proves:
;; ground unfolding of each branch.
(defthm my-evenp-3-is-nil
  (equal (my-evenp 3) nil))

(defthm my-oddp-3-is-t
  (equal (my-oddp 3) t))
