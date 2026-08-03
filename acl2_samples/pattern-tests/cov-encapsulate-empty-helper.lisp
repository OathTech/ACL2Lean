(in-package "ACL2")

;; PATTERN (fresh-verify N1, 2026-08-03): a LOCAL-ONLY encapsulate — every
;; event inside is local, so encapsulate-pass-2 returns :empty-encapsulate
;; and the event exits by the :empty-encapsulate SUCCESS path. Captured
;; directly (this file), it exercises the PROVING path's empty exit; captured
;; via cov-encapsulate-empty-include.lisp, the INCLUDE-BOOK path's empty exit
;; (the exit the first fix round missed — the fourth success exit). Both
;; must emit (:ENCAPSULATE-END): buildDevelopment enforces balance at EOF.
(encapsulate ()
  (local (defthm empty-enc-local-probe
           (equal (cdr (cons x y)) y)
           :rule-classes nil)))
