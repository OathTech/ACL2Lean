(in-package "ACL2")

; P1/double-negation PROBE (pattern map 2026-07-22): iterated SWAPPED-P.
; A (NOT (NOT ...)) in a DEFUN body is normalized away at admission (the
; stored world body is already (IF (CONSP X) ...) — first probe finding,
; 2026-07-22), so that route is unreachable-by-construction. This
; variant carries the double negation in the THEOREM's hypothesis,
; where the rewriter sees it: the outer NOT unfolds to the negation
; shape (swap #1), the stripped test is itself a NOT which unfolds
; again (swap #2).

(defun ddn (x)
  (if (consp x)
      (ddn (cdr x))
    0))

(defthm ddn-zero-under-double-neg
  (implies (not (not (consp x)))
           (equal (ddn x) (ddn (cdr x)))))
