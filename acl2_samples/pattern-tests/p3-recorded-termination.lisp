; (certify-book "p3-recorded-termination")
(in-package "ACL2")

; A LIST-SHRINKING helper whose count bound needs INDUCTION at a
; consumer's admission — the qsort/FILTER class, DECORRELATED: fresh
; name, not FILTER, not the EVENS/ODDS registry.
(defun skip-one (x)
  (cond ((endp x) nil)
        ((endp (cdr x)) x)
        (t (cons (car x) (skip-one (cdr (cdr x)))))))

; 1-ary defun recursing THROUGH skip-one: the admission runs a REAL
; waterfall for (o< (acl2-count (skip-one (cdr x))) (acl2-count x)) —
; the recorded-termination route's class, second independent instance.
(defun thin (x)
  (if (endp x) nil (cons (car x) (thin (skip-one (cdr x))))))

; consumes total:THIN end-to-end (theorem-side induction on THIN's scheme
; with the recorded IH decrease)
(defthm true-listp-thin
  (true-listp (thin x)))

; 2-ary NEGATIVE pin (audit F4): non-destructor decrease at arity 2 — the
; recorded totality route is arity-1 gated, so total:PRUNE must stay
; honestly hypothesis-backed, never abort a row.
(defun prune (e x)
  (cond ((endp x) nil)
        ((lexorder (car x) e) (cons (car x) (prune e (skip-one (cdr x)))))
        (t (prune e (skip-one (cdr x))))))

(defthm true-listp-prune
  (true-listp (prune e x)))
