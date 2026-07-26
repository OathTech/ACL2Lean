(in-package "ACL2")

; PROBE/beta-iff-context (S2b re-audit F1, reviewer artifact iffpre2):
; a `let` in an IF TEST — the ambient geneqv there is iff, but the
; entry-style preprocess beta is PURE SUBSTITUTION, an EQUAL fact.
; Pre-fix the step was labeled :EQUIV IFF (the context, not the fact)
; and hit the preprocess equiv gate; the identical EQUAL-context book
; replayed. Pins the site-3 arms emitting :equiv EQUAL.
; the replay gets past proveConv and reaches the preprocess equiv gate.
(defthm probe-iffpre2
  (equal (cons (if (let ((y (car a))) (cons y '1)) 'yes 'no) '2)
         (cons (if (cons (car a) '1) 'yes 'no) '2))
  :rule-classes nil)
