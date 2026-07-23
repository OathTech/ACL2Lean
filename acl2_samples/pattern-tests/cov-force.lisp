(in-package "ACL2")

; COVERAGE/forcing (map frame: rewriter situations — UNCOVERED): a
; rule with a FORCEd hypothesis; probes whether a forcing round
; appears and what its proof structure looks like in the log.

(defun hd (x) (car x))

(defthm hd-cons-elim
  (implies (force (consp x))
           (equal (cons (hd x) (cdr x)) x)))

(defthm use-hd-cons
  (implies (and (true-listp x) (not (equal x nil)))
           (equal (cons (hd x) (cdr x)) x)))
