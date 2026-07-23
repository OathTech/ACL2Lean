(in-package "ACL2")

; P1/descend+target (pattern map 2026-07-22): or-guard recursion. The
; base-case literal (IF (ATOM X) (ATOM X) (ATOM Y)) gets its test ATOM
; unfolded to the negation shape (IF (CONSP X) 'NIL 'T), firing
; rewrite-if's SWAPPED-P (rewrite.lisp:17726-37) — the swap the replay
; bridges at descend/target positions. Anchor: LEN-ZIP2
; (recon-tests/12-multi-controller).

(defun zipw (x y)
  (if (or (atom x) (atom y))
      nil
    (cons (car x) (zipw (cdr x) (cdr y)))))

(defthm zipw-true-listp
  (true-listp (zipw x y)))
