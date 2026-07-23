(in-package "ACL2")

; COVERAGE/MV-LET + multiple values, no stobjs (gap audit A4): mv
; returns + mv-let destructuring — translate11-mv-let's lambda
; encoding in bodies and proofs.

(defun two-parts (x)
  (mv (car x) (cdr x)))

(defun rejoin (x)
  (mv-let (hd tl)
          (two-parts x)
          (cons hd tl)))

(defthm rejoin-id
  (implies (consp x) (equal (rejoin x) x)))
