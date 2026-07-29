; p6-or-collapse-arith — the OR-COLLAPSE BRIDGE's second covering instance
; (equiv-lane arc, rung 1). p3-conj-mid-literal is the bridge's only
; instance; this book keeps the SHAPE that forces the collapse (an
; IH-position OR whose test survives clausify into the rewriter and
; rewrites open under *geneqv-iff*) and varies the RELATION axis:
; arithmetic <= (a macro expanding to (not (< b a)) — NOT-wrapped tests,
; different type-set behavior, the < builtin) instead of lexorder. Wild
; anchor unchanged (ORDEREDP-ISORT's or-shape family).
(in-package "ACL2")

(defun ordn (x)
  (cond ((endp x) t)
        ((endp (cdr x)) t)
        ((<= (car x) (car (cdr x))) (ordn (cdr x)))
        (t nil)))

(defun insn (e x)
  (cond ((endp x) (cons e x))
        ((<= e (car x)) (cons e x))
        (t (cons (car x) (insn e (cdr x))))))

(defthm ordn-insn-mid
  (implies (and (consp it)
                (not (<= x1 (car it)))
                (ordn (cdr it))
                (ordn it))
           (or (ordn (insn x1 it))
               (equal it 'junk)))
  :rule-classes nil)
