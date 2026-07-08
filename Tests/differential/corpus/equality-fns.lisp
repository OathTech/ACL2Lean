; Differential corpus: eq / eql / equal — all three are VALUE equality in ACL2's
; logic. Source: axioms.lisp:2073 `(defun eq (x y) ... (equal x y))` and
; axioms.lisp:2479 `(defun eql (x y) ... (equal x y))` — both are literally
; defined as `equal` (guards restrict their domain, but under the logical
; semantics we model — (set-guard-checking nil) — they ARE equal). So there is
; NO pointer/identity distinction in the logic: (eq '(1 2) '(1 2)) = T, not NIL.
;
; Our model: eql → equal (faithful, `match`); eq is NOT wired into callBuiltin
; yet (`unsupported`). The eq entries pin the target value a faithful model must
; produce — note especially the non-atom and big-integer cases, which a
; raw-Lisp-eq theory would get WRONG.

; eql / equal on assorted shapes — modeled and faithful
;@ match
(eql '(1 2) '(1 2))
;@ match
(eql "abc" "abc")
;@ match
(eql '1/2 '1/2)
;@ match
(eql #\a #\a)
;@ match
(eql 'a 'a)
;@ match
(eql 'a 'b)
;@ match
(equal '(1 2) '(1 2))
;@ match
(equal "abc" "abc")

; eq — target surface (unmodeled). ACL2 logic: eq = equal, so these are VALUE
; equality even on conses/strings/bignums (a pointer-eq theory would fail these).
;@ unsupported
(eq 'a 'a)
;@ unsupported
(eq 'a 'b)
;@ unsupported
(eq nil nil)
;@ unsupported
(eq '(1 2) '(1 2))
;@ unsupported
(eq "abc" "abc")
;@ unsupported
(eq '5 '5)
;@ unsupported
(eq '100000000000 '100000000000)
