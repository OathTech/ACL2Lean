; Differential corpus: car/cdr/cons, nesting, control (if/not), let scoping,
; nfix/ifix, comparison, list/len, atom/endp (all modeled).

; REGRESSION WITNESS (harness): a value wide enough that ACL2 pretty-prints it
; across MULTIPLE lines. The manager must rejoin the wrapped continuation lines
; (only the first carries the `ACL2 >` prompt) — a first-line-only slice would
; truncate it and could pass a wrong value as a match. Keep this here so that
; reconstruction stays covered.
;@ match
(quote (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30))

; car / cdr / cons incl. non-cons (logical: nil)
;@ match
(car '(1 2))
;@ match
(cdr '(1 2 3))
;@ match
(cons '1 '2)
;@ match
(car '5)
;@ match
(cdr '5)
;@ match
(car 'nil)
;@ match
(cdr 'nil)

; nested / dotted structure (also exercises the ACL2-faithful printer:
; nested cdrs collapse to list notation, only a final atom cdr uses the dot)
;@ match
(cons '1 (cons '2 (cons '3 'nil)))
;@ match
(car (cdr (cons '1 (cons '2 'nil))))
;@ match
(cons (car '(a b)) (cdr '(a b)))
;@ match
(cons '1 (cons '2 '3))

; control: if (incl. non-boolean tests: 0 and '() are NON-nil ⇒ truthy), not
;@ match
(if 't '1 '2)
;@ match
(if 'nil '1 '2)
;@ match
(if '0 'yes 'no)
;@ match
(if '(1) 'yes 'no)
;@ match
(if '5 'yes 'no)
;@ match
(if (binary-+ 'nil 'nil) 'a 'b)
;@ match
(if (< '1 '2) (if (< '3 '4) 'deep 'x) 'y)
;@ match
(not 'nil)
;@ match
(not 't)
;@ match
(not '5)

; let / let*. NOTE: the parallel-vs-sequential SHADOWING distinction cannot be
; a differential case — the form exercising `let`'s parallel semantics leaves
; the outer binding unused, which ACL2 rejects at translate time. That
; distinction is validated against evalOpt directly in the Lean unit tests.
; Here we keep only ACL2-translatable scope cases.
;@ match
(let ((a 2) (b 3)) (binary-+ a b))
;@ match
(let ((x 5)) (binary-* x x))
;@ match
(let* ((x 2) (y (binary-+ x x)) (z (binary-* y y))) z)
;@ match
(let* ((a 1) (b (binary-+ a 1)) (c (binary-+ b 1)) (d (binary-+ c 1))) d)
;@ match
(let ((x 1)) (let ((y (binary-+ x 1))) (let ((z (binary-+ y 1))) z)))

; nfix / ifix (ifix of a rational is 0)
;@ match
(nfix '5)
;@ match
(nfix '-3)
;@ match
(nfix 'nil)
;@ match
(ifix '5)
;@ match
(ifix '-2)
;@ match
(ifix '1/2)
;@ match
(ifix 'nil)

; comparison
;@ match
(< '2 '3)
;@ match
(< '3 '2)
;@ match
(< '1/3 '1/2)
;@ match
(< '3 '3)
;@ match
(< '-2 '-1)

; atom / endp
;@ match
(atom '5)
;@ match
(atom 'nil)
;@ match
(atom '(1))
;@ match
(endp 'nil)
;@ match
(endp '(1 2))

; implies / iff
;@ match
(implies 'nil '5)
;@ match
(implies 't 'nil)
;@ match
(implies 't '5)
;@ match
(iff 't '5)
;@ match
(iff 'nil 'nil)
;@ match
(iff 't 'nil)

; true-listp / len / list
;@ match
(true-listp '(1 2 3))
;@ match
(true-listp 'nil)
;@ match
(true-listp '(1 . 2))
;@ match
(true-listp '5)
;@ match
(len '(1 2 3 4))
;@ match
(len 'nil)
;@ match
(len '5)
;@ match
(list '1 '2 '3)
;@ match
(list)
