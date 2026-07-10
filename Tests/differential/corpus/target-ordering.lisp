; Differential corpus: ACL2's total-order primitive `lexorder` — NOW MODELED
; (wired into callBuiltin 2026-07-08, Task #7). These pin the faithful behavior
; per input kind against real ACL2; the full semantics + source grounding is in
; docs/notes/2026-07-08_lexorder-semantics.md. `alphorder` and `symbol-name`
; remain `unsupported` (frontiers — see the tail).

; ── class order: number < character < string < symbol; atoms < conses. ──
;@ match
(lexorder '1 '2)
;@ match
(lexorder '2 '1)
;@ match
(lexorder 5 "abc")
;@ match
(lexorder #\a 5)
;@ match
(lexorder "abc" 'abc)
;@ match
(lexorder '(a) 5)
;@ match
(lexorder 5 '(a))

; ── numbers by VALUE (alphorder's single `<=` over all reals — NOT by type or
;    lexicographic numerator/denominator; audit finding 2026-07-10). ──
;@ match
(lexorder -3 5)
;@ match
(lexorder 1/2 3/4)
;@ match
(lexorder 5 5)
; int vs rational compared by value (an int is NOT always smaller)
;@ match
(lexorder 1 1/2)
;@ match
(lexorder 1/2 1)
;@ match
(lexorder 5 1/2)
;@ match
(lexorder 7/2 3)
; rational vs rational by value (NOT by (numerator, denominator))
;@ match
(lexorder 1/3 1/2)
;@ match
(lexorder 2/5 1/2)
;@ match
(lexorder 1/2 2/5)

; ── characters by char-code; strings by string<= (prefix is smaller) ──
;@ match
(lexorder #\a #\b)
;@ match
(lexorder #\z #\a)
;@ match
(lexorder "abc" "abd")
;@ match
(lexorder "abc" "ab")

; ── symbols by NAME (string<) then PACKAGE (string<) ──
;@ match
(lexorder 'a 'b)
;@ match
(lexorder 'foo 'foo)
;@ match
(lexorder :abc 'abc)
;@ match
(lexorder 'abc :abc)
;@ match
(lexorder :aaa :bbb)
;@ match
(lexorder 'acl2::foo 'common-lisp::foo)

; ── nil / t are ORDINARY SYMBOLS (COMMON-LISP), NOT special "smallest": a
;    number/char/string sorts BEFORE them; nil ("NIL") < t ("T") by name. This
;    was the pre-2026-07-08 bug (nil treated as smallest). ──
;@ match
(lexorder nil 5)
;@ match
(lexorder 5 nil)
;@ match
(lexorder nil #\a)
;@ match
(lexorder nil "z")
;@ match
(lexorder nil 'zzz)
;@ match
(lexorder 'a nil)
;@ match
(lexorder nil t)
;@ match
(lexorder t nil)
;@ match
(lexorder nil nil)

; ── conses: LARGER than any atom; compared lexicographically (car then cdr);
;    a longer list with an equal prefix is larger. ──
;@ match
(lexorder '(1) '(2))
;@ match
(lexorder '(1 2) '(1 3))
;@ match
(lexorder '(1 2 3) '(1 2))
;@ match
(lexorder '(1 2) '(1 2 3))
;@ match
(lexorder '(1 . 2) '(1 . 3))

; ── FRONTIERS (still unsupported): `alphorder` is NOT aliased to lexorder — it
;    differs on conses (alphorder's guard requires atoms; `(alphorder '(1) '(2))`
;    = NIL in ACL2, not lexicographic), so it stays unmodeled. `symbol-name`
;    (a string accessor) is also not modeled. ──
;@ unsupported
(alphorder '1 '2)
;@ unsupported
(alphorder 'a 'b)
;@ unsupported
(alphorder '(1) '(2))
;@ unsupported
(symbol-name 'abc)
