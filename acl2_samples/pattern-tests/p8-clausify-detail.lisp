; p8-clausify-detail — clausify-region DETAIL-STEP pin (2e, bsort-recon
; fold-back audit F2: the detail attachment direction and runCheckedExpand's
; never-ignore guard had zero corpus coverage — the auditor's wrong-attachment
; tamper ran the whole suite green). Wild anchor: books/sorting/bsort.lisp's
; Subgoal *1/4.1.3' — clausify-input's expand-and-or fires CONS-EQUAL on an
; (EQUAL (CONS …) (CONS …)) clause literal and its INTERNAL
; expand-abbreviations pass emits the cleanup steps (equal-self on the
; residual (EQUAL X X), if-iff on the (IF c 'T 'NIL) shell) BEFORE the
; :CLAUSIFY-EXPAND marker is pushed. Axes drawn from the anchor: (1) the
; equal-cons-cons literal shape with one differing and one shared component
; (so CONS-EQUAL leaves an equal-self residue); (2) the literal sits in a
; GOAL-level clausify (no induction — the smallest book that walks the
; expand-and-or path end-to-end, so the replay row reaches the expansion
; consumer instead of dying on an unrelated earlier frontier).
; COMPLETION CRITERION (MDD 2026-08-01): a frontier-message pin only while
; the detail-chain replay is a frontier — when it lands, this book's state
; is a GREEN row + full lean-idiomatic native mirror, not a re-pin.
(in-package "ACL2")

(defthm cons-neq-detail
  (implies (not (equal a b))
           (not (equal (cons a (cons b d)) (cons b (cons a d))))))
