;@isolate
; Differential corpus (ISOLATED — one form per interpreter invocation): MIXED /
; PARTIAL symbol escaping within a single token (BUG-010). These forms are here,
; not in symbol-identity.lisp, because our parser FAILS CLOSED on them with a
; parse error that aborts a batched Lean stdin stream — exactly the halting case
; ;@isolate exists for (like floats/radix in boundary.lisp).
;
; ACL2's reader applies readtable-case :upcase to the UNESCAPED runs of a token
; and keeps |…|/\-escaped runs VERBATIM, WITHIN one token: `a|B|c` reads as name
; "ABC", `foo\Bar` as "FOOBAR", `|ABC|xyz` as "ABCXYZ" — all equal to the bare
; upcased spelling (ACL2 returns T). We do NOT implement per-run escaping (bars
; recognized only when they span the whole token, backslash never), so rather
; than silently upcase wholesale (a WRONG symbol name — the old fail-open bug:
; (equal 'a|B|c 'ABC) had returned NIL) or fuel-loop on trailing chars, the
; parser now refuses. Pinned known-bug: ACL2 T, us <refused> (fail-closed is
; correct-at-the-frontier — never a wrong value). Proper per-run escaping in the
; tokenizer is the eventual fix. See docs/BUGS.md BUG-010.

; interior escaped run
;@ known-bug bug:BUG-010 lean <refused>
(equal 'a|B|c 'ABC)
; backslash single-char escape
;@ known-bug bug:BUG-010 lean <refused>
(equal 'foo\Bar 'FOOBAR)
; leading escaped run then bare chars
;@ known-bug bug:BUG-010 lean <refused>
(equal '|ABC|xyz 'ABCXYZ)
