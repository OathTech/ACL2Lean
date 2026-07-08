; Differential corpus: SYMBOL IDENTITY & CASE — the discriminating experiments
; that pin ACL2's symbol semantics (docs/notes/2026-07-08_symbol-case-semantics.md).
; ACL2 reads unescaped tokens UPCASED (readtable-case :upcase, acl2.lisp:2026)
; and |bar|-escaped tokens VERBATIM; symbol identity is exact (name, package)
; string equality (symbol-equality, axioms.lisp:16884). Our model LOWERCASES
; bare tokens (BUG-002) → wrong collapse point. Every divergence is pinned
; known-bug (bug:BUG-002); the agreeing controls are `match`.

; ── CASE: normalization happens, and it is UPCASE (kills the "no-normalization"
;    and "downcase" theories). abc/ABC/aBc all read as name "ABC". ──
;@ match
(equal 'abc 'ABC)
;@ match
(equal 'aBc 'AbC)
; UPCASE payoff (T0 vs our downcase model): bare vs |UPPER| — ACL2 T, us NIL.
;@ known-bug bug:BUG-002 lean NIL
(equal 'abc '|ABC|)
;@ known-bug bug:BUG-002 lean NIL
(equal 'ABC '|ABC|)
; identity is EXACT string, not case-insensitive (kills the case-insensitive
; theory): two |bar| forms differing only in case are DISTINCT.
;@ match
(equal '|abc| '|ABC|)
; bare vs |lower|: ACL2 NIL (abc="ABC" != "abc"); us t (we downcase bare to "abc").
;@ known-bug bug:BUG-002 lean t
(equal 'abc '|abc|)
;@ known-bug bug:BUG-002 lean t
(equal 'ABC '|abc|)

; ── nil / t are ORDINARY symbols (names "NIL"/"T", package COMMON-LISP). ──
;@ match
(symbolp 'nil)
;@ match
(symbolp 't)
; |NIL| reads as the symbol named "NIL", which IS nil → ACL2 T. Our |bar| path
; makes a symbol{name:="NIL"} distinct from the SExpr.nil constructor → NIL.
;@ known-bug bug:BUG-002 lean NIL
(equal '|NIL| 'nil)
;@ known-bug bug:BUG-002 lean NIL
(equal '|T| 't)
; |nil| (name "nil") is a DISTINCT, non-nil symbol — ACL2 and us AGREE it's not
; nil, and that it is a symbol; ACL2 says it's truthy.
;@ match
(equal '|nil| 'nil)
;@ match
(symbolp '|nil|)
;@ match
(if '|nil| 'truthy 'falsy)
; |t| (name "t") vs t (name "T"): ACL2 NIL; us t (we downcase 't to "t").
;@ known-bug bug:BUG-002 lean t
(equal '|t| 't)

; ── number vs symbol via bar-escape: |5| is the SYMBOL "5", not the number.
;    (Our bar path already yields symbol{name:="5"}, so these AGREE — pinned so
;    a naive "does the token look numeric?" check on bar tokens can't regress.) ──
;@ match
(equal '|5| '5)
;@ match
(symbolp '|5|)
;@ match
(acl2-numberp '|5|)
;@ match
(symbolp '5)

; ── keywords obey the same case rule (name upcased, |bar| verbatim). ──
;@ match
(equal ':abc ':ABC)
;@ match
(equal ':abc ':|abc|)
;@ match
(equal ':FOO ':foo)
;@ match
(equal ':foo 'foo)
; UPCASE payoff for keywords: :abc vs :|ABC| — ACL2 T, us NIL (we downcase :abc).
;@ known-bug bug:BUG-002 lean NIL
(equal ':abc ':|ABC|)

; ── the case rule pays off through COMPUTATION (not just equal): alist lookup.
;    Both are currently unsupported (assoc-equal not modeled) — pinned as target.
;@ unsupported
(cdr (assoc-equal 'abc '((|ABC| . hit))))
;@ unsupported
(cdr (assoc-equal 'abc '((|abc| . hit))))
