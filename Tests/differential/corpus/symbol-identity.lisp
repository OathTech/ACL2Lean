; Differential corpus: SYMBOL IDENTITY & CASE — the discriminating experiments
; that pin ACL2's symbol semantics (docs/notes/2026-07-08_symbol-case-semantics.md).
; ACL2 reads unescaped tokens UPCASED (readtable-case :upcase, acl2.lisp:2026)
; and |bar|-escaped tokens VERBATIM; symbol identity is exact (name, package)
; string equality (symbol-equality, axioms.lisp:16884). Our model now matches:
; the parser UPCASES bare tokens and preserves |bar| verbatim (BUG-002 fixed) —
; so every discriminator below is `match`, including the ones that used to
; diverge (they are the regression guards for the fix).

; ── CASE: normalization happens, and it is UPCASE (kills the "no-normalization"
;    and "downcase" theories). abc/ABC/aBc all read as name "ABC". ──
;@ match
(equal 'abc 'ABC)
;@ match
(equal 'aBc 'AbC)
; UPCASE payoff (T0 discriminator): bare vs |UPPER| — both read as "ABC" → T.
;@ match
(equal 'abc '|ABC|)
;@ match
(equal 'ABC '|ABC|)
; identity is EXACT string, not case-insensitive (kills the case-insensitive
; theory): two |bar| forms differing only in case are DISTINCT.
;@ match
(equal '|abc| '|ABC|)
; bare vs |lower|: NIL (abc reads "ABC" ≠ verbatim "abc").
;@ match
(equal 'abc '|abc|)
;@ match
(equal 'ABC '|abc|)

; ── nil / t are ORDINARY symbols (names "NIL"/"T", package COMMON-LISP). ──
;@ match
(symbolp 'nil)
;@ match
(symbolp 't)
; |NIL| reads as the symbol named "NIL", which IS nil → T. Our |bar| path maps
; name "NIL"/"T" to the SExpr.nil/SExpr.t constructor so identity is preserved.
;@ match
(equal '|NIL| 'nil)
;@ match
(equal '|T| 't)
; |nil| (name "nil") is a DISTINCT, non-nil symbol — ACL2 and us AGREE it's not
; nil, and that it is a symbol; ACL2 says it's truthy.
;@ match
(equal '|nil| 'nil)
;@ match
(symbolp '|nil|)
;@ match
(if '|nil| 'truthy 'falsy)
; |t| (name "t") vs t (name "T"): NIL — distinct names, exact string identity.
;@ match
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
; UPCASE payoff for keywords: :abc vs :|ABC| — both name "ABC" → T.
;@ match
(equal ':abc ':|ABC|)

; ── the case rule pays off through COMPUTATION (not just equal): alist lookup.
;    Both are currently unsupported (assoc-equal not modeled) — pinned as target.
;@ unsupported
(cdr (assoc-equal 'abc '((|ABC| . hit))))
;@ unsupported
(cdr (assoc-equal 'abc '((|abc| . hit))))

; ── MIXED / PARTIAL escaping within one token (BUG-010) is pinned in the
;    ISOLATE file symbol-escaping.lisp — our parser fails closed on it (a parse
;    error aborts the batched Lean stream, so those forms need per-form
;    isolation). See docs/BUGS.md BUG-010.
