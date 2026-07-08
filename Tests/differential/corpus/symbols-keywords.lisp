; Differential corpus: symbols and keywords.

; KNOWN DIVERGENCE (found 2026-07-07): in ACL2 a KEYWORD is a symbol (it lives
; in the KEYWORD package), so (symbolp :foo) = T. Our Logic.symbolp recognizes
; only the .symbol atom variant, not .keyword, so it returns NIL. Narrow, real
; fidelity gap. Everything else about keywords agrees (atom/consp/equal/
; truthiness — see below), so this is isolated to symbolp.
;@ known-bug lean NIL
(symbolp ':foo)

; keyword behavior that AGREES with ACL2 (control — confirms the divergence is
; isolated to symbolp)
;@ match
(atom ':foo)
;@ match
(consp ':foo)
;@ match
(equal ':foo ':foo)
;@ match
(equal ':a ':b)
;@ match
(if ':foo '1 '2)
;@ match
(not ':foo)
;@ match
(acl2-numberp ':foo)

; plain symbol behavior (modeled, agrees)
;@ match
(symbolp 'a)
;@ match
(symbolp 't)
;@ match
(symbolp 'nil)
;@ match
(equal 'a 'a)
;@ match
(equal 'nil nil)
;@ match
(equal 't t)

; SYMBOL-CASE known bug (both directions of the same root cause). ACL2's reader
; UPCASES bare symbols and PRESERVES the case of |bar|-escaped ones; our parser
; LOWERCASES bare symbols and preserves |bar|-escaped ones. So the case at which
; two spellings collapse differs from ACL2:
;   ACL2: |ABC| = abc = ABC  (all become ABC)      → equal T
;   Lean: |ABC| stays ABC, abc/ABC become abc      → |ABC| ≠ abc  (NIL)
;@ known-bug lean NIL
(equal '|ABC| 'abc)
;@ known-bug lean NIL
(equal '|ABC| 'ABC)
; and the mirror: |abc| (preserved lower) vs ABC (bare, lowered to abc) — ACL2
; makes these DIFFER (abc vs ABC), we make them EQUAL.
;@ known-bug lean t
(equal '|abc| 'ABC)

; package-qualified symbols — these AGREE (control): acl2:: is the default
; package, common-lisp:: symbols are still symbols
;@ match
(equal 'acl2::foo 'foo)
;@ match
(symbolp 'common-lisp::car)
;@ match
(symbolp (quote nil))

; TARGET SURFACE — recognizers/accessors over symbols not modeled yet
;@ unsupported
(keywordp ':k)
;@ unsupported
(symbol-name 'abc)
;@ unsupported
(symbol-name 'nil)
