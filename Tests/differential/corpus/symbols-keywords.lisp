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

; TARGET SURFACE — recognizers/accessors over symbols not modeled yet
;@ unsupported
(keywordp ':k)
;@ unsupported
(symbol-name 'abc)
