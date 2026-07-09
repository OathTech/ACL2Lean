; Differential corpus: symbols and keywords.

; In ACL2 a KEYWORD is a symbol (it lives in the KEYWORD package;
; keywordp-forward-to-symbolp), so (symbolp :foo) = T. This was a known
; divergence (Logic.symbolp recognized only the .symbol variant, not .keyword);
; FIXED 2026-07-07 by adding .keyword to symbolp's truthy case. Now `match`. A
; keyword stays DISTINCT from the like-named symbol under equal (below).
;@ match
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

; SYMBOL-CASE (BUG-002 fixed — these are the regression guards). ACL2's reader
; UPCASES bare symbols and PRESERVES the case of |bar|-escaped ones; our parser
; now does the same, so two spellings collapse at exactly ACL2's point:
;   |ABC| = abc = ABC  (all become ABC)      → equal T
;   |abc| (verbatim lower) ≠ ABC (bare → ABC) → NIL
;@ match
(equal '|ABC| 'abc)
;@ match
(equal '|ABC| 'ABC)
; and the mirror: |abc| (verbatim lower) vs ABC (bare → ABC) — DIFFER → NIL.
;@ match
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
