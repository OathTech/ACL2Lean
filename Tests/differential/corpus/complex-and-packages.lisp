; Differential corpus: the remaining ACL2 AXIOMATIC PRIMITIVES not modeled by
; evalOpt (all `unsupported`) — complex numbers and package/symbol primitives.
; These complete the enumeration of ACL2's *primitive-formals-and-guards*
; (basis-b.lisp) in the corpus: exotic but part of the axiomatic core, so pinned
; here as a coverage record. Values are ACL2's; the completion values (a
; primitive on an out-of-domain arg) are pinned too.

; complex numbers (complex/complex-rationalp/realpart/imagpart). Note ACL2
; normalizes a zero-imaginary complex to the real: (complex 1 0) = 1.
;@ unsupported
(complex '1 '2)
;@ unsupported
(complex '1 '0)
;@ unsupported
(complex-rationalp (complex '1 '2))
;@ unsupported
(complex-rationalp '5)
;@ unsupported
(realpart (complex '3 '4))
;@ unsupported
(imagpart (complex '3 '4))
;@ unsupported
(< (complex '1 '2) (complex '1 '3))
; completion values on out-of-domain args (realpart/imagpart of non-number = 0)
;@ unsupported
(realpart 'abc)
;@ unsupported
(imagpart 'abc)
;@ unsupported
(denominator 'abc)
;@ unsupported
(numerator 'abc)

; package / symbol primitives. symbol-package-name of a Common-Lisp symbol is
; "COMMON-LISP", not "ACL2" — a subtlety worth pinning.
;@ unsupported
(intern-in-package-of-symbol "CAR" 'foo)
;@ unsupported
(pkg-witness "ACL2")
;@ unsupported
(symbol-package-name 'foo)
;@ unsupported
(symbol-package-name 'car)
;@ unsupported
(symbol-name '5)
; char-code/code-char are now modeled (see characters.lisp) — completion
; corners: char-code of a non-char = 0; code-char out of [0,256) = null char.
;@ match
(char-code 'abc)
;@ match
(code-char '256)
;@ unsupported
(intern-in-package-of-symbol "NIL" 'foo)

; bad-atom<= : the total order on "bad atoms" (the axiomatic fallback in
; alphorder for non-standard atoms); on ordinary atoms it is nil.
;@ unsupported
(bad-atom<= 'a 'b)

; ── BUG-013: package-IMPORT identity (found 2026-07-11 during the lexorder
;    order-proof work). In ACL2 the ACL2 package IMPORTS ~977 symbols from
;    COMMON-LISP (*common-lisp-symbols-from-main-lisp-package*): COMMON-
;    LISP::NIL IS nil, ACL2::NIL resolves to it, 'car IS COMMON-LISP::CAR.
;    MINIMAL FIX LANDED 2026-07-11 (MDD-ratified): the parser maps the
;    import-resolved NIL/T spellings to the canonical nil/t values, and the
;    COMMON-LISP::NIL/T identities are UNREPRESENTABLE as Symbols
;    (canonSym) — restoring equal/if faithfulness for nil/t and lexorder
;    view-injectivity (the order properties rest on it). The rows below are
;    now regression guards. The FULL import table (e.g. 'car's true
;    package, symbol-package-name) remains open — the car row stays pinned. ──
;@ match
(equal 'common-lisp::nil nil)
;@ match
(equal 'common-lisp::t t)
;@ match
(if 'common-lisp::nil 'truthy 'falsy)
;@ match
(equal 'acl2::nil nil)
;@ known-bug bug:BUG-013 lean NIL
(equal 'car 'common-lisp::car)
;@ match
(lexorder 'common-lisp::nil nil)

; ── BUG-014: the KEYWORD-package duplicate (found 2026-07-12 during the
;    lexorder order-proof work). `keyword::foo` IS `:foo` — KEYWORD is the
;    keywords' HOME package — but the parser built a KEYWORD-package Symbol
;    for it: a second representation of the keyword (the BUG-012/013
;    duplication pattern, third instance), giving a live wrong value on
;    `equal` and breaking lexorder antisymmetry (both representations view
;    as (name . "KEYWORD")). FIX LANDED 2026-07-12: the parser maps
;    KEYWORD-package tokens to the canonical `.keyword` representation and
;    KEYWORD-package Symbols are UNREPRESENTABLE (canonSym). Verified vs
;    running ACL2 2026-07-12; the rows below are regression guards. ──
;@ match
(equal :foo 'keyword::foo)
;@ match
(lexorder :foo 'keyword::foo)
;@ match
(lexorder 'keyword::foo :foo)
;@ match
(equal :nil 'keyword::nil)

; ── BUG-015 (single-colon package markers) is pinned in boundary.lisp, not
;    here: the interim fix fail-CLOSES the Lean parser on `pkg:name`, and a
;    parse error aborts the whole batched Lean stream — so those pins need
;    the per-form `;@isolate` path (boundary.lisp), which maps a parse error
;    to `<refused>`. See boundary.lisp's BUG-015 block. ──
