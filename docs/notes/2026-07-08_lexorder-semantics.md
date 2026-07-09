# ACL2 `lexorder` / `alphorder` — precise semantics for wiring into `callBuiltin`

Date: 2026-07-08. Goal: pin ACL2's `lexorder` EXACTLY (source + differential vs
running ACL2) before wiring it into `callBuiltin`, so the trusted-core primitive
has zero semantic difference from real ACL2. Task #7.

## Source (acl2/axioms.lisp)

`lexorder` (27041):
```
(defun lexorder (x y)
  (cond ((atom x)
         (cond ((atom y) (alphorder x y))     ; both atoms
               (t t)))                         ; x atom, y cons  → t (x ≤ y)
        ((atom y) nil)                          ; x cons, y atom  → nil
        ((equal (car x) (car y)) (lexorder (cdr x) (cdr y)))
        (t (lexorder (car x) (car y)))))
```

`alphorder` (26995) — total order on atoms, class order
**rational < complex < character < string < symbol**:
```
(cond ((real/rationalp x) (if (real/rationalp y) (<= x y) t))
      ((real/rationalp y) nil)
      ((complex/complex-rationalp x) …)         ; BUG-009 (not modeled)
      ((complex/complex-rationalp y) nil)
      ((characterp x) (if (characterp y) (<= (char-code x) (char-code y)) t))
      ((characterp y) nil)
      ((stringp x) (if (stringp y) (and (string<= x y) t) t))
      ((stringp y) nil)
      (t ; both are (non-string non-char non-number) atoms = SYMBOLS + bad-atoms
         (cond ((symbolp x) (if (symbolp y) (not (symbol< y x)) t))
               ((symbolp y) nil)
               (t (bad-atom<= x y)))))
```

`symbol<` (9225):
```
(defun symbol< (x y)
  (let ((x1 (symbol-name x)) (y1 (symbol-name y)))
    (or (string< x1 y1)
        (and (equal x1 y1) (string< (symbol-package-name x) (symbol-package-name y))))))
```
So for two symbols, `alphorder x y = (not (symbol< y x))`, i.e. `x ≤ y` iff NOT
`y < x` — a `≤` derived from the strict `symbol<`. Tie-break: NAME via `string<`,
then PACKAGE-NAME via `string<`.

## Differential facts (verified vs running ACL2, 2026-07-08)

Packages: `(symbol-package-name 'nil)` = `(symbol-package-name t)` =
**"COMMON-LISP"**; a bare symbol = **"ACL2"**; a keyword = **"KEYWORD"**.

**nil / t are ORDINARY SYMBOLS in lexorder — NOT special-cased "smallest".**
This is the bug in the current `Lexorder.lean` (lines 47–48 make `.nil` ≤
everything). Pinned:
- `(lexorder nil 5)` = **NIL**  (5 is a number, number < symbol, so nil > 5)
- `(lexorder 5 nil)` = T,  `(lexorder nil #\a)` = NIL,  `(lexorder nil "z")` = NIL
- `(lexorder 'a nil)` = T   ("A" < "NIL" by name),  `(lexorder nil 'zzz)` = T
- `(lexorder nil t)` = T,  `(lexorder t nil)` = NIL  ("NIL" < "T")
- `(lexorder nil nil)` = T

Class order (all confirmed): number < character < string < symbol; atoms < conses.
- `(lexorder #\a 5)` = NIL (number < char);  `(lexorder 5 "abc")` = T;
  `(lexorder "abc" 'abc)` = T (string < symbol);  `(lexorder '(a) 5)` = NIL,
  `(lexorder 5 '(a))` = T (atom < cons).
- numbers `(-3,5)`→T, rationals `(1/2,3/4)`→T, `(5,5)`→T.
- chars by code: `(#\a,#\b)`→T, `(#\z,#\a)`→NIL.
- strings by string<=: `("abc","abd")`→T, `("abc","ab")`→NIL, `("abc","ab")`… i.e.
  a proper prefix is smaller.
- cons lexicographic (car then cdr): `((1 2 3),(1 2))`→NIL, `((1 2),(1 2 3))`→T,
  `((1 . 2),(1 . 3))`→T.
- symbols by name then package: `(:abc,'abc)`→NIL, `('abc,:abc)`→T
  ("ACL2" < "KEYWORD" package tie-break, names equal); `(:aaa,:bbb)`→T;
  `('acl2::foo,'common-lisp::foo)`→T ("ACL2" < "COMMON-LISP").

## Representation note (nil/t package tie-break)

Our `SExpr` has `.nil` as its own constructor and `SExpr.t = {name:="T"}` with the
default package "ACL2" — whereas ACL2 says nil/t live in "COMMON-LISP". For a
FAITHFUL lexorder, treat `.nil` as the symbol (name "NIL", pkg "COMMON-LISP") and
`.t` as (name "T", pkg "COMMON-LISP") *inside lexorder*. The package only matters
on a NAME tie against another symbol also named "NIL"/"T" in a different package —
but such a symbol is unconstructible on our modeled surface: `|NIL|`/`|T|` map
back to the nil/t constructors (BUG-002), and `acl2::|NIL|` etc. are `<refused>`
by the parser (BUG-010 fail-closed) — and in ACL2 `acl2::nil` IS nil anyway
(imported, package resolves to COMMON-LISP). So this package choice is not
observably testable today, but pinning nil/t as COMMON-LISP is the faithful
choice and avoids a latent divergence if the surface later grows.

## Scope / frontiers

- Complex-rationals (BUG-009): the complex class between rational and character
  is not modeled — a frontier, not part of this wiring.
- `bad-atom<=`: only "bad atoms" (non-standard objects) hit this; SExpr atoms are
  all number/char/string/symbol, so it never applies to constructible values.
- Cross-package symbol IMPORT (`acl2::t` ≡ `t`): a package-semantics frontier
  independent of lexorder.
