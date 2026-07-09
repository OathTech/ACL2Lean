import ACL2Lean.Lexorder

open ACL2

private abbrev I (n : Int) : SExpr := .atom (.number (.int n))
private abbrev R (n : Int) (d : Nat) : SExpr := .atom (.number (.rational n d))
private abbrev Sym (n : String) : SExpr := .atom (.symbol { name := n })
private abbrev Kw (k : String) : SExpr := .atom (.keyword k)
private abbrev Str (s : String) : SExpr := .atom (.string s)

-- === nil / t are ORDINARY SYMBOLS (COMMON-LISP), NOT special "smallest" ===
-- ACL2 orders nil within the symbol class (name "NIL"): a number sorts BEFORE
-- it, and nil-vs-symbol goes by name. (Verified vs real ACL2; the old
-- "nil is smallest" was the bug fixed by lexAtom? — see
-- docs/notes/2026-07-08_lexorder-semantics.md.)

#guard lexorder .nil .nil = SExpr.t
#guard lexorder (I 1) .nil = SExpr.t             -- number < symbol NIL
#guard lexorder .nil (I 1) = SExpr.nil           -- symbol NIL > number
#guard lexorder .nil (Sym "x") = SExpr.t         -- "NIL" < "x" by name (N=78 < x=120)
#guard lexorder .nil (SExpr.cons .nil .nil) = SExpr.t  -- atom < cons
-- nil vs t: "NIL" < "T" by name
#guard lexorder .nil SExpr.t = SExpr.t
#guard lexorder SExpr.t .nil = SExpr.nil

-- === Atom kind ordering (faithful to ACL2 alphorder, axioms.lisp:26995):
--     number < character < string < symbol; keywords ARE symbols (sort in the
--     symbol class), so keyword > string. ===

private abbrev Ch (n : Nat) : SExpr := .atom (.char (UInt8.ofNat n))

#guard lexorder (I 1) (Ch 97) = SExpr.t          -- number < character
#guard lexorder (Ch 97) (Str "b") = SExpr.t      -- character < string
#guard lexorder (Str "b") (Sym "c") = SExpr.t    -- string < symbol
#guard lexorder (Str "b") (Kw "a") = SExpr.t     -- string < keyword (keyword is a symbol)
#guard lexorder (Kw "a") (Str "b") = SExpr.nil   -- keyword > string (ACL2: (lexorder :a "b")=NIL)
#guard lexorder (Sym "c") (I 1) = SExpr.nil
-- character ordering: by char-code
#guard lexorder (Ch 97) (Ch 98) = SExpr.t
#guard lexorder (Ch 98) (Ch 97) = SExpr.nil

-- === Integer ordering ===

#guard lexorder (I 1) (I 2) = SExpr.t
#guard lexorder (I 5) (I 3) = SExpr.nil
#guard lexorder (I 3) (I 3) = SExpr.t
#guard lexorder (I (-1)) (I 0) = SExpr.t

-- === Rational ordering (syntactic: numerator first, then denominator) ===

-- Same numerator: smaller denominator first
#guard lexorder (R 1 2) (R 1 3) = SExpr.t
#guard lexorder (R 1 3) (R 1 2) = SExpr.nil
-- Equal → t (reflexive)
#guard lexorder (R 1 2) (R 1 2) = SExpr.t
-- Different numerator: smaller numerator first
#guard lexorder (R 1 4) (R 2 3) = SExpr.t

-- === Mixed number types: int < rational < decimal ===

#guard lexorder (I 1) (R 1 2) = SExpr.t
#guard lexorder (R 1 2) (I 1) = SExpr.nil

-- === String ordering ===

#guard lexorder (Str "abc") (Str "abd") = SExpr.t
#guard lexorder (Str "b") (Str "a") = SExpr.nil
#guard lexorder (Str "a") (Str "a") = SExpr.t

-- === Keyword ordering ===

#guard lexorder (Kw "a") (Kw "b") = SExpr.t
#guard lexorder (Kw "b") (Kw "a") = SExpr.nil

-- === Symbol ordering ===

#guard lexorder (Sym "a") (Sym "b") = SExpr.t
#guard lexorder (Sym "b") (Sym "a") = SExpr.nil
#guard lexorder (Sym "a") (Sym "a") = SExpr.t

-- === Atoms before conses ===

#guard lexorder (I 1) (SExpr.cons .nil .nil) = SExpr.t
#guard lexorder (SExpr.cons .nil .nil) (I 1) = SExpr.nil

-- === Cons lexicographic: compare cars, then cdrs ===

#guard lexorder (SExpr.cons (I 1) (I 2)) (SExpr.cons (I 1) (I 3)) = SExpr.t
#guard lexorder (SExpr.cons (I 1) (I 3)) (SExpr.cons (I 1) (I 2)) = SExpr.nil
#guard lexorder (SExpr.cons (I 1) (I 2)) (SExpr.cons (I 2) (I 1)) = SExpr.t

-- === Reflexivity ===

#guard lexorder (SExpr.ofList [I 1, I 2, I 3]) (SExpr.ofList [I 1, I 2, I 3]) = SExpr.t
