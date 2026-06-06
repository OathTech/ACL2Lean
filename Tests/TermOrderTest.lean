import ACL2Lean.TermOrder

open ACL2

private abbrev I (n : Int) : SExpr := .atom (.number (.int n))
private abbrev Sym (n : String) : SExpr := .atom (.symbol { name := n })

-- === fnCountEvg: size of quoted constants ===

-- nil has size 8 (symbol encoding)
#guard fnCountEvg .nil = 8

-- Small integer: 1 + value
#guard fnCountEvg (I 0) = 1
#guard fnCountEvg (I 5) = 6

-- Negative integer: 2 + |value|
#guard fnCountEvg (I (-3)) = 5

-- Cons adds 1 per cell
#guard fnCountEvg (SExpr.cons (I 0) .nil) > fnCountEvg (I 0)

-- === term_order: variable/function counting ===

-- Variables (atoms) have var count 1
-- Fewer variables → ordered first
-- x has 1 var, (f x y) has 2 vars → x < (f x y)
#guard term_order (Sym "x") (SExpr.ofList [Sym "f", Sym "x", Sym "y"]) = SExpr.t

-- Same var count → compare fn count
-- (f x) has 1 fn, (g (h x)) has 2 fns → (f x) < (g (h x))
#guard term_order
  (SExpr.ofList [Sym "f", Sym "x"])
  (SExpr.ofList [Sym "g", SExpr.ofList [Sym "h", Sym "x"]]) = SExpr.t

-- Quoted constants: var=0, fn=0, pfc=fnCountEvg(value)
-- (quote 1) vs (quote 100) → smaller pfc first
#guard term_order
  (SExpr.ofList [Sym "quote", I 1])
  (SExpr.ofList [Sym "quote", I 100]) = SExpr.t

-- Same counts → falls back to lexorder
#guard term_order (Sym "a") (Sym "b") = SExpr.t
#guard term_order (Sym "b") (Sym "a") = SExpr.nil

-- === merge_term_order ===

-- Merge two singleton lists
#guard merge_term_order
  (SExpr.ofList [Sym "a"])
  (SExpr.ofList [Sym "b"]) =
  SExpr.ofList [Sym "a", Sym "b"]

-- Merge with empty
#guard merge_term_order .nil (SExpr.ofList [Sym "a"]) = SExpr.ofList [Sym "a"]
#guard merge_term_order (SExpr.ofList [Sym "a"]) .nil = SExpr.ofList [Sym "a"]

-- === merge_sort_term_order ===

-- Already sorted
#guard merge_sort_term_order (SExpr.ofList [Sym "a", Sym "b"]) =
  SExpr.ofList [Sym "a", Sym "b"]

-- Reverse sorted → sorts correctly
#guard merge_sort_term_order (SExpr.ofList [Sym "b", Sym "a"]) =
  SExpr.ofList [Sym "a", Sym "b"]

-- Single element → unchanged
#guard merge_sort_term_order (SExpr.ofList [Sym "x"]) = SExpr.ofList [Sym "x"]

-- Empty → unchanged
#guard merge_sort_term_order .nil = .nil
