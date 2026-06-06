import ACL2Lean.Logic

open ACL2

private abbrev I (n : Int) : SExpr := .atom (.number (.int n))
private abbrev R (n : Int) (d : Nat) : SExpr := .atom (.number (.rational n d))
private abbrev S (s : String) : SExpr := .atom (.string s)
private abbrev Sym (n : String) : SExpr := .atom (.symbol { name := n })

-- === Rational arithmetic ===

#guard Logic.plus (R 1 2) (R 1 3) = R 5 6
#guard Logic.minus (R 3 4) (R 1 4) = R 1 2
#guard Logic.times (R 1 2) (R 2 3) = R 1 3
#guard Logic.div (I 1) (I 3) = R 1 3

-- Integer arithmetic
#guard Logic.plus (I 3) (I 4) = I 7
#guard Logic.minus (I 10) (I 3) = I 7
#guard Logic.times (I 6) (I 7) = I 42

-- Division by zero → 0
#guard Logic.div (I 5) (I 0) = I 0

-- Non-numeric coercion → 0
#guard Logic.plus .nil (I 3) = I 3
#guard Logic.toInt .nil = 0
#guard Logic.toInt (SExpr.cons .nil .nil) = 0

-- === Exponentiation ===

#guard Logic.expt (I 2) (I (-3)) = R 1 8
#guard Logic.expt (I 2) (I 3) = I 8
#guard Logic.expt (I 10) (I 0) = I 1

-- === Comparisons ===

-- lt
#guard Logic.lt (R 1 3) (R 1 2) = SExpr.t
#guard Logic.lt (I 5) (I 3) = SExpr.nil
#guard Logic.lt (I 3) (I 3) = SExpr.nil

-- le
#guard Logic.le (I 3) (I 5) = SExpr.t
#guard Logic.le (I 3) (I 3) = SExpr.t
#guard Logic.le (I 5) (I 3) = SExpr.nil

-- ge
#guard Logic.ge (I 5) (I 3) = SExpr.t
#guard Logic.ge (I 3) (I 3) = SExpr.t
#guard Logic.ge (I 3) (I 5) = SExpr.nil

-- gt
#guard Logic.gt (I 5) (I 3) = SExpr.t
#guard Logic.gt (I 3) (I 3) = SExpr.nil

-- eq / equal
#guard Logic.eq (I 42) (I 42) = SExpr.t
#guard Logic.eq (I 1) (I 2) = SExpr.nil
#guard Logic.equal .nil .nil = SExpr.t
#guard Logic.equal SExpr.t .nil = SExpr.nil

-- === Predicates ===

-- consp
#guard Logic.consp (SExpr.cons .nil .nil) = SExpr.t
#guard Logic.consp .nil = SExpr.nil
#guard Logic.consp (I 1) = SExpr.nil

-- atom
#guard Logic.atom .nil = SExpr.t
#guard Logic.atom (I 5) = SExpr.t
#guard Logic.atom (SExpr.cons .nil .nil) = SExpr.nil

-- integerp
#guard Logic.integerp (I 42) = SExpr.t
#guard Logic.integerp .nil = SExpr.nil
#guard Logic.integerp (R 1 2) = SExpr.nil

-- natp
#guard Logic.natp (I 0) = SExpr.t
#guard Logic.natp (I 5) = SExpr.t
#guard Logic.natp (I (-1)) = SExpr.nil
#guard Logic.natp .nil = SExpr.nil

-- posp
#guard Logic.posp (I 1) = SExpr.t
#guard Logic.posp (I 0) = SExpr.nil
#guard Logic.posp (I (-1)) = SExpr.nil

-- zp
#guard Logic.zp (I 0) = SExpr.t
#guard Logic.zp (I (-1)) = SExpr.t
#guard Logic.zp (I 5) = SExpr.nil

-- evenp / oddp
#guard Logic.evenp (I 4) = SExpr.t
#guard Logic.evenp (I 3) = SExpr.nil
#guard Logic.oddp (I 3) = SExpr.t
#guard Logic.oddp (I 4) = SExpr.nil

-- endp
#guard Logic.endp .nil = SExpr.t
#guard Logic.endp (I 5) = SExpr.t
#guard Logic.endp (SExpr.cons .nil .nil) = SExpr.nil

-- stringp
#guard Logic.stringp (S "hello") = SExpr.t
#guard Logic.stringp (I 1) = SExpr.nil
#guard Logic.stringp .nil = SExpr.nil

-- === Logical operators ===

-- and
#guard Logic.and SExpr.t (I 5) = I 5
#guard Logic.and .nil (I 5) = .nil

-- or
#guard Logic.or SExpr.t (I 5) = SExpr.t
#guard Logic.or .nil (I 5) = I 5

-- not
#guard Logic.not SExpr.t = .nil
#guard Logic.not .nil = SExpr.t

-- implies
#guard Logic.implies SExpr.t SExpr.t = SExpr.t
#guard Logic.implies SExpr.t .nil = .nil
#guard Logic.implies .nil SExpr.t = SExpr.t
#guard Logic.implies .nil .nil = SExpr.t

-- iff truth table
#guard Logic.iff SExpr.t SExpr.t = SExpr.t
#guard Logic.iff SExpr.t SExpr.nil = SExpr.nil
#guard Logic.iff SExpr.nil SExpr.t = SExpr.nil
#guard Logic.iff SExpr.nil SExpr.nil = SExpr.t

-- === Identity functions ===

#guard Logic.force (I 42) = I 42
#guard Logic.double_rewrite (Sym "x") = Sym "x"

-- === Bitwise two's complement ===

#guard Logic.logand (I (-1)) (I 5) = I 5
#guard Logic.logand (I 0) (I 255) = I 0
#guard Logic.logor (I (-4)) (I 1) = I (-3)
#guard Logic.logor (I 0) (I 0) = I 0
#guard Logic.logxor (I (-1)) (I 0) = I (-1)
#guard Logic.logxor (I 5) (I 5) = I 0

-- lognot
#guard Logic.lognot (I 0) = I (-1)
#guard Logic.lognot (I (-1)) = I 0
#guard Logic.lognot (I 5) = I (-6)

-- ash (arithmetic shift)
#guard Logic.ash (I 1) (I 4) = I 16
#guard Logic.ash (I 16) (I (-2)) = I 4
#guard Logic.ash (I 0) (I 10) = I 0

-- === String operations ===

#guard Logic.string_append (S "a") (S "b") = S "ab"
#guard Logic.string_append (I 1) (S "x") = S ""
#guard Logic.string_append (S "") (S "") = S ""

-- === Car/cdr ===

#guard Logic.car .nil = .nil
#guard Logic.cdr .nil = .nil
#guard Logic.car (SExpr.cons (I 1) (I 2)) = I 1
#guard Logic.cdr (SExpr.cons (I 1) (I 2)) = I 2

-- first / second
#guard Logic.first (SExpr.ofList [I 10, I 20, I 30]) = I 10
#guard Logic.second (SExpr.ofList [I 10, I 20, I 30]) = I 20

-- === List operations ===

-- list
#guard Logic.list [I 1, I 2] = SExpr.ofList [I 1, I 2]
#guard Logic.list [] = .nil

-- append
#guard Logic.append (SExpr.ofList [I 1, I 2]) (SExpr.ofList [I 3]) =
  SExpr.ofList [I 1, I 2, I 3]
#guard Logic.append .nil (SExpr.ofList [I 1]) = SExpr.ofList [I 1]

-- len
#guard Logic.len (SExpr.ofList [I 1, I 2, I 3]) = I 3
#guard Logic.len .nil = I 0

-- trueListp
#guard Logic.trueListp (SExpr.ofList [I 1, I 2]) = SExpr.t
#guard Logic.trueListp .nil = SExpr.t
#guard Logic.trueListp (SExpr.cons (I 1) (I 2)) = SExpr.nil

-- evens/odds
#guard Logic.evens (SExpr.ofList [I 1, I 2, I 3, I 4]) = SExpr.ofList [I 1, I 3]
#guard Logic.odds (SExpr.ofList [I 1, I 2, I 3, I 4]) = SExpr.ofList [I 2, I 4]
#guard Logic.evens .nil = .nil
#guard Logic.odds .nil = .nil
#guard Logic.evens (SExpr.ofList [I 1]) = SExpr.ofList [I 1]

-- === Arithmetic edge cases ===

-- Negative base exponentiation
#guard Logic.expt (I (-2)) (I 3) = I (-8)
#guard Logic.expt (I (-3)) (I 2) = I 9

-- Rational base coerced to int (toInt of rational = 0)
#guard Logic.expt (R 1 2) (I 3) = I 0

-- Division by negative
#guard Logic.div (I 6) (I (-3)) = I (-2)
#guard Logic.div (I 1) (I (-2)) = R (-1) 2

-- Rational with zero denominator → (0, 1) via toRat
private def badRat : SExpr := .atom (.number (.rational 5 0))
#guard Logic.toRat badRat = (0, 1)
#guard Logic.plus badRat (I 3) = I 3

-- mkNumber GCD reduction
#guard Logic.mkNumber 6 3 = I 2
#guard Logic.mkNumber 2 4 = R 1 2
#guard Logic.mkNumber 0 5 = I 0
#guard Logic.mkNumber 5 0 = I 0

-- Decimal → rational conversion via toRat
private def dec : SExpr := .atom (.number (.decimal 1 (-2)))
#guard Logic.toRat dec = (1, 100)

-- Rational-to-rational arithmetic
#guard Logic.div (R 1 2) (R 1 3) = R 3 2
#guard Logic.times (R 2 3) (R 3 4) = R 1 2

-- car/cdr on atoms return nil
#guard Logic.car (I 5) = .nil
#guard Logic.cdr (I 5) = .nil
#guard Logic.car (Sym "x") = .nil

-- append on improper list
#guard Logic.append (SExpr.cons (I 1) (I 2)) (I 3) = SExpr.cons (I 1) (I 3)
