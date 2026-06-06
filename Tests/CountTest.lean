import ACL2Lean.Count

open ACL2

private abbrev I (n : Int) : SExpr := .atom (.number (.int n))

-- === acl2Count concrete values ===

-- Atoms and nil have count 0
#guard SExpr.nil.acl2Count = 0
#guard (I 42).acl2Count = 0
#guard (SExpr.atom (.string "hi")).acl2Count = 0
#guard (SExpr.atom (.symbol { name := "x" })).acl2Count = 0

-- Single cons: 1 + car.count + cdr.count
#guard (SExpr.cons (I 1) (I 2)).acl2Count = 1
#guard (SExpr.cons .nil .nil).acl2Count = 1

-- Proper list [1, 2, 3] = cons(1, cons(2, cons(3, nil)))
-- = 1 + 0 + (1 + 0 + (1 + 0 + 0)) = 3
#guard (SExpr.ofList [I 1, I 2, I 3]).acl2Count = 3

-- Nested structure: cons(cons(1,2), cons(3,4))
-- = 1 + (1 + 0 + 0) + (1 + 0 + 0) = 3
#guard (SExpr.cons (SExpr.cons (I 1) (I 2)) (SExpr.cons (I 3) (I 4))).acl2Count = 3

-- === cdr decreases count ===

-- cdr of a proper list decreases count
#guard (Logic.cdr (SExpr.ofList [I 1, I 2, I 3])).acl2Count <
  (SExpr.ofList [I 1, I 2, I 3]).acl2Count

-- car of cons decreases count
#guard (Logic.car (SExpr.cons (I 1) (I 2))).acl2Count <
  (SExpr.cons (I 1) (I 2)).acl2Count

-- === evens decreases count for 2+ element lists ===

private def list4 : SExpr := SExpr.ofList [I 1, I 2, I 3, I 4]
#guard (Logic.evens list4).acl2Count < list4.acl2Count
#guard (Logic.odds list4).acl2Count < list4.acl2Count
