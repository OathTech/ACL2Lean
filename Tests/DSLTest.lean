import ACL2Lean

open ACL2 ACL2.Logic

#acl {
  (defun my-plus (x y) (+ x y))

  (defun factorial (n)
    (if (zp n)
        1
      (* n (factorial (- n 1)))))

  (defun test-list ()
    (quote (1 2 3)))

  (defconst myconst 42)
}

#check my_plus
#check factorial
#check test_list
#check myconst

#eval! factorial (SExpr.atom (.number (.int 5)))
#eval! test_list
#eval! myconst
