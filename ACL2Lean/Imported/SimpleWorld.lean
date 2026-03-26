import ACL2Lean.EvalOpt

open ACL2

namespace ACL2.Worlds.Simple

private def sym (name : String) : Symbol := ⟨"ACL2", name⟩

def my_lenBody : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "if" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "consp" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "+" })) (SExpr.cons (SExpr.atom (.number (.int (1)))) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "cdr" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) SExpr.nil)) SExpr.nil))) (SExpr.cons (SExpr.atom (.number (.int (0)))) SExpr.nil))))

def my_appBody : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "if" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "consp" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "cons" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "car" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-app" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "cdr" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil))) SExpr.nil))) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil))))

def world : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert (sym "my-len") ([sym "x"], my_lenBody)
    |>.insert (sym "my-app") ([sym "x", sym "y"], my_appBody)

def defaultFuel : Nat := 1000000

def my_len_my_appFormula : SExpr :=
  (SExpr.cons (SExpr.atom (.symbol { name := "equal" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-app" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil))) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "+" })) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.atom (.symbol { name := "x" })) SExpr.nil)) (SExpr.cons (SExpr.cons (SExpr.atom (.symbol { name := "my-len" })) (SExpr.cons (SExpr.atom (.symbol { name := "y" })) SExpr.nil)) SExpr.nil))) SExpr.nil)))

theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f, f ≥ N → evalOpt f world env my_len_my_appFormula = some SExpr.t := sorry

end ACL2.Worlds.Simple

