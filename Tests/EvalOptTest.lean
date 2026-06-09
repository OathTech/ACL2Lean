/-
  evalOpt semantic characterization tests.

  Currently: the `let` (parallel) vs `let*` (sequential) binding distinction — a trust-core
  fidelity point that must NOT regress. ACL2's `let` evaluates every binding's value in the
  OUTER environment (bindings are simultaneous); `let*` threads them sequentially. So with
  `y`'s value referring to a same-clause `x`:
    (let  ((x (quote 1)) (y x)) y)  ⇒ y sees the OUTER x (here unbound ⇒ nil)
    (let* ((x (quote 1)) (y x)) y)  ⇒ y sees the just-bound x = 1
  These MUST differ; if they ever coincide, `let` has silently become `let*` (the bug the
  adversarial audit caught — the differential battery had no `let` term, so add one there
  too: see scripts/diff_eval.sh).
-/
import ACL2Lean.EvalOpt
import ACL2Lean.Parser

open ACL2

private def parseE (s : String) : SExpr :=
  ((ACL2.Parse.parseSExpr s.toList).toOption.map Prod.fst).getD .nil
private def intV (n : Int) : SExpr := .atom (.number (.int n))

-- `let*` is sequential: y = (just-bound) x = 1.
#guard evalOpt 100 World.empty {} (parseE "(let* ((x (quote 1)) (y x)) y)") = some (intV 1)
-- `let` is parallel: y sees the OUTER x (unbound here) ⇒ nil — NOT 1.
#guard evalOpt 100 World.empty {} (parseE "(let ((x (quote 1)) (y x)) y)") = some .nil
-- They must differ (the regression guard, stated directly).
#guard (evalOpt 100 World.empty {} (parseE "(let ((x (quote 1)) (y x)) y)")
      ≠ evalOpt 100 World.empty {} (parseE "(let* ((x (quote 1)) (y x)) y)"))

-- With an outer binding both are well-defined and still differ:
-- parallel `let` ⇒ inner y = outer x = 10; sequential `let*` ⇒ inner y = inner x = 1.
#guard evalOpt 100 World.empty {} (parseE "(let ((x (quote 10))) (let ((x (quote 1)) (y x)) y))") = some (intV 10)
#guard evalOpt 100 World.empty {} (parseE "(let ((x (quote 10))) (let* ((x (quote 1)) (y x)) y))") = some (intV 1)
