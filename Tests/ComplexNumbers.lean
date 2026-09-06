import ACL2Lean.Replay.Driver.Reflect
import ACL2Lean.Replay.Lemmas.TsAlgebra
import ACL2Lean.ValueCount

open ACL2 ACL2.Replay Lean

namespace ACL2.Tests.ComplexNumbers

/-! Numeric value, type-mask and literal-reflection checks for NS1.
These test primitives/representation, not fabricated replay records. The
differential corpus is the ACL2-facing counterpart of these focused checks.
-/

private def sampleComplex : SExpr := Logic.mkParts (mkRat 2 3) (mkRat (-4) 5)

elab "ns1_complex_literal%" : term =>
  pure (ACL2.Replay.Driver.reflectSExpr sampleComplex)

private def reflectedComplex : SExpr := ns1_complex_literal%

-- The reflected term is checked by the kernel, including both normalization
-- invariants; it is not a trusted runtime-value cast.
example : reflectedComplex = sampleComplex := by rfl
#guard reprStr reflectedComplex = "#C(2/3 -4/5)"
#guard tsIndex reflectedComplex = 6
#guard tsMember 64 (tsIndex reflectedComplex)
#guard tsMember 112 (tsIndex (Logic.mkParts 0 (-1)))
#guard tsMember 78 (tsIndex (Logic.mkParts 0 1))
#guard tsMember (-49) (tsIndex (Logic.mkParts 0 1))
#guard tsSubsumedM 64 48 = false
#guard tsSubsumedM 64 112 = true
#guard tsDisjointM 64 112 = false
#guard sampleComplex.valueCount = 15
#guard (Logic.realpart sampleComplex).valueCount = 5
#guard (Logic.imagpart sampleComplex).valueCount = 9
#guard sampleComplex.consCount = 0

-- Aliases at the Logic layer use ACL2 numeric order, including imaginary ties.
#guard Logic.le (Logic.mkParts 0 1) (Logic.mkParts 0 2) = SExpr.t
#guard Logic.ge (Logic.mkParts 0 1) (Logic.mkParts 0 2) = SExpr.nil
#guard Logic.gt (Logic.mkParts 0 (-1)) (Logic.mkParts 0 (-2)) = SExpr.t
#guard Logic.le sampleComplex sampleComplex = SExpr.t

-- Both strict comparison facts include the complex bit. Their false-branch
-- counterpart keeps -49: the whole complex class is not negative.
example : InTs 112 (Logic.mkParts 0 (-1)) := inTs_lt_zero_true (by decide)
example : InTs 78 (Logic.mkParts 0 1) := inTs_zero_lt_true (by decide)
example : InTs (-49) (Logic.mkParts 0 1) := inTs_lt_zero_false (by decide)

end ACL2.Tests.ComplexNumbers
