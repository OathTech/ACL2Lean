import ACL2Lean.Replay.Lemmas.TsComplexFacts

namespace ACL2.Replay
open ACL2

/-- Atomic image used by ACL2's TYPE-SET-UNARY-- / TS-BUILDER.
Nonnumber cells undergo numeric completion to zero. -/
def tsNegCell : Nat → Int
  | 0 => 1
  | 1 | 2 => 16
  | 3 => 32
  | 4 => 6
  | 5 => 8
  | 6 => 64
  | _ => 1

/-- Primitive negation transports each basic cell to its recorded atomic
image. This is independent of a book, theorem, or composite input mask. -/
theorem inTs_neg_cell (v : SExpr) : InTs (tsNegCell (tsIndex v)) (Logic.neg v) := by
  cases v with
  | nil => unfold InTs; decide
  | cons a d =>
    simp only [tsIndex_cons]
    split_ifs <;> (change tsMember 1 0 = true; decide)
  | atom a => cases a with
    | number n => cases n with
      | int n =>
        have he : Logic.neg (.atom (.number (.int n))) = .atom (.number (.int (-n))) := by
          simp [Logic.neg, Logic.isComplex, Logic.toRat, Logic.mkNumber]
        rw [he]
        simp only [InTs, tsIndex_int]
        split_ifs <;> first | decide | omega
      | rational n d hc =>
        have facts : 2 ≤ d ∧ n.natAbs.gcd d = 1 := by
          simpa only [canonRat, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hc
        have hn : n ≠ 0 := by
          intro hz
          simp only [hz, Int.natAbs_zero, Nat.gcd_zero_left] at facts
          omega
        simp only [Logic.neg, Logic.isComplex, Bool.false_eq_true, ↓reduceIte,
          Logic.toRat, Logic.mkNumber, Int.natAbs_neg, facts.2,
          show d ≠ 0 by omega, show d ≠ 1 by omega, ↓reduceDIte,
          show Int.ofNat 1 = (1 : Int) from rfl, Int.ediv_one, Nat.div_one]
        simp only [InTs, tsIndex_rat]
        split_ifs <;> first | decide | omega
      | complex r i hi =>
        exact inTs_neg_complex (by change tsMember 64 6 = true; decide)
    | symbol s =>
      simp only [tsIndex_symbol]
      split_ifs <;> (change tsMember 1 0 = true; decide)
    | keyword _ | string _ | char _ => change tsMember 1 0 = true; decide

/-- A finite inclusion certificate for the emitted input/output masks.
The replay checks this certificate; it does not infer an argument's type. -/
def tsNegTransfer (input output : Int) : Bool :=
  (List.range 14).all fun i => !tsMember input i || tsSubsumedM (tsNegCell i) output

theorem inTs_neg_transfer {input output : Int} {v : SExpr}
    (h : tsNegTransfer input output = true) (hv : InTs input v) :
    InTs output (Logic.neg v) := by
  have hi := List.all_eq_true.mp h (tsIndex v) (List.mem_range.mpr (tsIndex_lt v))
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
  rcases hi with hfalse | hsubset
  · exact False.elim (Bool.noConfusion (hfalse.symm.trans hv))
  · exact inTs_weaken hsubset (inTs_neg_cell v)

end ACL2.Replay
