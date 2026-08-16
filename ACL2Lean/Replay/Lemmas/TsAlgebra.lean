/-
  Replay/Lemmas/TsAlgebra — the TYPE-SET ALGEBRA over the value model
  (the D-A consumer, T1+2 sprint phase 1, 2026-08-14).

  ACL2's type-set machinery partitions the value space into fourteen
  BASIC TYPES and reasons with unions of them, encoded as bit masks
  (`acl2/type-set-a.lisp`'s `def-basic-type-sets`; a NEGATIVE mask is
  ACL2's two's-complement COMPLEMENT, e.g. `-24 = ~23`). The R2 fork
  batch made ACL2's own type-set derivation visible per leaf — the
  context-refined verdict, the governing tests, the derived TYPE-ALIST
  and the per-occurrence SUBTERM VERDICTS — so a return-path obligation
  can now be discharged the way ACL2 itself regards it.

  THE DIVISION OF LABOUR IS UNCHANGED (`Provers.lean`'s ratified rule):
  ACL2's emission says WHICH type-set a term has in a context; this
  module says only what a type-set MEANS in our value model, and proves
  the implications between them. Nothing here decides that a term has a
  type — an `InTs` fact enters a walk only from an in-scope BRANCH FACT
  (a recognizer the body itself tested) or from a registered primitive
  lemma, and every mask so composed is cross-checked against ACL2's own
  emitted type-alist entry before it may be used.
-/
import ACL2Lean.Replay.Lemmas.TpClosure

namespace ACL2.Replay

open ACL2

/-! ## The partition -/

/-- The BASIC TYPE-SET INDEX of a value: which one of ACL2's fourteen
    basic types the value inhabits (`def-basic-type-sets`' bit order —
    2^0 `*ts-zero*`, 2^1 `*ts-one*`, 2^2 `*ts-integer>1*`, 2^3
    positive-ratio, 2^4 negative-integer, 2^5 negative-ratio, 2^6
    complex-rational, 2^7 `*ts-nil*`, 2^8 `*ts-t*`, 2^9
    non-t-non-nil-symbol, 2^10 proper-cons, 2^11 improper-cons, 2^12
    string, 2^13 character).

    TOTAL and DISJOINT by construction: every value gets exactly one
    index, so the mask algebra below is the algebra of SETS of basic
    types, exactly as in ACL2. Index 6 (complex-rational) is
    UNINHABITED here — the model has no complex values (BUG-009), a
    domain restriction of the model, never a claim about ACL2. -/
def tsIndex (v : SExpr) : Nat :=
  match v with
  | .nil => 7
  | .cons a d => if Logic.toBool (Logic.trueListp (.cons a d)) then 10 else 11
  | .atom (.number (.int n)) =>
      if n = 0 then 0 else if n = 1 then 1 else if 1 < n then 2 else 4
  | .atom (.number (.rational n _ _)) => if 0 < n then 3 else 5
  | .atom (.string _) => 12
  | .atom (.char _) => 13
  | .atom (.keyword _) => 9
  | .atom (.symbol s) =>
      if (SExpr.atom (.symbol s)) == SExpr.t then 8 else 9

@[simp] theorem tsIndex_nil : tsIndex .nil = 7 := rfl

@[simp] theorem tsIndex_cons (a d : SExpr) :
    tsIndex (.cons a d)
      = if Logic.toBool (Logic.trueListp (.cons a d)) then 10 else 11 := rfl

@[simp] theorem tsIndex_int (n : Int) :
    tsIndex (.atom (.number (.int n)))
      = if n = 0 then 0 else if n = 1 then 1 else if 1 < n then 2 else 4 :=
  rfl

@[simp] theorem tsIndex_rat (n : Int) (d : Nat) (hc : canonRat n d = true) :
    tsIndex (.atom (.number (.rational n d hc))) = if 0 < n then 3 else 5 :=
  rfl

@[simp] theorem tsIndex_string (s : String) :
    tsIndex (.atom (.string s)) = 12 := rfl

@[simp] theorem tsIndex_char (c : UInt8) :
    tsIndex (.atom (.char c)) = 13 := rfl

@[simp] theorem tsIndex_keyword (k : Keyword) :
    tsIndex (.atom (.keyword k)) = 9 := rfl

@[simp] theorem tsIndex_symbol (s : Symbol) :
    tsIndex (.atom (.symbol s))
      = if (SExpr.atom (.symbol s)) == SExpr.t then 8 else 9 := rfl

/-- Every basic-type index is one of the fourteen. -/
theorem tsIndex_lt (v : SExpr) : tsIndex v < 14 := by
  match v with
  | .nil => decide
  | .cons a d => simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol s) => simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword k) => simp only [tsIndex_keyword]; decide
  | .atom (.string s) => simp only [tsIndex_string]; decide
  | .atom (.char c) => simp only [tsIndex_char]; decide
  | .atom (.number (.int n)) =>
      simp only [tsIndex_int]; split_ifs <;> decide
  | .atom (.number (.rational n d hc)) =>
      simp only [tsIndex_rat]; split_ifs <;> decide

/-- Is basic type `i` a member of the type-set `m`? ACL2 masks are
    INTEGERS with two's-complement complements (`-24 = ~23`), so the bit
    is read with FLOOR division — which is exactly two's-complement
    shifting on the negatives. -/
def tsMember (m : Int) (i : Nat) : Bool := (Int.fdiv m (2 ^ i)) % 2 == 1

/-- The value `v` inhabits the type-set `m`. The whole Lean-side meaning
    of an ACL2 type-set verdict. -/
def InTs (m : Int) (v : SExpr) : Prop := tsMember m (tsIndex v) = true

/-- Mask CONTAINMENT over the fourteen basic types (`m ⊆ m'`). Decidable
    by ground evaluation — the masks are always closed numerals read off
    the emission. -/
def tsSubsumedM (m m' : Int) : Bool :=
  (List.range 14).all fun i => !tsMember m i || tsMember m' i

/-- Mask INTERSECTION containment (`m1 ∩ m2 ⊆ m`) — the rule that lets
    two independent in-scope facts about the same value combine, as
    ACL2's `assume-true-false` combines the ruling tests' contributions
    into one type-alist entry. -/
def tsInter2Subsumed (m1 m2 m : Int) : Bool :=
  (List.range 14).all fun i =>
    !(tsMember m1 i && tsMember m2 i) || tsMember m i

/-! ## The algebra -/

/-- MONOTONICITY: a value in a type-set is in any superset of it. -/
theorem inTs_weaken {m m' : Int} {v : SExpr} (h : tsSubsumedM m m' = true)
    (hv : InTs m v) : InTs m' v := by
  have hmem : tsIndex v ∈ List.range 14 := List.mem_range.mpr (tsIndex_lt v)
  have hi := (List.all_eq_true.mp h) _ hmem
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
  rcases hi with h0 | h1
  · exact absurd hv (by simp only [InTs, h0]; exact Bool.noConfusion)
  · exact h1

/-- INTERSECTION: two in-scope facts about the same value combine. -/
theorem inTs_inter2 {m1 m2 m : Int} {v : SExpr}
    (h : tsInter2Subsumed m1 m2 m = true)
    (h1 : InTs m1 v) (h2 : InTs m2 v) : InTs m v := by
  have hmem : tsIndex v ∈ List.range 14 := List.mem_range.mpr (tsIndex_lt v)
  have hi := (List.all_eq_true.mp h) _ hmem
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_false_imp] at hi
  rcases hi with h0 | h3
  · exact absurd h2 (by
      simp only [InTs, h0 (by exact h1)]; exact Bool.noConfusion)
  · exact h3

/-! ## What the masks MEAN — the model's recognizer correspondences

Each lemma below is a statement about the LOGIC PRIMITIVES only: it says
what our value model's recognizers imply about the partition. The mask
each one lands in is the one ACL2's own type-set machinery uses for that
recognizer (`INTEGERP`'s emitted `:GROUND-ZERO-RECOGNIZER-TUPLES` true-ts
is 23; ACL2's `assume-true-false` splits a zero-compared `<` at
48 = negative-integer ∪ negative-ratio), and the driver additionally
CROSS-CHECKS every composed mask against ACL2's own emitted type-alist
entry for the term — a composition that does not land inside ACL2's own
verdict is refused. -/

/-- `INTEGERP` ⇒ `*ts-integer*` (23 = zero ∪ one ∪ integer>1 ∪
    negative-integer). -/
theorem inTs_integerp_true {v : SExpr}
    (h : Logic.toBool (Logic.integerp v) = true) : InTs 23 v := by
  match v with
  | .nil => simp [Logic.integerp, Logic.toBool] at h
  | .cons _ _ => simp [Logic.integerp, Logic.toBool] at h
  | .atom (.symbol _) => simp [Logic.integerp, Logic.toBool] at h
  | .atom (.keyword _) => simp [Logic.integerp, Logic.toBool] at h
  | .atom (.string _) => simp [Logic.integerp, Logic.toBool] at h
  | .atom (.char _) => simp [Logic.integerp, Logic.toBool] at h
  | .atom (.number (.rational _ _ _)) =>
      simp [Logic.integerp, Logic.toBool] at h
  | .atom (.number (.int n)) =>
      show tsMember 23 (tsIndex (.atom (.number (.int n)))) = true
      simp only [tsIndex_int]
      split_ifs <;> decide

/-- `(< v '0)` TRUE ⇒ the NEGATIVE numerics (48 = negative-integer ∪
    negative-ratio). -/
theorem inTs_lt_zero_true {v : SExpr}
    (h : Logic.toBool (Logic.lt v (.atom (.number (.int 0)))) = true) :
    InTs 48 v := by
  match v with
  | .nil => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .cons _ _ => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.symbol _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.keyword _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.string _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.char _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.number (.int n)) =>
      have hn : n < 0 := by
        by_contra hc
        rw [show Logic.lt (.atom (.number (.int n)))
              (.atom (.number (.int 0))) = SExpr.nil from by
            simp only [Logic.lt, Logic.toRat]
            exact if_neg (by omega)] at h
        exact Bool.noConfusion h
      show tsMember 48 (tsIndex (.atom (.number (.int n)))) = true
      simp only [tsIndex_int, if_neg (show ¬(n = 0) by omega),
        if_neg (show ¬(n = 1) by omega), if_neg (show ¬(1 < n) by omega)]
      decide
  | .atom (.number (.rational p q hc)) =>
      have hp : p < 0 := by
        by_contra hcc
        rw [show Logic.lt (.atom (.number (.rational p q hc)))
              (.atom (.number (.int 0))) = SExpr.nil from by
            simp only [Logic.lt, Logic.toRat]
            exact if_neg (by
              have : (0 : Int) * (q : Int) = 0 := by ring
              omega)] at h
        exact Bool.noConfusion h
      show tsMember 48 (tsIndex (.atom (.number (.rational p q hc)))) = true
      simp only [tsIndex_rat, if_neg (show ¬(0 < p) by omega)]
      decide

/-- `(< v '0)` FALSE ⇒ everything but the negative numerics
    (`-49 = ~48`). A canonical rational is never zero (`canonRat` forces
    `2 ≤ d` and `gcd = 1`), so a non-negative one is strictly
    positive. -/
theorem inTs_lt_zero_false {v : SExpr}
    (h : Logic.toBool (Logic.lt v (.atom (.number (.int 0)))) = false) :
    InTs (-49) v := by
  match v with
  | .nil => rfl
  | .cons a d =>
      show tsMember (-49) (tsIndex (.cons a d)) = true
      simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol s) =>
      show tsMember (-49) (tsIndex (.atom (.symbol s))) = true
      simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword _) => rfl
  | .atom (.string _) => rfl
  | .atom (.char _) => rfl
  | .atom (.number (.int n)) =>
      have hn : ¬ (n < 0) := by
        intro hc
        rw [show Logic.lt (.atom (.number (.int n)))
              (.atom (.number (.int 0))) = SExpr.t from by
            simp only [Logic.lt, Logic.toRat]
            exact if_pos (by omega)] at h
        exact Bool.noConfusion h
      show tsMember (-49) (tsIndex (.atom (.number (.int n)))) = true
      simp only [tsIndex_int]
      split_ifs with h0 h1 h2
      · decide
      · decide
      · decide
      · omega
  | .atom (.number (.rational p q hc)) =>
      have hq : 2 ≤ q := by
        simp only [canonRat, Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1
      have hp : ¬ (p < 0) := by
        intro hcc
        rw [show Logic.lt (.atom (.number (.rational p q hc)))
              (.atom (.number (.int 0))) = SExpr.t from by
            simp only [Logic.lt, Logic.toRat]
            exact if_pos (by
              have : (0 : Int) * (q : Int) = 0 := by ring
              omega)] at h
        exact Bool.noConfusion h
      have hp0 : p ≠ 0 := by
        intro hz
        subst hz
        simp only [canonRat, Bool.and_eq_true, decide_eq_true_eq,
          Int.natAbs_zero, Nat.gcd_zero_left, beq_iff_eq] at hc
        omega
      show tsMember (-49) (tsIndex (.atom (.number (.rational p q hc))))
        = true
      simp only [tsIndex_rat, if_pos (show 0 < p by omega)]
      decide

/-! ## What the PRIMITIVES do to a type-set

ACL2 stores NO type-prescription rule for its primitives (the fork
audit probed all 32: only 7 carry one, none of them these) — the
knowledge is Lisp code in `type-set-primitive`. The corresponding
Lean-side content is one PROVED implication per primitive the corpus
actually demands, and nothing more. -/

/-- Membership in the SINGLETON mask 16 is exactly "a negative
    integer". -/
theorem negInt_of_inTs16 {u : SExpr} (h : InTs 16 u) :
    ∃ n : Int, n < 0 ∧ u = .atom (.number (.int n)) := by
  match u with
  | .nil => simp only [InTs, tsIndex_nil] at h; exact absurd h (by decide)
  | .cons a d =>
      refine absurd h ?_
      show ¬ (tsMember 16 (tsIndex (.cons a d)) = true)
      simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol s) =>
      refine absurd h ?_
      show ¬ (tsMember 16 (tsIndex (.atom (.symbol s))) = true)
      simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword _) =>
      simp only [InTs, tsIndex_keyword] at h; exact absurd h (by decide)
  | .atom (.string _) =>
      simp only [InTs, tsIndex_string] at h; exact absurd h (by decide)
  | .atom (.char _) =>
      simp only [InTs, tsIndex_char] at h; exact absurd h (by decide)
  | .atom (.number (.rational p q hc)) =>
      refine absurd h ?_
      show ¬ (tsMember 16 (tsIndex (.atom (.number (.rational p q hc))))
        = true)
      simp only [tsIndex_rat]; split_ifs <;> decide
  | .atom (.number (.int n)) =>
      refine ⟨n, ?_, rfl⟩
      by_contra hc
      have h' : tsMember 16 (tsIndex (.atom (.number (.int n)))) = true := h
      simp only [tsIndex_int] at h'
      split_ifs at h' with h0 h1 h2
      · exact absurd h' (by decide)
      · exact absurd h' (by decide)
      · exact absurd h' (by decide)
      · omega

/-- `UNARY--` on a NEGATIVE INTEGER (16) yields a POSITIVE INTEGER
    (6 = one ∪ integer>1) — ACL2's `type-set-unary--` reflects the
    negatives onto the positives; this says our `Logic.neg` agrees. -/
theorem inTs_neg_of_negInt {u : SExpr} (h : InTs 16 u) :
    InTs 6 (Logic.neg u) := by
  obtain ⟨n, hn, rfl⟩ := negInt_of_inTs16 h
  rw [show Logic.neg (.atom (.number (.int n)))
        = .atom (.number (.int (-n))) from by
      simp only [Logic.neg, Logic.toRat, Logic.mkNumber]
      norm_num]
  show tsMember 6 (tsIndex (.atom (.number (.int (-n))))) = true
  simp only [tsIndex_int, if_neg (show ¬(-n = 0) by omega)]
  split_ifs with h1 h2
  · decide
  · decide
  · omega

/-- `DENOMINATOR` always yields a POSITIVE INTEGER (6). Unconditional:
    the value model stores rationals canonically (`canonRat` forces
    `2 ≤ d`) and completes every non-rational to `1`, so the denominator
    is `1` or an integer `> 1`. ACL2 derives the sharper `4`
    (`*ts-integer>1*`) in the context where the argument is a
    non-integer rational; landing inside its verdict is all the walk
    needs, and the driver checks exactly that. -/
theorem inTs_denominator (u : SExpr) : InTs 6 (Logic.denominator u) := by
  simp only [InTs]
  match u with
  | .nil => simp only [Logic.denominator]; rfl
  | .cons _ _ => simp only [Logic.denominator]; rfl
  | .atom (.symbol _) => simp only [Logic.denominator]; rfl
  | .atom (.keyword _) => simp only [Logic.denominator]; rfl
  | .atom (.string _) => simp only [Logic.denominator]; rfl
  | .atom (.char _) => simp only [Logic.denominator]; rfl
  | .atom (.number (.int _)) => simp only [Logic.denominator]; rfl
  | .atom (.number (.rational p q hc)) =>
      have hq : 2 ≤ q := by
        simp only [canonRat, Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1
      simp only [Logic.denominator]
      show tsMember 6 (tsIndex (.atom (.number (.int (q : Int))))) = true
      simp only [tsIndex_int, if_neg (show ¬((q : Int) = 0) by omega),
        if_neg (show ¬((q : Int) = 1) by omega),
        if_pos (show 1 < (q : Int) by omega)]
      decide

/-- `Logic.len` returns a NATURAL integer atom (both arms of its match
    build one, and the recursive arm only ever adds one). -/
theorem len_nat (v : SExpr) :
    ∃ k : Nat, Logic.len v = .atom (.number (.int (k : Int))) := by
  induction v with
  | nil => exact ⟨0, rfl⟩
  | atom _ => exact ⟨0, rfl⟩
  | cons a b _ ihb =>
    obtain ⟨k, hk⟩ := ihb
    refine ⟨k + 1, ?_⟩
    rw [show Logic.len (SExpr.cons a b)
          = .atom (.number (.int (Logic.toInt (Logic.len b) + 1))) from rfl,
        hk]
    simp only [Logic.toInt, SExpr.atom.injEq, Atom.number.injEq,
      Number.int.injEq]
    omega

/-- `LEN` always yields a NON-NEGATIVE INTEGER (7). Unconditional —
    ACL2's `LEN` is a `defun`, but the value model carries it as a
    trusted-core primitive, so it reaches the TP walk as a return-path
    PRIMITIVE (LENGTH's two leaves) rather than as a callee. ACL2's own
    emitted verdict for both leaves is exactly 7. -/
theorem inTs_len (u : SExpr) : InTs 7 (Logic.len u) := by
  obtain ⟨k, hk⟩ := len_nat u
  rw [hk]
  show tsMember 7 (tsIndex (.atom (.number (.int (k : Int))))) = true
  simp only [tsIndex_int]
  split_ifs with h0 h1 h2
  · decide
  · decide
  · decide
  · exfalso; omega

/-! ## From a type-set back to a corollary CLASS

The bridge into the TP walk: a value inside a mask the corollary class
covers satisfies the class's lifted predicate. One lemma per class, with
the containment decided on the closed masks. -/

/-- Anything inside `*ts-non-negative-integer*` (7) satisfies the lifted
    NON-NEGATIVE-INTEGER corollary — `TpCorClass.nonNegInt`'s bridge. -/
theorem nonNegIntCor_of_inTs (m : Int) (v : SExpr)
    (hm : tsSubsumedM m 7 = true) (hv : InTs m v) :
    (bif Logic.toBool (Logic.integerp v)
     then Logic.not (Logic.lt v (.atom (.number (.int 0))))
     else SExpr.nil) = SExpr.t := by
  have h7 : InTs 7 v := inTs_weaken hm hv
  have hnat : ∃ n : Nat, v = .atom (.number (.int (n : Int))) := by
    match v with
    | .nil =>
        simp only [InTs, tsIndex_nil] at h7; exact absurd h7 (by decide)
    | .cons a d =>
        refine absurd h7 ?_
        show ¬ (tsMember 7 (tsIndex (.cons a d)) = true)
        simp only [tsIndex_cons]; split_ifs <;> decide
    | .atom (.symbol s) =>
        refine absurd h7 ?_
        show ¬ (tsMember 7 (tsIndex (.atom (.symbol s))) = true)
        simp only [tsIndex_symbol]; split_ifs <;> decide
    | .atom (.keyword _) =>
        simp only [InTs, tsIndex_keyword] at h7; exact absurd h7 (by decide)
    | .atom (.string _) =>
        simp only [InTs, tsIndex_string] at h7; exact absurd h7 (by decide)
    | .atom (.char _) =>
        simp only [InTs, tsIndex_char] at h7; exact absurd h7 (by decide)
    | .atom (.number (.rational p q hc)) =>
        refine absurd h7 ?_
        show ¬ (tsMember 7 (tsIndex (.atom (.number (.rational p q hc))))
          = true)
        simp only [tsIndex_rat]; split_ifs <;> decide
    | .atom (.number (.int n)) =>
        refine ⟨n.toNat, ?_⟩
        have h' : tsMember 7 (tsIndex (.atom (.number (.int n)))) = true := h7
        simp only [tsIndex_int] at h'
        split_ifs at h' with h0 h1 h2
        · simp [h0]
        · simp [h1]
        · simp only [SExpr.atom.injEq, Atom.number.injEq, Number.int.injEq]
          omega
        · exact absurd h' (by decide)
  obtain ⟨n, rfl⟩ := hnat
  exact nonNegIntCor_of_nat n

/-! ## Type-set DISJOINTNESS — the verdict side (T1+2 sprint P3b)

ACL2's `type-set` closes an `EQUAL` (`:LHS-TS`/`:RHS-TS`) and a
RECOGNIZER (`:TRUETS`/`:FALSETS`) by comparing type-sets: two values in
DISJOINT type-sets cannot be equal, and a value outside a recognizer's
true-ts cannot satisfy it. Both directions are pure partition algebra
here; the masks themselves are always ACL2's OWN emitted numbers. -/

/-- Mask DISJOINTNESS (`m1 ∩ m2 = ∅`) over the fourteen basic types.
    Decidable by ground evaluation — the masks are closed numerals read
    off the emission. -/
def tsDisjointM (m1 m2 : Int) : Bool :=
  (List.range 14).all fun i => !(tsMember m1 i && tsMember m2 i)

/-- A value cannot inhabit two DISJOINT type-sets. -/
theorem inTs_disjoint_absurd {m1 m2 : Int} {v : SExpr}
    (h : tsDisjointM m1 m2 = true) (h1 : InTs m1 v) (h2 : InTs m2 v) :
    False := by
  have hmem : tsIndex v ∈ List.range 14 := List.mem_range.mpr (tsIndex_lt v)
  have hi := (List.all_eq_true.mp h) _ hmem
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_false_imp] at hi
  exact absurd h2 (by simp only [InTs, hi (by exact h1)]; exact Bool.noConfusion)

/-- Values in DISJOINT type-sets are unequal — ACL2's `equal/type-set-nil`
    verdict, at the value level. -/
theorem logic_equal_nil_of_ts_disjoint {m1 m2 : Int} {u v : SExpr}
    (h : tsDisjointM m1 m2 = true) (h1 : InTs m1 u) (h2 : InTs m2 v) :
    Logic.equal u v = SExpr.nil := by
  have hne : u ≠ v := by
    intro huv
    subst huv
    have hmem : tsIndex u ∈ List.range 14 := List.mem_range.mpr (tsIndex_lt u)
    have hi := (List.all_eq_true.mp h) _ hmem
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp] at hi
    exact absurd h2 (by simp only [InTs, hi (by exact h1)]; exact Bool.noConfusion)
  simp only [Logic.equal]
  exact if_neg (by simpa using hne)

/-- A CONS inhabits `*ts-cons*` (3072 = proper ∪ improper) — the model
    side of `CONSP`'s emitted `:TRUETS`. -/
theorem inTs_consp_true {v : SExpr}
    (h : Logic.toBool (Logic.consp v) = true) : InTs 3072 v := by
  match v with
  | .nil => simp [Logic.consp, Logic.toBool] at h
  | .atom _ => simp [Logic.consp, Logic.toBool] at h
  | .cons a d =>
      show tsMember 3072 (tsIndex (.cons a d)) = true
      simp only [tsIndex_cons]; split_ifs <;> decide

/-- A value in a type-set DISJOINT from `*ts-cons*` is not a cons —
    ACL2's `recognizer/false` verdict for `CONSP`, at the value level.
    The driver supplies `3072` from the step's OWN emitted `:TRUETS`. -/
theorem logic_consp_nil_of_ts_disjoint {m : Int} {v : SExpr}
    (h : tsDisjointM m 3072 = true) (hv : InTs m v) :
    Logic.consp v = SExpr.nil := by
  by_contra hc
  have ht : Logic.toBool (Logic.consp v) = true := by
    match v with
    | .nil => exact absurd rfl hc
    | .atom _ => exact absurd rfl hc
    | .cons _ _ => rfl
  have h2 := inTs_consp_true ht
  have hmem : tsIndex v ∈ List.range 14 := List.mem_range.mpr (tsIndex_lt v)
  have hi := (List.all_eq_true.mp h) _ hmem
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp] at hi
  exact absurd h2 (by simp only [InTs, hi (by exact hv)]; exact Bool.noConfusion)

/-- A value inside `*ts-integer*` IS an integer — ACL2's
    `recognizer/true` verdict for `INTEGERP`, at the value level. The
    driver supplies `23` from the step's OWN emitted `:TRUETS`. -/
theorem logic_integerp_t_of_inTs {m : Int} {v : SExpr}
    (h : tsSubsumedM m 23 = true) (hv : InTs m v) :
    Logic.integerp v = SExpr.t := by
  have h23 : InTs 23 v := inTs_weaken h hv
  match v with
  | .atom (.number (.int _)) => rfl
  | .nil => exact absurd h23 (by simp only [InTs, tsIndex_nil]; decide)
  | .cons a d =>
      refine absurd h23 ?_
      show ¬ (tsMember 23 (tsIndex (.cons a d)) = true)
      simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol s) =>
      refine absurd h23 ?_
      show ¬ (tsMember 23 (tsIndex (.atom (.symbol s))) = true)
      simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword _) =>
      exact absurd h23 (by simp only [InTs, tsIndex_keyword]; decide)
  | .atom (.string _) =>
      exact absurd h23 (by simp only [InTs, tsIndex_string]; decide)
  | .atom (.char _) =>
      exact absurd h23 (by simp only [InTs, tsIndex_char]; decide)
  | .atom (.number (.rational p q hc)) =>
      refine absurd h23 ?_
      show ¬ (tsMember 23 (tsIndex (.atom (.number (.rational p q hc))))
        = true)
      simp only [tsIndex_rat]; split_ifs <;> decide

/-! ## Further typing tests the corpus's branch facts spell -/

/-- `(< '0 v)` TRUE ⇒ the POSITIVE numerics (14 = one ∪ integer>1 ∪
    positive-ratio) — ACL2's `assume-true-false` split for a
    zero-compared `<` with the constant on the LEFT (`CLASSIFY-POS`'s
    `(< '0 N)` hypothesis). -/
theorem inTs_zero_lt_true {v : SExpr}
    (h : Logic.toBool (Logic.lt (.atom (.number (.int 0))) v) = true) :
    InTs 14 v := by
  match v with
  | .nil => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .cons _ _ => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.symbol _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.keyword _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.string _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.char _) => simp [Logic.lt, Logic.toRat, Logic.toBool] at h
  | .atom (.number (.int n)) =>
      have hn : 0 < n := by
        by_contra hc
        rw [show Logic.lt (.atom (.number (.int 0)))
              (.atom (.number (.int n))) = SExpr.nil from by
            simp only [Logic.lt, Logic.toRat]
            exact if_neg (by omega)] at h
        exact Bool.noConfusion h
      show tsMember 14 (tsIndex (.atom (.number (.int n)))) = true
      simp only [tsIndex_int, if_neg (show ¬(n = 0) by omega)]
      split_ifs with h1 h2
      · decide
      · decide
      · omega
  | .atom (.number (.rational p q hc)) =>
      have hp : 0 < p := by
        by_contra hcc
        rw [show Logic.lt (.atom (.number (.int 0)))
              (.atom (.number (.rational p q hc))) = SExpr.nil from by
            simp only [Logic.lt, Logic.toRat]
            exact if_neg (by
              have : (0 : Int) * (q : Int) = 0 := by ring
              omega)] at h
        exact Bool.noConfusion h
      show tsMember 14 (tsIndex (.atom (.number (.rational p q hc)))) = true
      simp only [tsIndex_rat, if_pos hp]
      decide

/-- A REFUTED `(ZP v)` ⇒ a POSITIVE INTEGER (6 = one ∪ integer>1) — the
    model side of ACL2's `ZP-COMPOUND-RECOGNIZER`, whose negative branch
    is `(and (integerp v) (< 0 v))`. Consumed only where that rune is
    CITED by the step (the BUG-023 anchor). -/
theorem inTs_zp_false {v : SExpr}
    (hb : Logic.toBool (Logic.zp v) = false) : InTs 6 v := by
  have h : Logic.zp v = SExpr.nil := (Logic.toBool_eq_false _).mp hb
  match v with
  | .nil => exact absurd h (by decide)
  | .cons _ _ => exact absurd h (by simp [Logic.zp, Logic.toInt])
  | .atom (.symbol _) => exact absurd h (by simp [Logic.zp, Logic.toInt])
  | .atom (.keyword _) => exact absurd h (by simp [Logic.zp, Logic.toInt])
  | .atom (.string _) => exact absurd h (by simp [Logic.zp, Logic.toInt])
  | .atom (.char _) => exact absurd h (by simp [Logic.zp, Logic.toInt])
  | .atom (.number (.rational p q hc)) =>
      exact absurd h (by simp [Logic.zp, Logic.toInt])
  | .atom (.number (.int n)) =>
      have hn : 0 < n := by
        by_contra hc
        simp only [Logic.zp, Logic.toInt, if_pos (show n ≤ 0 by omega)] at h
        exact absurd h (by decide)
      show tsMember 6 (tsIndex (.atom (.number (.int n)))) = true
      simp only [tsIndex_int, if_neg (show ¬(n = 0) by omega)]
      split_ifs with h1 h2
      · decide
      · decide
      · omega

/-- CASE SPLIT on an `IF`'s test at the VALUE level: a type-set holding
    in BOTH branches holds of the `cond`. The recognizer-under-`IF`
    walk's composition step (`:ARG-LEAVES`). -/
theorem inTs_cond {m : Int} {b : Bool} {x y : SExpr}
    (hx : b = true → InTs m x) (hy : b = false → InTs m y) :
    InTs m (cond b x y) := by
  cases b
  · exact hy rfl
  · exact hx rfl

/-- A value in a type-set DISJOINT from `(< v '0)`'s TRUE type-set (48)
    makes that test NIL — the `.isNil` direction of the same algebra
    (`CLASSIFY-POS`'s outer `(< N '0)` if-test, which ACL2 resolves by
    type-set and records only as an `:IF-TEST-FALSE` marker with a
    `fake-rune-for-type-set` justification). -/
theorem logic_lt_zero_nil_of_ts_disjoint {m : Int} {v : SExpr}
    (h : tsDisjointM m 48 = true) (hv : InTs m v) :
    Logic.lt v (.atom (.number (.int 0))) = SExpr.nil := by
  by_contra hc
  have ht : Logic.toBool (Logic.lt v (.atom (.number (.int 0)))) = true := by
    simp only [Logic.lt] at hc ⊢
    split_ifs at hc ⊢ <;> simp_all
  exact inTs_disjoint_absurd h hv (inTs_lt_zero_true ht)

/-- A value inside `*ts-non-negative-integer*` (7) IS a natural —
    `NATP`'s emitted `:TRUETS`, at the value level. -/
theorem logic_natp_t_of_inTs {m : Int} {v : SExpr}
    (h : tsSubsumedM m 7 = true) (hv : InTs m v) :
    Logic.natp v = SExpr.t := by
  have h7 : InTs 7 v := inTs_weaken h hv
  match v with
  | .nil => exact absurd h7 (by simp only [InTs, tsIndex_nil]; decide)
  | .cons a d =>
      refine absurd h7 ?_
      show ¬ (tsMember 7 (tsIndex (.cons a d)) = true)
      simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol s) =>
      refine absurd h7 ?_
      show ¬ (tsMember 7 (tsIndex (.atom (.symbol s))) = true)
      simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword _) =>
      exact absurd h7 (by simp only [InTs, tsIndex_keyword]; decide)
  | .atom (.string _) =>
      exact absurd h7 (by simp only [InTs, tsIndex_string]; decide)
  | .atom (.char _) =>
      exact absurd h7 (by simp only [InTs, tsIndex_char]; decide)
  | .atom (.number (.rational p q hc)) =>
      refine absurd h7 ?_
      show ¬ (tsMember 7 (tsIndex (.atom (.number (.rational p q hc))))
        = true)
      simp only [tsIndex_rat]; split_ifs <;> decide
  | .atom (.number (.int n)) =>
      have h' : tsMember 7 (tsIndex (.atom (.number (.int n)))) = true := h7
      simp only [tsIndex_int] at h'
      have hn : 0 ≤ n := by
        split_ifs at h' with h0 h1 h2
        · omega
        · omega
        · omega
        · exact absurd h' (by decide)
      simp only [Logic.natp, if_pos (show n ≥ 0 by omega)]

/-- A TRUE `(ZP v)` puts `v` outside the positive integers (`-7 = ~6`) —
    the model side of `ZP-COMPOUND-RECOGNIZER`'s emitted `:TRUETS`. -/
theorem inTs_zp_true {v : SExpr}
    (h : Logic.toBool (Logic.zp v) = true) : InTs (-7) v := by
  match v with
  | .nil => show tsMember (-7) (tsIndex SExpr.nil) = true; decide
  | .cons a d =>
      show tsMember (-7) (tsIndex (.cons a d)) = true
      simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol s) =>
      show tsMember (-7) (tsIndex (.atom (.symbol s))) = true
      simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword k) =>
      show tsMember (-7) (tsIndex (.atom (.keyword k))) = true
      simp only [tsIndex_keyword]; decide
  | .atom (.string str) =>
      show tsMember (-7) (tsIndex (.atom (.string str))) = true
      simp only [tsIndex_string]; decide
  | .atom (.char c) =>
      show tsMember (-7) (tsIndex (.atom (.char c))) = true
      simp only [tsIndex_char]; decide
  | .atom (.number (.rational p q hc)) =>
      show tsMember (-7) (tsIndex (.atom (.number (.rational p q hc)))) = true
      simp only [tsIndex_rat]; split_ifs <;> decide
  | .atom (.number (.int n)) =>
      have hn : n ≤ 0 := by
        by_contra hcn
        rw [show Logic.zp (.atom (.number (.int n))) = SExpr.nil from by
              simp only [Logic.zp, Logic.toInt]
              exact if_neg (by omega)] at h
        exact Bool.noConfusion h
      show tsMember (-7) (tsIndex (.atom (.number (.int n)))) = true
      simp only [tsIndex_int]
      split_ifs with h0 h1 h2
      · decide
      · omega
      · omega
      · decide

/-- A value INSIDE `(ZP v)`'s TRUE type-set (`-7 = ~6`, i.e. anything
    that is not a positive integer) makes `ZP` `'T` —
    `ZP-COMPOUND-RECOGNIZER`'s `recognizer/true` verdict, at the value
    level. The driver supplies `-7` from the step's OWN emitted
    `:TRUETS`. Demand-driven: `CD2-BOUND`'s `Subgoal 1`. -/
theorem logic_zp_t_of_inTs {m : Int} {v : SExpr}
    (h : tsSubsumedM m (-7) = true) (hv : InTs m v) :
    Logic.zp v = SExpr.t := by
  have h7 : InTs (-7) v := inTs_weaken h hv
  match v with
  | .nil => rfl
  | .cons _ _ => rfl
  | .atom (.symbol _) => rfl
  | .atom (.keyword _) => rfl
  | .atom (.string _) => rfl
  | .atom (.char _) => rfl
  | .atom (.number (.rational _ _ _)) => rfl
  | .atom (.number (.int n) ) =>
      have hn : n ≤ 0 := by
        by_contra hcn
        have h' : tsMember (-7) (tsIndex (.atom (.number (.int n)))) = true :=
          h7
        simp only [tsIndex_int] at h'
        split_ifs at h' with h0 h1 h2
        · omega
        · exact absurd h' (by decide)
        · exact absurd h' (by decide)
        · omega
      simp only [Logic.zp, Logic.toInt]
      exact if_pos (by omega)

/-- A value in a type-set DISJOINT from `(ZP v)`'s TRUE type-set (`-7`)
    makes `ZP` NIL — `ZP-COMPOUND-RECOGNIZER`'s `recognizer/false`
    verdict, at the value level. -/
theorem logic_zp_nil_of_ts_disjoint {m : Int} {v : SExpr}
    (h : tsDisjointM m (-7) = true) (hv : InTs m v) :
    Logic.zp v = SExpr.nil := by
  by_contra hc
  have ht : Logic.toBool (Logic.zp v) = true := by
    simp only [Logic.zp] at hc ⊢
    split_ifs at hc ⊢ <;> simp_all
  exact inTs_disjoint_absurd h hv (inTs_zp_true ht)

/-- A value inside `*ts-integer*` (23) IS an integer atom. -/
theorem int_of_inTs23 {v : SExpr} (h : InTs 23 v) :
    ∃ n : Int, v = .atom (.number (.int n)) := by
  match v with
  | .atom (.number (.int n)) => exact ⟨n, rfl⟩
  | .nil => exact absurd h (by simp only [InTs, tsIndex_nil]; decide)
  | .cons a d =>
      refine absurd h ?_
      show ¬ (tsMember 23 (tsIndex (.cons a d)) = true)
      simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol sy) =>
      refine absurd h ?_
      show ¬ (tsMember 23 (tsIndex (.atom (.symbol sy))) = true)
      simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword _) =>
      exact absurd h (by simp only [InTs, tsIndex_keyword]; decide)
  | .atom (.string _) =>
      exact absurd h (by simp only [InTs, tsIndex_string]; decide)
  | .atom (.char _) =>
      exact absurd h (by simp only [InTs, tsIndex_char]; decide)
  | .atom (.number (.rational p q hc)) =>
      refine absurd h ?_
      show ¬ (tsMember 23 (tsIndex (.atom (.number (.rational p q hc))))
        = true)
      simp only [tsIndex_rat]; split_ifs <;> decide

/-- ACL2's `type-set-binary-+` on the INTEGER cell: the integers are
    closed under `+`. The model side — the driver supplies each
    summand's mask from ACL2's OWN emitted data and cross-checks the
    result against the step's `:TYPESET`. Corpus witness: the
    arithmetic-countdown trio's `(INTEGERP (BINARY-+ '-1 N)) ⇒ 'T`. -/
theorem inTs_plus_int {a b : SExpr} (ha : InTs 23 a) (hb : InTs 23 b) :
    InTs 23 (Logic.plus a b) := by
  obtain ⟨n, rfl⟩ := int_of_inTs23 ha
  obtain ⟨m, rfl⟩ := int_of_inTs23 hb
  rw [show Logic.plus (.atom (.number (.int n))) (.atom (.number (.int m)))
        = .atom (.number (.int (n + m))) from by
      simp only [Logic.plus, Logic.toRat, Logic.mkNumber]
      norm_num]
  show tsMember 23 (tsIndex (.atom (.number (.int (n + m))))) = true
  simp only [tsIndex_int]; split_ifs <;> decide

/-- Mask `6` = `*ts-one*` ∪ `*ts-integer>1*` — the type-set
    `ZP-COMPOUND-RECOGNIZER`'s REFUTED branch gives its argument — is
    exactly the integers `≥ 1`. -/
theorem int_ge_one_of_inTs6 {v : SExpr} (h : InTs 6 v) :
    ∃ n : Int, v = .atom (.number (.int n)) ∧ 1 ≤ n := by
  match v with
  | .atom (.number (.int n)) =>
      refine ⟨n, rfl, ?_⟩
      by_contra hlt
      refine absurd h ?_
      show ¬ (tsMember 6 (tsIndex (.atom (.number (.int n)))) = true)
      simp only [tsIndex_int]
      split_ifs with h1 h2 h3
      · decide
      · exact absurd h2 (by omega)
      · exact absurd h3 (by omega)
      · decide
  | .nil => exact absurd h (by simp only [InTs, tsIndex_nil]; decide)
  | .cons a d =>
      refine absurd h ?_
      show ¬ (tsMember 6 (tsIndex (.cons a d)) = true)
      simp only [tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol sy) =>
      refine absurd h ?_
      show ¬ (tsMember 6 (tsIndex (.atom (.symbol sy))) = true)
      simp only [tsIndex_symbol]; split_ifs <;> decide
  | .atom (.keyword _) =>
      exact absurd h (by simp only [InTs, tsIndex_keyword]; decide)
  | .atom (.string _) =>
      exact absurd h (by simp only [InTs, tsIndex_string]; decide)
  | .atom (.char _) =>
      exact absurd h (by simp only [InTs, tsIndex_char]; decide)
  | .atom (.number (.rational p q hc)) =>
      refine absurd h ?_
      show ¬ (tsMember 6 (tsIndex (.atom (.number (.rational p q hc))))
        = true)
      simp only [tsIndex_rat]; split_ifs <;> decide

/-- ACL2's `type-set-binary-+` at the QUOTED CONSTANT `-1` — the SHARP
    cell `*ts-one*` exists in ACL2's partition to make possible, and the
    one the coarse integer cell (`inTs_plus_int`, 23 + 23 ⊆ 23) loses:
    an argument in mask `6` (the integers `≥ 1`) lands in mask `7`
    (`*ts-zero*` ∪ `6` — the integers `≥ 0`).

    Model side only, as always: the driver supplies the summand's mask
    from ACL2's OWN emitted data. Corpus witness: `COUNT-DOWN` /
    `MY-EVENP`'s termination, where ACL2 resolves the `NFIX` body's
    inner if-test `(< (BINARY-+ '-1 N) '0)` FALSE off exactly this
    type-set (emitted `:TYPESET 7` under `ZP-COMPOUND-RECOGNIZER`). -/
theorem inTs_plus_neg_one {a : SExpr} (ha : InTs 6 a) :
    InTs 7 (Logic.plus (.atom (.number (.int (-1)))) a) := by
  obtain ⟨n, rfl, hn⟩ := int_ge_one_of_inTs6 ha
  rw [show Logic.plus (.atom (.number (.int (-1))))
          (.atom (.number (.int n)))
        = .atom (.number (.int (-1 + n))) from by
      simp only [Logic.plus, Logic.toRat, Logic.mkNumber]
      norm_num]
  show tsMember 7 (tsIndex (.atom (.number (.int (-1 + n))))) = true
  simp only [tsIndex_int]
  split_ifs with h1 h2 h3
  · decide
  · decide
  · decide
  · exact absurd hn (by omega)

end ACL2.Replay
