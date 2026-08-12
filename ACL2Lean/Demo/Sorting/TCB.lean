import ACL2Lean.Lexorder
import Batteries.Data.List.Basic

/-! # THE DEMO'S TCB — the definitions you must read

**Part 1 of the demo (`docs/demo/1-tcb.md`); the trust base is this
folder.**

Every headline in `Statements.lean` is a proposition about the ordinary
Lean functions defined HERE — `isortL`, `msortL`, `qsortL`, `merge2L`,
`evensL`, `insertL`, `bnextL`, `pceL`, `orderedpRec`, `LexSorted`, …
They are plain recursive definitions over `SExpr` (ACL2's value
universe: `nil`, an atom, or a `cons`) and `lexorderB` (ACL2's built-in
total order on that universe, as a `Bool`). Read them and satisfy
yourself they are the functions YOU mean — exactly as you would for any
Lean development. That is the whole obligation this file carries.

There is NO evaluator here, no `World`, no proof log, no replay: this
module's imports are the value core alone (`ACL2Lean.Lexorder` →
`Logic` → `Syntax`, plus `List.IsChain`), pinned by
`scripts/check-trust-imports.sh`.
-/

open ACL2

namespace ACL2.Lifting

/-- The 2-ary chain fold: `p` holds of every adjacent pair. -/
def chain2Rec (p : SExpr → SExpr → Bool) : List SExpr → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => p a b && chain2Rec p (b :: t)

end ACL2.Lifting

namespace ACL2.Worlds.Sorting

open ACL2.Lifting

/-! ## The LEXORDER Bool kit

`lexorder` (the trusted-core primitive, Lexorder.lean) is two-valued;
`lexorderB` is its Bool reading, and the bridge lets the chain2
schematic consume LEXORDER as its comparison. -/

/-- The Bool reading of the two-valued `lexorder`. -/
def lexorderB (x y : SExpr) : Bool := lexorder x y == SExpr.t

/-! ## ORDEREDP: the chain2 instance -/

/-- The native reading of ORDEREDP: every adjacent pair is
    lexorder-related. -/
abbrev orderedpRec (xs : List SExpr) : Bool := chain2Rec lexorderB xs

/-! ## The isort book: `insert` / `isort` -/

/-- `insert`'s native reading: ordered insertion by `lexorderB`. -/
def insertL (e : SExpr) : List SExpr → List SExpr
  | [] => [e]
  | a :: t => bif lexorderB e a then e :: a :: t else a :: insertL e t

/-- `isort`'s native reading: insertion sort by `lexorderB`. -/
def isortL : List SExpr → List SExpr
  | [] => []
  | a :: t => insertL a (isortL t)

/-! ## The REL / ALL-REL kit (qsort's comparison dispatch) -/

def symV (s : String) : SExpr := .atom (.symbol { name := s })

/-- The NATIVE reading of one REL verdict — an ordinary Lean match on the
    four comparison modes, in `lexorderB`/`==` vocabulary only (the mirror
    criterion: no exec function in a mirror statement). -/
def relL (fv a e : SExpr) : Bool :=
  if fv == symV "LT" then lexorderB a e && !(a == e)
  else if fv == symV "LTE" then lexorderB a e
  else if fv == symV "GT" then lexorderB e a && !(a == e)
  else lexorderB e a

/-- The native reading of ALL-REL: every element is `relL`-related to
    `ev`. -/
def allRelL (fv ev : SExpr) (xs : List SExpr) : Bool :=
  xs.all (fun a => relL fv a ev)

/-! ## The FILTER kit -/

/-- The native reading of FILTER: `List.filter` by the `relL` verdict. -/
def filterL (fv ev : SExpr) (xs : List SExpr) : List SExpr :=
  xs.filter (fun a => relL fv a ev)

/-- Strict lexorder: `≤` and not equal. -/
def lexLtB (a e : SExpr) : Bool := lexorderB a e && !(a == e)

/-! ## The msort book: `merge2` / `evens` / `msort` -/

/-- The native merge: Lean's ordinary two-list merge by `lexorderB`. -/
def merge2L : List SExpr → List SExpr → List SExpr
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | a :: xs, b :: ys =>
    bif lexorderB a b then a :: merge2L xs (b :: ys)
    else b :: merge2L (a :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- The native evens: every other element, starting at the head. -/
def evensL : List SExpr → List SExpr
  | [] => []
  | a :: t => a :: evensL t.tail
termination_by l => l.length
decreasing_by
  cases t with
  | nil => simp
  | cons b t' => simp only [List.tail_cons, List.length_cons]; omega

/-- The evens split halves the length (rounding up). -/
theorem evensL_length : ∀ l : List SExpr,
    (evensL l).length = (l.length + 1) / 2
  | [] => by simp [evensL]
  | [_] => by simp [evensL]
  | _ :: _ :: t => by
    have := evensL_length t
    simp only [evensL, List.tail_cons, List.length_cons, this]
    omega
termination_by l => l.length

/-- The native merge sort. -/
def msortL (xs : List SExpr) : List SExpr :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    merge2L (msortL (evensL (a :: b :: t))) (msortL (evensL (b :: t)))
termination_by xs.length
decreasing_by
  · rw [evensL_length]; simp; omega
  · rw [evensL_length]; simp; omega

/-! ## The qsort book: `qsort` itself -/

/-- The native quicksort. -/
def qsortL (xs : List SExpr) : List SExpr :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    qsortL ((b :: t).filter (fun c => relL (symV "LT") c a))
      ++ a :: qsortL ((b :: t).filter (fun c => relL (symV "GTE") c a))
termination_by xs.length
decreasing_by
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-! ## PERM-COUNTER-EXAMPLE — the qsort flagship's witness -/

/-- The NATIVE counterexample witness: walk `xs`, erasing each element
    from `ys` as it is matched; the first element of `xs` that `ys`
    cannot match IS the witness, and when `xs` is exhausted the witness
    is `ys`'s head (`nil` when both are). Self-contained (mirror
    criterion: `List` vocabulary only). -/
def pceL : List SExpr → List SExpr → SExpr
  | [], ys => ys.headD SExpr.nil
  | x :: xs, ys => bif ys.contains x then pceL xs (ys.erase x) else x

/-! ## The bsort book: the bubble pass and its measure -/

/-- The NATIVE bubble pass over Lean lists — self-contained (mirror
    criterion: `lexorderB` only, no evaluator vocabulary). -/
def bnextL : List SExpr → List SExpr
  | [] => []
  | [x] => [x]
  | x1 :: x2 :: rest =>
    bif lexorderB x1 x2 then x1 :: bnextL (x2 :: rest)
    else x2 :: bnextL (x1 :: rest)
termination_by l => l.length

/-- The NATIVE count of the elements strictly below `e` — self-contained
    (mirror criterion: `lexorderB` and `List` vocabulary only). -/
def howManySmallerL (e : SExpr) : List SExpr → Nat
  | [] => 0
  | a :: t =>
    bif e == a then howManySmallerL e t
    else bif lexorderB a e then 1 + howManySmallerL e t
      else howManySmallerL e t

/-- The NATIVE bubble measure: for each element, how many of the
    elements AFTER it are strictly below it. -/
def bnextSizeL : List SExpr → Nat
  | [] => 0
  | a :: t => howManySmallerL a t + bnextSizeL t

end ACL2.Worlds.Sorting

namespace ACL2.Imported.Mirrors

/-! ## The idiomatic `List.IsChain` reading (mirror criterion 1):
sortedness in Mathlib vocabulary — `IsChain (lexorderB · · = true)`,
adjacent-pairs order over the imported total order (LexorderOrder.lean
proves it reflexive/antisymmetric/transitive/total). -/

/-- Sortedness, idiomatically. -/
abbrev LexSorted (xs : List SExpr) : Prop :=
  xs.IsChain (fun a b => Worlds.Sorting.lexorderB a b = true)

end ACL2.Imported.Mirrors
