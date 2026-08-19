/-! # The sorting mirror spec — the ACL2 sorting book in idiomatic Lean

A MIRROR is a Lean-idiomatic theorem — no ACL2 notions whatsoever —
mirroring a property proved in an ACL2 book. This file is the sorting
book's mirror SPEC: the book's four sorting algorithms and their
correctness properties, restated in pure idiomatic Lean. No `SExpr`,
no `lexorder`, no `evalOpt`, no imports from the replay machinery —
in fact no imports at all: the file elaborates from Lean's core
prelude alone (`just check-mirrors-pure` gates the layer). A user of
these theorems knows nothing about ACL2 and never needs to.

**The definitions are our own, on purpose.** Every construct that
mirrors a book function (`isort` = `ISORT`, `relMode` = `REL`,
`howMany` = `HOW-MANY`, …) is an own definition, recursing the way
the book's function recurses, and every name is chosen to collide
with no core/Std/Batteries/Mathlib name (`Tests/MirrorNameCheck.lean`
lints this at build time). If the spec spoke library vocabulary —
Mathlib's `Perm`, `List.count` — its properties could be closed by
library lemmas instead of the ACL2 replay, which would defeat the
product.

**The properties are named `Prop`s, proved elsewhere.** The fifteen
`Prop`s at the bottom stand in a BIJECTION with the sorting corpus's
RESULT-TIER theorems — what each book proves about its own top-level
function (the four sorts, `PERM`, the permutation witness), as
against internal lemmas about helpers. Every result-tier book theorem
has exactly one `Prop`, and every `Prop` names exactly one book
theorem in its docstring; each becomes a `theorem` in
`ACL2Lean/MirrorProofs/Sorting.lean`, proved BY REPLAYING the ACL2
proof. Nothing here proves a property and there is no `sorry`: an
unproved target is a named `Prop`, never a fake theorem.

Two classes of book theorems have no `Prop` of their own, by design:

* **Type absorption.** The corpus's `TRUE-LISTP` theorems and
  hypotheses are absorbed exactly by the type `List α`, and its
  `BOOLEANP` facts by a relation's being a `Prop` — the faithful
  rendering of an untyped logic in a typed one, not a gap.
* **The equisort capstone** is an instantiation device — stated over
  `encapsulate`d constrained sorter symbols and consumed only via
  `:functional-instance` — and is mirrored by its instances, the
  three `*_is_isort` `Prop`s below. Record:
  `docs/notes/2026-08-18_sorting-spec-reshape.md`, Part 8.

**Disclosed in full: two book theorems are proved natively here.**
Lean's kernel demands `bsort`'s measure decrease BEFORE `bsort` may
exist as a definition, so the decrease cannot arrive by replay — and
the decrease is, statement for statement, the book's own lemmas:
`howManySmaller_bnext` is `HOW-MANY-SMALLER-BNEXT` and
`howManyBadPairs_bnext_lt` is `HOW-MANY-BAD-PAIRS-BNEXT`
(`acl2/books/sorting/bsort.lisp`), the same obligations ACL2
discharges at `BSORT`'s admission. These two are OUTSIDE the fifteen
via-replay `Prop`s and are the whole of that class in this file; the
governing ruling is `docs/notes/2026-08-11_thin-lean-boundary.md`.

Design history — the spec reshape that fixed the bijection, and the
rulings this file used to recite — lives in
`docs/notes/2026-08-18_sorting-spec-reshape.md` and
`docs/plans/2026-08-18_close-out-arc-charter.md`, not here. -/

namespace ACL2Lean.Sorting

universe u

/-- The order interface for mirror specs — our own minimal class,
    deliberately NOT Mathlib's `LinearOrder` (this file imports
    nothing; see the header). A user type instantiates it with four
    small proofs; the instances the replay reaches are backed by
    kernel-checked theorems about ACL2's own order
    (`LexorderOrder.lean`). -/
class TotalOrder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  decLE : DecidableRel (α := α) (· ≤ ·)

attribute [instance_reducible, instance] TotalOrder.decLE

/-- Strict order, derived: `a < b` iff not `b ≤ a`. -/
instance (priority := low) {α : Type u} [TotalOrder α] : LT α :=
  ⟨fun a b => ¬ b ≤ a⟩

instance {α : Type u} [TotalOrder α] : DecidableRel (α := α) (· < ·) :=
  fun _ _ => instDecidableNot

/-- Decidable equality, derived from the order: `a = b` exactly when
    `a ≤ b` and `b ≤ a` (antisymmetry). It is `local` and low-priority
    on purpose: it lets the book's `REL` below decide
    `(not (equal i j))` without `qsort` acquiring a `[DecidableEq α]`
    binder, and never competes with a `DecidableEq` instance a
    downstream file already has. -/
local instance (priority := low) decEqOfOrder {α : Type u} [TotalOrder α] :
    DecidableEq α := fun a b =>
  if h : a ≤ b ∧ b ≤ a then
    isTrue (TotalOrder.le_antisymm h.1 h.2)
  else
    isFalse fun hab => by
      subst hab
      exact h ⟨TotalOrder.le_refl a, TotalOrder.le_refl a⟩

/-! ## The objects of study -/

section Structural
variable {α : Type u}

/-- Every other element, starting with the first (the book's `EVENS` —
    its merge sort splits by ALTERNATION, not by halving). -/
def evens : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: t => a :: evens t

/-- Termination support for `msort`: `evens` never lengthens a list. -/
theorem length_evens_le : ∀ (xs : List α), (evens xs).length ≤ xs.length
  | [] => by simp [evens]
  | [a] => by simp [evens]
  | _ :: _ :: t => by
    have h := length_evens_le t
    simp [evens]; omega

/-- The odd-position elements: `evens` of the tail (the book's
    `(EVENS (CDR X))`). -/
def odds : List α → List α
  | [] => []
  | _ :: t => evens t

end Structural

variable {α : Type u} [TotalOrder α]

/-- Ordered: each element ≤ its successor (the book's `ORDEREDP`, as
    an adjacent chain). -/
def Ordered : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a ≤ b ∧ Ordered (b :: t)

/-- Insert into an ordered list (the book's `INSERT`). -/
def insertOrd (a : α) : List α → List α
  | [] => [a]
  | b :: t => if a ≤ b then a :: b :: t else b :: insertOrd a t

/-- Insertion sort (the book's `ISORT`). -/
def isort : List α → List α
  | [] => []
  | a :: t => insertOrd a (isort t)

/-- Merge two ordered lists (the book's `MERGE2`). -/
def merge2 : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | a :: xs, b :: ys =>
    if a ≤ b then a :: merge2 xs (b :: ys) else b :: merge2 (a :: xs) ys
  termination_by xs ys => xs.length + ys.length

/-- Merge sort by alternation split (the book's `MSORT`). -/
def msort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    merge2 (msort (evens (a :: b :: t))) (msort (odds (a :: b :: t)))
  termination_by xs => xs.length
  decreasing_by
  · have h := length_evens_le t
    simp [evens]; omega
  · have h := length_evens_le (b :: t)
    simp only [List.length_cons] at h
    simp [odds]; omega

/-- The comparison MODE — `REL`'s `FN` argument, which the book passes
    as one of the quoted symbols `'LT`, `'LTE`, `'GT`, `'GTE`. All
    four are here because the book's `REL` has four cases (`QSORT`
    itself uses only `'LT` and `'GTE`). -/
inductive RelMode where
  /-- the book's `'LT`. -/
  | lt
  /-- the book's `'LTE`. -/
  | lte
  /-- the book's `'GT`. -/
  | gt
  /-- the book's `'GTE` (also `REL`'s `otherwise` branch). -/
  | gte

/-- One comparison verdict (the book's `REL`: `(rel fn i j)` is
    `(and (lexorder i j) (not (equal i j)))` for `'LT`, `(lexorder i j)`
    for `'LTE`, `(and (lexorder j i) (not (equal i j)))` for `'GT`, and
    `(lexorder j i)` otherwise). -/
def relMode [DecidableEq α] (fn : RelMode) (i j : α) : Bool :=
  match fn with
  | .lt => decide (i ≤ j) && !decide (i = j)
  | .lte => decide (i ≤ j)
  | .gt => decide (j ≤ i) && !decide (i = j)
  | .gte => decide (j ≤ i)

/-- Keep the elements the mode relates to the pivot (the book's
    `FILTER`: `(filter fn x e)` — a mode, the list, and the pivot
    element `e`, keeping each `a` with `(rel fn a e)`). -/
def filterRel [DecidableEq α] (fn : RelMode) (e : α) : List α → List α
  | [] => []
  | a :: t =>
    if relMode fn a e then a :: filterRel fn e t else filterRel fn e t

/-- Termination support for `qsort`: filtering never lengthens a
    list. -/
theorem length_filterRel_le [DecidableEq α] (fn : RelMode) (e : α) :
    ∀ (xs : List α), (filterRel fn e xs).length ≤ xs.length
  | [] => Nat.le_refl _
  | a :: t => by
    simp only [filterRel]
    split
    · exact Nat.succ_le_succ (length_filterRel_le fn e t)
    · exact Nat.le_succ_of_le (length_filterRel_le fn e t)

/-- Quicksort, first-element pivot (the book's `QSORT`: the pivot is
    `(car x)` and the filtered list is `(cdr x)`, in the modes `'LT` and
    `'GTE`). -/
def qsort : List α → List α
  | [] => []
  | p :: t =>
    qsort (filterRel .lt p t) ++ p :: qsort (filterRel .gte p t)
  termination_by xs => xs.length
  decreasing_by
  · simp only [List.length_cons]
    exact Nat.lt_succ_of_le (length_filterRel_le _ _ t)
  · simp only [List.length_cons]
    exact Nat.lt_succ_of_le (length_filterRel_le _ _ t)

/-- One bubble pass: swap adjacent out-of-order pairs, left to right
    (the book's `BNEXT`). -/
def bnext : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    if a ≤ b then a :: bnext (b :: t) else b :: bnext (a :: t)
  termination_by xs => xs.length

/-- How many elements of the list the order puts strictly below `e`
    (the book's `HOW-MANY-SMALLER`: skip the ones equal to `e`, count
    the ones at-or-below it). One half of the book's bubble measure. -/
def howManySmaller [DecidableEq α] (e : α) : List α → Nat
  | [] => 0
  | a :: t =>
    if e = a then howManySmaller e t
    else if a ≤ e then 1 + howManySmaller e t
    else howManySmaller e t

/-- The bad-pair count (the book's `BNEXT-SIZE`), the measure that
    justifies `BSORT`'s recursion: summed over the list, how many of
    the elements after it each element is out of order with. -/
def howManyBadPairs [DecidableEq α] : List α → Nat
  | [] => 0
  | a :: t => howManySmaller a t + howManyBadPairs t

/-! The facts below are `bsort`'s termination argument — the measure
decrease Lean's kernel demands before the book's fixpoint recursion is
a definition at all. Two of them are the book's own theorems, proved
natively under the disclosure in the header; the other two
(`howManySmaller_cons`, `howManyBadPairs_bnext_le`) are our own support
lemmas with no book correspondent. -/

/-- Unfolding form of `howManySmaller` at a cons (support lemma, no
    book correspondent). -/
theorem howManySmaller_cons [DecidableEq α] (e a : α) (t : List α) :
    howManySmaller e (a :: t) =
      (if e = a then 0 else if a ≤ e then 1 else 0) + howManySmaller e t := by
  by_cases h : e = a
  · simp [howManySmaller, h]
  · by_cases h2 : a ≤ e <;> simp [howManySmaller, h, h2]

/-- A bubble pass MOVES elements without changing how many of them the
    order puts below `e` (the book's `HOW-MANY-SMALLER-BNEXT`; proved
    natively — see the header disclosure). -/
theorem howManySmaller_bnext [DecidableEq α] (e : α) (xs : List α) :
    howManySmaller e (bnext xs) = howManySmaller e xs := by
  fun_induction bnext xs with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b t h ih => simp [howManySmaller_cons, ih]
  | case4 a b t h ih => simp [howManySmaller_cons, ih]; omega

/-- A bubble pass never INCREASES the bad-pair count (support lemma,
    no book correspondent). -/
theorem howManyBadPairs_bnext_le [DecidableEq α] (xs : List α) :
    howManyBadPairs (bnext xs) ≤ howManyBadPairs xs := by
  fun_induction bnext xs with
  | case1 => exact Nat.le_refl _
  | case2 a => exact Nat.le_refl _
  | case3 a b t h ih =>
    simp only [howManyBadPairs, howManySmaller_bnext] at ih ⊢
    omega
  | case4 a b t h ih =>
    simp only [howManyBadPairs, howManySmaller_bnext,
      howManySmaller_cons] at ih ⊢
    have hba : b ≤ a := (TotalOrder.le_total a b).resolve_left h
    have hne : ¬ b = a := fun e => h (e ▸ TotalOrder.le_refl a)
    simp [hba, hne, h] at ih ⊢
    omega

/-- THE DECREASE — a bubble pass that CHANGES the list strictly
    decreases the bad-pair count (the book's
    `HOW-MANY-BAD-PAIRS-BNEXT`, which is exactly what admits `BSORT`
    there; proved natively — see the header disclosure). -/
theorem howManyBadPairs_bnext_lt [DecidableEq α] (xs : List α) :
    bnext xs ≠ xs → howManyBadPairs (bnext xs) < howManyBadPairs xs := by
  fun_induction bnext xs with
  | case1 => exact fun h => absurd rfl h
  | case2 a => exact fun h => absurd rfl h
  | case3 a b t h ih =>
    intro hne
    have hb : bnext (b :: t) ≠ b :: t := by
      intro e; exact hne (by rw [e])
    have ih' := ih hb
    simp only [howManyBadPairs, howManySmaller_bnext] at ih' ⊢
    omega
  | case4 a b t h ih =>
    intro _
    have hle := howManyBadPairs_bnext_le (a :: t)
    simp only [howManyBadPairs, howManySmaller_bnext,
      howManySmaller_cons] at hle ⊢
    have hba : b ≤ a := (TotalOrder.le_total a b).resolve_left h
    have hne : ¬ b = a := fun e => h (e ▸ TotalOrder.le_refl a)
    have hne' : ¬ a = b := fun e => hne e.symm
    simp [hba, hne, hne', h] at hle ⊢
    omega

/-- Bubble sort: bubble passes until a pass changes nothing (the book's
    `BSORT` — `(if (equal (bnext x) x) x (bsort (bnext x)))`, whose
    measure is the bad-pair count). -/
def bsort (xs : List α) : List α :=
  if bnext xs = xs then xs else bsort (bnext xs)
  termination_by howManyBadPairs xs
  decreasing_by exact howManyBadPairs_bnext_lt xs ‹_›

/-- Multiplicity of an element (the book's `HOW-MANY`). -/
def howMany [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | b :: t => (if a = b then 1 else 0) + howMany a t

/-- Membership test (the book's `MEMB`). -/
def memb [DecidableEq α] (a : α) : List α → Bool
  | [] => false
  | b :: t => if a = b then true else memb a t

/-- Remove the FIRST occurrence (the book's `RM`). -/
def rm [DecidableEq α] (e : α) : List α → List α
  | [] => []
  | a :: t => if e = a then t else a :: rm e t

/-- Permutation, the book's way (`PERM`): every head occurs in the
    other list, and the tails-after-removal are permutations. Its
    equivalence with multiplicity agreement is a THEOREM of the book
    (`CONVERT-PERM-TO-HOW-MANY`), not a library import. -/
def Permuted [DecidableEq α] : List α → List α → Prop
  | [], [] => True
  | [], _ :: _ => False
  | a :: xs, ys => memb a ys = true ∧ Permuted xs (rm a ys)

/-- The permutation counterexample witness (the book's
    `PERM-COUNTER-EXAMPLE`): walk `xs`, removing each element from `ys`
    as it is found; the first element of `xs` that is not found is the
    witness, and if every one is found the head of what is left of `ys`
    is. The fallback arm at `[], []` returns `default` — the price of a
    TOTAL Lean rendering of an untyped ACL2 function, standing in for
    ACL2's `(car nil)` and reached on exactly the pairs ACL2 returns
    `(car nil)` on: the permuting ones. `permWitness_complete` below is
    insensitive to the fallback value. -/
def permWitness [DecidableEq α] [Inhabited α] : List α → List α → α
  | [], [] => default
  | [], y :: _ => y
  | a :: xs, ys => if memb a ys then permWitness xs (rm a ys) else a

/-! ## The target properties — the definition of done

Fifteen `Prop`s, one per RESULT-TIER theorem of the ACL2 sorting
corpus, in the corpus's own order. Each names its book theorem; each
is a `theorem`, proved via replay, in
`ACL2Lean/MirrorProofs/Sorting.lean`. -/

/-- ISORT orders (the book's `ORDEREDP-ISORT`). -/
def isort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (isort xs)

/-- ISORT preserves multiplicity (the book's `HOW-MANY-ISORT`: the
    count of every element is unchanged by the sort). -/
def isort_howMany (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (a : α) (xs : List α), howMany a (isort xs) = howMany a xs

/-- MSORT orders (`ORDEREDP-MSORT`). -/
def msort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (msort xs)

/-- MSORT preserves multiplicity (`HOW-MANY-MSORT`). -/
def msort_howMany (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (a : α) (xs : List α), howMany a (msort xs) = howMany a xs

/-- QSORT orders (`ORDEREDP-QSORT`). -/
def qsort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (qsort xs)

/-- QSORT preserves multiplicity (`HOW-MANY-QSORT`). -/
def qsort_howMany (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (a : α) (xs : List α), howMany a (qsort xs) = howMany a xs

/-- QSORT permutes (`PERM-QSORT` — the one sort the corpus states in
    `PERM` terms as well as in multiplicity terms). -/
def qsort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (qsort xs) xs

/-- BSORT orders (`ORDEREDP-BSORT`). -/
def bsort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (bsort xs)

/-- BSORT preserves multiplicity (`HOW-MANY-BSORT`). -/
def bsort_howMany (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (a : α) (xs : List α), howMany a (bsort xs) = howMany a xs

/-- An ordered permutation is unique — the book's `ORDERED-PERMS`,
    which states it as the EQUIVALENCE `(EQUAL A B) = (PERM A B)` for
    ordered `A`, `B`, and that is the shape here: for ordered lists,
    equality and permutation are the same relation. -/
def ordered_perm_unique (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α), Ordered xs → Ordered ys → (xs = ys ↔ Permuted xs ys)

/-- Permutation is an equivalence relation (the book's
    `PERM-IS-AN-EQUIVALENCE`, ACL2's `defequiv` content: reflexive,
    symmetric, transitive). -/
def permuted_equivalence (α : Type u) [DecidableEq α] : Prop :=
  ∀ (xs ys zs : List α),
    Permuted xs xs ∧
    (Permuted xs ys → Permuted ys xs) ∧
    (Permuted xs ys → Permuted ys zs → Permuted xs zs)

/-- The witness is complete (the book's `CONVERT-PERM-TO-HOW-MANY`):
    two lists are permutations EXACTLY WHEN their multiplicities agree
    at the ONE element the witness picks out — the whole point of the
    witness, since it turns a `∀`-quantified count check into a single
    one. Order-free, like the book theorem: the binders are
    `[DecidableEq α]` and (for the witness's fallback arm)
    `[Inhabited α]`, and no order. (The corpus's
    `PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS` is this
    same statement under hypotheses the types absorb — the step the
    book proves it from, not a second result.) -/
def permWitness_complete (α : Type u) [DecidableEq α]
    [Inhabited α] : Prop :=
  ∀ (xs ys : List α),
    (Permuted xs ys ↔
      howMany (permWitness xs ys) xs = howMany (permWitness xs ys) ys)

/-- MSORT is ISORT (the book's `MSORT-IS-ISORT` capstone). -/
def msort_is_isort (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), msort xs = isort xs

/-- QSORT is ISORT (`QSORT-IS-ISORT`). -/
def qsort_is_isort (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), qsort xs = isort xs

/-- BSORT is ISORT (`BSORT-IS-ISORT`). -/
def bsort_is_isort (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), bsort xs = isort xs

end ACL2Lean.Sorting
