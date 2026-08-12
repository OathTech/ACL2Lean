/-! # THE MIRRORS — sorting (the product; the buildout's north star)

A MIRROR is a Lean-idiomatic theorem — no ACL2 notions whatsoever —
that mirrors a property proved in an ACL2 book. This file is the
sorting book's mirror spec: the top-level definitions and target
properties in PURE IDIOMATIC LEAN, with **no
ACL2 taint whatsoever** — no `SExpr`, no `lexorder`, no `evalOpt`, no
imports from the replay machinery — in fact NO IMPORTS AT ALL: this
file elaborates from Lean's core prelude alone, and
`just check-mirrors-pure` pins the layer's imports to Std/Batteries
at most (Mathlib excluded — mirror content arrives via replay, never
via library lemmas). A user of these theorems knows nothing about
ACL2 and never needs to.

The DEFINITIONS below are the user's objects of study: the sorting
book's four algorithms in Lean-native dress — polymorphic over a
`LinearOrder`, recursing the way the ACL2 book's functions recurse
(that structural agreement is what the machinery-side isomorphisms
will consume; the definitions remain fully idiomatic on their own
terms). The PROPERTIES are stated as named `Prop`s — the definition
of done for the buildout: each becomes a `theorem` when its proof
arrives VIA ACL2 REPLAY (the two-category workflow: user definitions
→ isomorphism to the ACL2-like layer → replay → these theorems).
No proof-of-property lives in this file and no `sorry` anywhere: an
unproved target is a named `Prop`, never a fake theorem. (The only
proofs here are the termination measures Lean's kernel demands for
the definitions to exist.)

SELF-CONTAINED VOCABULARY (deliberate): the predicates below —
`Sorted`, `count`, `Permuted`, the witness — are OUR OWN idiomatic
definitions, not Mathlib/Batteries notions. Mathlib proves plenty
about ITS `Perm` and order theory; if the spec spoke that vocabulary,
the properties could be closed by library lemmas instead of the ACL2
replay, which would defeat the product (the import route working
end-to-end). `LinearOrder` is used ONLY as the interface class for
the order parameter; its lemma library is not to be leaned on when
proving these properties — the proofs arrive via replay. -/

namespace ACL2Lean.Sorting

universe u

/-- The order interface for mirror specs — our own minimal class,
    deliberately NOT Mathlib's `LinearOrder`: the mirror layer helps
    itself to no external order theory (and this file imports nothing
    at all — core prelude only). Instances for replay-reachable
    fragments are backed by the interpreter's CORE-LOGIC theorems
    (e.g. `LexorderOrder.lean` — our model provably satisfies ACL2's
    ground-zero order axioms); a user type instantiates it with four
    small proofs. -/
class TotalOrder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  decLE : DecidableRel (α := α) (· ≤ ·)

attribute [instance] TotalOrder.decLE

/-- Strict order, derived: `a < b` iff not `b ≤ a`. -/
instance (priority := low) {α : Type u} [TotalOrder α] : LT α :=
  ⟨fun a b => ¬ b ≤ a⟩

instance {α : Type u} [TotalOrder α] : DecidableRel (α := α) (· < ·) :=
  fun _ _ => instDecidableNot

/-! ## The objects of study -/

section Structural
variable {α : Type u}

/-- Every other element, starting with the first (the book's `evens` —
    its merge sort splits by ALTERNATION, not by halving). -/
def evens : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: t => a :: evens t

theorem length_evens_le : ∀ (xs : List α), (evens xs).length ≤ xs.length
  | [] => by simp [evens]
  | [a] => by simp [evens]
  | _ :: _ :: t => by
    have h := length_evens_le t
    simp [evens]; omega

/-- The odd-position elements: `evens` of the tail. -/
def odds (xs : List α) : List α := evens xs.tail

end Structural

variable {α : Type u} [TotalOrder α]

/-- Sorted: each element ≤ its successor (the book's `orderedp`,
    idiomatically — an adjacent chain; our own definition, so no
    library lemma speaks about it directly). -/
def Sorted : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a ≤ b ∧ Sorted (b :: t)

/-- Insert into a sorted list (the book's `insert`). -/
def insertSorted (a : α) : List α → List α
  | [] => [a]
  | b :: t => if a ≤ b then a :: b :: t else b :: insertSorted a t

/-- Insertion sort (the book's `isort`). -/
def insertionSort : List α → List α
  | [] => []
  | a :: t => insertSorted a (insertionSort t)

/-- Merge two sorted lists (the book's `merge2`). -/
def merge : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | a :: xs, b :: ys =>
    if a ≤ b then a :: merge xs (b :: ys) else b :: merge (a :: xs) ys
  termination_by xs ys => xs.length + ys.length

/-- Merge sort by alternation split (the book's `msort`). -/
def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    merge (mergeSort (evens (a :: b :: t))) (mergeSort (odds (a :: b :: t)))
  termination_by xs => xs.length
  decreasing_by
  · have h := length_evens_le t
    simp [evens]; omega
  · have h := length_evens_le (b :: t)
    simp only [List.length_cons] at h
    simp [odds]; omega

/-- Quicksort, first-element pivot (the book's `qsort`). -/
def quickSort : List α → List α
  | [] => []
  | p :: t =>
    quickSort (t.filter fun x => decide (x < p))
      ++ p :: quickSort (t.filter fun x => !decide (x < p))
  termination_by xs => xs.length
  decreasing_by
  · simp only [List.length_unattach, List.length_cons]
    refine Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) ?_)
    simp [List.length_attach]
  · simp only [List.length_unattach, List.length_cons]
    refine Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) ?_)
    simp [List.length_attach]

/-- One bubble pass: swap adjacent out-of-order pairs, left to right
    (the book's `bnext`). -/
def bubblePass : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    if a ≤ b then a :: bubblePass (b :: t) else b :: bubblePass (a :: t)
  termination_by xs => xs.length

/-- Bubble sort: `length`-many passes reach the fixpoint (the book's
    `bsort`, whose measure is the bad-pair count). -/
def bubbleSort (xs : List α) : List α :=
  (List.range xs.length).foldl (fun acc _ => bubblePass acc) xs

/-- Multiplicity of an element (the book's `how-many`; our own
    definition). -/
def count [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | b :: t => (if a = b then 1 else 0) + count a t

/-- Permutation, the book's way (`perm`): every head occurs in the
    other list, and the tails-after-erasure are permutations. Our own
    definition — its equivalence with multiplicity agreement is a
    THEOREM of the book (`CONVERT-PERM-TO-HOW-MANY`), not a library
    import. -/
def Permuted [DecidableEq α] : List α → List α → Prop
  | [], ys => ys = []
  | a :: xs, ys => a ∈ ys ∧ Permuted xs (ys.erase a)

/-- The permutation counterexample witness (the book's
    `perm-counter-example`): an element whose multiplicities differ,
    if one exists. -/
def permWitness [DecidableEq α] (xs ys : List α) : Option α :=
  (xs ++ ys).find? fun a => count a xs != count a ys

/-! ## The target properties — the definition of done

Each `Prop` below reflects a theorem the ACL2 sorting book proves.
The buildout is DONE for sorting when every one is a `theorem`
proved via replay. -/

/-- ISORT sorts (the book's `ORDEREDP-ISORT`). -/
def insertionSort_sorted (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Sorted (insertionSort xs)

/-- ISORT permutes (the book's `HOW-MANY-ISORT`, in its idiomatic
    `Perm` form — multiplicity preservation and permutation coincide). -/
def insertionSort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (insertionSort xs) xs

/-- MSORT sorts (`ORDEREDP-MSORT`). -/
def mergeSort_sorted (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Sorted (mergeSort xs)

/-- MSORT permutes (`HOW-MANY-MSORT`). -/
def mergeSort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (mergeSort xs) xs

/-- QSORT sorts (`ORDEREDP-QSORT`). -/
def quickSort_sorted (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Sorted (quickSort xs)

/-- QSORT permutes (`HOW-MANY-QSORT`). -/
def quickSort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (quickSort xs) xs

/-- BSORT sorts (`ORDEREDP-BSORT`; the book's route goes through
    `ORDEREDP-WHEN-BNEXT-CONSTANT` — a bubble-pass fixpoint is sorted —
    and the bad-pair progress measure). -/
def bubbleSort_sorted (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Sorted (bubbleSort xs)

/-- BSORT permutes (`HOW-MANY-BSORT`). -/
def bubbleSort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (bubbleSort xs) xs

/-- A sorted permutation is unique — the book's `ORDERED-PERMS`
    content, and the lemma that powers every equivalence below. -/
def sorted_perm_unique (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α), Sorted xs → Sorted ys → Permuted xs ys → xs = ys

/-- All four sorts agree (the book's `MSORT-IS-ISORT`,
    `QSORT-IS-ISORT`, `BSORT-IS-ISORT` capstones). -/
def sorts_agree (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α),
    mergeSort xs = insertionSort xs ∧
    quickSort xs = insertionSort xs ∧
    bubbleSort xs = insertionSort xs

/-- The abstract capstone (the book's `SORTS-EQUIVALENT` /
    encapsulate content): ANY function that sorts and permutes IS
    insertion sort. -/
def sortingFunction_unique (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (f : List α → List α),
    (∀ xs, Sorted (f xs)) → (∀ xs, Permuted (f xs) xs) →
    ∀ xs, f xs = insertionSort xs

/-- Permutation is exactly multiplicity agreement (the book's
    `CONVERT-PERM-TO-HOW-MANY` capstone; Mathlib states the same fact
    as `List.perm_iff_count` — the book's proof arrives independently,
    via replay). -/
def perm_iff_counts (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α), Permuted xs ys ↔ ∀ a, count a xs = count a ys

/-- The witness is complete (the book's
    `PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE`): no witness means
    permutation, and any witness really is a counterexample. -/
def permWitness_complete (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α),
    (permWitness xs ys = none ↔ Permuted xs ys) ∧
    ∀ a ∈ permWitness xs ys, count a xs ≠ count a ys

end ACL2Lean.Sorting
