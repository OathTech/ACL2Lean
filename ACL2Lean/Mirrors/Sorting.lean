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
book's four algorithms in Lean-native dress — polymorphic over our own
`TotalOrder`, recursing the way the ACL2 book's functions recurse
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

VOCABULARY PRACTICE (Mike, 2026-08-13 — disambiguate hard, as
design practice): body constructs that MIRROR A BOOK FUNCTION are
OWN-DEFINITIONS (`filterRel` = FILTER, `rm` = RM — their iso squares
arrive with their mirrors); pure-Lean idiom is FULLY QUALIFIED
(`List.find?`, `List.length`) or an own device (`iterate`); operator
notation (`++`, `∈`) is permitted as unambiguous; names are
collision-linted (Tests/MirrorNameCheck).

SELF-CONTAINED VOCABULARY (deliberate): the predicates below —
`Ordered`, `howMany`, `Permuted`, the witness — are OUR OWN idiomatic
definitions, not Mathlib/Batteries notions. Mathlib proves plenty
about ITS `Perm` and order theory; if the spec spoke that vocabulary,
the properties could be closed by library lemmas instead of the ACL2
replay, which would defeat the product (the import route working
end-to-end). `TotalOrder` is our own minimal interface class for the
order parameter; no external order theory is leaned on when proving
these properties — the proofs arrive via replay.

THE NAMING RULE (Mike, 2026-08-13 — the naming pass): a mirror spec
name must have ZERO overlap with a core/Std/Batteries/Mathlib name,
neither at the root nor DOT-NOTATION-REACHABLE on a type the spec
uses (`List.merge`, `List.mergeSort`, `List.insertionSort`,
`List.count`, `List.mergeSort_perm`, `Nat.count`, `Option.merge` were
the seven real overlaps this file carried). The reason is the
vocabulary rule one level up (`Imported/SimGen.lean`): a shared name
is the channel by which a library lemma — or a reader — can be
mistaken for mirror content that must come via replay. The names are
therefore taken from the ACL2 BOOK, Lean-cased (`isort`, `msort`,
`qsort`, `bsort`, `bnext`, `merge2`, `insertOrd`, `Ordered`,
`howMany`); the uppercase ACL2 rune names in the docstrings below are
the cross-reference to the source book and are the point.
`Tests/MirrorNameCheck.lean` enforces the rule over this namespace at
build time. -/

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

/-- Every other element, starting with the first (the book's `EVENS` —
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

/-- The odd-position elements: `evens` of the tail (own
    pattern-match — the book's `(EVENS (CDR X))`). -/
def odds : List α → List α
  | [] => []
  | _ :: t => evens t

end Structural

variable {α : Type u} [TotalOrder α]

/-- Ordered: each element ≤ its successor (the book's `ORDEREDP`,
    idiomatically — an adjacent chain; our own definition, so no
    library lemma speaks about it directly). -/
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

/-- Keep the elements satisfying the test (the book's `FILTER` — a
    book function, so an own-definition per the vocabulary practice;
    its iso square arrives with the sorting mirrors). -/
def filterRel (keep : α → Bool) : List α → List α
  | [] => []
  | a :: t => if keep a then a :: filterRel keep t else filterRel keep t

theorem length_filterRel_le (keep : α → Bool) :
    ∀ (xs : List α), (filterRel keep xs).length ≤ xs.length
  | [] => Nat.le_refl _
  | a :: t => by
    simp only [filterRel]
    split
    · exact Nat.succ_le_succ (length_filterRel_le keep t)
    · exact Nat.le_succ_of_le (length_filterRel_le keep t)

/-- Quicksort, first-element pivot (the book's `QSORT`). -/
def qsort : List α → List α
  | [] => []
  | p :: t =>
    qsort (filterRel (fun x => decide (x < p)) t)
      ++ p :: qsort (filterRel (fun x => !decide (x < p)) t)
  termination_by xs => xs.length
  decreasing_by
  · simp only [List.length_cons]
    exact Nat.lt_succ_of_le (length_filterRel_le _ t)
  · simp only [List.length_cons]
    exact Nat.lt_succ_of_le (length_filterRel_le _ t)

/-- One bubble pass: swap adjacent out-of-order pairs, left to right
    (the book's `BNEXT`). -/
def bnext : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    if a ≤ b then a :: bnext (b :: t) else b :: bnext (a :: t)
  termination_by xs => xs.length

/-- Bubble sort: `length`-many passes reach the fixpoint (the book's
    `BSORT`, whose measure is the bad-pair count). -/
def bsort (xs : List α) : List α :=
  (List.range xs.length).foldl (fun acc _ => bnext acc) xs

/-- Multiplicity of an element (the book's `HOW-MANY`; our own
    definition). -/
def howMany [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | b :: t => (if a = b then 1 else 0) + howMany a t

/-- Permutation, the book's way (`PERM`): every head occurs in the
    other list, and the tails-after-erasure are permutations. Our own
    definition — its equivalence with multiplicity agreement is a
    THEOREM of the book (`CONVERT-PERM-TO-HOW-MANY`), not a library
    import. -/
def Permuted [DecidableEq α] : List α → List α → Prop
  | [], ys => ys = []
  | a :: xs, ys => a ∈ ys ∧ Permuted xs (ys.erase a)

/-- The permutation counterexample witness (the book's
    `PERM-COUNTER-EXAMPLE`): an element whose multiplicities differ,
    if one exists. -/
def permWitness [DecidableEq α] (xs ys : List α) : Option α :=
  List.find? (fun a => howMany a xs != howMany a ys) (xs ++ ys)

/-! ## The target properties — the definition of done

Each `Prop` below reflects a theorem the ACL2 sorting book proves.
The buildout is DONE for sorting when every one is a `theorem`
proved via replay. -/

/-- ISORT orders (the book's `ORDEREDP-ISORT`). -/
def isort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (isort xs)

/-- ISORT permutes (the book's `HOW-MANY-ISORT`, in its idiomatic
    permutation form — multiplicity preservation and permutation
    coincide). -/
def isort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (isort xs) xs

/-- MSORT orders (`ORDEREDP-MSORT`). -/
def msort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (msort xs)

/-- MSORT permutes (`HOW-MANY-MSORT`). -/
def msort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (msort xs) xs

/-- QSORT orders (`ORDEREDP-QSORT`). -/
def qsort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (qsort xs)

/-- QSORT permutes (`HOW-MANY-QSORT`). -/
def qsort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (qsort xs) xs

/-- BSORT orders (`ORDEREDP-BSORT`; the book's route goes through
    `ORDEREDP-WHEN-BNEXT-CONSTANT` — a bubble-pass fixpoint is ordered —
    and the bad-pair progress measure). -/
def bsort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (bsort xs)

/-- BSORT permutes (`HOW-MANY-BSORT`). -/
def bsort_perm (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs : List α), Permuted (bsort xs) xs

/-- An ordered permutation is unique — the book's `ORDERED-PERMS`
    content, and the lemma that powers every equivalence below. -/
def ordered_perm_unique (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α), Ordered xs → Ordered ys → Permuted xs ys → xs = ys

/-- All four sorts agree (the book's `MSORT-IS-ISORT`,
    `QSORT-IS-ISORT`, `BSORT-IS-ISORT` capstones). -/
def sorts_agree (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α),
    msort xs = isort xs ∧
    qsort xs = isort xs ∧
    bsort xs = isort xs

/-- The abstract capstone (the book's `SORTS-EQUIVALENT` /
    encapsulate content): ANY function that orders and permutes IS
    insertion sort. -/
def sorter_unique (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (f : List α → List α),
    (∀ xs, Ordered (f xs)) → (∀ xs, Permuted (f xs) xs) →
    ∀ xs, f xs = isort xs

/-- Permutation is exactly multiplicity agreement (the book's
    `CONVERT-PERM-TO-HOW-MANY` capstone; Mathlib states the same fact
    about ITS notions as `List.perm_iff_count` — the book's proof
    arrives independently, via replay). -/
def perm_iff_howMany (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α), Permuted xs ys ↔ ∀ a, howMany a xs = howMany a ys

/-- The witness is complete (the book's
    `PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE`): no witness means
    permutation, and any witness really is a counterexample. -/
def permWitness_complete (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α),
    (permWitness xs ys = none ↔ Permuted xs ys) ∧
    ∀ a ∈ permWitness xs ys, howMany a xs ≠ howMany a ys

end ACL2Lean.Sorting
