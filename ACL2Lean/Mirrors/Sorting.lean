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
the definitions to exist — including `bsort`'s bad-pair decrease, the
same obligation ACL2 discharges at `BSORT`'s admission — plus the
decidable-equality derivation `decEqOfOrder` — see its docstring.)

VOCABULARY PRACTICE (Mike, 2026-08-13 — disambiguate hard, as
design practice): body constructs that MIRROR A BOOK FUNCTION are
OWN-DEFINITIONS (`relMode` = REL, `filterRel` = FILTER, `memb` = MEMB,
`rm` = RM, `howManySmaller` = HOW-MANY-SMALLER, `howManyBadPairs` =
BNEXT-SIZE — their iso squares arrive with their mirrors); pure-Lean
idiom is FULLY QUALIFIED (`List.find?`, `List.length`) or an own
device; operator notation (`++`) is permitted as unambiguous; names are
collision-linted (Tests/MirrorNameCheck).

THE BIJECTION INVARIANT — the rule that decides what belongs in the
target-property section at the bottom of this file. The `Prop`s there
stand in a BIJECTION with the ACL2 sorting corpus's RESULT-TIER
theorems: every result-tier book theorem has EXACTLY ONE `Prop`, and
every `Prop` names EXACTLY ONE book theorem in its docstring. The
RESULT TIER is what each book proves about its OWN TOP-LEVEL function
— the four sorts, `PERM`, the permutation witness, the equisort
capstone — as against the internal lemmas about helper functions
(`BNEXT`, `MERGE2`, `EVENS`, `RM`, `MEMB`, `FILTER`, `ALL-REL`,
`TLFIX`), which are steps inside those proofs and not results. So the
section states nothing the books do not prove, and leaves nothing they
prove at that tier unstated; a `Prop` with no book theorem behind it is
a statement the replay could never deliver, and a book result with no
`Prop` is a hole in the definition of done.

THE TYPE-ABSORBED CLASS — the one place a book theorem legitimately
has no `Prop`, because Lean's TYPES already carry it. The corpus's
`TRUE-LISTP-ISORT` / `-MSORT` / `-QSORT` / `-BSORT` / `-BNEXT` / `-RM`
say the result is a proper list, which here is the type `List α` the
definitions return; the `BOOLEANP` conjunct of `PERM-IS-AN-EQUIVALENCE`
says the relation is two-valued, which here is `Permuted`'s being a
`Prop`. Absorbing those into the type discipline is the faithful
rendering of an untyped logic in a typed one, not a gap — and each
absorption is noted in one clause on the `Prop` that carries the rest
of its book.

THE INSTANTIATION-DEVICE CLASS — the second place a result-tier book
theorem legitimately has no `Prop` of its own, because its Lean-facing
content arrives through its INSTANCES. The equisort book's
`STRONG-SSORTFN1-IS-SSORTFN2` and `WEAK-SORTFN1-IS-SORTFN2` are stated
over that book's `encapsulate`d CONSTRAINED SORTER SYMBOLS
(`ssortfn1`/`ssortfn2`, `sortfn1`/`sortfn2`) — symbols with no
definition, introduced solely so the capstone can be instantiated —
and downstream the corpus consumes them EXCLUSIVELY through
`:functional-instance`, which is how `sorts-equivalent` mints
`MSORT-IS-ISORT`, `QSORT-IS-ISORT` and `BSORT-IS-ISORT`. Those three
ARE the book's external face and each has its `Prop` below, so the
capstone's content is fully represented here; a `Prop` for the
capstone itself would quantify over an arbitrary Lean function, which
no `:functional-instance` can be carried back to (there is no
construction taking an arbitrary Lean function to an ACL2 world). The
device is mirrored by its instances, which is what the device is for.

CLOSEST IDIOMATIC LEAN (Mike, 2026-08-14): a mirror is what someone
would write as a reasonably close Lean analog of the ACL2 theorem —
step (1) of a two-step use, step (2) being ordinary Lean reasoning
from it to the theorem the user actually wants. CLOSENESS TO THE BOOK
BEATS maximal Lean-idiom polish. That ruling is why `FILTER` is
rendered below the way the book writes it — a MODE (`REL`'s `FN`
argument: `'LT`/`'LTE`/`'GT`/`'GTE`) and a PIVOT ELEMENT — and not as
the Lean-idiomatic predicate closure it carried until 2026-08-14.

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
`howMany`, and — with the 2026-08-14 FILTER re-render — `relMode`,
`RelMode`, `filterRel`, where the bare book names `REL`/`Rel` and
`FILTER`/`filter` are both taken by the libraries the linter sees; and
`memb`, `rm`, `howManySmaller`, `howManyBadPairs` — the last named for
the book's own lemma `HOW-MANY-BAD-PAIRS-BNEXT` about the function
`BNEXT-SIZE` it renders);
the uppercase ACL2 rune names in the docstrings below are
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

/-- Decidable EQUALITY, derived from the order: `a = b` exactly when
    `a ≤ b` and `b ≤ a` (antisymmetry), and `≤` is decidable — the same
    bundling Lean's own `LinearOrder`-style interfaces carry.

    It is `local` (and low priority) ON PURPOSE. It exists so the book's
    `REL` below can spell `(not (equal i j))` as a decision of `i = j`
    without `qsort` acquiring a `[DecidableEq α]` binder: the target
    `Prop`s at the bottom of this file take the order alone, exactly as
    they did before the 2026-08-14 FILTER re-render, and `local` keeps
    the derivation from competing with any `DecidableEq` instance a
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

/-- The comparison MODE — `REL`'s `FN` argument, which the book passes
    as one of the quoted symbols `'LT`, `'LTE`, `'GT`, `'GTE`. All four
    are here because the book's `REL` has four cases; that `QSORT` uses
    only two of them (`'LT` and `'GTE`) is the book's business, not the
    mirror's. -/
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
    `(lexorder j i)` otherwise). A book function, so an own-definition
    per the vocabulary practice. -/
def relMode [DecidableEq α] (fn : RelMode) (i j : α) : Bool :=
  match fn with
  | .lt => decide (i ≤ j) && !decide (i = j)
  | .lte => decide (i ≤ j)
  | .gt => decide (j ≤ i) && !decide (i = j)
  | .gte => decide (j ≤ i)

/-- Keep the elements the mode relates to the pivot (the book's
    `FILTER`: `(filter fn x e)` — a MODE, the list, and the PIVOT
    element `e`, keeping each `a` with `(rel fn a e)`). A book function,
    so an own-definition per the vocabulary practice; its iso square
    arrives with the sorting mirrors. -/
def filterRel [DecidableEq α] (fn : RelMode) (e : α) : List α → List α
  | [] => []
  | a :: t =>
    if relMode fn a e then a :: filterRel fn e t else filterRel fn e t

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

/-- How many elements of the list the order puts strictly BELOW `e` (the
    book's `HOW-MANY-SMALLER`: skip the ones equal to `e`, count the ones
    at-or-below it). A book function, so an own-definition per the
    vocabulary practice; one half of the book's bubble measure. -/
def howManySmaller [DecidableEq α] (e : α) : List α → Nat
  | [] => 0
  | a :: t =>
    if e = a then howManySmaller e t
    else if a ≤ e then 1 + howManySmaller e t
    else howManySmaller e t

/-- The BAD-PAIR COUNT — the book's `BNEXT-SIZE`, the measure that
    justifies `BSORT`'s recursion: summed over the list, how many of the
    elements after it each element is out of order with. -/
def howManyBadPairs [DecidableEq α] : List α → Nat
  | [] => 0
  | a :: t => howManySmaller a t + howManyBadPairs t

/-! The three facts below are `bsort`'s TERMINATION ARGUMENT — the
measure decrease Lean's kernel demands before the book's fixpoint
recursion is a definition at all (the same obligation ACL2 discharges
at `BSORT`'s admission, where it is the book's own lemma
`HOW-MANY-BAD-PAIRS-BNEXT`). They are about OUR OWN definitions and
prove no target property; every `Prop` at the bottom of this file still
arrives via replay. -/

theorem howManySmaller_cons [DecidableEq α] (e a : α) (t : List α) :
    howManySmaller e (a :: t) =
      (if e = a then 0 else if a ≤ e then 1 else 0) + howManySmaller e t := by
  by_cases h : e = a
  · simp [howManySmaller, h]
  · by_cases h2 : a ≤ e <;> simp [howManySmaller, h, h2]

/-- A bubble pass MOVES elements without changing how many of them the
    order puts below `e`. -/
theorem howManySmaller_bnext [DecidableEq α] (e : α) (xs : List α) :
    howManySmaller e (bnext xs) = howManySmaller e xs := by
  fun_induction bnext xs with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b t h ih => simp [howManySmaller_cons, ih]
  | case4 a b t h ih => simp [howManySmaller_cons, ih]; omega

/-- A bubble pass never INCREASES the bad-pair count. -/
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
    decreases the bad-pair count (the book's `HOW-MANY-BAD-PAIRS-BNEXT`,
    which is exactly what admits `BSORT` there). -/
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

/-- Multiplicity of an element (the book's `HOW-MANY`; our own
    definition). -/
def howMany [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | b :: t => (if a = b then 1 else 0) + howMany a t

/-- Membership test (the book's `MEMB`). A book function, so an
    own-definition per the vocabulary practice. -/
def memb [DecidableEq α] (a : α) : List α → Bool
  | [] => false
  | b :: t => if a = b then true else memb a t

/-- Remove the FIRST occurrence (the book's `RM`). A book function, so
    an own-definition per the vocabulary practice. -/
def rm [DecidableEq α] (e : α) : List α → List α
  | [] => []
  | a :: t => if e = a then t else a :: rm e t

/-- Permutation, the book's way (`PERM`): every head occurs in the
    other list, and the tails-after-removal are permutations. Our own
    definition — its equivalence with multiplicity agreement is a
    THEOREM of the book (`CONVERT-PERM-TO-HOW-MANY`), not a library
    import. -/
def Permuted [DecidableEq α] : List α → List α → Prop
  | [], [] => True
  | [], _ :: _ => False
  | a :: xs, ys => memb a ys = true ∧ Permuted xs (rm a ys)

/-- The permutation counterexample witness (the book's
    `PERM-COUNTER-EXAMPLE`), as the book writes it: walk `xs`, removing
    each element from `ys` as it is found; the FIRST element of `xs`
    that is not found is the witness, and if every one is found the
    head of what is left of `ys` is. The book's function returns a
    VALUE, never an option, which is why this one does too.

    The `(CAR Y)` arm DESTRUCTURES `ys`, exactly as ACL2's `(CAR Y)`
    dispatches on `(CONSP Y)` — the same access-pattern rendering
    `Permuted` above carries for `(IF (CONSP Y) 'NIL 'T)`.

    **THE JUNK ARM.** At `xs = ys = []` — and at NO other input — the
    value is `Inhabited.default`: this type's stand-in for ACL2's
    `(car nil)`, carrying no information about either list. It is the
    one place where a TOTAL Lean rendering of an untyped ACL2 function
    must invent a value, and it is harmless to the property below,
    which holds for ANY witness on that input (both sides of its `Iff`
    are true there). The function stays total and stays exactly as the
    book writes it.

    The junk arm is also what decides WHICH ELEMENT TYPE the property
    below is proved at: a type whose `default` is the same junk value
    ACL2 has. `Option α` is that type — its `default` is `none` — which
    is why `permWitness_complete`'s theorem is instantiated at
    `Option Int` rather than `Int` (Mike's ruling, 2026-08-18). -/
def permWitness [DecidableEq α] [Inhabited α] : List α → List α → α
  | [], [] => default
  | [], y :: _ => y
  | a :: xs, ys => if memb a ys then permWitness xs (rm a ys) else a

/-! ## The target properties — the definition of done

FIFTEEN `Prop`s, one per RESULT-TIER theorem of the ACL2 sorting
corpus, in the corpus's own order (`isort`, `msort`, `qsort`, `bsort`,
`ordered-perms`, `perm`, `convert-perm-to-how-many`,
`sorts-equivalent`). Each names its book theorem; the bijection
invariant, the type-absorbed class and the instantiation-device class
are stated in the file header. The buildout is DONE for sorting when
every one is a `theorem` proved via replay. -/

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

/-- BSORT orders (`ORDEREDP-BSORT`; the book's route goes through
    `ORDEREDP-WHEN-BNEXT-CONSTANT` — a bubble-pass fixpoint is ordered —
    and the bad-pair progress measure). -/
def bsort_ordered (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), Ordered (bsort xs)

/-- BSORT preserves multiplicity (`HOW-MANY-BSORT`). -/
def bsort_howMany (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (a : α) (xs : List α), howMany a (bsort xs) = howMany a xs

/-- An ordered permutation is unique — the book's `ORDERED-PERMS`,
    which states it as the EQUIVALENCE `(EQUAL A B) = (PERM A B)` for
    ordered `A`, `B`, and that is the shape here: for ordered lists,
    equality and permutation are the same relation. (The book's two
    `TRUE-LISTP` hypotheses are type-absorbed.) -/
def ordered_perm_unique (α : Type u) [TotalOrder α] [DecidableEq α] : Prop :=
  ∀ (xs ys : List α), Ordered xs → Ordered ys → (xs = ys ↔ Permuted xs ys)

/-- Permutation is an equivalence relation (the book's
    `PERM-IS-AN-EQUIVALENCE`, ACL2's `defequiv` content: reflexive,
    symmetric, transitive — its `BOOLEANP` conjunct is type-absorbed by
    `Permuted`'s being a `Prop`). -/
def permuted_equivalence (α : Type u) [DecidableEq α] : Prop :=
  ∀ (xs ys zs : List α),
    Permuted xs xs ∧
    (Permuted xs ys → Permuted ys xs) ∧
    (Permuted xs ys → Permuted ys zs → Permuted xs zs)

/-- The witness is complete (the book's `CONVERT-PERM-TO-HOW-MANY`):
    two lists are permutations EXACTLY WHEN their multiplicities agree
    at the ONE element the witness picks out — the whole point of the
    witness, since it turns a `∀`-quantified count check into a single
    one. (The corpus's `PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-
    TRUE-LISTS` is this same statement under `TRUE-LISTP` hypotheses
    the types absorb, and is the step the book proves it from, not a
    second result.)

    ORDER-FREE, like the book theorem: `CONVERT-PERM-TO-HOW-MANY` says
    nothing about LEXORDER, and neither does anything this `Prop` is
    stated in (`Permuted`, `howMany`, `permWitness` all take
    `[DecidableEq α]`, and the witness additionally `[Inhabited α]` for
    its junk arm). So the binders are those two and no order — the same
    reading `permuted_equivalence` above carries. -/
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

/-- BSORT is ISORT (`BSORT-IS-ISORT`, whose `TRUE-LISTP` hypothesis is
    type-absorbed). -/
def bsort_is_isort (α : Type u) [TotalOrder α] : Prop :=
  ∀ (xs : List α), bsort xs = isort xs

end ACL2Lean.Sorting
