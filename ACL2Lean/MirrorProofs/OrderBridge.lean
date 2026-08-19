import ACL2Lean.LexorderOrder
import ACL2Lean.Imported.Sorting
import ACL2Lean.MirrorProofs.IsoGen
import ACL2Lean.Mirrors.Sorting

/-! # The order bridge (R1 Track C, concrete half)

Machinery-side, CORE-LOGIC-provenance content: the spec's `TotalOrder`
instantiated at `SExpr` by LEXORDER's Bool reading (the four laws are
the ground-zero order rules ACL2 admits at axioms.lisp:27154ff, PROVED
about our implementation in `LexorderOrder.lean` — nothing here trusts
ACL2), and the restriction lemma pinning what LEXORDER *is* on the
`intEmbed` image: exactly `Int.≤`. Named consumers: witness W1's
square statement (`MirrorProofs/Sorting.lean`) and the R4 sorting
transports. The instance-THREADING machinery (`mirror_transport%`
carrying instances through the crossing) is NOT here — it has no
elaborating witness before R4's exec kits and is deferred per the
charter's anti-"infrastructure now, wire later" rule. -/

namespace ACL2Lean.MirrorProofs

universe u

open ACL2 (SExpr)
open ACL2.Worlds.Sorting (lexorderB)

/-- `TotalOrder SExpr` by LEXORDER: `a ≤ b` is `lexorderB a b = true`.
    The four laws are `LexorderOrder.lean`'s core-logic theorems. -/
instance instTotalOrderSExpr : ACL2Lean.Sorting.TotalOrder SExpr where
  le a b := lexorderB a b = true
  le_refl a := by
    show lexorderB a a = true
    simp [lexorderB, ACL2.lexorder_refl]
  le_trans {a b c} h1 h2 := by
    show lexorderB a c = true
    have h1' : ACL2.lexorder a b = SExpr.t := by
      simpa [lexorderB] using h1
    have h2' : ACL2.lexorder b c = SExpr.t := by
      simpa [lexorderB] using h2
    simp [lexorderB, ACL2.lexorder_trans h1' h2']
  le_antisymm {a b} h1 h2 :=
    ACL2.lexorder_antisymm (by simpa [lexorderB] using h1)
      (by simpa [lexorderB] using h2)
  le_total a b := by
    rcases ACL2.lexorder_total a b with h | h
    · exact Or.inl (by simp [lexorderB, h])
    · exact Or.inr (by simp [lexorderB, h])
  decLE a b := inferInstanceAs (Decidable (_ = true))

/-- The restriction lemma: on integer atoms (the `intEmbed` image)
    LEXORDER is exactly `Int.≤` — the R4 order bridge. -/
theorem lexorderB_intEmbed (m n : Int) :
    lexorderB (intEmbed.enc m) (intEmbed.enc n) = decide (m ≤ n) := by
  simp only [lexorderB, intEmbed, ACL2.lexorder, ACL2.lexView?,
    ACL2.alphLe, ACL2.viewKind, ACL2.Logic.toRat]
  by_cases h : m ≤ n <;> simp [h]

/-! ## The ORDER-RESPECTING embedding (R4 wave 1)

`Acl2Embed` has exactly two fields and no order field — deliberately
("that dimension arrives with sorting", `IsoGen`). This is that
dimension, and it lands as a RICHER EMBEDDING rather than as a ladder
rung, because the fact it carries is not plumbing the closer may reach
for: a homomorphism square over an order-using mirror definition is
FALSE for an embedding that does not respect the order, so the
order-respect fact is a HYPOTHESIS OF THE SQUARE'S STATEMENT. The
generator's `embed S via [...]` clause (see `IsoGen`'s "the
order-respect route" for the criterion text) binds it per square and
makes exactly the named fields available to that square's closer —
the same scope, and the same visibility, a registered callee square
has.

It lives HERE, not in `IsoGen`, because its statement mentions the
order at `SExpr`: the generic generator stays free of order
vocabulary, and the clause resolves `S` by name in the consuming
file. -/

/-- An embedding that RESPECTS THE ORDER: `enc` is an injection (the
    inherited `Acl2Embed` fields) which additionally reflects and
    preserves `≤` — at `SExpr` that is LEXORDER's Bool reading, via
    `instTotalOrderSExpr`.

    The field is an IFF at the `Prop` level on purpose. It is what the
    square closer actually consumes: a homomorphism square's encoded
    side splits on `if e.enc a ≤ e.enc b`, and rewriting that condition
    to the SOURCE condition `a ≤ b` is what lets the split's own case
    hypothesis reduce the branch (measured on `insertOrd_map_hom`; the
    `Bool`-level form `lexorderB (enc a) (enc b) = decide (a ≤ b)` —
    which is `lexorderB_intEmbed`'s shape — would additionally need
    `decide_eq_true_eq`, a rung the ladder's criterion explicitly does
    NOT admit). -/
structure OrderedEmbed (α : Type u) [ACL2Lean.Sorting.TotalOrder α]
    extends Acl2Embed α where
  /-- the embedding reflects and preserves the order -/
  ord : ∀ a b : α, (enc a ≤ enc b) ↔ (a ≤ b)

/-- `Int` under its own `≤` — the order interface at the element type
    the `intEmbed` witness needs. All four laws are core `Int` facts;
    nothing here is about ACL2. -/
instance instTotalOrderInt : ACL2Lean.Sorting.TotalOrder Int where
  toLE := inferInstanceAs (LE Int)
  le_refl := Int.le_refl
  le_trans h1 h2 := Int.le_trans h1 h2
  le_antisymm h1 h2 := Int.le_antisymm h1 h2
  le_total := Int.le_total
  decLE := inferInstanceAs (DecidableRel (α := Int) (· ≤ ·))

/-- **The order-respect witness**: `intEmbed` respects the order, by the
    restriction lemma above — so LEXORDER on the integer-atom image IS
    `Int.≤`, and every homomorphism square declared `embed OrderedEmbed`
    is available at `Int`. Proved, not assumed: `lexorderB_intEmbed` is
    itself proved about our implementation. -/
def intOrderedEmbed : OrderedEmbed Int where
  toAcl2Embed := intEmbed
  ord a b := by
    show lexorderB (intEmbed.enc a) (intEmbed.enc b) = true ↔ a ≤ b
    rw [lexorderB_intEmbed]
    exact decide_eq_true_iff

/-! ## THE `Option` ROW'S WITNESS AT `Int` (close-out arc item 2)

`IsoKit.lean`'s `optEmbed` is the generic row (`none ↦ nil`,
`some a ↦ e.enc a`, under the fail-closed nil-avoidance side
condition). This section discharges that side condition for `intEmbed`,
giving the ELEMENT TYPE at which ACL2's value-or-nil idiom is a Lean
type rather than a junk value.

NO ORDER LIVES HERE, and the record of why (audit round, 2026-08-19).
This section briefly carried a `TotalOrder (Option Int)` instance, two
LEXORDER-against-`nil` facts and a pin tying the instance to LEXORDER
on the image. None of it had a consumer: it existed ONLY so
`permWitness_complete`'s then-`[TotalOrder α]` binder could be
synthesised at this element type, and that binder was itself spurious —
`CONVERT-PERM-TO-HOW-MANY` is order-free and so is everything the
`Prop` is stated in (`Permuted`/`howMany`/`permWitness` take
`[DecidableEq α]`, the witness additionally `[Inhabited α]`). With the
binder removed from the spec the whole block became dead weight and was
deleted rather than kept as decoration. -/

/-- The `Option` row's SIDE CONDITION, discharged for `intEmbed`: an
    integer atom is never `nil`, so `none` has the image to itself and
    the row's map is injective. -/
theorem intEmbed_enc_ne_nil (n : Int) : intEmbed.enc n ≠ SExpr.nil := by
  intro h; exact SExpr.noConfusion h

/-- **`Option Int` embeds** — the value-or-nil element type, by the
    generic row at `intEmbed`. The row lands a `ValueOrNilEmbed`, so
    `none ↦ nil` is available to an element-result square as the
    declared `encDefault` field. -/
def optIntEmbed : ValueOrNilEmbed (Option Int) :=
  optEmbed intEmbed intEmbed_enc_ne_nil

end ACL2Lean.MirrorProofs
