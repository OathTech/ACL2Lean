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

end ACL2Lean.MirrorProofs
