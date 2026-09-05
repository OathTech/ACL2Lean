/-! # Word truncation — the NS1 native specifications

Pure Lean, core prelude only. These propositions are the agreed targets
for replay of `kestrel/bv/bvchop.lisp`; they do not yet have mirror proofs.
All natural widths and integer inputs are included, even width zero and
negative inputs. See `docs/plans/2026-09-05_bvchop-foundation-charter.md`.
-/

namespace ACL2Lean.WordOps

/-- The logical word-truncation operation corresponding to `bvchop`. -/
def wordClip (width : Nat) (value : Int) : Int :=
  value % (2 : Int) ^ width

/-- Target: `bvchop-upper-bound`. -/
def wordClipBound : Prop :=
  ∀ (width : Nat) (value : Int),
    wordClip width value < (2 : Int) ^ width

/-- Target: `bvchop-of-bvchop-same`. -/
def wordClipIdempotent : Prop :=
  ∀ (width : Nat) (value : Int),
    wordClip width (wordClip width value) = wordClip width value

/-- Target: `bvchop-identity`, restricted to integer values in range. -/
def wordClipIdentity : Prop :=
  ∀ (width : Nat) (value : Int),
    0 ≤ value → value < (2 : Int) ^ width → wordClip width value = value

end ACL2Lean.WordOps
