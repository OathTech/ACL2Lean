import ACL2Lean.Mirrors.Basics
import ACL2Lean.Mirrors.Sorting

/-! # THE CHALLENGE — independent validation of the 21 mirror products

This file (with the two verbatim spec modules it imports, its whole
import closure beyond the core prelude) is the TRUSTED STATEMENT of
what the ACL2Lean pipeline claims to have proven: the 21 mirror
products (6 Basics + 15 Sorting), each a Lean-idiomatic theorem with
zero ACL2 notions, proved in the project VIA ACL2 REPLAY. It is
readable end-to-end as pure Lean: a reader of this file alone knows exactly which
mathematical statements are being validated, with no ACL2 vocabulary and
no project machinery.

Validated by leanprover/comparator: the project-side `Solution` module
must prove every `theorem` below (here left as `sorry`) with the SAME
statement (compared transitively, constant by constant, over the
lean4export output of both environments), using ONLY the axioms
`propext`, `Quot.sound`, `Classical.choice`, and the whole solution
environment is replayed through BOTH the Lean kernel and the independent
nanoda kernel. See `validation/README.md` for the full flow and the
sandbox scoping note.

PROVENANCE (verbatim-copy discipline): the definitions this challenge
states are byte-for-byte copies of the project's zero-import mirror
spec files (imported above; in THIS workspace those module names
resolve to `validation/ACL2Lean/Mirrors/*.lean`, byte-identical copies
built locally under the project's own module names — private auxiliary
constants embed the defining module name, so the copies must keep both
the per-file module split and the exact module names) —
  ACL2Lean/Mirrors/Basics.lean   (git blob b83d9ea106598587334fe78081d67ade1c4d035c)
  ACL2Lean/Mirrors/Sorting.lean  (git blob 00870e80f4f42063c242fbe81c85ec156028734e)
— plus the single `TotalOrder Int` instance the sorting statements bind,
copied verbatim from ACL2Lean/MirrorProofs/OrderBridge.lean
(git blob c7694037463672f2ab96f3dfa4d9a9c366fd4475), all three blobs
verified unchanged at main 71399d2c1eccf0f8529365c4a7c0dacdcfc800cd
(the commit this harness branch is cut from, 2026-08-19). The comparator does not trust this note: it re-checks that
every constant reachable from the 21 statements is identical in the
challenge and solution environments.

The 21 target theorems are at the BOTTOM of the file, namespace
`Validation`. -/

/- ═══════════════════════════════════════════════════════════════════
   VERBATIM COPY: the `TotalOrder Int` instance the sorting
   statements bind, from ACL2Lean/MirrorProofs/OrderBridge.lean
   ═══════════════════════════════════════════════════════════════════ -/

namespace ACL2Lean.MirrorProofs

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

end ACL2Lean.MirrorProofs

/- ═══════════════════════════════════════════════════════════════════
   THE 21 PRODUCT STATEMENTS — the challenge.
   Each is a project mirror product, stated at the same type and
   instances. `sorry` here; the Solution must supply real proofs.
   ═══════════════════════════════════════════════════════════════════ -/

namespace Validation

/-! ## Basics (6) -/

/-- MY-LEN-MY-APP (`simple.lisp`). -/
theorem len_app_int : ACL2Lean.Basics.len_app Int := sorry

/-- APP-ASSOC (the 02-rev book). -/
theorem app_assoc_int : ACL2Lean.Basics.app_assoc Int := sorry

/-- APP-NIL (the 01/02 books). -/
theorem app_nil_int : ACL2Lean.Basics.app_nil Int := sorry

/-- REV-APP (the 02-rev book). -/
theorem rev_app_int : ACL2Lean.Basics.rev_app Int := sorry

/-- REV-REV (the 02-rev book). -/
theorem rev_rev_int : ACL2Lean.Basics.rev_rev Int := sorry

/-- LEN-REV-ACC (the 14-accumulator book). -/
theorem len_revAcc_int : ACL2Lean.Basics.len_revAcc Int := sorry

/-! ## Sorting (15) -/

/-- ORDEREDP-ISORT. -/
theorem isort_ordered_int : ACL2Lean.Sorting.isort_ordered Int := sorry

/-- HOW-MANY-ISORT. -/
theorem isort_howMany_int : ACL2Lean.Sorting.isort_howMany Int := sorry

/-- ORDEREDP-MSORT. -/
theorem msort_ordered_int : ACL2Lean.Sorting.msort_ordered Int := sorry

/-- HOW-MANY-MSORT. -/
theorem msort_howMany_int : ACL2Lean.Sorting.msort_howMany Int := sorry

/-- ORDEREDP-QSORT. -/
theorem qsort_ordered_int : ACL2Lean.Sorting.qsort_ordered Int := sorry

/-- HOW-MANY-QSORT. -/
theorem qsort_howMany_int : ACL2Lean.Sorting.qsort_howMany Int := sorry

/-- PERM-QSORT. -/
theorem qsort_perm_int : ACL2Lean.Sorting.qsort_perm Int := sorry

/-- ORDEREDP-BSORT. -/
theorem bsort_ordered_int : ACL2Lean.Sorting.bsort_ordered Int := sorry

/-- HOW-MANY-BSORT. -/
theorem bsort_howMany_int : ACL2Lean.Sorting.bsort_howMany Int := sorry

/-- ORDERED-PERMS. -/
theorem ordered_perm_unique_int : ACL2Lean.Sorting.ordered_perm_unique Int := sorry

/-- PERM-IS-AN-EQUIVALENCE (+ the book's PERM-SYMMETRIC, PERM-TRANSITIVE). -/
theorem permuted_equivalence_int : ACL2Lean.Sorting.permuted_equivalence Int := sorry

/-- CONVERT-PERM-TO-HOW-MANY, at the value-or-nil element type. -/
theorem permWitness_complete_optint :
    ACL2Lean.Sorting.permWitness_complete (Option Int) := sorry

/-- MSORT-IS-ISORT. -/
theorem msort_is_isort_int : ACL2Lean.Sorting.msort_is_isort Int := sorry

/-- QSORT-IS-ISORT. -/
theorem qsort_is_isort_int : ACL2Lean.Sorting.qsort_is_isort Int := sorry

/-- BSORT-IS-ISORT. -/
theorem bsort_is_isort_int : ACL2Lean.Sorting.bsort_is_isort Int := sorry

end Validation
