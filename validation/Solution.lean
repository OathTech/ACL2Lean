import ACL2Lean.MirrorProofs.Basics
import ACL2Lean.MirrorProofs.Sorting

/-! # THE SOLUTION — the project's 21 mirror products, presented for
independent validation

Imports the project's mirror-proof modules and restates each of the 21
products under the `Validation` names the challenge uses. Every proof is
an alias of the corresponding project product — the theorems proved VIA
ACL2 REPLAY in `ACL2Lean/MirrorProofs/Basics.lean` and
`ACL2Lean/MirrorProofs/Sorting.lean`. Nothing is re-proved here: the
comparator checks that each statement matches the challenge's exactly
(transitively, constant by constant), that only
`propext`/`Quot.sound`/`Classical.choice` are used, and replays the
whole environment through the Lean kernel and nanoda. -/

namespace Validation

/-! ## Basics (6) -/

theorem len_app_int : ACL2Lean.Basics.len_app Int :=
  ACL2Lean.MirrorProofs.len_app_int

theorem app_assoc_int : ACL2Lean.Basics.app_assoc Int :=
  ACL2Lean.MirrorProofs.app_assoc_int

theorem app_nil_int : ACL2Lean.Basics.app_nil Int :=
  ACL2Lean.MirrorProofs.app_nil_int

theorem rev_app_int : ACL2Lean.Basics.rev_app Int :=
  ACL2Lean.MirrorProofs.rev_app_int

theorem rev_rev_int : ACL2Lean.Basics.rev_rev Int :=
  ACL2Lean.MirrorProofs.rev_rev_int

theorem len_revAcc_int : ACL2Lean.Basics.len_revAcc Int :=
  ACL2Lean.MirrorProofs.len_revAcc_int

/-! ## Sorting (15) -/

theorem isort_ordered_int : ACL2Lean.Sorting.isort_ordered Int :=
  ACL2Lean.MirrorProofs.isort_ordered_int

theorem isort_howMany_int : ACL2Lean.Sorting.isort_howMany Int :=
  ACL2Lean.MirrorProofs.isort_howMany_int

theorem msort_ordered_int : ACL2Lean.Sorting.msort_ordered Int :=
  ACL2Lean.MirrorProofs.msort_ordered_int

theorem msort_howMany_int : ACL2Lean.Sorting.msort_howMany Int :=
  ACL2Lean.MirrorProofs.msort_howMany_int

theorem qsort_ordered_int : ACL2Lean.Sorting.qsort_ordered Int :=
  ACL2Lean.MirrorProofs.qsort_ordered_int

theorem qsort_howMany_int : ACL2Lean.Sorting.qsort_howMany Int :=
  ACL2Lean.MirrorProofs.qsort_howMany_int

theorem qsort_perm_int : ACL2Lean.Sorting.qsort_perm Int :=
  ACL2Lean.MirrorProofs.qsort_perm_int

theorem bsort_ordered_int : ACL2Lean.Sorting.bsort_ordered Int :=
  ACL2Lean.MirrorProofs.bsort_ordered_int

theorem bsort_howMany_int : ACL2Lean.Sorting.bsort_howMany Int :=
  ACL2Lean.MirrorProofs.bsort_howMany_int

theorem ordered_perm_unique_int : ACL2Lean.Sorting.ordered_perm_unique Int :=
  ACL2Lean.MirrorProofs.ordered_perm_unique_int

theorem permuted_equivalence_int : ACL2Lean.Sorting.permuted_equivalence Int :=
  ACL2Lean.MirrorProofs.permuted_equivalence_int

theorem permWitness_complete_optint :
    ACL2Lean.Sorting.permWitness_complete (Option Int) :=
  ACL2Lean.MirrorProofs.permWitness_complete_optint

theorem msort_is_isort_int : ACL2Lean.Sorting.msort_is_isort Int :=
  ACL2Lean.MirrorProofs.msort_is_isort_int

theorem qsort_is_isort_int : ACL2Lean.Sorting.qsort_is_isort Int :=
  ACL2Lean.MirrorProofs.qsort_is_isort_int

theorem bsort_is_isort_int : ACL2Lean.Sorting.bsort_is_isort Int :=
  ACL2Lean.MirrorProofs.bsort_is_isort_int

end Validation
