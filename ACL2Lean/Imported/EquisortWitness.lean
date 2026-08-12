import ACL2Lean.Imported.Sorting

/-! # Equisort WITNESS exec kits + TP dischargers (close-out queue item 1)

The equisort scopes' `:LOCAL-WITNESS` defuns are insertion-sort clones
(`SORTFN1-INSERT`/`SORTFN1` and the `SS` pair differ from the isort
book's `INSERT`/`ISORT` only in their self-call names).  The witness TP
corollaries (`tp:SORTFN1-INSERT` — `(CONSP …)`; `tp:SORTFN1` — the
consp-or-nil `IF`) are the `proveTp` return-path-CONS frontier class
kept on the equisort constraint rows and blocking the AtCanonical
constants' full non-vacuity (deferral D1).  This module builds their
exec kits and (formerly `derive_exec_tp%`-generated) TP dischargers on
the established
hand-mirror pattern — bodies transcribed from the emitted `(:DEFUN …)`
events (equisort.proof-log lines 123/127/13674/13678).

DEMO V2 RE-HOMING: the transcribed witness BODIES/SYMBOLS
(`sortfn1InsertBody`, `sortfn1_sym`, …) now live with the rest of the
ACL2 source data in `Demo/Sorting/AclSource.lean`, and the four TP
dischargers — statements kept, proofs `sorry`-ed under the thin-Lean
ruling (2026-08-11); live consumers in `Mirrors/EquisortParametric` —
live with the rest of the sorting family's assumed facts in
`Demo/Sorting/Assumptions.lean`. What remains here is the exec-kit
build alone. -/

namespace ACL2.Worlds.Sorting

open ACL2

derive_exec% sortfn1InsertExec corr sortfn1_insert_exec_corr
  for sortfn1_insert_sym formals [eS, xS] body sortfn1InsertBody
  measured 1

derive_exec% sortfn1Exec corr sortfn1_exec_corr
  for sortfn1_sym formals [xS] body sortfn1Body measured 0

derive_exec% ssortfn1InsertExec corr ssortfn1_insert_exec_corr
  for ssortfn1_insert_sym formals [eS, xS] body ssortfn1InsertBody
  measured 1

derive_exec% ssortfn1Exec corr ssortfn1_exec_corr
  for ssortfn1_sym formals [xS] body ssortfn1Body measured 0

end ACL2.Worlds.Sorting
