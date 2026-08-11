import ACL2Lean.Imported.Sorting.Sims
import ACL2Lean.Imported.Sorting.Iso
import ACL2Lean.Imported.Sorting.IsoAdmission
import ACL2Lean.Imported.Sorting.Decode
import ACL2Lean.Imported.Sorting.DecodeSorts
import ACL2Lean.Imported.Sorting.Debt
import ACL2Lean.Imported.GzPrelude

/-! # Imported: the sorting books — world-parametric support beyond perm

World-parametric (invariant L3) support for the SORTING MIRROR PROGRAM
(the sorting-completion-2 amended criteria): the LEXORDER Bool kit, the
ORDEREDP simulation (an instance of the `corr_chain2_enc` schematic —
ORDEREDP is EXACTLY `chain2Body "LEXORDER" "ORDEREDP"` in every sorting
book), and the assembly lemmas for the ordered-perms book's native
entries. The `memb`/`rm`/`perm` simulations are REUSED from
`Imported/Perm.lean` — the sorting books carry those defuns verbatim
(same formals, same bodies; the `by decide` world facts at each
log-derived world enforce this at build time).

## MODULE LAYOUT (split 2026-08-11, the demo build)

This file is now a FACADE: the book's content lives in
`ACL2Lean/Imported/Sorting/`, layered so that the `import` lines ARE
the trust story (design: `docs/plans/2026-08-11_demo-design.md`;
reader path: `docs/DEMO.md`).

| module | layer | what it is |
| --- | --- | --- |
| `Sorting/Sims.lean` | 1 | the definitions: native readings, measures, symbol/body constants. Knows nothing of the replay |
| `Sorting/Iso.lean` | 2 | the `*_exec_corr` / `*Exec_enc` correspondence for the book programs |
| `Sorting/IsoAdmission.lean` | 2 | the same for the ordinal / `acl2-count` admission substrate |
| `Sorting/Decode.lean` | 3 | the `*_native_of_replayed` transports — ordered-perms / convert-perm / isort |
| `Sorting/DecodeSorts.lean` | 3 | the same for qsort / msort / bsort |
| `Sorting/Debt.lean` | 4 | the 12 quarantined FORBIDDEN-DEBT sorries |

Four LAYERS, six modules: `Iso` and `Decode` are each two modules
purely to respect the 1500-line module norm (`just check-file-weight`);
`scripts/check-trust-imports.sh` pins the layer imports.

Every existing `import ACL2Lean.Imported.Sorting` keeps working: this
facade re-exports all six, plus `Imported/GzPrelude.lean` (the D5
ground-zero rule content downstream books reach through here). -/
