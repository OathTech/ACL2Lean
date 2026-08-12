import ACL2Lean.Demo.Sorting.TCB
import ACL2Lean.Demo.Sorting.AclSource
import ACL2Lean.Demo.Sorting.Assumptions
import ACL2Lean.Imported.Sorting.Iso
import ACL2Lean.Imported.Sorting.IsoAdmission
import ACL2Lean.Imported.Sorting.Decode
import ACL2Lean.Imported.Sorting.DecodeSorts
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

## MODULE LAYOUT (demo v2, 2026-08-12)

This file is a FACADE. The layering IS the trust story, and it now
splits across two trees — THE DEMO (what a reader must trust) and THE
MACHINERY (what they need not) — with the arrow running one way:
machinery imports the demo, never the reverse.

| module | tree | what it is |
| --- | --- | --- |
| `Demo/Sorting/TCB.lean` | demo | the DEFINITIONS: `isortL`, `msortL`, `qsortL`, `merge2L`, `bnextL`, `pceL`, `orderedpRec`, `LexSorted`, … Imports the value core alone |
| `Demo/Sorting/AclSource.lean` | demo | the transcribed ACL2 `defun` DATA: bodies, symbols, term builders. Pure data; imports the syntax core alone |
| `Demo/Sorting/Assumptions.lean` | demo | the 18 quarantined FORBIDDEN-DEBT sorries — the whole sorting family's assumed facts |
| `Sorting/Iso.lean` | machinery | the `*_exec_corr` / `*Exec_enc` correspondence for the book programs |
| `Sorting/IsoAdmission.lean` | machinery | the same for the ordinal / `acl2-count` admission substrate |
| `Sorting/Decode.lean` | machinery | the `*_native_of_replayed` transports — ordered-perms / convert-perm / isort |
| `Sorting/DecodeSorts.lean` | machinery | the same for qsort / msort / bsort |

`Demo/Sorting/Statements.lean` (the front door) sits above all of it and
is the ONE demo file that imports machinery — statements only, zero
proof content. `scripts/check-trust-imports.sh` pins every one of these
import sets; the reader path is `docs/demo/`.

Every existing `import ACL2Lean.Imported.Sorting` keeps working: this
facade re-exports all seven, plus `Imported/GzPrelude.lean` (the D5
ground-zero rule content downstream books reach through here). -/
