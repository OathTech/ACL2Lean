import ACL2Lean.Imported.Sorting

/-! # THE DISPATCH-FREE PER-MODE FILTER READINGS (R4 wave 2a)

The finding wave 0 stopped on (`MirrorProofs/Sorting.lean` W3 stage 3,
verbatim on the witness page): the general reading `filterL` keeps a
RUNTIME MODE DISPATCH — `relL` selects by comparing symbols
(`if fv == symV "LT" then …`) — and the square closer cannot evaluate a
ground `SExpr` comparison, so instantiating the MODE ARGUMENT does not
remove the dispatch. What removes it is a reading that never had one.

That is what this module carries: four readings, one per `RelMode`
constructor, each an OWN-DEFINITION with no dispatch at all — which is
also the vocabulary the real waypoint drivers speak
(`Imported/Waypoints/Qsort.lean` states `xs.filter (fun a => lexLtB a ev)`,
never `filterL '<mode>`).

**Each is VALIDATED, not asserted.** `derive_sim%` proves each reading
against the REAL `FILTER` exec at its own literal mode
(`filterExec <lit> (enc xs) ev = enc (<reading> ev xs)`), by the fixed
template whose failure is a hard error — the same gate every other
reading passes. A reading that did not match the exec's recursion could
not be declared here at all.

WHY A SEPARATE MODULE, and why the mode literals are re-spelled:
`Imported/Sorting.lean` is a grandfathered giant under the module-size
ratchet and may only shrink; and its `symV` is `private`, so the quoted
mode symbols cannot be named from here. The four literals below are the
same values (`symV s` is `.atom (.symbol { name := s })`), which is why
the three bridge lemmas can cite the existing `relL_LT`/`relL_LTE`/
`relL_GTE` directly.
-/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.Sorting

/-! ## The four quoted mode symbols, as values -/

/-- The book's `'LT`, as a value. -/
def modeLT : SExpr := .atom (.symbol { name := "LT" })
/-- The book's `'LTE`, as a value. -/
def modeLTE : SExpr := .atom (.symbol { name := "LTE" })
/-- The book's `'GT`, as a value. -/
def modeGT : SExpr := .atom (.symbol { name := "GT" })
/-- The book's `'GTE`, as a value (also `REL`'s `otherwise` branch). -/
def modeGTE : SExpr := .atom (.symbol { name := "GTE" })

/-! ## The dispatch bridges

One per mode: what `relL`'s runtime dispatch computes AT that literal.
Three are the existing rows verbatim (the literals are the same values as
`symV`'s); `GT` had no row and gets one in the same shape. -/

theorem relL_modeLT (a e : SExpr) : relL modeLT a e = lexLtB a e :=
  relL_LT a e
theorem relL_modeLTE (a e : SExpr) : relL modeLTE a e = lexorderB a e :=
  relL_LTE a e
theorem relL_modeGT (a e : SExpr) :
    relL modeGT a e = (lexorderB e a && !(a == e)) := by
  rw [relL, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
theorem relL_modeGTE (a e : SExpr) : relL modeGTE a e = lexorderB e a :=
  relL_GTE a e

/-! ## The four readings, and their validations

Each keeps the pivot `ev` on the RIGHT of the comparison, exactly as the
book's `(rel fn a e)` does. -/

/-- FILTER at `'LT`: keep the elements STRICTLY below the pivot. -/
def filterLtL (ev : SExpr) : List SExpr → List SExpr
  | [] => []
  | a :: t => bif lexLtB a ev then a :: filterLtL ev t else filterLtL ev t

/-- FILTER at `'LTE`: keep the elements at or below the pivot. -/
def filterLteL (ev : SExpr) : List SExpr → List SExpr
  | [] => []
  | a :: t =>
    bif lexorderB a ev then a :: filterLteL ev t else filterLteL ev t

/-- FILTER at `'GT`: keep the elements STRICTLY above the pivot. -/
def filterGtL (ev : SExpr) : List SExpr → List SExpr
  | [] => []
  | a :: t =>
    bif lexorderB ev a && !(a == ev) then a :: filterGtL ev t
    else filterGtL ev t

/-- FILTER at `'GTE`: keep the elements at or above the pivot. -/
def filterGteL (ev : SExpr) : List SExpr → List SExpr
  | [] => []
  | a :: t =>
    bif lexorderB ev a then a :: filterGteL ev t else filterGteL ev t

/-- Stage 2 at `'LT` — GENERATED. -/
derive_sim% filterExec_enc_LT for "FILTER"
  vars (fv : lit modeLT) (ev : raw) (xs : list)
  exec [fv, xs, ev]
  native (enc (filterLtL ev xs))
  simp [filterLtL, toBool_relExec, relL_modeLT]
  induct structural xs

/-- Stage 2 at `'LTE` — GENERATED. -/
derive_sim% filterExec_enc_LTE for "FILTER"
  vars (fv : lit modeLTE) (ev : raw) (xs : list)
  exec [fv, xs, ev]
  native (enc (filterLteL ev xs))
  simp [filterLteL, toBool_relExec, relL_modeLTE]
  induct structural xs

/-- Stage 2 at `'GT` — GENERATED. -/
derive_sim% filterExec_enc_GT for "FILTER"
  vars (fv : lit modeGT) (ev : raw) (xs : list)
  exec [fv, xs, ev]
  native (enc (filterGtL ev xs))
  simp [filterGtL, toBool_relExec, relL_modeGT]
  induct structural xs

/-- Stage 2 at `'GTE` — GENERATED. -/
derive_sim% filterExec_enc_GTE for "FILTER"
  vars (fv : lit modeGTE) (ev : raw) (xs : list)
  exec [fv, xs, ev]
  native (enc (filterGteL ev xs))
  simp [filterGteL, toBool_relExec, relL_modeGTE]
  induct structural xs

end ACL2.Worlds.Sorting
