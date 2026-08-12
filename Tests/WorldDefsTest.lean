/-
  Characterization tests for the `World.defs` lookup/insert CONTRACT.

  These pin the observable behaviour of `World.defs.get?` / `.insert` so the
  representation can be swapped (HashMap → reduction-friendly `DefMap`) with
  confidence: the new impl must satisfy exactly these. Written against the CURRENT
  impl first (they pass now); they are the spec, not a description.

  Contract: `get?` returns the LATEST inserted value for a key, `none` for an
  absent key; `insert` overwrites. (See docs/plans/2026-06-08_defmap-refactor.md.)
-/
import ACL2Lean.Syntax
import ACL2Lean.Imported.SimpleWorld
import ACL2Lean.Imported.AppAssoc

open ACL2

private def fSym : Symbol := { name := "f" }
private def gSym : Symbol := { name := "g" }
private def absent : Symbol := { name := "nope" }
private def body1 : SExpr := .atom (.symbol { name := "b1" })
private def body2 : SExpr := .atom (.symbol { name := "b2" })

/-- A world with `f ↦ ([x], body1)`. -/
private def w1 : World :=
  { World.empty with defs := World.empty.defs.insert fSym ([{ name := "x" }], body1) }
/-- `f` re-inserted with a different value (shadowing). -/
private def w2 : World :=
  { w1 with defs := w1.defs.insert fSym ([{ name := "y" }], body2) }
/-- A second key alongside `f`. -/
private def w3 : World :=
  { w1 with defs := w1.defs.insert gSym ([], body2) }

-- === get? contract ===
-- empty world: every key absent
#guard World.empty.defs.get? fSym = none
-- present key returns its value
#guard w1.defs.get? fSym = some ([{ name := "x" }], body1)
-- absent key in a non-empty world
#guard w1.defs.get? absent = none
-- shadowing: latest insert wins
#guard w2.defs.get? fSym = some ([{ name := "y" }], body2)
-- unrelated key unaffected by another insert
#guard w3.defs.get? fSym = some ([{ name := "x" }], body1)
#guard w3.defs.get? gSym = some ([], body2)
#guard w3.defs.get? absent = none

/-! ## Standing axiom-cleanliness gates for the integration nets.

The two `#print axioms` gates that stood here pinned
`ACL2.Worlds.Simple.my_len_my_app_uncond` and
`ACL2.Worlds.AppAssoc.app_assoc_uncond` — the HAND-REPLAY chain, which
was PURGED under the thin-Lean ruling (2026-08-11) as Lean-side content
ACL2 derives. The driver-based natives in `Imported/Waypoints/Basics`
carry that content now, gated by the catalog's per-entry
axiom-exactness check — but NOT at parity (audit fix F7): APP-ASSOC is
`.native` (exact clean trio), while MY-LEN-MY-APP is `.nativeSorried`
(carries `sorryAx` via the `drv_tp_mylen` FORBIDDEN-DEBT). The simple
book's clean-axioms assertion is RETIRED by the ruling until that debt
retires by replay, not relocated. -/
