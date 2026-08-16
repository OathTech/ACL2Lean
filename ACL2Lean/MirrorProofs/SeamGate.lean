import ACL2Lean.MirrorProofs.Basics
import ACL2Lean.MirrorProofs.Sorting

/-!
# THE MIRROR-LEVEL SEAM GATE (R-1b, ruled by Mike 2026-08-16)

The end-of-branch audit's finding A1-F2
(`docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md`): *"there is no
mirror-level seam gate."* The waypoint layer has one
(`Imported/Waypoints/Catalog.lean` — every catalogued native's proof must
transitively consume its `driver_replayed%` statement), but nothing checked
the same one rung up: `mirror_transport%`'s `from` argument accepts any
constant, so `crossing … from List.append_assoc` would have produced a
trio-clean "mirror" with zero replay content and no gate would have
objected. The auditor VERIFIED by proof-term traversal that the property
holds today for all six mirrors; this module makes the build check it.

**What it checks.** Every mirror PRODUCT theorem's proof term transitively
consumes a registered replayed statement — the seam between the product
layer and the replay.

* THE PRODUCTS are enumerated MECHANICALLY, so a new mirror joins with no
  edit here: a theorem under `ACL2Lean.MirrorProofs` whose STATEMENT
  mentions a spec constant declared in `ACL2Lean/Mirrors/` and mentions NO
  other constant of this package. That is the product criterion itself
  (`just check-mirrors-pure`'s "zero ACL2 notions", applied per statement),
  which is why it cleanly excludes the SQUARES and the CROSSINGS: their
  statements are in waypoint vocabulary (`SExpr`, the waypoint readings).
* THE SEAMS are enumerated MECHANICALLY too: `driver_replayed%` registers
  its enclosing definition in `replayedRegistryExt`, so the seam set is
  every replayed statement the environment carries — no hand list.

**THREAT MODEL (two-standard rule — this is a SPEEDBUMP).** It catches the
HONEST WIRING MISTAKE: a mirror cited from a library lemma, from a hand
waypoint restatement, or from a `sorry`-free but replay-free route. It is
NOT a barrier and must NOT be hardened: it rules out DETACHMENT, not
MIS-PAIRING (the same bound the waypoint gate states at
`Catalog.lean`) — a mirror could consume some OTHER book's seam and pass.
Nothing here makes "proved via replay" a kernel-certified property; it
stays strongly-evidenced engineering (A1 §Q4), backed by the generated
templates, these gates and review. If it ever becomes fragile or wrong,
DELETE IT — do not add another gate.
-/

namespace ACL2Lean.MirrorProofs

open Lean

/-- Declared in the PRODUCT layer's spec files (`ACL2Lean/Mirrors/`)? -/
private def declaredInMirrorSpec (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => (`ACL2Lean.Mirrors).isPrefixOf m
  | none => false

/-- Declared anywhere ELSE in this package — i.e. an ACL2 notion, by the
    product criterion (the mirror spec files import nothing of ours). -/
private def declaredInPackageNonSpec (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => (`ACL2Lean).isPrefixOf m && !(`ACL2Lean.Mirrors).isPrefixOf m
  | none => false

open Lean.Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  -- THE SEAMS: every `driver_replayed%` invocation's enclosing definition.
  let seams : List Name :=
    (ACL2.Replay.Driver.replayedRegistryExt.getState env).map
      (fun (_, _, decl, _, _) => decl)
  if seams.isEmpty then
    throwError "mirror seam gate: the replayed-statement registry is EMPTY \
      — this gate would be vacuous; the waypoint layer is not in scope"
  -- THE PRODUCTS (mechanical: statement mentions a `Mirrors/` spec
  -- constant and nothing else of ours).
  let mut products : List Name := []
  for (c, ci) in env.constants.toList do
    if (`ACL2Lean.MirrorProofs).isPrefixOf c && !c.isInternalDetail then
      if let .thmInfo _ := ci then
        let used := ci.type.getUsedConstants.toList
        if used.any (declaredInMirrorSpec env) &&
            !used.any (declaredInPackageNonSpec env) then
          products := products ++ [c]
  if products.isEmpty then
    throwError "mirror seam gate: NO mirror product theorem found — either \
      the product layer is not in scope here or the enumeration criterion \
      has drifted (it must not silently check nothing)"
  -- THE CHECK.
  let mut witnesses : List MessageData := []
  for m in products do
    match ACL2.Imported.Waypoints.seamReachesAny? env m seams
        (expandUnder := [`ACL2Lean.MirrorProofs, `ACL2.Imported]) with
    | some s => witnesses := witnesses ++ [m!"{m} → {s}"]
    | none =>
      throwError "mirror seam gate: {m} is a mirror PRODUCT theorem whose \
        proof term consumes NO replayed statement — the ornamental-import \
        antipattern one rung up (audit A1-F2). A mirror's content must \
        arrive through a `driver_replayed%` seam (cite the waypoint native \
        in `mirror_transport% … crossing … from …`), never from a library \
        lemma or a hand restatement."
  logInfo m!"mirror seam gate: {products.length} mirror product theorems, \
    each consuming a replayed statement ({seams.length} seams in scope):\n\
    {MessageData.joinSep witnesses (m!"\n")}"

end ACL2Lean.MirrorProofs
