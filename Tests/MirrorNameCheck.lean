/-
  Tests/MirrorNameCheck — THE COLLISION LINTER for the product layer's
  names (the naming pass, Mike 2026-08-13).

  THE RULE. A mirror spec name (anything declared directly in a
  `ACL2Lean/Mirrors/` namespace) must have ZERO overlap with a
  core/Std/Batteries/Mathlib name — neither at the ROOT nor
  DOT-NOTATION-REACHABLE on a type the specs use. `Mirrors/Sorting.lean`
  carried seven such overlaps before the rename (`List.merge`,
  `Option.merge`, `List.mergeSort`, `List.mergeSort_perm`,
  `List.insertionSort`, `List.count`, `Nat.count`).

  WHY. It is the vocabulary rule (`Imported/SimGen.lean`) at the product
  layer: mirror content arrives via REPLAY, never via a library lemma,
  and a shared name is the channel by which a library lemma — or a
  reader, or an `exact?` — mistakes one for the other. `xs.count a`
  resolving to OUR `count` in one file and Lean's in the next is exactly
  the confusion the mirror layer cannot afford.

  THREAT MODEL (two-standard rule — this is a SPEEDBUMP, not a gate).
  It catches the honest naming mistake: you add `def count` to a spec
  namespace and the build tells you `List.count` exists. It is NOT
  hardened and makes no claim against a motivated author — the library
  surface it sees is the import list below (the modules this package can
  actually elaborate against, not all of Mathlib: the full `Mathlib`
  root olean is not in the local cache), the carrier list is enumerated
  by hand, and anyone can delete this file. If it ever becomes fragile
  or wrong, DELETE IT — do not harden it. Reviewed by "does it catch the
  honest mistake, is it simple enough to never be wrong".
  (One known bound: Lake does not track the directory read below, so the
  COVERAGE check re-runs when this module re-elaborates — on a fresh
  build, or when it or an import changes — not the instant a new
  `Mirrors/` file appears.)

  PROBED 2026-08-13, both arms, with a scratch `Mirrors/Probe.lean`
  carrying `def count` in `ACL2Lean.Sorting` (created, run, deleted):
  the coverage arm errored `ACL2Lean.Mirrors.Probe is NOT imported
  here`; with the import added, the collision arm errored
  `ACL2Lean.Sorting.count COLLIDES WITH List.count (module
  Init.Data.List.Basic)` and `… Nat.count (module
  Mathlib.Data.Nat.Count)`.
-/
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Count
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Infix
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Chain
import Mathlib.Data.Option.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
-- the spec modules under test (one import per ACL2Lean/Mirrors/ file;
-- the coverage check below FAILS if a Mirrors file is missing here)
import ACL2Lean.Mirrors.Basics
import ACL2Lean.Mirrors.Sorting

namespace ACL2.Tests.MirrorNameCheck

open Lean

/-- The module prefix the spec files live under — the ONLY hardcoded
    location; the spec NAMESPACES are derived from the declarations
    those modules actually contain. -/
private def mirrorsModPrefix : Name := `ACL2Lean.Mirrors

/-- Library surface: a constant counts as a collision only if its
    defining module is rooted here. -/
private def libRoots : List Name := [`Init, `Lean, `Std, `Batteries, `Mathlib]

/-- The DOT-NOTATION carriers: the types the spec files actually mention,
    so `xs.foo`-style resolution is in scope for them. `List`/`Nat`/`Bool`
    (`Mirrors/Basics.lean`: `List α`, `Nat`, `DecidableEq`), `Int` and
    `Option` (the types the mirror theorems instantiate the `Prop`s at —
    `Option Int` is ACL2's value-or-nil element type, which
    `permWitness_complete`'s product uses), plus `Prod`/`Function` as
    cheap defensive entries. -/
private def carriers : List Name :=
  [`List, `Option, `Nat, `Int, `Bool, `Prod, `Function]

run_cmd do
  let env ← getEnv
  -- COVERAGE: every ACL2Lean/Mirrors/*.lean must be imported above, or
  -- this linter would silently check nothing for it.
  -- (elaboration runs from the package root; a read failure surfaces as
  -- a build error, which is the fail-closed direction)
  let dir : System.FilePath := "ACL2Lean" / "Mirrors"
  let entries ← dir.readDir
  for e in entries do
    if e.path.extension == some "lean" then
      let stem := e.path.fileStem.getD ""
      let mod := mirrorsModPrefix ++ Name.mkSimple stem
      unless env.header.moduleNames.contains mod do
        throwError "MirrorNameCheck: {mod} is NOT imported here — add \
          `import {mod}` so its spec names are checked"
  -- The spec declarations: public, authored, top-of-namespace constants
  -- coming from a Mirrors module. `isInternalDetail` + parent-is-a-
  -- constant drop the compiler satellites (equations, `eq_def`, match
  -- helpers, structure projections) — the WaypointCensus filters.
  let specs : List Name :=
    env.constants.fold (init := []) fun acc c _ =>
      match env.getModuleFor? c with
      | some m =>
        if mirrorsModPrefix.isPrefixOf m && !c.isInternalDetail
            && !env.contains c.getPrefix then c :: acc else acc
      | none => acc
  let mut hits : List MessageData := []
  for s in specs do
    let last := s.componentsRev.headD Name.anonymous
    for cand in (last :: carriers.map (· ++ last)) do
      if env.contains cand then
        match env.getModuleFor? cand with
        | some m =>
          if libRoots.any (·.isPrefixOf m) then
            hits := hits ++ [m!"{s}  COLLIDES WITH  {cand}  (module {m})"]
        | none => pure ()
  unless hits.isEmpty do
    let listing := MessageData.joinSep hits (m!"\n")
    throwError "MIRROR NAME COLLISION ({hits.length}) — a product-layer \
      spec name overlaps a library name, at the root or dot-notation-\
      reachable:\n{listing}\n\
      Rename the spec declaration (take the name from the ACL2 BOOK, \
      Lean-cased — `isort`/`msort`/`howMany` were derived that way); \
      the ACL2 rune stays in the docstring as the cross-reference. \
      See the rule in this file's header (Tests/MirrorNameCheck.lean)."
  logInfo m!"mirror name check: {specs.length} spec names, no collision \
    with {libRoots} over carriers {carriers}"

end ACL2.Tests.MirrorNameCheck
