/-
  Driver/DevQuery — the DEVELOPMENT-query front end, MOVED out of
  Driver/Harness (T1+2 sprint P6, 2026-08-16) so Harness stays under the
  1500-line norm when the post-replay discharge lane grew its quiescence
  loop. MOVE-ONLY: bodies are byte-identical to the Harness copies.

  These five declarations query a parsed `Development` — which theorems it
  carries, which stored rules precede each one — and define a `World`
  constant from it. They touch none of the walker/discharge machinery, so
  they are a leaf beneath it; Harness imports this module, which keeps
  every existing `import …Driver.Harness` consumer resolving the names
  exactly as before.

  (The precedent chain for resolving a weight-cap overrun by a MOVE rather
  than a baseline loosening: J-RT2e, J-P3b-f, J-P4a-i, J-P5a-h.)
-/
import ACL2Lean.Replay.Driver.Reflect

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ## Importer front-end helpers (promoted from the test harness)

`derive_world` defines a `World` constant PROJECTED from a parsed
`Development` (the world the replay reasons over is derived from the log, not
hand-written); `findThm` extracts a theorem's reconstructed proof from a
development by name. -/

private partial def theoremsWithRulesGo (dev : Development)
    (acc : List RuleSpec) : List (ClauseProof × List RuleSpec) :=
  match dev with
  | .bind (.theorem cp) rest => (cp, acc) :: theoremsWithRulesGo rest acc
  | .bind (.rules specs) rest => theoremsWithRulesGo rest (acc ++ specs)
  | .bind _ rest => theoremsWithRulesGo rest acc
  | .done => []

/-- Theorems of a development, each paired with the STORED rules created
    BEFORE it — the rules its proof could cite (creation order; ACL2's
    certification order makes citing a later rule impossible, so the offer
    is exactly the citable set). GROUND-ZERO snapshot rules (D5) seed the
    accumulator: boot-stored, they precede every theorem — the emitted
    `(:GROUND-ZERO-RULES …)` event itself sits at the log's TAIL (capture
    end), so it cannot be picked up by the in-order walk. -/
def developmentTheoremsWithRules (dev : Development) :
    List (ClauseProof × List RuleSpec) :=
  theoremsWithRulesGo dev dev.groundZeroRuleSpecs

/-- The stored rules created BEFORE the first theorem named `nm`
    (case-insensitive) — the `rules` argument for replaying it by name. -/
def rulesBefore (dev : Development) (nm : String) : List RuleSpec :=
  match (developmentTheoremsWithRules dev).find?
    (fun (cp, _) => cp.name.toLower == nm.toLower) with
  | some (_, rules) => rules
  | none => []

/-- All theorems matching a name (case-insensitive), in development order. -/
partial def findThms : Development → String → List ClauseProof
  | .bind (.theorem cp) rest, nm =>
    if cp.name.toLower == nm.toLower then cp :: findThms rest nm
    else findThms rest nm
  | .bind _ rest, nm => findThms rest nm
  | .done, _ => []

/-- The UNIQUE theorem named `nm` (case-insensitive). `none` when absent — and
    also when AMBIGUOUS (two theorems differing only in case): selecting the
    first match would silently pick a theorem the caller did not name, so we
    refuse to guess (fail-closed; audited 2026-06-10). -/
def findThm (dev : Development) (nm : String) : Option ClauseProof :=
  match findThms dev nm with
  | [cp] => some cp
  | _ => none

open Lean.Elab Lean.Elab.Command in
/-- `derive_world name from devTerm` — define `name : World` as the world
    PROJECTED from a `Development` (`Development.toWorld`), REFLECTED to a
    concrete (fast-reducing) def. -/
elab "derive_world " id:ident " from " t:term : command => do
  let ns ← Lean.getCurrNamespace
  liftTermElabM do
    let devE ← Lean.Elab.Term.elabTermAndSynthesize t (some (mkConst ``ACL2.Development))
    let dev ← unsafe Lean.Meta.evalExpr ACL2.Development (mkConst ``ACL2.Development) devE
    Lean.addAndCompile <| .defnDecl
      { name := ns ++ id.getId, levelParams := [], type := mkConst ``ACL2.World,
        value := ← reflectWorld dev.toWorld, hints := .abbrev, safety := .safe }
    Lean.enableRealizationsForConst (ns ++ id.getId)

end ACL2.Replay.Driver
