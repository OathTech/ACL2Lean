/-
  THE NATIVE MIRROR CATALOG (task #62; design doc §6).

  One section per corpus theorem: the result stated in NATIVE Lean terms,
  proved THROUGH the ACL2 replay — the driver's conditional mirror, its
  hypotheses discharged for the log-derived world, decoded to the native
  statement via the `enc`/`corr_*` simulation layer. Each PROVED entry is a
  build-enforced regression; each PENDING entry names the blocking frontier.
  The accumulated patterns are the seed of a future standard lifting library
  (polymorphic `α ↪ SExpr` statements are deliberately deferred — TODO.md).

  ── SCOREBOARD ────────────────────────────────────────────────────────────
  PROVED (via the driver's mirror):
    1. my-len-my-app   (xs ++ ys).length = xs.length + ys.length  [List SExpr]
  PROVED (via the HAND mirror — driver upgrade pending):
    -  my-len-my-app   ACL2Lean/Imported/SimpleWorld.lean (the original)
    -  nat-refl        Tests/DriverTests.lean `native_nat_refl` (trivial, driver)
  PENDING:
    -  app-assoc       (xs ++ ys) ++ zs = xs ++ (ys ++ zs)   [needs: corr_app
                        chain decode for the 3-var formula; machinery exists]
    -  equal-symm, equal-trans, cdr-cons-refl  generic SExpr facts   [needs: generic-
                        equality decode pattern — no simulation layer, direct]
    -  app-nil          xs ++ [] = xs                        [G5: multi-literal
                        pushed clause induction]
    -  rev-rev          xs.reverse.reverse = xs              [G5 + rev corr]
    -  len2-app family  length_append via len2               [corr_len2 +
                        hypothesis discharge for the 04/05 worlds]
    -  ground-arith / sq-of-3 / sq-rewrites  Int facts       [ground decode
                        pattern]
    -  linear-chain     Int order transitivity               [#50 DP tactic]
    -  len2-nonneg      0 ≤ (xs.length : Int)                [decode; the Nat
                        form is type-absorbed]
    -  true-listp-*     type-absorbed natively (List is well-formed by type) —
                        documented, mirror-only
  ──────────────────────────────────────────────────────────────────────────
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.Imported.SimpleWorld

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Meta Lean.Elab

/-! ## Entry 1 — `my-len-my-app`: `(xs ++ ys).length = xs.length + ys.length`

The full chain, end to end: the REAL `simple.proof-log` → parse → reconstruct
→ the log-DERIVED world → the driver's conditional mirror (totality/TP
hypotheses) → hypotheses DISCHARGED (the hand-proof dischargers, transferred
by defs-extensionality — the two worlds list the same definitions in a
different order) → instantiated at encoded lists → the simulation lemmas →
the native statement. -/

private def simpleLog : String := include_str "../../acl2_samples/simple.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def simpleDev : Development :=
  (((ProofLog.parse simpleLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world simpleWorldD from simpleDev

/-- The driver's CONDITIONAL mirror for `my-len-my-app`, over the log-derived
    world: `∀ env, total:my-len → total:my-app → total:fix → tp:my-len →
    ∃N∀f≥N, eval (equal (my-len (my-app x y)) (+ (my-len x) (my-len y))) = some t`. -/
elab "mylen_driver_mirror%" : term => do
  let devE := mkConst ``simpleDev
  let dev ← unsafe evalExpr Development (mkConst ``ACL2.Development) devE
  let some cp := Driver.findThm dev "my-len-my-app"
    | throwError "my-len-my-app not found in the development"
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``simpleWorldD, envExpr := env,
        worldVal := simpleDev.toWorld }
    let (proof, _conds) ← replayProofConditional cfg dev.typePrescriptions cp
    Meta.mkLambdaFVars #[env] proof

/-- The conditional mirror as a definition (the driver's proof OBJECT). -/
def mylenMirrorCond := mylen_driver_mirror%

/-! ### The world-agreement transfer

The hand-proof world (`ACL2.Worlds.Simple.world`) and the log-derived
`simpleWorldD` contain the SAME three definitions in different list order —
`get?`-equal, so `evalOpt_defs_ext` transfers every result between them. -/

private theorem worlds_get_eq :
    ∀ s, ACL2.Worlds.Simple.world.defs.get? s = simpleWorldD.defs.get? s := by
  intro s
  by_cases h1 : s = { name := "my-len" }
  · subst h1; decide
  · by_cases h2 : s = { name := "my-app" }
    · subst h2; decide
    · by_cases h3 : s = { name := "fix" }
      · subst h3; decide
      · -- s matches none of the three keys: both lookups run off the end
        have b1 : ¬({ name := "my-len" } : Symbol) = s := fun h => h1 h.symm
        have b2 : ¬({ name := "my-app" } : Symbol) = s := fun h => h2 h.symm
        have b3 : ¬({ name := "fix" } : Symbol) = s := fun h => h3 h.symm
        simp [ACL2.Worlds.Simple.world, ACL2.Worlds.Simple.sym, simpleWorldD,
              World.ofDefs, DefMap.get?, DefMap.get?.go, DefMap.insert, b1, b2, b3]

/-- `evalOpt` cannot distinguish the hand world from the log-derived world. -/
private theorem eval_eq (f : Nat) (env : Env) (t : SExpr) :
    evalOpt f Worlds.Simple.world env t = evalOpt f simpleWorldD env t :=
  evalOpt_defs_ext worlds_get_eq f env t

/-! ### The unconditional driver mirror, over the hand world

Each of the driver's four hypotheses is discharged by the corresponding
driver-form hand discharger, transported between the worlds by
defs-extensionality. The formula is the hand `my_len_my_appFormula` — it and
the log-derived statement are the same term (the translation produced exactly
the hand-written formula), so `exact` closes the gap definitionally. -/

theorem mylenMirror_world (env : Env) :
    ∃ N, ∀ f, f ≥ N → evalOpt f Worlds.Simple.world env
      Worlds.Simple.my_len_my_appFormula = some SExpr.t := by
  simp only [eval_eq]
  exact mylenMirrorCond env
    (fun e' a0 h => by
      simp only [← eval_eq] at h ⊢
      exact Worlds.Simple.drv_total_mylen e' a0 h)
    (fun e' a0 a1 h0 h1 => by
      simp only [← eval_eq] at h0 h1 ⊢
      exact Worlds.Simple.drv_total_myapp e' a0 a1 h0 h1)
    (fun e' a0 h => by
      simp only [← eval_eq] at h ⊢
      exact Worlds.Simple.drv_total_fix e' a0 h)
    (fun e' a0 v h => by
      simp only [← eval_eq] at h
      exact Worlds.Simple.drv_tp_mylen e' a0 v h)

/-- ENTRY 1, PROVED — the native statement through the DRIVER's replayed
    mirror: log → parse → reconstruct → derived world → conditional replay →
    discharged hypotheses → simulation decode. -/
theorem my_len_my_app_native_driver (xs ys : List SExpr) :
    (xs ++ ys).length = xs.length + ys.length :=
  Worlds.Simple.my_len_my_app_native_of_mirror mylenMirror_world xs ys

end ACL2.Imported.Mirrors
