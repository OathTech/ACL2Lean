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
    2. app-assoc       (xs ++ ys) ++ zs = xs ++ (ys ++ zs)        [List SExpr]
    3. ground-arith    (1 + (2 + 3) : Int) = 6                    [ground decode]
  PROVED (via the HAND mirror — driver upgrade pending):
    -  my-len-my-app   ACL2Lean/Imported/SimpleWorld.lean (the original)
    -  nat-refl        Tests/DriverTests.lean `native_nat_refl` (trivial, driver)
  PENDING:
    -  equal-symm, equal-trans, cdr-cons-refl  generic SExpr facts   [needs: generic-
                        equality decode pattern — no simulation layer, direct]
    -  app-nil          xs ++ [] = xs                        [G5: multi-literal
                        pushed clause induction]
    -  rev-rev          xs.reverse.reverse = xs              [G5 + rev corr]
    -  len2-app family  length_append via len2               [corr_len2 +
                        hypothesis discharge for the 04/05 worlds]
    -  sq-of-3 / sq-rewrites  Int facts                      [ground decode +
                        sq unfold; ground-arith's pattern extends]
    -  linear-chain     Int order transitivity               [#50 DP tactic]
    -  len2-nonneg      0 ≤ (xs.length : Int)                [decode; the Nat
                        form is type-absorbed]
    -  true-listp-*     type-absorbed natively (List is well-formed by type) —
                        documented, mirror-only
  ──────────────────────────────────────────────────────────────────────────
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.Imported.SimpleWorld
import ACL2Lean.Imported.AppAssoc

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

/-! ## Entry 2 — `app-assoc`: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`

From the REAL `recon-tests/02-rev.proof-log` (app-assoc is its first theorem;
the log's world carries `app` AND `rev`). Unlike entry 1, NO world-transfer
is needed: the `AppAssoc` support lemmas are world-PARAMETRIC (invariant L3),
so they instantiate directly at the log-derived world — every world fact is a
`decide` on the derived world, and the driver mirror's single hypothesis
(`total:app`) is discharged by the generic driver-shape totality. -/

private def revLog : String := include_str "../../acl2_samples/recon-tests/02-rev.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def revDev : Development :=
  (((ProofLog.parse revLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world revWorldD from revDev

/-- The driver's CONDITIONAL mirror for `app-assoc`, over the log-derived
    world: `∀ env, total:app → ∃N∀f≥N, eval (equal (app (app a b) c)
    (app a (app b c))) = some t`. -/
elab "app_assoc_driver_mirror%" : term => do
  let devE := mkConst ``revDev
  let dev ← unsafe evalExpr Development (mkConst ``ACL2.Development) devE
  let some cp := Driver.findThm dev "app-assoc"
    | throwError "app-assoc not found in the development"
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``revWorldD, envExpr := env,
        worldVal := revDev.toWorld }
    let (proof, _conds) ← replayProofConditional cfg dev.typePrescriptions cp
    Meta.mkLambdaFVars #[env] proof

/-- The conditional mirror as a definition (the driver's proof OBJECT). -/
def appAssocMirrorCond := app_assoc_driver_mirror%

/-- The driver mirror, its `total:app` hypothesis DISCHARGED — unconditional
    over the log-derived world. -/
theorem appAssocMirror_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → evalOpt f revWorldD env
      Worlds.AppAssoc.app_assocFormula = some SExpr.t :=
  appAssocMirrorCond env
    (fun e' a0 a1 h0 h1 =>
      Worlds.AppAssoc.drv_total_app revWorldD (by decide) (by decide)
        (by decide) (by decide) (by decide) e' a0 a1 h0 h1)

/-- ENTRY 2, PROVED — `List.append_assoc` (over `SExpr`) through the DRIVER's
    replayed mirror, with the world-parametric native assembly instantiated
    directly at the log-derived world. -/
theorem app_assoc_native_driver (xs ys zs : List SExpr) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  Worlds.AppAssoc.app_assoc_native_of_mirror revWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) appAssocMirror_uncond xs ys zs

/-! ## Entry 3 — `ground-arith`: `(1 + (2 + 3) : Int) = 6`

From `recon-tests/00-direct.proof-log` (the executable-counterpart/preprocess
class — no waterfall reasoning, no hypotheses on the mirror). The GROUND
DECODE pattern: both formula sides are evaluated SYMBOLICALLY to
`Logic`-primitive values over UNREDUCED Lean arithmetic (`int (1 + (2 + 3))`,
`int 6`), and the mirror's `equal ⇒ t` fact equates them — the arithmetic
fact comes from ACL2's replayed evaluation, never from a Lean decision
procedure. -/

private def directLog : String := include_str "../../acl2_samples/recon-tests/00-direct.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def directDev : Development :=
  (((ProofLog.parse directLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world directWorldD from directDev

/-- The driver's mirror for `ground-arith` (UNCONDITIONAL — the tree is a
    pure preprocess discharge, so the driver emits no hypotheses). -/
elab "ground_arith_driver_mirror%" : term => do
  let devE := mkConst ``directDev
  let dev ← unsafe evalExpr Development (mkConst ``ACL2.Development) devE
  let some cp := Driver.findThm dev "ground-arith"
    | throwError "ground-arith not found in the development"
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``directWorldD, envExpr := env,
        worldVal := directDev.toWorld }
    let (proof, _conds) ← replayProofConditional cfg dev.typePrescriptions cp
    Meta.mkLambdaFVars #[env] proof

/-- The mirror as a definition (the driver's proof OBJECT). -/
def groundArithMirrorCond := ground_arith_driver_mirror%

private def qInt (n : Int) : SExpr :=
  .cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int n))) .nil)
private def plusT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "binary-+" })) (.cons a (.cons b .nil))

/-- Ground quote convergence. -/
private theorem conv_qInt (w : World) (e : Env) (n : Int) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (qInt n) = some (.atom (.number (.int n))) :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w e _⟩

/-- Ground `binary-+` convergence to the SYMBOLIC sum. -/
private theorem conv_plus_int (w : World) (e : Env) (a b : SExpr) (m n : Int)
    (h_no : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some (.atom (.number (.int m))))
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some (.atom (.number (.int n)))) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (plusT a b)
      = some (.atom (.number (.int (m + n)))) := by
  have h := conv_builtin2 w e { name := "binary-+" } a b
    (.atom (.number (.int m))) (.atom (.number (.int n)))
    (Logic.plus (.atom (.number (.int m))) (.atom (.number (.int n))))
    (by decide) h_no ha hb (callBuiltin_plus _ _)
  rwa [logic_plus_int] at h

/-- ENTRY 3, PROVED — the ground arithmetic fact through the DRIVER's
    replayed mirror (executable-counterpart class). -/
theorem ground_arith_native : (1 + (2 + 3) : Int) = 6 := by
  let e : Env := {}
  have hL := conv_plus_int directWorldD e (qInt 1) (plusT (qInt 2) (qInt 3)) 1 (2 + 3)
    (by decide) (conv_qInt _ _ 1)
    (conv_plus_int directWorldD e (qInt 2) (qInt 3) 2 3 (by decide)
      (conv_qInt _ _ 2) (conv_qInt _ _ 3))
  have hR := conv_qInt directWorldD e 6
  obtain ⟨NL, hL'⟩ := hL
  obtain ⟨NR, hR'⟩ := hR
  obtain ⟨Nm, hm⟩ := groundArithMirrorCond e
  set f := max (max NL NR) Nm
  have hval : (.atom (.number (.int (1 + (2 + 3)))) : SExpr)
            = .atom (.number (.int 6)) :=
    eval_equal_t_implies_eq f directWorldD e
      (plusT (qInt 1) (plusT (qInt 2) (qInt 3))) (qInt 6)
      (.atom (.number (.int (1 + (2 + 3))))) (.atom (.number (.int 6)))
      (hL' f (by omega)) (hR' f (by omega)) (by decide)
      (hm (f + 1) (by omega))
  injection hval with h; injection h with h; injection h with h

end ACL2.Imported.Mirrors
