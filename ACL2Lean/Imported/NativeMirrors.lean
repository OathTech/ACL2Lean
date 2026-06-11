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
    4. sq-of-3         (3 * 3 : Int) = 9                          [defn unfold]
    5. cdr-cons-refl   Logic.cdr (cons u v) = v                   [symbolic-value]
    6. equal-symm      u = v → v = u                              [hypothesis decode]
    7. equal-trans     u = v → v = w → u = w                      [hypothesis + if]
    8. app-cons-car    Logic.car (cons u v) = u                   [nested unfold +
                                                                   symbolic-value]
  PROVED (via the HAND mirror — driver upgrade pending):
    -  my-len-my-app   ACL2Lean/Imported/SimpleWorld.lean (the original)
    -  nat-refl        Tests/DriverTests.lean `native_nat_refl` (trivial, driver)
  MIRROR-ONLY (replayed by the driver — DriverCoverage regression — but the
  decode is REFLEXIVE: our own evaluation of both sides computes the same
  value, so no non-vacuous native fact exists to extract):
    -  sq-rewrites, idf-rewrites, count-down-zero, my-evenp-3-is-nil,
       my-oddp-3-is-t
  PENDING:
    -  app-nil          xs ++ [] = xs                        [G5: multi-literal
                        pushed clause induction]
    -  rev-rev          xs.reverse.reverse = xs              [G5 + rev corr]
    -  len2-app family  length_append via len2               [needs the len2
                        world's dischargers (totality inductions + TP) — the
                        entry-1 recipe over the 01 world]
    -  linear-chain     Int order transitivity               [#50 DP tactic]
    -  len2-nonneg      0 ≤ (xs.length : Int)                [decode; the Nat
                        form is type-absorbed; needs len2 dischargers]
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

/-- `driver_mirror% dev world "thm-name"` — the DRIVER's conditional mirror
    for the named theorem of the development `dev`, over the derived world
    constant `world`: a `∀ env, <hypotheses> → ∃N∀f≥N, eval = some t` proof
    OBJECT produced by `replayProofConditional` from the reconstructed tree. -/
elab "driver_mirror%" devId:ident worldId:ident nm:str : term => do
  let devName ← Lean.resolveGlobalConstNoOverload devId
  let worldName ← Lean.resolveGlobalConstNoOverload worldId
  let dev ← unsafe Meta.evalExpr Development (mkConst ``ACL2.Development)
    (mkConst devName)
  let some cp := Driver.findThm dev nm.getString
    | throwError "{nm.getString} not found in the development"
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst worldName, envExpr := env, worldVal := dev.toWorld }
    let (proof, _conds) ← replayProofConditional cfg dev.typePrescriptions cp
    Meta.mkLambdaFVars #[env] proof

/-- The conditional mirror as a definition (the driver's proof OBJECT). -/
def mylenMirrorCond := driver_mirror% simpleDev simpleWorldD "my-len-my-app"

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

/-- The conditional mirror as a definition (the driver's proof OBJECT):
    `∀ env, total:app → ∃N∀f≥N, eval (equal (app (app a b) c)
    (app a (app b c))) = some t`. -/
def appAssocMirrorCond := driver_mirror% revDev revWorldD "app-assoc"

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

/-- The mirror as a definition (UNCONDITIONAL — the tree is a pure preprocess
    discharge, so the driver emits no hypotheses). -/
def groundArithMirrorCond := driver_mirror% directDev directWorldD "ground-arith"

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

/-! ## Entry 4 — `sq-of-3`: `(3 * 3 : Int) = 9`

Same log (00-direct), one step richer than entry 3: the formula applies the
USER-DEFINED `sq` (body `(binary-* n n)`) to a ground argument, so the decode
unfolds the definition (`conv_defn_1`) and evaluates the body symbolically —
`int (3 * 3)` — before the mirror's `equal ⇒ t` fact equates it with `int 9`. -/

/-- The mirror as a definition (UNCONDITIONAL — executable-counterpart
    discharge; `sq`'s unfold is part of the replayed evaluation). -/
def sqOf3MirrorCond := driver_mirror% directDev directWorldD "sq-of-3"

private def n_sym : Symbol := ⟨"ACL2", "n"⟩
private def nT : SExpr := .atom (.symbol { name := "n" })
private def sqBody : SExpr :=
  .cons (.atom (.symbol { name := "binary-*" })) (.cons nT (.cons nT .nil))

/-- Ground `binary-*` convergence to the SYMBOLIC product. -/
private theorem conv_times_int (w : World) (e : Env) (a b : SExpr) (m n : Int)
    (h_no : w.defs.get? ({ name := "binary-*" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some (.atom (.number (.int m))))
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some (.atom (.number (.int n)))) :
    ∃ N, ∀ f ≥ N, evalOpt f w e
      (.cons (.atom (.symbol { name := "binary-*" })) (.cons a (.cons b .nil)))
      = some (.atom (.number (.int (m * n)))) := by
  have h := conv_builtin2 w e { name := "binary-*" } a b
    (.atom (.number (.int m))) (.atom (.number (.int n)))
    (Logic.times (.atom (.number (.int m))) (.atom (.number (.int n))))
    (by decide) h_no ha hb (callBuiltin_times _ _)
  rwa [Logic.times_int] at h

/-- ENTRY 4, PROVED — the ground fact about the user-defined `sq` through the
    DRIVER's replayed mirror (definition unfold + symbolic body evaluation). -/
theorem sq_of_3_native : (3 * 3 : Int) = 9 := by
  let e : Env := {}
  -- (sq '3) ⇒ int (3*3): unfold the definition, evaluate the body in bindArgs
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f directWorldD (bindArgs [n_sym] [.atom (.number (.int 3))]) sqBody
      = some (.atom (.number (.int (3 * 3)))) := by
    have hn : ∃ N, ∀ f ≥ N,
        evalOpt f directWorldD (bindArgs [n_sym] [.atom (.number (.int 3))]) nT
        = some (.atom (.number (.int 3))) :=
      ⟨1, fun f hf => by
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        exact evalOpt_var g directWorldD _ n_sym _ (bindArgs_single_get_self _ _)⟩
    exact conv_times_int directWorldD _ nT nT 3 3 (by decide) hn hn
  have hL : ∃ N, ∀ f ≥ N, evalOpt f directWorldD e
      (.cons (.atom (.symbol { name := "sq" })) (.cons (qInt 3) .nil))
      = some (.atom (.number (.int (3 * 3)))) :=
    conv_defn_1 directWorldD e { name := "sq" } (qInt 3) (.atom (.number (.int 3)))
      n_sym sqBody (.atom (.number (.int (3 * 3))))
      (by decide) (by decide) (conv_qInt _ _ 3) hbody
  have hR := conv_qInt directWorldD e 9
  obtain ⟨NL, hL'⟩ := hL
  obtain ⟨NR, hR'⟩ := hR
  obtain ⟨Nm, hm⟩ := sqOf3MirrorCond e
  set f := max (max NL NR) Nm
  have hval : (.atom (.number (.int (3 * 3))) : SExpr) = .atom (.number (.int 9)) :=
    eval_equal_t_implies_eq f directWorldD e
      (.cons (.atom (.symbol { name := "sq" })) (.cons (qInt 3) .nil)) (qInt 9)
      (.atom (.number (.int (3 * 3)))) (.atom (.number (.int 9)))
      (hL' f (by omega)) (hR' f (by omega)) (by decide)
      (hm (f + 1) (by omega))
  injection hval with h; injection h with h; injection h with h

/-! ## Entries 5–7 — the equality-reasoning trio (`08-equality-reasoning`)

`cdr-cons-refl`, `equal-symm`, `equal-trans` — generic facts over arbitrary
`SExpr` values, decoded DIRECTLY (no `enc` simulation layer; the formula's
free variables are instantiated by the env). The mirrors are unconditional
(the 08 world has no defuns; the trees are preprocess discharges). Two new
decode patterns: the SYMBOLIC-VALUE decode (entry 5: the lhs is evaluated
only to `Logic.cdr (cons u v)`, so the mirror's equality fact is the
non-trivial content) and the HYPOTHESIS decode (entries 6–7: a native
hypothesis truthifies the `implies` antecedent; the mirror's `implies ⇒ t`
forces the conclusion's truth). -/

private def eqLog : String := include_str "../../acl2_samples/recon-tests/08-equality-reasoning.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def eqDev : Development :=
  (((ProofLog.parse eqLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world eqWorldD from eqDev

def cdrConsMirrorCond := driver_mirror% eqDev eqWorldD "cdr-cons-refl"
def equalSymmMirrorCond := driver_mirror% eqDev eqWorldD "equal-symm"
def equalTransMirrorCond := driver_mirror% eqDev eqWorldD "equal-trans"

private def xT : SExpr := .atom (.symbol { name := "x" })
private def yT : SExpr := .atom (.symbol { name := "y" })
private def zT : SExpr := .atom (.symbol { name := "z" })
private def equalT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "equal" })) (.cons a (.cons b .nil))
private def impliesT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "implies" })) (.cons a (.cons b .nil))

/-- Variable convergence from a concrete env binding. -/
private theorem conv_var_of_get (w : World) (e : Env) (s : Symbol) (v : SExpr)
    (h : e.get? s = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (.atom (.symbol s)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w e s v h⟩

/-- `(equal a b)` converges to the SYMBOLIC `Logic.equal` of the values. -/
private theorem conv_equalT (w : World) (e : Env) (a b av bv : SExpr)
    (h_no : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (equalT a b) = some (Logic.equal av bv) :=
  conv_builtin2 w e { name := "equal" } a b av bv _ (by decide) h_no ha hb
    (callBuiltin_equal _ _)

/-- `(implies a b)` converges to the SYMBOLIC `Logic.implies` of the values. -/
private theorem conv_impliesT (w : World) (e : Env) (a b av bv : SExpr)
    (h_no : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (impliesT a b) = some (Logic.implies av bv) :=
  conv_builtin2 w e { name := "implies" } a b av bv _ (by decide) h_no ha hb
    (callBuiltin_implies _ _)

/-- ENTRY 5, PROVED — `cdr ∘ cons = snd` at the `Logic` layer, through the
    DRIVER's mirror: the lhs is evaluated only SYMBOLICALLY (to
    `Logic.cdr (cons u v)`), so the equation is the mirror's content. -/
theorem cdr_cons_native (u v : SExpr) : Logic.cdr (SExpr.cons u v) = v := by
  let e : Env := (({} : Env).insert ⟨"ACL2", "y"⟩ v).insert ⟨"ACL2", "x"⟩ u
  have hx : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e xT = some u :=
    conv_var_of_get _ _ _ _ (by simp [e, Env.get?_insert])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e yT = some v :=
    conv_var_of_get _ _ _ _ (by
      simp only [e, Env.get?_insert]
      rw [if_neg (by decide)]; simp)
  have hcons : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e
      (.cons (.atom (.symbol { name := "cons" })) (.cons xT (.cons yT .nil)))
      = some (SExpr.cons u v) :=
    conv_builtin2 eqWorldD e { name := "cons" } xT yT u v _ (by decide)
      (by decide) hx hy (callBuiltin_cons _ _)
  have hcdr : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e
      (.cons (.atom (.symbol { name := "cdr" }))
        (.cons (.cons (.atom (.symbol { name := "cons" })) (.cons xT (.cons yT .nil))) .nil))
      = some (Logic.cdr (SExpr.cons u v)) :=
    conv_builtin1 eqWorldD e { name := "cdr" } _ (SExpr.cons u v) _ (by decide)
      (by decide) hcons (callBuiltin_cdr _)
  obtain ⟨NL, hL'⟩ := hcdr
  obtain ⟨NR, hR'⟩ := hy
  obtain ⟨Nm, hm⟩ := cdrConsMirrorCond e
  set f := max (max NL NR) Nm
  exact eval_equal_t_implies_eq f eqWorldD e _ yT (Logic.cdr (SExpr.cons u v)) v
    (hL' f (by omega)) (hR' f (by omega)) (by decide) (hm (f + 1) (by omega))

/-- ENTRY 6, PROVED — symmetry of equality over `SExpr`, through the DRIVER's
    mirror (the HYPOTHESIS decode: `h` truthifies the antecedent, the mirror's
    `implies ⇒ t` forces the conclusion). -/
theorem equal_symm_native (u v : SExpr) (h : u = v) : v = u := by
  by_cases hvu : v = u
  · exact hvu
  exfalso
  let e : Env := (({} : Env).insert ⟨"ACL2", "y"⟩ v).insert ⟨"ACL2", "x"⟩ u
  have hx : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e xT = some u :=
    conv_var_of_get _ _ _ _ (by simp [e, Env.get?_insert])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e yT = some v :=
    conv_var_of_get _ _ _ _ (by
      simp only [e, Env.get?_insert]
      rw [if_neg (by decide)]; simp)
  have himp := conv_impliesT eqWorldD e (equalT xT yT) (equalT yT xT)
    (Logic.equal u v) (Logic.equal v u) (by decide)
    (conv_equalT eqWorldD e xT yT u v (by decide) hx hy)
    (conv_equalT eqWorldD e yT xT v u (by decide) hy hx)
  obtain ⟨Ni, hi⟩ := himp
  obtain ⟨Nm, hm⟩ := equalSymmMirrorCond e
  set f := max Ni Nm
  have hval : Logic.implies (Logic.equal u v) (Logic.equal v u) = SExpr.t :=
    Option.some.inj ((hi f (by omega)).symm.trans (hm f (by omega)))
  rw [logic_implies_cond, (Logic.equal_t_iff _ _).mpr h] at hval
  rw [show Logic.equal v u = SExpr.nil by
    simp [Logic.equal, beq_iff_eq, hvu]] at hval
  exact absurd hval (by decide)

/-- ENTRY 7, PROVED — transitivity of equality over `SExpr`, through the
    DRIVER's mirror (hypothesis decode through the formula's `if`-spine:
    `(implies (if (equal x y) (equal y z) 'nil) (equal x z))`). -/
theorem equal_trans_native (u v w' : SExpr) (h1 : u = v) (h2 : v = w') :
    u = w' := by
  by_cases huw : u = w'
  · exact huw
  exfalso
  let e : Env := ((({} : Env).insert ⟨"ACL2", "z"⟩ w').insert ⟨"ACL2", "y"⟩ v).insert
    ⟨"ACL2", "x"⟩ u
  have hx : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e xT = some u :=
    conv_var_of_get _ _ _ _ (by simp [e, Env.get?_insert])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e yT = some v :=
    conv_var_of_get _ _ _ _ (by
      simp only [e, Env.get?_insert]
      rw [if_neg (by decide)]; simp)
  have hz : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e zT = some w' :=
    conv_var_of_get _ _ _ _ (by
      simp only [e, Env.get?_insert]
      rw [if_neg (by decide), if_neg (by decide)]; simp)
  -- the if-spine antecedent: test (equal x y) ⇒ t (from h1), so the spine
  -- converges to the then-branch value (equal y z)'s value
  have hif : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e
      (.cons (.atom (.symbol { name := "if" }))
        (.cons (equalT xT yT) (.cons (equalT yT zT)
          (.cons (.cons (.atom (.symbol { name := "quote" })) (.cons .nil .nil)) .nil))))
      = some (Logic.equal v w') :=
    conv_if_true eqWorldD e (equalT xT yT) (equalT yT zT) _
      (Logic.equal u v) (Logic.equal v w')
      (conv_equalT eqWorldD e xT yT u v (by decide) hx hy)
      (by rw [(Logic.equal_t_iff _ _).mpr h1]; decide)
      (conv_equalT eqWorldD e yT zT v w' (by decide) hy hz)
  have himp := conv_impliesT eqWorldD e _ (equalT xT zT)
    (Logic.equal v w') (Logic.equal u w') (by decide) hif
    (conv_equalT eqWorldD e xT zT u w' (by decide) hx hz)
  obtain ⟨Ni, hi⟩ := himp
  obtain ⟨Nm, hm⟩ := equalTransMirrorCond e
  set f := max Ni Nm
  have hval : Logic.implies (Logic.equal v w') (Logic.equal u w') = SExpr.t :=
    Option.some.inj ((hi f (by omega)).symm.trans (hm f (by omega)))
  rw [logic_implies_cond, (Logic.equal_t_iff _ _).mpr h2] at hval
  rw [show Logic.equal u w' = SExpr.nil by
    simp [Logic.equal, beq_iff_eq, huw]] at hval
  exact absurd hval (by decide)

/-! ## Entry 8 — `app-cons-car`: `Logic.car (cons u v) = u`

From `recon-tests/01-multi-theorem.proof-log` (`(equal (car (app (cons a b) y))
a)`, cond[total:app]). The deepest decode so far: instantiating `b ↦ nil`
makes the app-value collapse to `cons u v` — the decode layer UNFOLDS `app`
twice (cons-case then nil-case of the body's if) — while the outer `car` is
kept SYMBOLIC, so the mirror's equality yields the fully generic
`Logic.car (cons u v) = u`. -/

private def multiLog : String := include_str "../../acl2_samples/recon-tests/01-multi-theorem.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def multiDev : Development :=
  (((ProofLog.parse multiLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world multiWorldD from multiDev

def appConsCarMirrorCond := driver_mirror% multiDev multiWorldD "app-cons-car"

private def aT : SExpr := .atom (.symbol { name := "a" })
private def bT : SExpr := .atom (.symbol { name := "b" })
private def consT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil))
private def carT (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "car" })) (.cons a .nil)
private def cdrT (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "cdr" })) (.cons a .nil)
private def conspT (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "consp" })) (.cons a .nil)
private def appT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "app" })) (.cons a (.cons b .nil))
private def xS : Symbol := ⟨"ACL2", "x"⟩
private def yS : Symbol := ⟨"ACL2", "y"⟩

/-- `app`'s body converges to `v` when `x ↦ nil, y ↦ v` (the if's else). -/
private theorem appBody_nil_case (v : SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.nil, v])
      Worlds.AppAssoc.appBody = some v := by
  have hx : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.nil, v]) xT
      = some SExpr.nil :=
    conv_var_of_get _ _ _ _ (by
      show (((({} : Env).insert yS v).insert xS SExpr.nil)).get? xS = some SExpr.nil
      simp [Env.get?_insert])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.nil, v]) yT
      = some v :=
    conv_var_of_get _ _ _ _ (by
      show (((({} : Env).insert yS v).insert xS SExpr.nil)).get? yS = some v
      simp only [Env.get?_insert]
      rw [if_neg (by decide)]; simp)
  have hconsp : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.nil, v]) (conspT xT)
      = some (Logic.consp SExpr.nil) :=
    conv_builtin1 multiWorldD _ { name := "consp" } xT SExpr.nil _ (by decide)
      (by decide) hx (callBuiltin_consp _)
  obtain ⟨Nc, hc⟩ := hconsp
  obtain ⟨Ny, hyv⟩ := hy
  refine ⟨max Nc Ny + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show evalOpt (g + 1) multiWorldD (bindArgs [xS, yS] [SExpr.nil, v])
    (.cons (.atom (.symbol { name := "if" }))
      (.cons (conspT xT)
        (.cons (consT (carT xT) (appT (cdrT xT) yT)) (.cons yT .nil))))
    = some v
  rw [evalOpt_if_false g multiWorldD _ _ _ yT (by rw [hc g (by omega)]; rfl)]
  exact hyv g (by omega)

/-- `app`'s body converges to `cons u v` when `x ↦ cons u nil, y ↦ v` (the
    if's then-branch; the recursive `app` call lands in the nil case). -/
private theorem appBody_cons_case (u v : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v])
        Worlds.AppAssoc.appBody = some (SExpr.cons u v) := by
  have hx : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v]) xT
      = some (SExpr.cons u SExpr.nil) :=
    conv_var_of_get _ _ _ _ (by
      show (((({} : Env).insert yS v).insert xS (SExpr.cons u SExpr.nil))).get? xS
        = some (SExpr.cons u SExpr.nil)
      simp [Env.get?_insert])
  have hy : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v]) yT
      = some v :=
    conv_var_of_get _ _ _ _ (by
      show (((({} : Env).insert yS v).insert xS (SExpr.cons u SExpr.nil))).get? yS
        = some v
      simp only [Env.get?_insert]
      rw [if_neg (by decide)]; simp)
  have hconsp : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v]) (conspT xT)
      = some (Logic.consp (SExpr.cons u SExpr.nil)) :=
    conv_builtin1 multiWorldD _ { name := "consp" } xT _ _ (by decide)
      (by decide) hx (callBuiltin_consp _)
  -- (car x) ⇒ u, (cdr x) ⇒ nil
  have hcar : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v]) (carT xT)
      = some u := by
    have h := conv_builtin1 multiWorldD _ { name := "car" } xT
      (SExpr.cons u SExpr.nil) _ (by decide) (by decide) hx (callBuiltin_car _)
    rwa [logic_car_cons] at h
  have hcdr : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v]) (cdrT xT)
      = some SExpr.nil := by
    have h := conv_builtin1 multiWorldD _ { name := "cdr" } xT
      (SExpr.cons u SExpr.nil) _ (by decide) (by decide) hx (callBuiltin_cdr _)
    rwa [logic_cdr_cons] at h
  -- the recursive call: app nil v ⇒ v  (definition unfold into the nil case)
  have hinner : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v])
        (appT (cdrT xT) yT) = some v :=
    conv_defn_2 multiWorldD _ { name := "app" } (cdrT xT) yT SExpr.nil v xS yS
      Worlds.AppAssoc.appBody v (by decide) (by decide) hcdr hy (appBody_nil_case v)
  -- then-branch: (cons (car x) (app (cdr x) y)) ⇒ cons u v
  have hthen : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v])
        (consT (carT xT) (appT (cdrT xT) yT)) = some (SExpr.cons u v) :=
    conv_builtin2 multiWorldD _ { name := "cons" } _ _ u v _ (by decide)
      (by decide) hcar hinner (callBuiltin_cons _ _)
  exact conv_if_true multiWorldD _ (conspT xT) (consT (carT xT) (appT (cdrT xT) yT))
    yT (Logic.consp (SExpr.cons u SExpr.nil)) (SExpr.cons u v) hconsp rfl hthen

/-- ENTRY 8, PROVED — the fully generic `car ∘ cons = fst` at the `Logic`
    layer, through the DRIVER's mirror: instantiate `b ↦ nil` so
    `(app (cons a b) y)` collapses to `cons u v` (two definition unfolds in
    the decode), keep the outer `car` symbolic, and the mirror equates. -/
theorem car_cons_native (u v : SExpr) : Logic.car (SExpr.cons u v) = u := by
  let e : Env := ((({} : Env).insert ⟨"ACL2", "y"⟩ v).insert
    ⟨"ACL2", "b"⟩ SExpr.nil).insert ⟨"ACL2", "a"⟩ u
  have ha : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e aT = some u :=
    conv_var_of_get _ _ _ _ (by simp [e, Env.get?_insert])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e bT = some SExpr.nil :=
    conv_var_of_get _ _ _ _ (by
      simp only [e, Env.get?_insert]
      rw [if_neg (by decide)]; simp)
  have hy : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e yT = some v :=
    conv_var_of_get _ _ _ _ (by
      simp only [e, Env.get?_insert]
      rw [if_neg (by decide), if_neg (by decide)]; simp)
  have hcons : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e (consT aT bT)
      = some (SExpr.cons u SExpr.nil) :=
    conv_builtin2 multiWorldD e { name := "cons" } aT bT u SExpr.nil _ (by decide)
      (by decide) ha hb (callBuiltin_cons _ _)
  have happ : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e (appT (consT aT bT) yT)
      = some (SExpr.cons u v) :=
    conv_defn_2 multiWorldD e { name := "app" } (consT aT bT) yT
      (SExpr.cons u SExpr.nil) v xS yS Worlds.AppAssoc.appBody (SExpr.cons u v)
      (by decide) (by decide) hcons hy (appBody_cons_case u v)
  -- the outer car: kept SYMBOLIC — the mirror's equality is the content
  have hL : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e (carT (appT (consT aT bT) yT))
      = some (Logic.car (SExpr.cons u v)) :=
    conv_builtin1 multiWorldD e { name := "car" } _ (SExpr.cons u v) _ (by decide)
      (by decide) happ (callBuiltin_car _)
  obtain ⟨NL, hL'⟩ := hL
  obtain ⟨NR, hR'⟩ := ha
  obtain ⟨Nm, hm⟩ := appConsCarMirrorCond e
    (fun e' a0 a1 h0 h1 =>
      Worlds.AppAssoc.drv_total_app multiWorldD (by decide) (by decide)
        (by decide) (by decide) (by decide) e' a0 a1 h0 h1)
  set f := max (max NL NR) Nm
  exact eval_equal_t_implies_eq f multiWorldD e _ aT (Logic.car (SExpr.cons u v)) u
    (hL' f (by omega)) (hR' f (by omega)) (by decide) (hm (f + 1) (by omega))

end ACL2.Imported.Mirrors
