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
    9. perm-cons       a ∈ xs → (xs ~ a::ys ↔ xs.erase a ~ ys)    [UNCONDITIONAL
                                                                   mirror; List.Perm]
   10. perm-symmetric  isPerm symm (+ Perm corollary)             [decode kit]
   11. memb-rm         contains survives erase                    [decode kit]
   12. comm-rm         erase_comm (LIST equality via enc_inj)     [decode kit]
   13. perm-memb       membership transports across isPerm        [and-cond decode]
   14. perm-rm         isPerm preserved by erase (+ corollary)    [decode kit]
   15. perm-transitive isPerm trans (+ Perm corollary)            [and-cond decode]
   16. perm-refl       isPerm refl, peeled from the defequiv
                       tower; + isPerm_equivalence_driver bundle  [mirror_peel_guard]
  THE WHOLE PERM BOOK IS IMPORTED: 8 unconditional mirrors, 8 native facts,
  zero hypotheses (lifter sprint 2026-07-06).
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
import ACL2Lean.Imported.Lifting
import ACL2Lean.Imported.Perm

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## Entry 1 — `my-len-my-app`: `(xs ++ ys).length = xs.length + ys.length`

The full chain, end to end: the REAL `simple.proof-log` → parse → reconstruct
→ the log-DERIVED world → the driver's conditional mirror (totality/TP
hypotheses) → hypotheses DISCHARGED (the WORLD-PARAMETRIC hand dischargers,
instantiated directly at the log-derived world) → instantiated at encoded
lists → the simulation lemmas → the native statement. -/

private def simpleLog : String := include_str "../../acl2_samples/simple.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def simpleDev : Development :=
  (((ProofLog.parse simpleLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world simpleWorldD from simpleDev

/-- `driver_mirror% dev world "thm-name"` — the DRIVER's conditional mirror
    for the named theorem of the development `dev`, over the derived world
    constant `world`: a `∀ env, <hypotheses> → ∃N∀f≥N ∃v, eval = some v ∧
    v ≠ nil` proof OBJECT (ACL2's truthiness claim, G2) produced by
    `replayProofConditional` from the reconstructed tree. -/
elab "driver_mirror%" devId:ident worldId:ident nm:str : term => do
  let devName ← Lean.resolveGlobalConstNoOverload devId
  let worldName ← Lean.resolveGlobalConstNoOverload worldId
  let dev ← unsafe Meta.evalExpr Development (mkConst ``ACL2.Development)
    (mkConst devName)
  let some cp := Driver.findThm dev nm.getString
    | throwError "{nm.getString}: not found in the development (or ambiguous \
                  up to case — findThm refuses to guess)"
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst worldName, envExpr := env, worldVal := dev.toWorld,
        gzDefs := dev.groundZeroSnapshotDefs, justs := dev.justifications }
    let (proof, _conds) ← replayProofConditional cfg dev.typePrescriptions cp
      dev.justifications (Driver.rulesBefore dev nm.getString)
      ((Driver.developmentTheoremsWithRules dev).map fun (c, _) => (c.name, c))
    Meta.mkLambdaFVars #[env] proof

/-- The conditional mirror as a definition (the driver's proof OBJECT). -/
def mylenMirrorCond := driver_mirror% simpleDev simpleWorldD "my-len-my-app"

/-! ### The unconditional driver mirror — direct world-parametric discharge

The driver's four hypotheses are discharged by the WORLD-PARAMETRIC hand
dischargers (invariant L3) instantiated directly at the log-derived world —
every world fact a `decide` on the reflected world. No defs-extensionality
transfer is needed; the `evalOpt_defs_ext` route remains in `EvalOpt` as the
documented fallback for world-concrete machinery. The stated formula is the
hand `my_len_my_appFormula` — it and the log-derived statement are the same
term, so the proof closes definitionally. -/

theorem mylenMirror_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f simpleWorldD env
      Worlds.Simple.my_len_my_appFormula = some v ∧ v ≠ SExpr.nil :=
  -- the total:my-len/my-app/fix hypotheses are AUTO-DISCHARGED by the driver
  -- from the emitted admission data (#37); only the TP hypothesis remains
  mylenMirrorCond env
    (Worlds.Simple.drv_tp_mylen simpleWorldD (by decide) (by decide)
      (by decide) (by decide))

/-- ENTRY 1, PROVED — the native statement through the DRIVER's replayed
    mirror: log → parse → reconstruct → derived world → conditional replay →
    discharged hypotheses → simulation decode, all directly over the
    log-derived world. -/
theorem my_len_my_app_native_driver (xs ys : List SExpr) :
    (xs ++ ys).length = xs.length + ys.length :=
  Worlds.Simple.my_len_my_app_native_of_mirror simpleWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) mylenMirror_uncond xs ys

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
    `∀ env, total:app → <EvTrue of (equal (app (app a b) c)
    (app a (app b c)))>` (truthiness, G2). -/
def appAssocMirrorCond := driver_mirror% revDev revWorldD "app-assoc"

/-- The driver mirror — UNCONDITIONAL: its sole `total:app` hypothesis is
    AUTO-DISCHARGED by the driver from the emitted admission data (#37). -/
theorem appAssocMirror_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f revWorldD env
      Worlds.AppAssoc.app_assocFormula = some v ∧ v ≠ SExpr.nil :=
  appAssocMirrorCond env

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

/-- ENTRY 3, PROVED — the ground arithmetic fact through the DRIVER's
    replayed mirror (executable-counterpart class). -/
theorem ground_arith_native : (1 + (2 + 3) : Int) = 6 :=
  native_of_mirror_equal directWorldD {} intRep
    (plusT (qInt 1) (plusT (qInt 2) (qInt 3))) (qInt 6) (1 + (2 + 3)) 6
    (by decide)
    (implements_plus directWorldD (by decide) {} (qInt 1) (plusT (qInt 2) (qInt 3))
      1 (2 + 3) (conv_qInt _ _ 1)
      (implements_plus directWorldD (by decide) {} (qInt 2) (qInt 3) 2 3
        (conv_qInt _ _ 2) (conv_qInt _ _ 3)))
    (conv_qInt _ _ 6)
    (groundArithMirrorCond {})

/-! ## Entry 4 — `sq-of-3`: `(3 * 3 : Int) = 9`

Same log (00-direct), one step richer than entry 3: the formula applies the
USER-DEFINED `sq` (body `(binary-* n n)`) to a ground argument, so the decode
unfolds the definition (`conv_defn_1`) and evaluates the body symbolically —
`int (3 * 3)` — before the mirror's `equal ⇒ t` fact equates it with `int 9`. -/

/-- The mirror as a definition (UNCONDITIONAL — executable-counterpart
    discharge; `sq`'s unfold is part of the replayed evaluation). -/
def sqOf3MirrorCond := driver_mirror% directDev directWorldD "sq-of-3"

private def n_sym : Symbol := { package := "ACL2", name := "N" }
private def nT : SExpr := .atom (.symbol { name := "N" })
private def sqBody : SExpr :=
  .cons (.atom (.symbol { name := "BINARY-*" })) (.cons nT (.cons nT .nil))

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
      (.cons (.atom (.symbol { name := "SQ" })) (.cons (qInt 3) .nil))
      = some (.atom (.number (.int (3 * 3)))) :=
    conv_defn_1 directWorldD e { name := "SQ" } (qInt 3) (.atom (.number (.int 3)))
      n_sym sqBody (.atom (.number (.int (3 * 3))))
      (by decide) (by decide) (conv_qInt _ _ 3) hbody
  have hR := conv_qInt directWorldD e 9
  exact native_of_mirror_equal directWorldD e intRep
    (app1 "SQ" (qInt 3)) (qInt 9) (3 * 3) 9 (by decide) hL hR (sqOf3MirrorCond e)

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

private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def zT : SExpr := .atom (.symbol { name := "Z" })
/-- ENTRY 5, PROVED — `cdr ∘ cons = snd` at the `Logic` layer, through the
    DRIVER's mirror: the lhs is evaluated only SYMBOLICALLY (to
    `Logic.cdr (cons u v)`), so the equation is the mirror's content. -/
theorem cdr_cons_native (u v : SExpr) : Logic.cdr (SExpr.cons u v) = v := by
  let e : Env := (({} : Env).insert { package := "ACL2", name := "Y" } v).insert { package := "ACL2", name := "X" } u
  have hx : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e xT = some u :=
    conv_var_of_get _ _ _ _ (by simp [e, Env.get?_insert])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e yT = some v :=
    conv_var_of_get _ _ _ _ (by
      simp only [e, Env.get?_insert]
      rw [if_neg (by decide)]; simp)
  have hcons : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e
      (.cons (.atom (.symbol { name := "CONS" })) (.cons xT (.cons yT .nil)))
      = some (SExpr.cons u v) :=
    conv_builtin2 eqWorldD e { name := "CONS" } xT yT u v _ (by decide)
      (by decide) hx hy (callBuiltin_cons _ _)
  have hcdr : ∃ N, ∀ f ≥ N, evalOpt f eqWorldD e
      (.cons (.atom (.symbol { name := "CDR" }))
        (.cons (.cons (.atom (.symbol { name := "CONS" })) (.cons xT (.cons yT .nil))) .nil))
      = some (Logic.cdr (SExpr.cons u v)) :=
    conv_builtin1 eqWorldD e { name := "CDR" } _ (SExpr.cons u v) _ (by decide)
      (by decide) hcons (callBuiltin_cdr _)
  exact native_of_mirror_equal eqWorldD e idRep
    (cdrT (consT xT yT)) yT (Logic.cdr (SExpr.cons u v)) v
    (by decide) hcdr hy (cdrConsMirrorCond e)

/-- ENTRY 6, PROVED — symmetry of equality over `SExpr`, through the DRIVER's
    mirror (the HYPOTHESIS decode: `h` truthifies the antecedent, the mirror's
    `implies ⇒ t` forces the conclusion). -/
theorem equal_symm_native (u v : SExpr) (h : u = v) : v = u := by
  let e : Env := (({} : Env).insert { package := "ACL2", name := "Y" } v).insert { package := "ACL2", name := "X" } u
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
  have hval : Logic.implies (Logic.equal u v) (Logic.equal v u) = SExpr.t :=
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (equalSymmMirrorCond e) himp)
  exact eq_of_equal_truthy (truthy_of_implies_t hval (equal_truthy_of_eq h))

/-- ENTRY 7, PROVED — transitivity of equality over `SExpr`, through the
    DRIVER's mirror (hypothesis decode through the formula's `if`-spine:
    `(implies (if (equal x y) (equal y z) 'nil) (equal x z))`). -/
theorem equal_trans_native (u v w' : SExpr) (h1 : u = v) (h2 : v = w') :
    u = w' := by
  let e : Env := ((({} : Env).insert { package := "ACL2", name := "Z" } w').insert { package := "ACL2", name := "Y" } v).insert
    { package := "ACL2", name := "X" } u
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
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons (equalT xT yT) (.cons (equalT yT zT)
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)) .nil))))
      = some (Logic.equal v w') :=
    conv_if_true eqWorldD e (equalT xT yT) (equalT yT zT) _
      (Logic.equal u v) (Logic.equal v w')
      (conv_equalT eqWorldD e xT yT u v (by decide) hx hy)
      (equal_truthy_of_eq h1)
      (conv_equalT eqWorldD e yT zT v w' (by decide) hy hz)
  have himp := conv_impliesT eqWorldD e _ (equalT xT zT)
    (Logic.equal v w') (Logic.equal u w') (by decide) hif
    (conv_equalT eqWorldD e xT zT u w' (by decide) hx hz)
  have hval : Logic.implies (Logic.equal v w') (Logic.equal u w') = SExpr.t :=
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (equalTransMirrorCond e) himp)
  exact eq_of_equal_truthy (truthy_of_implies_t hval (equal_truthy_of_eq h2))

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

private def aT : SExpr := .atom (.symbol { name := "A" })
private def bT : SExpr := .atom (.symbol { name := "B" })
private def appT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "APP" })) (.cons a (.cons b .nil))
private def xS : Symbol := { package := "ACL2", name := "X" }
private def yS : Symbol := { package := "ACL2", name := "Y" }

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
    conv_builtin1 multiWorldD _ { name := "CONSP" } xT SExpr.nil _ (by decide)
      (by decide) hx (callBuiltin_consp _)
  obtain ⟨Nc, hc⟩ := hconsp
  obtain ⟨Ny, hyv⟩ := hy
  refine ⟨max Nc Ny + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show evalOpt (g + 1) multiWorldD (bindArgs [xS, yS] [SExpr.nil, v])
    (.cons (.atom (.symbol { name := "IF" }))
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
    conv_builtin1 multiWorldD _ { name := "CONSP" } xT _ _ (by decide)
      (by decide) hx (callBuiltin_consp _)
  -- (car x) ⇒ u, (cdr x) ⇒ nil
  have hcar : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v]) (carT xT)
      = some u := by
    have h := conv_builtin1 multiWorldD _ { name := "CAR" } xT
      (SExpr.cons u SExpr.nil) _ (by decide) (by decide) hx (callBuiltin_car _)
    rwa [logic_car_cons] at h
  have hcdr : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v]) (cdrT xT)
      = some SExpr.nil := by
    have h := conv_builtin1 multiWorldD _ { name := "CDR" } xT
      (SExpr.cons u SExpr.nil) _ (by decide) (by decide) hx (callBuiltin_cdr _)
    rwa [logic_cdr_cons] at h
  -- the recursive call: app nil v ⇒ v  (definition unfold into the nil case)
  have hinner : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v])
        (appT (cdrT xT) yT) = some v :=
    conv_defn_2 multiWorldD _ { name := "APP" } (cdrT xT) yT SExpr.nil v xS yS
      Worlds.AppAssoc.appBody v (by decide) (by decide) hcdr hy (appBody_nil_case v)
  -- then-branch: (cons (car x) (app (cdr x) y)) ⇒ cons u v
  have hthen : ∃ N, ∀ f ≥ N,
      evalOpt f multiWorldD (bindArgs [xS, yS] [SExpr.cons u SExpr.nil, v])
        (consT (carT xT) (appT (cdrT xT) yT)) = some (SExpr.cons u v) :=
    conv_builtin2 multiWorldD _ { name := "CONS" } _ _ u v _ (by decide)
      (by decide) hcar hinner (callBuiltin_cons _ _)
  exact conv_if_true multiWorldD _ (conspT xT) (consT (carT xT) (appT (cdrT xT) yT))
    yT (Logic.consp (SExpr.cons u SExpr.nil)) (SExpr.cons u v) hconsp rfl hthen

/-- ENTRY 8, PROVED — the fully generic `car ∘ cons = fst` at the `Logic`
    layer, through the DRIVER's mirror: instantiate `b ↦ nil` so
    `(app (cons a b) y)` collapses to `cons u v` (two definition unfolds in
    the decode), keep the outer `car` symbolic, and the mirror equates. -/
theorem car_cons_native (u v : SExpr) : Logic.car (SExpr.cons u v) = u := by
  let e : Env := ((({} : Env).insert { package := "ACL2", name := "Y" } v).insert
    { package := "ACL2", name := "B" } SExpr.nil).insert { package := "ACL2", name := "A" } u
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
    conv_builtin2 multiWorldD e { name := "CONS" } aT bT u SExpr.nil _ (by decide)
      (by decide) ha hb (callBuiltin_cons _ _)
  have happ : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e (appT (consT aT bT) yT)
      = some (SExpr.cons u v) :=
    conv_defn_2 multiWorldD e { name := "APP" } (consT aT bT) yT
      (SExpr.cons u SExpr.nil) v xS yS Worlds.AppAssoc.appBody (SExpr.cons u v)
      (by decide) (by decide) hcons hy (appBody_cons_case u v)
  -- the outer car: kept SYMBOLIC — the mirror's equality is the content
  have hL : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e (carT (appT (consT aT bT) yT))
      = some (Logic.car (SExpr.cons u v)) :=
    conv_builtin1 multiWorldD e { name := "CAR" } _ (SExpr.cons u v) _ (by decide)
      (by decide) happ (callBuiltin_car _)
  exact native_of_mirror_equal multiWorldD e idRep
    (carT (appT (consT aT bT) yT)) aT (Logic.car (SExpr.cons u v)) u
    (by decide) hL ha
    (appConsCarMirrorCond e)

/-! ## Entry 9 — `perm-cons` (the sorting corpus, R1):
`a ∈ xs → (xs ~ a :: ys ↔ xs.erase a ~ ys)`

The FULL chain on the perm book's first replayed theorem: the REAL
`sorting/perm.proof-log` → parse → reconstruct → the log-DERIVED world → the
driver's mirror (the branch-split composer, destructor elimination, the
whole R1 node family) — UNCONDITIONAL: all totality auto-discharged from
admission data and all TP corollaries by the TP prover (`proveTp`), both
landed in the 2026-07-06 lifter sprint — → the `contains`/`erase`/`isPerm`
simulations → the native statement over `List.Perm`. The hand dischargers
in `Imported/Perm.lean` remain as the provers' validated models. -/

private def permLog9 : String := include_str "../../acl2_samples/sorting/perm.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def permDev : Development :=
  (((ProofLog.parse permLog9).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world permWorldD from permDev

/-- The driver's mirror proof OBJECT — UNCONDITIONAL as produced (totality
    by the admission prover, TP corollaries by the TP prover): no
    hypotheses left to discharge. -/
def permConsMirrorCond := driver_mirror% permDev permWorldD "perm-cons"

theorem permConsMirror_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f permWorldD env
      Worlds.Perm.perm_consFormula = some v ∧ v ≠ SExpr.nil :=
  permConsMirrorCond env

/-- ENTRY 9, PROVED — the Boolean form through the DRIVER's replayed mirror. -/
theorem perm_cons_native_driver (a : SExpr) (xs ys : List SExpr)
    (h : xs.contains a = true) :
    xs.isPerm (a :: ys) = (xs.erase a).isPerm ys :=
  Worlds.Perm.perm_cons_native_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permConsMirror_uncond a xs ys h

/-- ENTRY 9, PROVED — the idiomatic `List.Perm` form: a member moves across
    the permutation relation. -/
theorem perm_cons_native_perm_driver (a : SExpr) (xs ys : List SExpr)
    (h : a ∈ xs) :
    xs.Perm (a :: ys) ↔ (xs.erase a).Perm ys :=
  Worlds.Perm.perm_cons_native_perm_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permConsMirror_uncond a xs ys h

#print axioms perm_cons_native_perm_driver

/-! ## Entries 10–16 — the REST of the perm book (lifter sprint 2026-07-06)

Every remaining theorem's UNCONDITIONAL driver mirror, decoded natively
through the same `corr_*` layer with the Lifting decode kit. The whole ACL2
book is now imported: 8 mirrors, 8 native facts, zero hypotheses. -/

def permSymmetricMirror := driver_mirror% permDev permWorldD "perm-symmetric"
def membRmMirror := driver_mirror% permDev permWorldD "memb-rm"
def permMembMirror := driver_mirror% permDev permWorldD "perm-memb"
def commRmMirror := driver_mirror% permDev permWorldD "comm-rm"
def permRmMirror := driver_mirror% permDev permWorldD "perm-rm"
def permTransitiveMirror := driver_mirror% permDev permWorldD "perm-transitive"
def permEquivMirror := driver_mirror% permDev permWorldD "perm-is-an-equivalence"

/-- ENTRY 10, PROVED — perm-symmetric: `isPerm` is symmetric. -/
theorem perm_symmetric_native_driver (xs ys : List SExpr)
    (h : xs.isPerm ys = true) : ys.isPerm xs = true :=
  Worlds.Perm.perm_symmetric_native_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permSymmetricMirror xs ys h

/-- ENTRY 11, PROVED — memb-rm: membership survives erasing another element. -/
theorem memb_rm_native_driver (av bv : SExpr) (xs : List SExpr)
    (h : (xs.erase bv).contains av = true) : xs.contains av = true :=
  Worlds.Perm.memb_rm_native_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    membRmMirror av bv xs h

/-- ENTRY 12, PROVED — comm-rm: erasures commute (the Mathlib
    `List.erase_comm` fact, imported from ACL2). -/
theorem comm_rm_native_driver (av bv : SExpr) (xs : List SExpr) :
    (xs.erase bv).erase av = (xs.erase av).erase bv :=
  Worlds.Perm.comm_rm_native_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) commRmMirror av bv xs

/-- ENTRY 13, PROVED — perm-memb: membership transports across `isPerm`. -/
theorem perm_memb_native_driver (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) (hm : xs.contains av = true) :
    ys.contains av = true :=
  Worlds.Perm.perm_memb_native_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permMembMirror av xs ys hp hm

/-- ENTRY 14, PROVED — perm-rm: `isPerm` is preserved by erasing the same
    element from both sides. -/
theorem perm_rm_native_driver (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) :
    (xs.erase av).isPerm (ys.erase av) = true :=
  Worlds.Perm.perm_rm_native_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permRmMirror av xs ys hp

/-- ENTRY 15, PROVED — perm-transitive: `isPerm` is transitive. -/
theorem perm_transitive_native_driver (xs ys zs : List SExpr)
    (hxy : xs.isPerm ys = true) (hyz : ys.isPerm zs = true) :
    xs.isPerm zs = true :=
  Worlds.Perm.perm_transitive_native_of_mirror permWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) permTransitiveMirror xs ys zs hxy hyz

/-- ENTRY 16, PROVED — perm-is-an-equivalence: reflexivity (the conjunct
    with no standalone theorem), decoded by peeling the defequiv tower. -/
theorem perm_refl_native_driver (xs : List SExpr) : xs.isPerm xs = true :=
  Worlds.Perm.perm_refl_native_of_mirror permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permEquivMirror xs

/-- The BUNDLE — ACL2's defequiv, in Lean's own terms: `isPerm` is an
    equivalence relation, assembled from entries 10/15/16. -/
theorem isPerm_equivalence_driver :
    Equivalence (fun xs ys : List SExpr => xs.isPerm ys = true) where
  refl := perm_refl_native_driver
  symm := fun h => perm_symmetric_native_driver _ _ h
  trans := fun h1 h2 => perm_transitive_native_driver _ _ _ h1 h2

/-- The idiomatic `List.Perm` corollaries. -/
theorem perm_symm_perm_driver {xs ys : List SExpr} (h : xs.Perm ys) :
    ys.Perm xs :=
  List.isPerm_iff.mp
    (perm_symmetric_native_driver xs ys (List.isPerm_iff.mpr h))

theorem perm_trans_perm_driver {xs ys zs : List SExpr}
    (h1 : xs.Perm ys) (h2 : ys.Perm zs) : xs.Perm zs :=
  List.isPerm_iff.mp (perm_transitive_native_driver xs ys zs
    (List.isPerm_iff.mpr h1) (List.isPerm_iff.mpr h2))

theorem perm_erase_perm_driver (av : SExpr) {xs ys : List SExpr}
    (h : xs.Perm ys) : (xs.erase av).Perm (ys.erase av) :=
  List.isPerm_iff.mp
    (perm_rm_native_driver av xs ys (List.isPerm_iff.mpr h))

theorem mem_transport_perm_driver {av : SExpr} {xs ys : List SExpr}
    (h : xs.Perm ys) (hm : av ∈ xs) : av ∈ ys := by
  have := perm_memb_native_driver av xs ys (List.isPerm_iff.mpr h)
    (by simpa [List.contains_iff_mem] using hm)
  simpa [List.contains_iff_mem] using this

#print axioms isPerm_equivalence_driver
#print axioms comm_rm_native_driver
#print axioms perm_erase_perm_driver

-- BUILD-FAILING axiom gate (audit #4; completed to ALL native entries in
-- audit #5): `#print axioms` only prints — this run_cmd THROWS if any native
-- entry ever acquires an axiom beyond the classical trio (sorryAx,
-- native_decide's ofReduceBool, …), so a future edit cannot smuggle a hole
-- into the native layer without failing CI. The list must name EVERY proved
-- native entry in this file (the earlier list omitted the 7 pre-perm
-- entries — all clean, but ungated; audit #5 closed that gap).
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ACL2.Imported.Mirrors.perm_cons_native_driver,
            ``ACL2.Imported.Mirrors.perm_cons_native_perm_driver,
            ``ACL2.Imported.Mirrors.perm_symmetric_native_driver,
            ``ACL2.Imported.Mirrors.memb_rm_native_driver,
            ``ACL2.Imported.Mirrors.comm_rm_native_driver,
            ``ACL2.Imported.Mirrors.perm_memb_native_driver,
            ``ACL2.Imported.Mirrors.perm_rm_native_driver,
            ``ACL2.Imported.Mirrors.perm_transitive_native_driver,
            ``ACL2.Imported.Mirrors.perm_refl_native_driver,
            ``ACL2.Imported.Mirrors.isPerm_equivalence_driver,
            ``ACL2.Imported.Mirrors.perm_symm_perm_driver,
            ``ACL2.Imported.Mirrors.perm_trans_perm_driver,
            ``ACL2.Imported.Mirrors.perm_erase_perm_driver,
            ``ACL2.Imported.Mirrors.mem_transport_perm_driver,
            ``ACL2.Imported.Mirrors.my_len_my_app_native_driver,
            ``ACL2.Imported.Mirrors.app_assoc_native_driver,
            ``ACL2.Imported.Mirrors.ground_arith_native,
            ``ACL2.Imported.Mirrors.sq_of_3_native,
            ``ACL2.Imported.Mirrors.cdr_cons_native,
            ``ACL2.Imported.Mirrors.equal_symm_native,
            ``ACL2.Imported.Mirrors.equal_trans_native,
            ``ACL2.Imported.Mirrors.car_cons_native] do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "native-entry axiom gate: {n} uses forbidden axioms {bad}"

end ACL2.Imported.Mirrors
