/-
  THE NATIVE MIRROR CATALOG (task #62; design doc §6).

  One section per corpus theorem: the result stated in NATIVE Lean terms,
  proved THROUGH the ACL2 replay — the driver's conditional replayed statement, its
  hypotheses discharged for the log-derived world, decoded to the native
  statement via the `enc`/`corr_*` simulation layer. Each PROVED entry is a
  build-enforced regression; each PENDING entry names the blocking frontier.
  The accumulated patterns are the seed of a future standard lifting library
  (polymorphic `α ↪ SExpr` statements are deliberately deferred — TODO.md).

  ── SCOREBOARD ────────────────────────────────────────────────────────────
  PROVED (via the driver's replayed statement):
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
                                                                   replayed stmt; List.Perm]
   10. perm-symmetric  isPerm symm (+ Perm corollary)             [decode kit]
   11. memb-rm         contains survives erase                    [decode kit]
   12. comm-rm         erase_comm (LIST equality via enc_inj)     [decode kit]
   13. perm-memb       membership transports across isPerm        [and-cond decode]
   14. perm-rm         isPerm preserved by erase (+ corollary)    [decode kit]
   15. perm-transitive isPerm trans (+ Perm corollary)            [and-cond decode]
   16. perm-refl       isPerm refl, peeled from the defequiv
                       tower; + isPerm_equivalence_driver bundle  [replayed_peel_guard]
  THE WHOLE PERM BOOK IS IMPORTED: 8 unconditional replayed statements, 8 native facts,
  zero hypotheses (lifter sprint 2026-07-06).
   17. p7-cong-collapse (l.map (fun _ => '0)).length = l.length
                        [FIRST VALIDATION-BOOK mirror — rung 2's ground
                        truth; name-generic drv_tp_len + corr_mapconst_enc,
                        validator/lifter arc inc-0]
   18. p5-or-shape-flipped  duppRec (e::tl) → duppRec (e::e::tl)
                        [chain2 schematic (comparison-generic) + boolEnc +
                        implies decode + junk-disjunct elimination,
                        validator/lifter arc inc-1]
  PROVED (via the HAND replayed statement — driver upgrade pending):
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
                        documented, replayed-only
  ──────────────────────────────────────────────────────────────────────────
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.Imported.SimpleWorld
import ACL2Lean.Imported.AppAssoc
import ACL2Lean.Imported.Lifting
import ACL2Lean.Imported.Perm
import ACL2Lean.Imported.Sorting

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## Entry 1 — `my-len-my-app`: `(xs ++ ys).length = xs.length + ys.length`

The full chain, end to end: the REAL `simple.proof-log` → parse → reconstruct
→ the log-DERIVED world → the driver's conditional replayed statement (totality/TP
hypotheses) → hypotheses DISCHARGED (the WORLD-PARAMETRIC hand dischargers,
instantiated directly at the log-derived world) → instantiated at encoded
lists → the simulation lemmas → the native statement. -/

private def simpleLog : String := include_str "../../acl2_samples/simple.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def simpleDev : Development :=
  (((ProofLog.parse simpleLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world simpleWorldD from simpleDev

/-- `driver_replayed% dev world "thm-name"` — the DRIVER's conditional replayed statement
    for the named theorem of the development `dev`, over the derived world
    constant `world`: a `∀ env, <hypotheses> → ∃N∀f≥N ∃v, eval = some v ∧
    v ≠ nil` proof OBJECT (ACL2's truthiness claim, G2) produced by
    `replayProofConditional` from the reconstructed tree. -/
elab "driver_replayed%" devId:ident worldId:ident nm:str : term => do
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
        gzDefs := dev.groundZeroSnapshotDefs, justs := dev.justifications,
        fcRules := dev.groundZeroFcRuleSpecs }
    let (proof, _conds) ← replayProofConditional cfg dev.typePrescriptions cp
      dev.justifications (Driver.rulesBefore dev nm.getString)
      ((Driver.developmentTheoremsWithRules dev).map fun (c, _) => (c.name, c))
    Meta.mkLambdaFVars #[env] proof

/-- The conditional replayed statement as a definition (the driver's proof OBJECT). -/
def mylenReplayedCond := driver_replayed% simpleDev simpleWorldD "my-len-my-app"

/-! ### The unconditional driver replayed statement — direct world-parametric discharge

The driver's four hypotheses are discharged by the WORLD-PARAMETRIC hand
dischargers (invariant L3) instantiated directly at the log-derived world —
every world fact a `decide` on the reflected world. No defs-extensionality
transfer is needed; the `evalOpt_defs_ext` route remains in `EvalOpt` as the
documented fallback for world-concrete machinery. The stated formula is the
hand `my_len_my_appFormula` — it and the log-derived statement are the same
term, so the proof closes definitionally. -/

theorem mylenReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f simpleWorldD env
      Worlds.Simple.my_len_my_appFormula = some v ∧ v ≠ SExpr.nil :=
  -- the total:my-len/my-app/fix hypotheses are AUTO-DISCHARGED by the driver
  -- from the emitted admission data (#37); only the TP hypothesis remains
  mylenReplayedCond env
    (Worlds.Simple.drv_tp_mylen simpleWorldD (by decide) (by decide)
      (by decide) (by decide))

/-- ENTRY 1, PROVED — the native statement through the DRIVER's replayed
    replayed statement: log → parse → reconstruct → derived world → conditional replay →
    discharged hypotheses → simulation decode, all directly over the
    log-derived world. -/
theorem my_len_my_app_native_driver (xs ys : List SExpr) :
    (xs ++ ys).length = xs.length + ys.length :=
  Worlds.Simple.my_len_my_app_native_of_replayed simpleWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) mylenReplayed_uncond xs ys

/-! ## Entry 2 — `app-assoc`: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`

From the REAL `recon-tests/02-rev.proof-log` (app-assoc is its first theorem;
the log's world carries `app` AND `rev`). Unlike entry 1, NO world-transfer
is needed: the `AppAssoc` support lemmas are world-PARAMETRIC (invariant L3),
so they instantiate directly at the log-derived world — every world fact is a
`decide` on the derived world, and the driver replayed statement's single hypothesis
(`total:app`) is discharged by the generic driver-shape totality. -/

private def revLog : String := include_str "../../acl2_samples/recon-tests/02-rev.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def revDev : Development :=
  (((ProofLog.parse revLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world revWorldD from revDev

/-- The conditional replayed statement as a definition (the driver's proof OBJECT):
    `∀ env, total:app → <EvTrue of (equal (app (app a b) c)
    (app a (app b c)))>` (truthiness, G2). -/
def appAssocReplayedCond := driver_replayed% revDev revWorldD "app-assoc"

/-- The driver replayed statement — UNCONDITIONAL: its sole `total:app` hypothesis is
    AUTO-DISCHARGED by the driver from the emitted admission data (#37). -/
theorem appAssocReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f revWorldD env
      Worlds.AppAssoc.app_assocFormula = some v ∧ v ≠ SExpr.nil :=
  appAssocReplayedCond env

/-- ENTRY 2, PROVED — `List.append_assoc` (over `SExpr`) through the DRIVER's
    replayed statement, with the world-parametric native assembly instantiated
    directly at the log-derived world. -/
theorem app_assoc_native_driver (xs ys zs : List SExpr) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  Worlds.AppAssoc.app_assoc_native_of_replayed revWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) appAssocReplayed_uncond xs ys zs

/-! ## Entry 3 — `ground-arith`: `(1 + (2 + 3) : Int) = 6`

From `recon-tests/00-direct.proof-log` (the executable-counterpart/preprocess
class — no waterfall reasoning, no hypotheses on the replayed statement). The GROUND
DECODE pattern: both formula sides are evaluated SYMBOLICALLY to
`Logic`-primitive values over UNREDUCED Lean arithmetic (`int (1 + (2 + 3))`,
`int 6`), and the replayed statement's `equal ⇒ t` fact equates them — the arithmetic
fact comes from ACL2's replayed evaluation, never from a Lean decision
procedure. -/

private def directLog : String := include_str "../../acl2_samples/recon-tests/00-direct.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def directDev : Development :=
  (((ProofLog.parse directLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world directWorldD from directDev

/-- The replayed statement as a definition (UNCONDITIONAL — the tree is a pure preprocess
    discharge, so the driver emits no hypotheses). -/
def groundArithReplayedCond := driver_replayed% directDev directWorldD "ground-arith"

/-- ENTRY 3, PROVED — the ground arithmetic fact through the DRIVER's
    replayed statement (executable-counterpart class). -/
theorem ground_arith_native : (1 + (2 + 3) : Int) = 6 :=
  native_of_replayed_equal directWorldD {} intRep
    (plusT (qInt 1) (plusT (qInt 2) (qInt 3))) (qInt 6) (1 + (2 + 3)) 6
    (by decide)
    (implements_plus directWorldD (by decide) {} (qInt 1) (plusT (qInt 2) (qInt 3))
      1 (2 + 3) (conv_qInt _ _ 1)
      (implements_plus directWorldD (by decide) {} (qInt 2) (qInt 3) 2 3
        (conv_qInt _ _ 2) (conv_qInt _ _ 3)))
    (conv_qInt _ _ 6)
    (groundArithReplayedCond {})

/-! ## Entry 4 — `sq-of-3`: `(3 * 3 : Int) = 9`

Same log (00-direct), one step richer than entry 3: the formula applies the
USER-DEFINED `sq` (body `(binary-* n n)`) to a ground argument, so the decode
unfolds the definition (`conv_defn_1`) and evaluates the body symbolically —
`int (3 * 3)` — before the replayed statement's `equal ⇒ t` fact equates it with `int 9`. -/

/-- The replayed statement as a definition (UNCONDITIONAL — executable-counterpart
    discharge; `sq`'s unfold is part of the replayed evaluation). -/
def sqOf3ReplayedCond := driver_replayed% directDev directWorldD "sq-of-3"

private def n_sym : Symbol := { package := "ACL2", name := "N" }
private def nT : SExpr := .atom (.symbol { name := "N" })
private def sqBody : SExpr :=
  .cons (.atom (.symbol { name := "BINARY-*" })) (.cons nT (.cons nT .nil))

/-- ENTRY 4, PROVED — the ground fact about the user-defined `sq` through the
    DRIVER's replayed statement (definition unfold + symbolic body evaluation). -/
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
  exact native_of_replayed_equal directWorldD e intRep
    (app1 "SQ" (qInt 3)) (qInt 9) (3 * 3) 9 (by decide) hL hR (sqOf3ReplayedCond e)

/-! ## Entries 5–7 — the equality-reasoning trio (`08-equality-reasoning`)

`cdr-cons-refl`, `equal-symm`, `equal-trans` — generic facts over arbitrary
`SExpr` values, decoded DIRECTLY (no `enc` simulation layer; the formula's
free variables are instantiated by the env). The replayed statements are unconditional
(the 08 world has no defuns; the trees are preprocess discharges). Two new
decode patterns: the SYMBOLIC-VALUE decode (entry 5: the lhs is evaluated
only to `Logic.cdr (cons u v)`, so the replayed statement's equality fact is the
non-trivial content) and the HYPOTHESIS decode (entries 6–7: a native
hypothesis truthifies the `implies` antecedent; the replayed statement's `implies ⇒ t`
forces the conclusion's truth). -/

private def eqLog : String := include_str "../../acl2_samples/recon-tests/08-equality-reasoning.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def eqDev : Development :=
  (((ProofLog.parse eqLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world eqWorldD from eqDev

def cdrConsReplayedCond := driver_replayed% eqDev eqWorldD "cdr-cons-refl"
def equalSymmReplayedCond := driver_replayed% eqDev eqWorldD "equal-symm"
def equalTransReplayedCond := driver_replayed% eqDev eqWorldD "equal-trans"

private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def zT : SExpr := .atom (.symbol { name := "Z" })
/-- ENTRY 5, PROVED — `cdr ∘ cons = snd` at the `Logic` layer, through the
    DRIVER's replayed statement: the lhs is evaluated only SYMBOLICALLY (to
    `Logic.cdr (cons u v)`), so the equation is the replayed statement's content. -/
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
  exact native_of_replayed_equal eqWorldD e idRep
    (cdrT (consT xT yT)) yT (Logic.cdr (SExpr.cons u v)) v
    (by decide) hcdr hy (cdrConsReplayedCond e)

/-- ENTRY 6, PROVED — symmetry of equality over `SExpr`, through the DRIVER's
    replayed statement (the HYPOTHESIS decode: `h` truthifies the antecedent, the replayed statement's
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
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (equalSymmReplayedCond e) himp)
  exact eq_of_equal_truthy (truthy_of_implies_t hval (equal_truthy_of_eq h))

/-- ENTRY 7, PROVED — transitivity of equality over `SExpr`, through the
    DRIVER's replayed statement (hypothesis decode through the formula's `if`-spine:
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
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (equalTransReplayedCond e) himp)
  exact eq_of_equal_truthy (truthy_of_implies_t hval (equal_truthy_of_eq h2))

/-! ## Entry 8 — `app-cons-car`: `Logic.car (cons u v) = u`

From `recon-tests/01-multi-theorem.proof-log` (`(equal (car (app (cons a b) y))
a)`, cond[total:app]). The deepest decode so far: instantiating `b ↦ nil`
makes the app-value collapse to `cons u v` — the decode layer UNFOLDS `app`
twice (cons-case then nil-case of the body's if) — while the outer `car` is
kept SYMBOLIC, so the replayed statement's equality yields the fully generic
`Logic.car (cons u v) = u`. -/

private def multiLog : String := include_str "../../acl2_samples/recon-tests/01-multi-theorem.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def multiDev : Development :=
  (((ProofLog.parse multiLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world multiWorldD from multiDev

def appConsCarReplayedCond := driver_replayed% multiDev multiWorldD "app-cons-car"

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
    layer, through the DRIVER's replayed statement: instantiate `b ↦ nil` so
    `(app (cons a b) y)` collapses to `cons u v` (two definition unfolds in
    the decode), keep the outer `car` symbolic, and the replayed statement equates. -/
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
  -- the outer car: kept SYMBOLIC — the replayed statement's equality is the content
  have hL : ∃ N, ∀ f ≥ N, evalOpt f multiWorldD e (carT (appT (consT aT bT) yT))
      = some (Logic.car (SExpr.cons u v)) :=
    conv_builtin1 multiWorldD e { name := "CAR" } _ (SExpr.cons u v) _ (by decide)
      (by decide) happ (callBuiltin_car _)
  exact native_of_replayed_equal multiWorldD e idRep
    (carT (appT (consT aT bT) yT)) aT (Logic.car (SExpr.cons u v)) u
    (by decide) hL ha
    (appConsCarReplayedCond e)

/-! ## Entry 9 — `perm-cons` (the sorting corpus, R1):
`a ∈ xs → (xs ~ a :: ys ↔ xs.erase a ~ ys)`

The FULL chain on the perm book's first replayed theorem: the REAL
`sorting/perm.proof-log` → parse → reconstruct → the log-DERIVED world → the
driver's replayed statement (the branch-split composer, destructor elimination, the
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

/-- The driver's replayed-statement proof OBJECT — UNCONDITIONAL as produced (totality
    by the admission prover, TP corollaries by the TP prover): no
    hypotheses left to discharge. -/
def permConsReplayedCond := driver_replayed% permDev permWorldD "perm-cons"

theorem permConsReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f permWorldD env
      Worlds.Perm.perm_consFormula = some v ∧ v ≠ SExpr.nil :=
  permConsReplayedCond env

/-- ENTRY 9, PROVED — the Boolean form through the DRIVER's replayed statement. -/
theorem perm_cons_native_driver (a : SExpr) (xs ys : List SExpr)
    (h : xs.contains a = true) :
    xs.isPerm (a :: ys) = (xs.erase a).isPerm ys :=
  Worlds.Perm.perm_cons_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permConsReplayed_uncond a xs ys h

/-- ENTRY 9, PROVED — the idiomatic `List.Perm` form: a member moves across
    the permutation relation. -/
theorem perm_cons_native_perm_driver (a : SExpr) (xs ys : List SExpr)
    (h : a ∈ xs) :
    xs.Perm (a :: ys) ↔ (xs.erase a).Perm ys :=
  Worlds.Perm.perm_cons_native_perm_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permConsReplayed_uncond a xs ys h

#print axioms perm_cons_native_perm_driver

/-! ## Entries 10–16 — the REST of the perm book (lifter sprint 2026-07-06)

Every remaining theorem's UNCONDITIONAL driver replayed statement, decoded natively
through the same `corr_*` layer with the Lifting decode kit. The whole ACL2
book is now imported: 8 replayed statements, 8 native facts, zero hypotheses. -/

def permSymmetricReplayed := driver_replayed% permDev permWorldD "perm-symmetric"
def membRmReplayed := driver_replayed% permDev permWorldD "memb-rm"
def permMembReplayed := driver_replayed% permDev permWorldD "perm-memb"
def commRmReplayed := driver_replayed% permDev permWorldD "comm-rm"
def permRmReplayed := driver_replayed% permDev permWorldD "perm-rm"
def permTransitiveReplayed := driver_replayed% permDev permWorldD "perm-transitive"
def permEquivReplayed := driver_replayed% permDev permWorldD "perm-is-an-equivalence"

/-- ENTRY 10, PROVED — perm-symmetric: `isPerm` is symmetric. -/
theorem perm_symmetric_native_driver (xs ys : List SExpr)
    (h : xs.isPerm ys = true) : ys.isPerm xs = true :=
  Worlds.Perm.perm_symmetric_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permSymmetricReplayed xs ys h

/-- ENTRY 11, PROVED — memb-rm: membership survives erasing another element. -/
theorem memb_rm_native_driver (av bv : SExpr) (xs : List SExpr)
    (h : (xs.erase bv).contains av = true) : xs.contains av = true :=
  Worlds.Perm.memb_rm_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    membRmReplayed av bv xs h

/-- ENTRY 12, PROVED — comm-rm: erasures commute (the Mathlib
    `List.erase_comm` fact, imported from ACL2). -/
theorem comm_rm_native_driver (av bv : SExpr) (xs : List SExpr) :
    (xs.erase bv).erase av = (xs.erase av).erase bv :=
  Worlds.Perm.comm_rm_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) commRmReplayed av bv xs

/-- ENTRY 13, PROVED — perm-memb: membership transports across `isPerm`. -/
theorem perm_memb_native_driver (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) (hm : xs.contains av = true) :
    ys.contains av = true :=
  Worlds.Perm.perm_memb_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permMembReplayed av xs ys hp hm

/-- ENTRY 14, PROVED — perm-rm: `isPerm` is preserved by erasing the same
    element from both sides. -/
theorem perm_rm_native_driver (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) :
    (xs.erase av).isPerm (ys.erase av) = true :=
  Worlds.Perm.perm_rm_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permRmReplayed av xs ys hp

/-- ENTRY 15, PROVED — perm-transitive: `isPerm` is transitive. -/
theorem perm_transitive_native_driver (xs ys zs : List SExpr)
    (hxy : xs.isPerm ys = true) (hyz : ys.isPerm zs = true) :
    xs.isPerm zs = true :=
  Worlds.Perm.perm_transitive_native_of_replayed permWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) permTransitiveReplayed xs ys zs hxy hyz

/-- ENTRY 16, PROVED — perm-is-an-equivalence: reflexivity (the conjunct
    with no standalone theorem), decoded by peeling the defequiv tower. -/
theorem perm_refl_native_driver (xs : List SExpr) : xs.isPerm xs = true :=
  Worlds.Perm.perm_refl_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permEquivReplayed xs

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

/-! ## Entry 17 — true-listp-flatten (J8, induction-generality arc exit)

From the REAL `recon-tests/10-tree-induction.proof-log`: the arc's first
WF-induction theorem, replayed UNCONDITIONALLY by the driver (its
`rule:TRUE-LISTP-APP` dependency discharged through the D1 registry from the
dependency's own replayed statement). The native decode: **the imported FLATTEN
program, run on ANY input, converges to the encoding of a genuine Lean
`List`** — `true-listp`-ness decoded through the `enc` isomorphism
(`exists_enc_of_trueListp`). For a recognizer theorem the subject IS the
imported program, so `evalOpt` remains in the statement: a fully native
restatement would need a simulation that subsumes — and so bypasses — the
replayed theorem. The OUTER recognizer needs no simulation at all:
`TRUE-LISTP` is absent from the derived world (gz snapshots live in
`gzDefs`, not `w.defs`), so it dispatches to the trusted-core builtin
(`Logic.trueListp`) directly; FLATTEN itself is untouched — its list-ness
comes entirely from ACL2's replayed induction. -/

private def treeLog : String :=
  include_str "../../acl2_samples/recon-tests/10-tree-induction.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def treeDev : Development :=
  (((ProofLog.parse treeLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world treeWorldD from treeDev

/-- The UNCONDITIONAL driver replayed statement (zero hypotheses — see the coverage row
    `TRUE-LISTP-FLATTEN → REPLAYED ✓`). -/
def trueListpFlattenReplayed := driver_replayed% treeDev treeWorldD "true-listp-flatten"

private def flattenXT : SExpr := Lifting.app1 "FLATTEN" (.atom (.symbol { name := "X" }))

/-- ENTRY 17, PROVED — FLATTEN's value is always an encoded Lean list. -/
theorem true_listp_flatten_native_driver (env : Env) :
    ∃ (N : Nat) (l : List SExpr), ∀ f ≥ N,
      evalOpt f treeWorldD env flattenXT = some (enc l) := by
  -- the replayed statement: (TRUE-LISTP (FLATTEN X)) is eventually truthy
  obtain ⟨N₀, hN₀⟩ := trueListpFlattenReplayed env
  -- fix the composite's value across fuels
  obtain ⟨N₁, vTL, hTL⟩ := ACL2.Replay.conv_fix
    ⟨N₀, fun f hf => ⟨(hN₀ f hf).choose, (hN₀ f hf).choose_spec.1⟩⟩
  have hvTLne : vTL ≠ SExpr.nil := by
    obtain ⟨v, hv, hne⟩ := hN₀ (max N₀ N₁) (le_max_left _ _)
    rw [hTL (max N₀ N₁) (le_max_right _ _)] at hv
    exact (Option.some.inj hv) ▸ hne
  -- invert: the argument (FLATTEN X) converges, to a fixed value
  obtain ⟨N₂, vF, hF⟩ := ACL2.Replay.conv_fix
    (ACL2.Replay.conv_arg1_of_conv_app treeWorldD env
      { name := "TRUE-LISTP" } flattenXT vTL (by decide) ⟨N₁, hTL⟩)
  -- builtin dispatch: TRUE-LISTP is not in the world, so the composite
  -- computes the trusted-core Logic.trueListp on FLATTEN's value
  obtain ⟨N₃, hC⟩ := ACL2.Replay.conv_builtin1 treeWorldD env
    { name := "TRUE-LISTP" } flattenXT vF (Logic.trueListp vF)
    (by decide) (by decide) ⟨N₂, hF⟩ (ACL2.Replay.callBuiltin_true_listp _)
  -- determinism: the composite's value IS Logic.trueListp vF
  have hEq : vTL = Logic.trueListp vF := by
    have h1 := hTL (max N₁ N₃) (le_max_left _ _)
    have h2 := hC (max N₁ N₃) (le_max_right _ _)
    exact Option.some.inj (h1.symm.trans h2)
  -- decode through the enc isomorphism
  have hT : Logic.trueListp vF = SExpr.t :=
    ACL2.Replay.logic_trueListp_ne_nil_t vF (hEq ▸ hvTLne)
  obtain ⟨l, hl⟩ := Lifting.exists_enc_of_trueListp hT
  exact ⟨N₂, l, fun f hf => by rw [hF f hf, hl]⟩

#print axioms true_listp_flatten_native_driver

/-! ## Entry — `p7-cong-collapse`: the first VALIDATION-BOOK mirror
(validator/lifter arc inc-0, 2026-07-30)

Rung 2's ground truth: `P7-TARGET` — `(equal (ln (dub x)) (ln x))`, the
theorem whose replay validates the congruence collapse — lifted to the
native fact `(l.map (fun _ => '0)).length = l.length`. The chain: the real
p7 log → parse → reconstruct → derived world → the driver's conditional
replayed statement (`tp:LN` only) → discharged by the NAME-GENERIC
`drv_tp_len` (the industrialization dividend: LN's body is exactly
`lenBody "LN"`) → instantiated at an encoded list → `corr_mapconst_enc` ∘
`corr_len_enc` → `native_of_replayed_equal intRep`. MIRRORS establish that
a replayed theorem means what the user intends (CLAUDE.md terminology,
2026-07-30) — this is the first for a pattern-test book. -/

private def p7Log : String :=
  include_str "../../acl2_samples/pattern-tests/p7-cong-collapse.proof-log"

def p7Dev : Development :=
  (((ProofLog.parse p7Log).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world p7WorldD from p7Dev

def p7TargetReplayedCond := driver_replayed% p7Dev p7WorldD "p7-target"

private def q0Atom : SExpr := .atom (.number (.int 0))
private def xVarT : SExpr := .atom (.symbol { name := "X" })
private def p7xSym : Symbol := { package := "ACL2", name := "X" }
private def lnDubT : SExpr := app1 "LN" (app1 "DUB" xVarT)
private def lnXT : SExpr := app1 "LN" xVarT

/-- The replayed statement, UNCONDITIONAL: the sole `tp:LN` hypothesis is
    discharged by the name-generic len-class discharger. -/
theorem p7TargetReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f p7WorldD env
      (equalT lnDubT lnXT) = some v ∧ v ≠ SExpr.nil :=
  p7TargetReplayedCond env
    (drv_tp_len p7WorldD "LN" (by decide) (by decide) (by decide)
      (by decide) (by decide))

/-- The MIRROR: `(l.map (fun _ => '0)).length = l.length` — proved FROM the
    replayed P7-TARGET (via `Int` lengths and `Nat.cast` injectivity).
    NARROWING vs the book theorem (audit F6): the ACL2 statement holds for
    ALL X (atoms, improper lists); the mirror quantifies over `List SExpr`
    — the true-listp fragment, inherent to native Lean lists. The
    discriminating content is the proof ROUTE through the replayed
    statement (the native statement alone is a simp one-liner — audit
    F5); nothing pins the route mechanically, so a future edit replacing
    it with a direct proof would silently drop the ground-truth value. -/
theorem p7_dub_len_native_driver (l : List SExpr) :
    (l.map (fun _ => q0Atom)).length = l.length := by
  let e : Env := ({} : Env).insert p7xSym (enc l)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e xVarT = some (enc l) :=
    conv_var_of_get p7WorldD e p7xSym (enc l) (by simp [e])
  have hdub : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e (app1 "DUB" xVarT)
      = some (enc (l.map (fun _ => q0Atom))) :=
    corr_mapconst_enc p7WorldD q0Atom "DUB" (by decide) (by decide)
      (by decide) (by decide) (by decide) l e xVarT hx
  have hlhs : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e lnDubT
      = some (.atom (.number (.int (l.map (fun _ => q0Atom)).length))) :=
    corr_len_enc p7WorldD "LN" (by decide) (by decide) (by decide)
      (by decide) (by decide) (l.map (fun _ => q0Atom)) e
      (app1 "DUB" xVarT) hdub
  have hrhs : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e lnXT
      = some (.atom (.number (.int l.length))) :=
    corr_len_enc p7WorldD "LN" (by decide) (by decide) (by decide)
      (by decide) (by decide) l e xVarT hx
  have hnat : ((l.map (fun _ => q0Atom)).length : Int) = (l.length : Int) :=
    native_of_replayed_equal p7WorldD e intRep lnDubT lnXT _ _
      (by decide) hlhs hrhs (p7TargetReplayed_uncond e)
  exact_mod_cast hnat

/-! ## Entry — `p5-or-shape-flipped`: the SECOND validation-book mirror
(validator/lifter arc inc-1)

`DUPP-REP-MID` — `(implies (and (consp x) (equal (car x) e) (dupp x))
(or (equal x 'junk) (dupp (cons e x))))`, replayed UNCONDITIONAL — lifted
to the native fact: prepending an element equal to the head of an
adjacent-equal chain keeps it a chain. Exercises the machinery p7 did not:
the `chain2` schematic (comparison-generic — `dupp` is EQUAL's instance),
`boolEnc`, the IMPLIES hypothesis decode, and the or-disjunct
elimination (`enc l` is never the symbol `JUNK`). -/

private def p5MirrorLog : String :=
  include_str "../../acl2_samples/pattern-tests/p5-or-shape-flipped.proof-log"

def p5Dev : Development :=
  (((ProofLog.parse p5MirrorLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world p5WorldD from p5Dev

def duppRepReplayed := driver_replayed% p5Dev p5WorldD "dupp-rep-mid"

private def p5eSym : Symbol := { package := "ACL2", name := "E" }
private def p5xSym : Symbol := { package := "ACL2", name := "X" }
private def p5eT : SExpr := .atom (.symbol { name := "E" })
private def p5xT : SExpr := .atom (.symbol { name := "X" })
private def junkQ : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.symbol { name := "JUNK" })) .nil)
private def junkA : SExpr := .atom (.symbol { name := "JUNK" })
/-- `dupp`'s native content: the EQUAL instance of the chain2 fold. -/
def duppRec : List SExpr → Bool := chain2Rec (· == ·)

private theorem callBuiltin_equal_bool (a b : SExpr) :
    callBuiltin "EQUAL" [a, b] = some (boolEnc (a == b)) := by
  rw [callBuiltin_equal]
  cases h : a == b <;> simp [Logic.equal, h, boolEnc]

/-- The dupp correspondence — ONE instantiation of the schematic. -/
private theorem corr_dupp (xs : List SExpr) (e' : Env) (a : SExpr)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD e' a = some (enc xs)) :
    ∃ N, ∀ f ≥ N, evalOpt f p5WorldD e' (app1 "DUPP" a)
      = some (boolEnc (duppRec xs)) :=
  corr_chain2_enc p5WorldD "EQUAL" "DUPP" (· == ·) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    callBuiltin_equal_bool xs e' a ha

/-- ENTRY, PROVED — the p5 MIRROR: prepending an element equal to the head
    preserves the adjacent-equal chain, THROUGH the replayed DUPP-REP-MID
    (implies decode; the `junk` disjunct dies because an encoded list is
    never that symbol).
    NARROWING vs the book theorem (audit F6): the ACL2 statement holds for
    ANY cons X including improper lists; this mirror quantifies over
    `List SExpr` (the true-listp fragment — inherent to native Lean lists)
    and instantiates the `(equal (car x) e)` hypothesis at hd := e (faithful
    — EQUAL is identity here). -/
theorem p5_dupp_prepend_native_driver (e : SExpr) (tl : List SExpr)
    (h : duppRec (e :: tl) = true) : duppRec (e :: e :: tl) = true := by
  let env : Env := (({} : Env).insert p5eSym e).insert p5xSym (enc (e :: tl))
  have hx : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env p5xT = some (enc (e :: tl)) :=
    conv_var_of_get _ _ _ _ (by
      simp only [env, Env.get?_insert]
      rw [if_pos (by decide)])
  have he : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env p5eT = some e :=
    conv_var_of_get _ _ _ _ (by
      simp only [env, Env.get?_insert]
      rw [if_neg (by decide), if_pos (by decide)])
  have hconsp : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env (conspT p5xT)
      = some (Logic.consp (.cons e (enc tl))) :=
    conv_builtin1 p5WorldD env { name := "CONSP" } p5xT _ _ (by decide)
      (by decide) hx (callBuiltin_consp _)
  have hcar : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env (carT p5xT) = some e := by
    have hcar0 := conv_builtin1 p5WorldD env { name := "CAR" } p5xT
      (.cons e (enc tl)) (Logic.car (.cons e (enc tl))) (by decide)
      (by decide) hx (callBuiltin_car _)
    simpa [Logic.car] using hcar0
  have heqcar : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (equalT (carT p5xT) p5eT)
      = some (Logic.equal e e) :=
    conv_equalT p5WorldD env (carT p5xT) p5eT e e (by decide) hcar he
  have hdupx : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env (app1 "DUPP" p5xT)
      = some (boolEnc (duppRec (e :: tl))) :=
    corr_dupp (e :: tl) env p5xT hx
  -- the antecedent: (IF (CONSP X) (IF (EQUAL (CAR X) E) (DUPP X) 'NIL) 'NIL)
  -- — both tests TRUE by construction, so it converges to dupp's value
  have hanteInner : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (equalT (carT p5xT) p5eT)
            (.cons (app1 "DUPP" p5xT)
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons .nil .nil)) .nil))))
      = some (boolEnc (duppRec (e :: tl))) := by
    obtain ⟨Ni, hi⟩ := re_if_true p5WorldD env (equalT (carT p5xT) p5eT)
      _ _ (Logic.equal e e) (boolEnc (duppRec (e :: tl))) heqcar
      (by simp [Logic.equal, SExpr.t, Logic.toBool]) hdupx
    obtain ⟨Nd, hd⟩ := hdupx
    exact ⟨max Ni Nd, fun f hf => (hi f (by omega)).trans (hd f (by omega))⟩
  have hante : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (conspT p5xT)
            (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons (equalT (carT p5xT) p5eT)
                (.cons (app1 "DUPP" p5xT)
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                    (.cons .nil .nil)) .nil))))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons .nil .nil)) .nil))))
      = some (boolEnc (duppRec (e :: tl))) := by
    obtain ⟨Ni, hi⟩ := re_if_true p5WorldD env (conspT p5xT) _ _
      (Logic.consp (.cons e (enc tl))) (boolEnc (duppRec (e :: tl)))
      hconsp rfl hanteInner
    obtain ⟨Na, ha⟩ := hanteInner
    exact ⟨max Ni Na, fun f hf => (hi f (by omega)).trans (ha f (by omega))⟩
  -- the consequent: (IF (EQUAL X 'JUNK) (EQUAL X 'JUNK) (DUPP (CONS E X)))
  -- — the test is FALSE (an encoded list is never the JUNK symbol)
  have hjunk : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env junkQ = some junkA :=
    ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                       exact evalOpt_quote g p5WorldD env _⟩
  have heqjunk : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (equalT p5xT junkQ) = some SExpr.nil := by
    have h0 := conv_equalT p5WorldD env p5xT junkQ (enc (e :: tl)) junkA
      (by decide) hx hjunk
    simpa [Logic.equal, enc, junkA] using h0
  have hconsex : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (consT p5eT p5xT)
      = some (enc (e :: e :: tl)) := by
    have h0 := conv_builtin2 p5WorldD env { name := "CONS" } p5eT p5xT
      e (enc (e :: tl)) (Logic.cons e (enc (e :: tl))) (by decide)
      (by decide) he hx (callBuiltin_cons _ _)
    simpa [Logic.cons, enc] using h0
  have hdupcons : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (app1 "DUPP" (consT p5eT p5xT))
      = some (boolEnc (duppRec (e :: e :: tl))) :=
    corr_dupp (e :: e :: tl) env (consT p5eT p5xT) hconsex
  have hcons' : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (equalT p5xT junkQ)
            (.cons (equalT p5xT junkQ)
              (.cons (app1 "DUPP" (consT p5eT p5xT)) .nil))))
      = some (boolEnc (duppRec (e :: e :: tl))) := by
    obtain ⟨Ni, hi⟩ := re_if_false p5WorldD env (equalT p5xT junkQ)
      (equalT p5xT junkQ) (app1 "DUPP" (consT p5eT p5xT))
      (boolEnc (duppRec (e :: e :: tl))) heqjunk hdupcons
    obtain ⟨Nd, hd⟩ := hdupcons
    exact ⟨max Ni Nd, fun f hf => (hi f (by omega)).trans (hd f (by omega))⟩
  -- the whole formula's value, pinned truthy by the replayed statement
  have himp := conv_impliesT p5WorldD env _ _
    (boolEnc (duppRec (e :: tl))) (boolEnc (duppRec (e :: e :: tl)))
    (by decide) hante hcons'
  have hval : Logic.implies (boolEnc (duppRec (e :: tl)))
      (boolEnc (duppRec (e :: e :: tl))) = SExpr.t :=
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (duppRepReplayed env) himp)
  have hconc := truthy_of_implies_t hval (by rw [h]; rfl)
  cases hc : duppRec (e :: e :: tl) with
  | true => rfl
  | false => rw [hc] at hconc; exact absurd hconc (by decide)


/-! ## The ordered-perms book — the SORTING MIRROR PROGRAM's first tranche
(sorting-completion-2 amended criteria). The `Imported/Sorting.lean`
support: the LEXORDER Bool kit + the ORDEREDP chain2 instance; `rm`'s
simulation is the perm book's, reused verbatim. -/

private def orderedPermsLog : String :=
  include_str "../../acl2_samples/sorting/ordered-perms.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def orderedPermsDev : Development :=
  (((ProofLog.parse orderedPermsLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world orderedPermsWorldD from orderedPermsDev

/-- The UNCONDITIONAL driver replayed statement (zero hypotheses — see the
    coverage row). -/
def orderedpRmReplayed := driver_replayed% orderedPermsDev orderedPermsWorldD
  "orderedp-rm"

/-- ENTRY, PROVED — ORDEREDP-RM natively: erasing an element preserves
    adjacent-pair lexorder-sortedness (`chain2Rec lexorderB`, the ORDEREDP
    reading over encoded lists). -/
theorem orderedp_rm_native_driver (ev : SExpr) (xs : List SExpr)
    (h : Worlds.Sorting.orderedpRec xs = true) :
    Worlds.Sorting.orderedpRec (xs.erase ev) = true :=
  Worlds.Sorting.orderedp_rm_native_of_replayed orderedPermsWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) orderedpRmReplayed ev xs h

#print axioms orderedp_rm_native_driver

/-- The UNCONDITIONAL driver replayed statement for CAR-RM. -/
def carRmReplayed := driver_replayed% orderedPermsDev orderedPermsWorldD
  "car-rm"

/-- ENTRY, PROVED — CAR-RM natively: the head of `xs.erase ev` — nil on
    the empty list, the tail's head if the head was erased, else the
    head (`carRmSpec`). -/
theorem car_rm_native_driver (ev : SExpr) (xs : List SExpr) :
    (xs.erase ev).headD SExpr.nil = Worlds.Sorting.carRmSpec ev xs :=
  Worlds.Sorting.car_rm_native_of_replayed orderedPermsWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    carRmReplayed ev xs

#print axioms car_rm_native_driver

/-! ## The isort book — ORDEREDP-ISORT: insertion sort always sorts.
The row's ONE condition (`tp:INSERT`, insert's emitted `(CONSP (INSERT E
X))` corollary) is discharged by the world-parametric `dis_insert_tp`
(every branch of the body is a `cons`), making the replayed statement
unconditional; the `insert`/`isort` exec kit decodes it natively. -/

private def isortLog : String :=
  include_str "../../acl2_samples/sorting/isort.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def isortDev : Development :=
  (((ProofLog.parse isortLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world isortWorldD from isortDev

/-- The driver's CONDITIONAL replayed statement (one hypothesis:
    `tp:INSERT`). -/
def orderedpIsortReplayedCond := driver_replayed% isortDev isortWorldD
  "orderedp-isort"

/-- The unconditional form — `tp:INSERT` discharged world-parametrically. -/
theorem orderedpIsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f isortWorldD env
      Worlds.Sorting.orderedp_isortFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpIsortReplayedCond env
    (Worlds.Sorting.dis_insert_tp isortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))

/-- ENTRY, PROVED — ORDEREDP-ISORT natively: INSERTION SORT ALWAYS SORTS —
    `isortL` (insertion sort by `lexorderB`) yields an adjacent-pair
    lexorder-sorted list for EVERY input list. -/
theorem orderedp_isort_native_driver (xs : List SExpr) :
    Worlds.Sorting.orderedpRec (Worlds.Sorting.isortL xs) = true :=
  Worlds.Sorting.orderedp_isort_native_of_replayed isortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) orderedpIsortReplayed_uncond xs

#print axioms orderedp_isort_native_driver

/-- The driver's CONDITIONAL replayed statement for EQUAL-CONS (one
    hypothesis: `rule:CONS-CAR-CDR`, the stored ground-zero rule). -/
def equalConsReplayedCond := driver_replayed% orderedPermsDev
  orderedPermsWorldD "equal-cons"

/-- The unconditional form — the ground-zero rule discharged
    world-parametrically (`dis_cons_car_cdr`). -/
theorem equalConsReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f orderedPermsWorldD env
      Worlds.Sorting.equal_consFormula = some v ∧ v ≠ SExpr.nil :=
  equalConsReplayedCond env
    (Worlds.Sorting.dis_cons_car_cdr orderedPermsWorldD (by decide)
      (by decide) (by decide) (by decide))

/-- ENTRY, PROVED — EQUAL-CONS natively: equality with a cons decomposes
    componentwise (`==` over SExpr). -/
theorem equal_cons_native_driver (av bv xv : SExpr) :
    (SExpr.cons av bv == xv) = Worlds.Sorting.equalConsSpec av bv xv :=
  Worlds.Sorting.equal_cons_native_of_replayed orderedPermsWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide)
    equalConsReplayed_uncond av bv xv

#print axioms equal_cons_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's CONDITIONAL replayed statement for ORDEREDP-MEMB (one
    hypothesis: `rule:DEFAULT-CAR`). The raised heartbeat budget covers
    the replay-time `isDefEq` pinning over this row's larger tree. -/
def orderedpMembReplayedCond := driver_replayed% orderedPermsDev
  orderedPermsWorldD "orderedp-memb"

/-- The unconditional form — `rule:DEFAULT-CAR` discharged
    world-parametrically. -/
theorem orderedpMembReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f orderedPermsWorldD env
      Worlds.Sorting.orderedp_membFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpMembReplayedCond env
    (Worlds.Sorting.dis_default_car orderedPermsWorldD (by decide)
      (by decide) (by decide))

/-- ENTRY, PROVED — ORDEREDP-MEMB natively: an element strictly below the
    head of a lexorder-sorted list is not in the list. -/
theorem orderedp_memb_native_driver (ev a : SExpr) (t : List SExpr)
    (hord : Worlds.Sorting.orderedpRec (a :: t) = true)
    (hne : (ev == a) = false)
    (hlex : Worlds.Sorting.lexorderB ev a = true) :
    (a :: t).contains ev = false :=
  Worlds.Sorting.orderedp_memb_native_of_replayed orderedPermsWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) orderedpMembReplayed_uncond
    ev a t hord hne hlex

#print axioms orderedp_memb_native_driver

/-! ## The LIFT-COVERAGE GATE (W2(a), validator/lifter arc)

Every GREEN row of the sweep golden must carry an explicit lift DECISION:
a native mirror (whose constant must exist), an explicit PENDING marker
(the blocking work named), or replayed-only (no non-vacuous native fact —
reflexive decodes and type-absorbed statements). A NEW green row without a
catalog entry FAILS this build — "replayed but never lifted" can no longer
accumulate silently (the survey's headline finding, now a ratchet). The
golden is the input, so the catalog can never drift from the sweep. -/

private def liftCoverageGolden : String :=
  include_str "../../Tests/driver-coverage.golden"

inductive LiftStatus where
  | native (decl : Lean.Name)
  | pending (blockedOn : String)
  | replayedOnly (why : String)

/-- The catalog: one DECISION per green sweep row (book, theorem, status). -/
def liftCatalog : List (String × String × LiftStatus) := [
  ("simple", "MY-LEN-MY-APP", .native ``my_len_my_app_native_driver),
  ("00-direct", "GROUND-ARITH", .native ``ground_arith_native),
  ("00-direct", "SQ-OF-3", .native ``sq_of_3_native),
  ("00-direct", "SQ-REWRITES", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("01-multi-theorem", "APP-CONS-CAR", .native ``car_cons_native),
  ("01-multi-theorem", "APP-NIL", .pending "rule:CONS-CAR-CDR discharger + the true-listp hypothesis decode (the row replays green; audit F7 corrected the stale G5 reason)"),
  ("01-multi-theorem", "LEN2-APP", .pending "len2 world dischargers (entry-1 recipe over the 01 world)"),
  ("02-rev", "APP-ASSOC", .native ``app_assoc_native_driver),
  ("02-rev", "TRUE-LISTP-REV", .pending "the flatten-recipe mirror (the image-of-enc fact, cf TRUE-LISTP-FLATTEN — unconditional, transfers directly)"),
  ("02-rev", "APP-NIL", .pending "rule:CONS-CAR-CDR discharger + the true-listp hypothesis decode"),
  ("02-rev", "REV-APP", .pending "rev correspondence + tp:REV/rule:CONS-CAR-CDR dischargers"),
  ("02-rev", "REV-REV", .pending "rev correspondence + tp:REV/rule:CONS-CAR-CDR dischargers"),
  ("03-linear", "LEN2-NONNEG", .pending "len2 dischargers; Nat form is type-absorbed"),
  ("03-linear", "LEN2-CDR-SMALLER", .pending "len2 dischargers"),
  ("03-linear", "LINEAR-CHAIN", .pending "#50 DP tactic decode"),
  ("04-multi-case-induction", "EVENLEN-BOOLEANP", .pending "boolean-recognizer decode (near type-absorbed)"),
  ("05-hints", "LEN2-APP-HELPER", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-VIA-INDUCT", .pending "len2 dischargers"),
  ("05-hints", "LEN2-APP-NO-HELPER", .pending "len2 dischargers"),
  ("06-measure", "COUNT-DOWN-ZERO", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("07-mutual-recursion", "MY-EVENP-3-IS-NIL", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("07-mutual-recursion", "MY-ODDP-3-IS-T", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("08-equality-reasoning", "CDR-CONS-REFL", .native ``cdr_cons_native),
  ("08-equality-reasoning", "EQUAL-SYMM", .native ``equal_symm_native),
  ("08-equality-reasoning", "EQUAL-TRANS", .native ``equal_trans_native),
  ("09-defn-unfold", "SQ-REWRITES", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("09-defn-unfold", "IDF-REWRITES", .replayedOnly "reflexive decode — no non-vacuous native fact"),
  ("10-tree-induction", "TRUE-LISTP-APP", .pending "the flatten-recipe mirror (unconditional — transfers directly)"),
  ("10-tree-induction", "TRUE-LISTP-FLATTEN", .native ``true_listp_flatten_native_driver),
  ("12-multi-controller", "LEN-ZIP2", .pending "zip2 correspondence (validator/lifter backlog)"),
  ("13-multi-measured-var", "LEN-INTERLEAVE", .pending "interleave correspondence (backlog)"),
  ("14-accumulator", "LEN-REV-ACC", .pending "accumulator correspondence (backlog)"),
  ("15-nested-induction", "NESTED-INDUCTION", .pending "backlog (validator/lifter survey)"),
  ("16-three-way", "LEN-ZIP3", .pending "zip3 correspondence (backlog)"),
  ("17-rule-application", "TLP-APP-NIL", .pending "rule-application family decode (backlog)"),
  ("17-rule-application", "TLP-APP-NIL-TWICE", .pending "rule-application family decode (backlog)"),
  ("sorting/perm", "PERM-CONS", .native ``perm_cons_native_driver),
  ("sorting/perm", "PERM-SYMMETRIC", .native ``perm_symmetric_native_driver),
  ("sorting/perm", "MEMB-RM", .native ``memb_rm_native_driver),
  ("sorting/perm", "PERM-MEMB", .native ``perm_memb_native_driver),
  ("sorting/perm", "COMM-RM", .native ``comm_rm_native_driver),
  ("sorting/perm", "PERM-RM", .native ``perm_rm_native_driver),
  ("sorting/perm", "PERM-TRANSITIVE", .native ``perm_transitive_native_driver),
  ("sorting/perm", "PERM-IS-AN-EQUIVALENCE", .native ``perm_refl_native_driver),
  ("sorting/isort", "ORDEREDP-ISORT", .native ``orderedp_isort_native_driver),
  ("sorting/isort", "TRUE-LISTP-ISORT", .replayedOnly "subsumed by the isort simulation (corr_isort_enc/isortExec_enc): the program's value on any encoded input IS an encoded List by the sim — no native content beyond it (the type-absorbed true-listp doctrine)"),
  ("sorting/isort", "HOW-MANY-ISORT", .pending "how-many correspondence (count fn; backlog)"),
  ("sorting/ordered-perms", "ORDEREDP-RM", .native ``orderedp_rm_native_driver),
  ("sorting/ordered-perms", "ORDEREDP-MEMB", .native ``orderedp_memb_native_driver),
  ("sorting/ordered-perms", "EQUAL-CONS", .native ``equal_cons_native_driver),
  ("sorting/ordered-perms", "ORDERED-PERMS", .pending "chain2/LEXORDER + perm/rm/memb correspondences + the ASSUMED:dp-fact dischargers (backlog)"),
  ("sorting/ordered-perms", "CAR-RM", .native ``car_rm_native_driver),
  ("sorting/ordered-perms", "TRUE-LISTP-RM", .replayedOnly "subsumed by the rm simulation: `true-listp` restricts the input to the enc image (exists_enc_of_trueListp), where corr_rm_enc already yields an encoded List — no native content beyond the sim (the type-absorbed true-listp doctrine; the flatten recipe applies only where NO simulation exists)"),
  ("sorting/msort", "TRUE-LISTP-MSORT", .pending "the flatten-recipe mirror + its cond dischargers (total:MERGE2/MSORT, tp:EVENS)"),
  ("sorting/msort", "HOW-MANY-MERGE2", .pending "how-many/merge2 correspondences (backlog)"),
  ("sorting/msort", "HOW-MANY-EVENS-AND-ODDS", .pending "how-many/evens/odds correspondences (backlog)"),
  ("sorting/msort", "ORDEREDP-MSORT", .pending "chain2/LEXORDER + merge2/msort correspondences + cond dischargers (backlog)"),
  ("sorting/msort", "HOW-MANY-MSORT", .pending "how-many/msort correspondences (backlog)"),
  ("sorting/qsort", "termination:QSORT", .pending "termination replayed statement; native decrease fact not lifted"),
  ("sorting/qsort", "HOW-MANY-APPEND", .pending "how-many correspondence (backlog)"),
  ("sorting/qsort", "ORDEREDP-APPEND", .pending "chain2/LEXORDER + all-rel/append correspondences + cond dischargers (backlog)"),
  ("sorting/qsort", "HOW-MANY-FILTER-1", .pending "how-many/filter correspondences (backlog)"),
  ("sorting/qsort", "HOW-MANY-QSORT", .pending "how-many/qsort correspondences (landed 2026-07-31 via the truthy branch-fact channel; backlog)"),
  ("sorting/qsort", "PERM-QSORT", .pending "qsort correspondence + isPerm lift (the flagship; backlog)"),
  ("sorting/qsort", "CAR-APPEND", .pending "append correspondence at qsort world (backlog)"),
  ("sorting/qsort", "ALL-REL-FILTER-1", .pending "all-rel/filter correspondences (backlog)"),
  ("sorting/qsort", "ALL-REL-FILTER-2", .pending "all-rel/filter correspondences (backlog)"),
  ("sorting/qsort", "ALL-REL-RM-1", .pending "all-rel/rm correspondences (backlog)"),
  ("sorting/qsort", "ALL-REL-RM-2", .pending "all-rel/rm correspondences (backlog)"),
  ("sorting/qsort", "PERM-IMPLIES-EQUAL-ALL-REL-2", .pending "all-rel correspondence; the defcong congruence fact natively (backlog)"),
  ("sorting/qsort", "ORDEREDP-QSORT", .pending "chain2/LEXORDER + qsort correspondences (the headline; backlog)"),
  ("sorting/qsort", "TRUE-LISTP-QSORT", .pending "the flatten-recipe mirror + its cond dischargers (total:O<, tp:QSORT, …)")]

open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  -- parse the golden's green rows, book-qualified
  let mut rows : List (String × String) := []
  let mut book := ""
  for line in liftCoverageGolden.splitOn "\n" do
    if line.startsWith "• " then
      book := (((line.drop 2).toString.splitOn " ").headD "").dropSuffix ":" |>.toString
    else if line.startsWith "    " && (line.splitOn " → REPLAYED ✓").length > 1 then
      rows := rows ++ [(book, ((line.trimAscii.toString.splitOn " → ").headD ""))]
  -- every green row has exactly one catalog decision
  for (b, n) in rows do
    match liftCatalog.filter (fun (cb, cn, _) => cb == b && cn == n) with
    | [(_, _, st)] =>
      if let .native decl := st then
        unless (← getEnv).contains decl do
          throwError "lift-coverage gate: {b}/{n} claims native {decl}, \
            which does not exist"
    | [] => throwError "lift-coverage gate: green row {b}/{n} has NO \
        catalog decision — add a native entry, a PENDING marker, or a \
        replayed-only justification"
    | _ => throwError "lift-coverage gate: {b}/{n} has multiple catalog \
        entries"
  -- no stale catalog entries (an entry whose row vanished)
  for (b, n, _) in liftCatalog do
    unless rows.contains (b, n) do
      throwError "lift-coverage gate: catalog entry {b}/{n} matches no \
        green golden row (stale — remove or fix)"

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
  for n in [``ACL2.Imported.Mirrors.p5_dupp_prepend_native_driver,
            ``ACL2.Imported.Mirrors.p7_dub_len_native_driver,
            ``ACL2.Imported.Mirrors.perm_cons_native_driver,
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
            ``ACL2.Imported.Mirrors.true_listp_flatten_native_driver,
            ``ACL2.Imported.Mirrors.my_len_my_app_native_driver,
            ``ACL2.Imported.Mirrors.app_assoc_native_driver,
            ``ACL2.Imported.Mirrors.ground_arith_native,
            ``ACL2.Imported.Mirrors.sq_of_3_native,
            ``ACL2.Imported.Mirrors.cdr_cons_native,
            ``ACL2.Imported.Mirrors.equal_symm_native,
            ``ACL2.Imported.Mirrors.equal_trans_native,
            ``ACL2.Imported.Mirrors.car_cons_native,
            ``ACL2.Imported.Mirrors.orderedp_rm_native_driver,
            ``ACL2.Imported.Mirrors.car_rm_native_driver,
            ``ACL2.Imported.Mirrors.orderedp_isort_native_driver,
            ``ACL2.Imported.Mirrors.equal_cons_native_driver,
            ``ACL2.Imported.Mirrors.orderedp_memb_native_driver] do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "native-entry axiom gate: {n} uses forbidden axioms {bad}"

end ACL2.Imported.Mirrors
