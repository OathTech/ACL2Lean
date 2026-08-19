import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.RevAcc
import ACL2Lean.Imported.Rev
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## Entry 1 — `my-len-my-app`: `(xs ++ ys).length = xs.length + ys.length`

The full chain, end to end: the REAL `simple.proof-log` → parse → reconstruct
→ the log-DERIVED world → the driver's conditional replayed statement (totality/TP
hypotheses) → hypotheses DISCHARGED (the WORLD-PARAMETRIC hand dischargers,
instantiated directly at the log-derived world) → instantiated at encoded
lists → the simulation lemmas → the native statement. -/

private def simpleLog : String := include_str "../../../acl2_samples/simple.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def simpleDev : Development :=
  load_development% simpleLog

derive_world simpleWorldD from simpleDev
/-- The conditional replayed statement as a definition (the driver's proof OBJECT). -/
replayed_theorem mylenReplayedCond := driver_replayed% simpleDev simpleWorldD "my-len-my-app"

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
  -- from the emitted admission data (#37), and tp:MY-LEN by the TP prover
  -- from the emitted corollary + `:LEAVES` (TP-replay arc increment 1) —
  -- the replayed statement is now UNCONDITIONAL as the driver emits it
  mylenReplayedCond env

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

private def revLog : String := include_str "../../../acl2_samples/recon-tests/02-rev.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def revDev : Development :=
  load_development% revLog

derive_world revWorldD from revDev

/-- The conditional replayed statement as a definition (the driver's proof OBJECT):
    `∀ env, total:app → <EvTrue of (equal (app (app a b) c)
    (app a (app b c)))>` (truthiness, G2). -/
replayed_theorem appAssocReplayedCond := driver_replayed% revDev revWorldD "app-assoc"

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

private def directLog : String := include_str "../../../acl2_samples/recon-tests/00-direct.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def directDev : Development :=
  load_development% directLog

derive_world directWorldD from directDev

/-- The replayed statement as a definition (UNCONDITIONAL — the tree is a pure preprocess
    discharge, so the driver emits no hypotheses). -/
replayed_theorem groundArithReplayedCond := driver_replayed% directDev directWorldD "ground-arith"

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
replayed_theorem sqOf3ReplayedCond := driver_replayed% directDev directWorldD "sq-of-3"

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

private def eqLog : String := include_str "../../../acl2_samples/recon-tests/08-equality-reasoning.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def eqDev : Development :=
  load_development% eqLog

derive_world eqWorldD from eqDev

replayed_theorem cdrConsReplayedCond := driver_replayed% eqDev eqWorldD "cdr-cons-refl"
replayed_theorem equalSymmReplayedCond := driver_replayed% eqDev eqWorldD "equal-symm"
replayed_theorem equalTransReplayedCond := driver_replayed% eqDev eqWorldD "equal-trans"

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

private def multiLog : String := include_str "../../../acl2_samples/recon-tests/01-multi-theorem.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def multiDev : Development :=
  load_development% multiLog

derive_world multiWorldD from multiDev

replayed_theorem appConsCarReplayedCond := driver_replayed% multiDev multiWorldD "app-cons-car"

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

/-! ## Entry 9 — `len-rev-acc`: `(revAccL xs acc).length = xs.length + acc.length`

From the REAL `recon-tests/14-accumulator.proof-log` — the ACCUMULATOR
class, and the `derive_sim%` template gate's decisive case. The book's
`REV-ACC` admits two candidate native readings; only the ALIGNED one
(`Worlds.RevAcc.revAccL`, the exec's own recursion) passes the fixed iso
template, so the decode's simulation step carries no reassociation
content (the reassociating reading `xs.reverse ++ acc` is the fact ACL2
states as a separate book theorem). `LEN` is a builtin — world-absent by
the `builtinNames` exclusion — so the three `(LEN …)` calls dispatch
straight to `Logic.len` (`logic_len_enc` is their sim step).

The row is UNCONDITIONAL: the driver emits no hypotheses (its
`total:REV-ACC` obligation is auto-discharged from the emitted admission
data). -/

private def accLog : String :=
  include_str "../../../acl2_samples/recon-tests/14-accumulator.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def accDev : Development :=
  load_development% accLog

derive_world accWorldD from accDev

/-- The driver's replayed statement as a definition (the proof OBJECT). -/
replayed_theorem lenRevAccReplayedCond := driver_replayed% accDev accWorldD "len-rev-acc"

/-- The driver replayed statement — UNCONDITIONAL, and STATEMENT-PINNED to the
    hand `len_rev_accFormula` (read off the log's root Goal clause:
    `(EQUAL (LEN (REV-ACC X ACC)) (BINARY-+ (LEN X) (LEN ACC)))`); the two
    are the same term, so the proof closes definitionally. -/
theorem lenRevAccReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f accWorldD env
      Worlds.RevAcc.len_rev_accFormula = some v ∧ v ≠ SExpr.nil :=
  lenRevAccReplayedCond env

/-- ENTRY 9, PROVED — the accumulator's length law through the DRIVER's
    replayed statement. -/
theorem len_rev_acc_native_driver (xs acc : List SExpr) :
    (Worlds.RevAcc.revAccL xs acc).length = xs.length + acc.length :=
  Worlds.RevAcc.len_rev_acc_native_of_replayed accWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) lenRevAccReplayed_uncond xs acc

/-! ## Entries 10–12 — the rest of the 02-rev book: `app-nil`, `rev-app`,
    `rev-rev`

The same log/world as entry 2 (`revDev`/`revWorldD`), three more rows —
all three UNCONDITIONAL as the driver emits them (the `cond[…]` labels on
the golden's APP-NIL/REV-REV lines sit inside `[DISCHARGE: …]`, i.e. on
the standalone informational DP probe, not on the row).

What was missing until now was decode-side only: the APP/REV exec+iso kit
(`Imported/Rev.lean`, generated by `derive_exec%`/`derive_sim%`) and, for
the two `(IMPLIES (TRUE-LISTP X) …)` rows, the hypothesis absorption —
discharged at the seam by `Lifting.trueListp_enc` (every `enc` image is a
true list), never assumed. -/

/-- The driver's replayed statement for APP-NIL (the proof OBJECT). -/
replayed_theorem appNilReplayedCond := driver_replayed% revDev revWorldD "app-nil"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to the
    hand `app_nilFormula` (read off the log's root Goal clause:
    `(IMPLIES (TRUE-LISTP X) (EQUAL (APP X 'NIL) X))`). -/
theorem appNilReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f revWorldD env
      Worlds.Rev.app_nilFormula = some v ∧ v ≠ SExpr.nil :=
  appNilReplayedCond env

/-- ENTRY 10, PROVED — `xs ++ [] = xs` (over `SExpr`) through the DRIVER's
    replayed statement, with the true-listp antecedent discharged at the
    encoded instance. -/
theorem app_nil_native_driver (xs : List SExpr) : xs ++ [] = xs :=
  Worlds.Rev.app_nil_native_of_replayed revWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    appNilReplayed_uncond xs

/-- The driver's replayed statement for REV-APP (the proof OBJECT). -/
replayed_theorem revAppReplayedCond := driver_replayed% revDev revWorldD "rev-app"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to the
    hand `rev_appFormula`
    (`(EQUAL (REV (APP A B)) (APP (REV B) (REV A)))`). -/
theorem revAppReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f revWorldD env
      Worlds.Rev.rev_appFormula = some v ∧ v ≠ SExpr.nil :=
  revAppReplayedCond env

/-- ENTRY 11, PROVED — reversal distributes over append (in `revL`/`++`
    vocabulary) through the DRIVER's replayed statement. -/
theorem rev_app_native_driver (xs ys : List SExpr) :
    Worlds.Rev.revL (xs ++ ys) = Worlds.Rev.revL ys ++ Worlds.Rev.revL xs :=
  Worlds.Rev.rev_app_native_of_replayed revWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    revAppReplayed_uncond xs ys

/-- The driver's replayed statement for REV-REV (the proof OBJECT). -/
replayed_theorem revRevReplayedCond := driver_replayed% revDev revWorldD "rev-rev"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to the
    hand `rev_revFormula`
    (`(IMPLIES (TRUE-LISTP X) (EQUAL (REV (REV X)) X))`). -/
theorem revRevReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f revWorldD env
      Worlds.Rev.rev_revFormula = some v ∧ v ≠ SExpr.nil :=
  revRevReplayedCond env

/-- ENTRY 12, PROVED — reversal is an involution through the DRIVER's
    replayed statement, with the true-listp antecedent discharged at the
    encoded instance. -/
theorem rev_rev_native_driver (xs : List SExpr) :
    Worlds.Rev.revL (Worlds.Rev.revL xs) = xs :=
  Worlds.Rev.rev_rev_native_of_replayed revWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) revRevReplayed_uncond xs

end ACL2.Imported.Waypoints
