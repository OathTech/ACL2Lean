import ACL2Lean.Imported.SimGen

/-! # Imported: the perm book — hand support for the `perm-cons` bridge

World-parametric (invariant L3) support for lifting the driver-replayed
`perm-cons` mirror to the native Lean statement

    `xs.contains a → (xs.isPerm (a :: ys) = (xs.erase a).isPerm ys)`

(with the propositional corollary over `List.Perm` via `List.isPerm_iff`).

Contents:
- HAND HYPOTHESIS DISCHARGERS for the replayed statement's two conditions — `total:perm`
  (the totality prover's user-fn-if-test frontier) and `tp:memb` (no TP
  prover exists yet). Both are the ratified "demos for industrialization"
  (2026-07-04): each mechanizes exactly the induction a future prover
  extension will generate.
- SIMULATIONS under `enc`: `memb` computes `List.contains`, `rm` computes
  `List.erase`, `perm` computes `List.isPerm` (all `BEq`-based, matching
  ACL2's `equal`).
- THE ASSEMBLY `perm_cons_native_of_replayed`: any proof of the mirror
  statement over a world carrying the three defuns yields the native
  theorem; the driver's replayed statement plugs in at exactly one seam
  (`Imported/NativeMirrors`). -/

open ACL2 ACL2.Replay ACL2.Lifting

namespace ACL2.Worlds.Perm

/-! ## The defuns, exactly as the log-derived world carries them

The book's symbol/term vocabulary and the three macroexpanded bodies
(`membBody` / `rmBody` / `permBody`) are ACL2 transcription data and
live in `Demo/Sorting/AclSource.lean`; everything below consumes them
from there. -/

private def memb_sym : Symbol := { package := "ACL2", name := "MEMB" }
private def rm_sym : Symbol := { package := "ACL2", name := "RM" }
private def perm_sym : Symbol := { package := "ACL2", name := "PERM" }

private theorem memb_ns :
    (memb_sym.isNamed "QUOTE" = false ∧ memb_sym.isNamed "IF" = false ∧
     memb_sym.isNamed "LET" = false ∧ memb_sym.isNamed "LET*" = false) := by decide
private theorem rm_ns :
    (rm_sym.isNamed "QUOTE" = false ∧ rm_sym.isNamed "IF" = false ∧
     rm_sym.isNamed "LET" = false ∧ rm_sym.isNamed "LET*" = false) := by decide
private theorem perm_ns :
    (perm_sym.isNamed "QUOTE" = false ∧ perm_sym.isNamed "IF" = false ∧
     perm_sym.isNamed "LET" = false ∧ perm_sym.isNamed "LET*" = false) := by decide

/-! ## Small kit -/

private theorem nil_of_toBool_false {v : SExpr} (h : Logic.toBool v = false) :
    v = SExpr.nil := by
  cases v <;> simp_all [Logic.toBool]

/-- Fix a per-fuel existential value by fuel monotonicity. -/
private theorem conv_fix {w : World} {e : Env} {t : SExpr}
    (h : ∃ N, ∀ f ≥ N, ∃ u, evalOpt f w e t = some u) :
    ∃ N, ∃ u, ∀ f ≥ N, evalOpt f w e t = some u := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨u, hu⟩ := hN N (le_refl N)
  exact ⟨N, u, fun f hf => evalOpt_ge_fuel N f w e t u hu hf⟩

/-- 2-ary argument STRICTNESS: a converging 2-ary (non-special) application
    has converging arguments. -/
private theorem evalOpt_app2_args (f : Nat) (w : World) (env : Env)
    (s : Symbol) (a1 a2 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) = some v) :
    (∃ u, evalOpt f w env a1 = some u) ∧ (∃ u, evalOpt f w env a2 = some u) := by
  rw [show evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil)))
        = evalOptStep (evalOpt f) w env
            (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) from rfl] at h
  unfold evalOptStep at h
  simp only [Symbol.isNamed, SExpr.toList?] at h
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self,
             ↓reduceIte] at h
  cases hu1 : evalOpt f w env a1 with
  | none => simp [List.mapM, List.mapM.loop, hu1] at h
  | some u1 =>
    cases hu2 : evalOpt f w env a2 with
    | none => simp [List.mapM, List.mapM.loop, hu1, hu2] at h
    | some u2 => exact ⟨⟨u1, rfl⟩, ⟨u2, rfl⟩⟩

private theorem conv_args2_of_conv_app (w : World) (env : Env) (s : Symbol)
    (a1 a2 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) = some v) :
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a1 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a2 = some u) := by
  obtain ⟨N, hN⟩ := h
  constructor
  · exact conv_fix ⟨N, fun f hf =>
      (evalOpt_app2_args f w env s a1 a2 v h_ns (hN (f + 1) (by omega))).1⟩
  · exact conv_fix ⟨N, fun f hf =>
      (evalOpt_app2_args f w env s a1 a2 v h_ns (hN (f + 1) (by omega))).2⟩

/-! ## Env plumbing for the `bindArgs`-shaped bodies -/

private theorem bindArgs_ax_a (va vx : SExpr) :
    (bindArgs [aS, xS] [va, vx]).get? aS = some va := by
  show ((({} : Env).insert xS vx).insert aS va).get? aS = some va
  simp
private theorem bindArgs_ax_x (va vx : SExpr) :
    (bindArgs [aS, xS] [va, vx]).get? xS = some vx := by
  show ((({} : Env).insert xS vx).insert aS va).get? xS = some vx
  simp [Env.get?_insert, aS, xS]
private theorem bindArgs_ex_e (ve vx : SExpr) :
    (bindArgs [eS, xS] [ve, vx]).get? eS = some ve := by
  show ((({} : Env).insert xS vx).insert eS ve).get? eS = some ve
  simp
private theorem bindArgs_ex_x (ve vx : SExpr) :
    (bindArgs [eS, xS] [ve, vx]).get? xS = some vx := by
  show ((({} : Env).insert xS vx).insert eS ve).get? xS = some vx
  simp [Env.get?_insert, eS, xS]
private theorem bindArgs_xy_x (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? xS = some vx := by
  show ((({} : Env).insert yS vy).insert xS vx).get? xS = some vx
  simp
private theorem bindArgs_xy_y (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? yS = some vy := by
  show ((({} : Env).insert yS vy).insert xS vx).get? yS = some vy
  simp [Env.get?_insert, xS, yS]

/-! ## Exec functions (the two-stage lift, stage 1)

Design: docs/plans/2026-07-06_two-stage-lift.md. Each `*Exec` is a TOTAL
Lean rendering of its defun body, shape-exact (D2: ite on
`Logic.toBool … = true`, `Logic.*` at builtin calls, recursion at the
self-call). `*_exec_corr` is the stage-1 corr over ALL SExpr argument
values — the same interface shape as `conv_builtin2`, so exec'd functions
compose into callers' walks like builtins (D1). The `corr_*_enc`
simulations below are corollaries (stage 1 ∘ stage 2). -/

/-- `memb`'s body as a total Lean function. -/
def membExec (a x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (Logic.equal a (Logic.car x)) = true then SExpr.t
    else membExec a (Logic.cdr x)
  else SExpr.nil
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

register_exec_kit% "MEMB" => membExec arity 2

/-- Stage 1: a `memb` call converges to `membExec` of its argument values.
    Strong induction on the measured formal's count; the body walk is the
    intended mechanized walk's exact move sequence. -/
theorem memb_exec_corr (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none) :
    ∀ (env : Env) (a x av xv : SExpr),
      ConvTo w env a av → ConvTo w env x xv →
      ConvTo w env (membT a x) (membExec av xv) := by
  have hbody : ∀ xv av : SExpr,
      ConvTo w (bindArgs [aS, xS] [av, xv]) membBody (membExec av xv) := by
    refine consCount_strong_induction
      (fun xv => ∀ av, ConvTo w (bindArgs [aS, xS] [av, xv]) membBody
        (membExec av xv)) ?_
    intro xv ih av
    have hav := re_val_var_get w (bindArgs [aS, xS] [av, xv])
      { name := "A" } av (bindArgs_ax_a av xv)
    have hxv := re_val_var_get w (bindArgs [aS, xS] [av, xv])
      { name := "X" } xv (bindArgs_ax_x av xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have heq := conv_builtin2 w _ { name := "EQUAL" } aT (carT xT) av
      (Logic.car xv) (Logic.equal av (Logic.car xv)) (by decide) h_no_equal
      hav hcar (callBuiltin_equal _ _)
    have houter := conv_if_lift w (bindArgs [aS, xS] [av, xv]) (conspT xT)
      (ifT (equalT aT (carT xT)) qT (membT aT (cdrT xT))) qNil
      (Logic.consp xv)
      (if Logic.toBool (Logic.equal av (Logic.car xv)) = true then SExpr.t
       else membExec av (Logic.cdr xv))
      SExpr.nil hconsp
      (fun hb =>
        conv_if_lift w _ (equalT aT (carT xT)) qT (membT aT (cdrT xT))
          (Logic.equal av (Logic.car xv)) SExpr.t
          (membExec av (Logic.cdr xv)) heq
          (fun _ => re_val_quote w _ SExpr.t)
          (fun _ =>
            conv_defn_2 w _ memb_sym aT (cdrT xT) av (Logic.cdr xv) aS xS
              membBody _ memb_ns h_memb hav hcdr
              (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb) av)))
      (fun _ => re_val_quote w _ SExpr.nil)
    rw [membExec.eq_def]
    exact houter
  intro env a x av xv ha hx
  exact conv_defn_2 w env memb_sym a x av xv aS xS membBody _
    memb_ns h_memb ha hx (hbody xv av)

/-- Stage 2: `membExec` on an encoded list computes `List.contains` — pure
    Lean, no evaluator, no fuel. GENERATED (`derive_sim%`): the reading is
    the t-nil Bool reading of `List.contains`. -/
derive_sim% membExec_enc for "MEMB"
  vars (a : raw) (xs : list)
  exec [a, xs]
  native (bif xs.contains a then SExpr.t else SExpr.nil)
  simp []
  induct structural xs

/-- `rm`'s body as a total Lean function. -/
def rmExec (e x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (Logic.equal e (Logic.car x)) = true then Logic.cdr x
    else Logic.cons (Logic.car x) (rmExec e (Logic.cdr x))
  else SExpr.nil
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

register_exec_kit% "RM" => rmExec arity 2

/-- Stage 1: an `rm` call converges to `rmExec` of its argument values. -/
theorem rm_exec_corr (w : World)
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (env : Env) (a x av xv : SExpr),
      ConvTo w env a av → ConvTo w env x xv →
      ConvTo w env (rmT a x) (rmExec av xv) := by
  have hbody : ∀ xv av : SExpr,
      ConvTo w (bindArgs [eS, xS] [av, xv]) rmBody (rmExec av xv) := by
    refine consCount_strong_induction
      (fun xv => ∀ av, ConvTo w (bindArgs [eS, xS] [av, xv]) rmBody
        (rmExec av xv)) ?_
    intro xv ih av
    have hav := re_val_var_get w (bindArgs [eS, xS] [av, xv])
      { name := "E" } av (bindArgs_ex_e av xv)
    have hxv := re_val_var_get w (bindArgs [eS, xS] [av, xv])
      { name := "X" } xv (bindArgs_ex_x av xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have heq := conv_builtin2 w _ { name := "EQUAL" } eT (carT xT) av
      (Logic.car xv) (Logic.equal av (Logic.car xv)) (by decide) h_no_equal
      hav hcar (callBuiltin_equal _ _)
    have houter := conv_if_lift w (bindArgs [eS, xS] [av, xv]) (conspT xT)
      (ifT (equalT eT (carT xT)) (cdrT xT)
        (consT (carT xT) (rmT eT (cdrT xT))))
      qNil (Logic.consp xv)
      (if Logic.toBool (Logic.equal av (Logic.car xv)) = true then
        Logic.cdr xv
       else Logic.cons (Logic.car xv) (rmExec av (Logic.cdr xv)))
      SExpr.nil hconsp
      (fun hb =>
        conv_if_lift w _ (equalT eT (carT xT)) (cdrT xT)
          (consT (carT xT) (rmT eT (cdrT xT)))
          (Logic.equal av (Logic.car xv)) (Logic.cdr xv)
          (Logic.cons (Logic.car xv) (rmExec av (Logic.cdr xv))) heq
          (fun _ => hcdr)
          (fun _ =>
            conv_builtin2 w _ { name := "CONS" } (carT xT) (rmT eT (cdrT xT))
              (Logic.car xv) (rmExec av (Logic.cdr xv))
              (Logic.cons (Logic.car xv) (rmExec av (Logic.cdr xv)))
              (by decide) h_no_cons hcar
              (conv_defn_2 w _ rm_sym eT (cdrT xT) av (Logic.cdr xv) eS xS
                rmBody _ rm_ns h_rm hav hcdr
                (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb) av))
              rfl))
      (fun _ => re_val_quote w _ SExpr.nil)
    rw [rmExec.eq_def]
    exact houter
  intro env a x av xv ha hx
  exact conv_defn_2 w env rm_sym a x av xv eS xS rmBody _
    rm_ns h_rm ha hx (hbody xv av)

/-- Stage 2: `rmExec` on an encoded list computes `List.erase` —
    GENERATED (`derive_sim%`). -/
derive_sim% rmExec_enc for "RM"
  vars (a : raw) (xs : list)
  exec [a, xs]
  native (enc (xs.erase a))
  simp [List.erase_cons]
  induct structural xs

/-- `perm`'s body as a total Lean function — calls the callees' exec
    functions at their call sites (D1 composition). -/
def permExec (x y : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (membExec (Logic.car x) y) = true then
      permExec (Logic.cdr x) (rmExec (Logic.car x) y)
    else SExpr.nil
  else if Logic.toBool (Logic.consp y) = true then SExpr.nil else SExpr.t
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

register_exec_kit% "PERM" => permExec arity 2

/-- Stage 1: a `perm` call converges to `permExec` of its argument values.
    The walk cites `memb_exec_corr`/`rm_exec_corr` at the callee call sites
    exactly as it cites `callBuiltin` lemmas at builtin sites. -/
theorem perm_exec_corr (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (env : Env) (x y xv yv : SExpr),
      ConvTo w env x xv → ConvTo w env y yv →
      ConvTo w env (permT x y) (permExec xv yv) := by
  have hbody : ∀ xv yv : SExpr,
      ConvTo w (bindArgs [xS, yS] [xv, yv]) permBody (permExec xv yv) := by
    refine consCount_strong_induction
      (fun xv => ∀ yv, ConvTo w (bindArgs [xS, yS] [xv, yv]) permBody
        (permExec xv yv)) ?_
    intro xv ih yv
    have hxv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
      { name := "X" } xv (bindArgs_xy_x xv yv)
    have hyv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
      { name := "Y" } yv (bindArgs_xy_y xv yv)
    have hconspx := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hconspy := conv_builtin1 w _ { name := "CONSP" } yT yv
      (Logic.consp yv) (by decide) h_no_consp hyv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hmemb := memb_exec_corr w h_memb h_no_consp h_no_equal h_no_car
      h_no_cdr _ (carT xT) yT (Logic.car xv) yv hcar hyv
    have hrm := rm_exec_corr w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
      h_no_cons _ (carT xT) yT (Logic.car xv) yv hcar hyv
    have houter := conv_if_lift w (bindArgs [xS, yS] [xv, yv]) (conspT xT)
      (ifT (membT (carT xT) yT) (permT (cdrT xT) (rmT (carT xT) yT)) qNil)
      (ifT (conspT yT) qNil qT) (Logic.consp xv)
      (if Logic.toBool (membExec (Logic.car xv) yv) = true then
        permExec (Logic.cdr xv) (rmExec (Logic.car xv) yv)
       else SExpr.nil)
      (if Logic.toBool (Logic.consp yv) = true then SExpr.nil else SExpr.t)
      hconspx
      (fun hb =>
        conv_if_lift w _ (membT (carT xT) yT)
          (permT (cdrT xT) (rmT (carT xT) yT)) qNil
          (membExec (Logic.car xv) yv)
          (permExec (Logic.cdr xv) (rmExec (Logic.car xv) yv))
          SExpr.nil hmemb
          (fun _ =>
            conv_defn_2 w _ perm_sym (cdrT xT) (rmT (carT xT) yT)
              (Logic.cdr xv) (rmExec (Logic.car xv) yv) xS yS permBody _
              perm_ns h_perm hcdr hrm
              (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb)
                (rmExec (Logic.car xv) yv)))
          (fun _ => re_val_quote w _ SExpr.nil))
      (fun _ =>
        conv_if_lift w _ (conspT yT) qNil qT (Logic.consp yv)
          SExpr.nil SExpr.t hconspy
          (fun _ => re_val_quote w _ SExpr.nil)
          (fun _ => re_val_quote w _ SExpr.t))
    rw [permExec.eq_def]
    exact houter
  intro env x y xv yv hx hy
  exact conv_defn_2 w env perm_sym x y xv yv xS yS permBody _
    perm_ns h_perm hx hy (hbody xv yv)

/-- Stage 2: `permExec` on encoded lists computes `List.isPerm` —
    GENERATED (`derive_sim%`); the MEMB/RM callee isos resolve through the
    exec-kit registry. -/
derive_sim% permExec_enc for "PERM"
  vars (xs : list) (ys : list)
  exec [xs, ys]
  native (bif xs.isPerm ys then SExpr.t else SExpr.nil)
  simp [List.isPerm]
  induct structural xs generalizing ys

/-! ## Simulations under `enc` -/

/-- `memb` over an encoded second argument computes `List.contains`. -/
theorem corr_memb_enc (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a x : SExpr) (av : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some av) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' x = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (membT a x)
      = some (bif xs.contains av then SExpr.t else SExpr.nil) := by
  intro xs e' a x av ha hx
  have h := memb_exec_corr w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
    e' a x av (enc xs) ha hx
  rwa [membExec_enc] at h

/-- `rm` over an encoded second argument computes `List.erase`. -/
theorem corr_rm_enc (w : World)
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a x : SExpr) (av : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some av) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' x = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (rmT a x) = some (enc (xs.erase av)) := by
  intro xs e' a x av ha hx
  have h := rm_exec_corr w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons e' a x av (enc xs) ha hx
  rwa [rmExec_enc] at h

/-- `perm` over encoded arguments computes `List.isPerm`. -/
theorem corr_perm_enc (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (xs ys : List SExpr) (e' : Env) (x y : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' x = some (enc xs)) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' y = some (enc ys)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (permT x y)
      = some (bif xs.isPerm ys then SExpr.t else SExpr.nil) := by
  intro xs ys e' x y hx hy
  have h := perm_exec_corr w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons e' x y (enc xs) (enc ys) hx hy
  rwa [permExec_enc] at h

/-! ## The assembly -/

/-- The perm-cons replayed-statement formula, exactly as the log emits it. -/
def perm_consFormula : SExpr :=
  impliesT (membT aT xT)
    (equalT (permT xT (consT aT yT)) (permT (rmT aT xT) yT))

/-- The native theorem FROM the mirror: any proof of the (truthiness) mirror
    statement over a world carrying the three defuns yields
    `xs.contains a → (xs.isPerm (a :: ys) = (xs.erase a).isPerm ys)`. The
    replayed statement is consumed at exactly one seam. -/
theorem perm_cons_native_of_replayed (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env,
      ∃ N, ∀ f, f ≥ N → ∃ v,
        evalOpt f w env perm_consFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr) (hmem : xs.contains av = true) :
    xs.isPerm (av :: ys) = (xs.erase av).isPerm ys := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  -- the antecedent: (memb a x) computes contains = t
  have hP : ∃ N, ∀ f ≥ N, evalOpt f w e (membT aT xT) = some SExpr.t := by
    have h := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
      xs e aT xT av ha hx
    simpa only [hmem, cond_true] using h
  -- (cons a y) encodes (av :: ys)
  have hcons : ∃ N, ∀ f ≥ N,
      evalOpt f w e (consT aT yT) = some (enc (av :: ys)) :=
    conv_builtin2 w e { name := "CONS" } aT yT av (enc ys)
      (enc (av :: ys)) (by decide) h_no_cons ha hy rfl
  -- LHS: (perm x (cons a y)) computes isPerm xs (av :: ys)
  have hL : ∃ N, ∀ f ≥ N, evalOpt f w e (permT xT (consT aT yT))
      = some (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil) :=
    corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons xs (av :: ys) e xT (consT aT yT) hx hcons
  -- RHS: (perm (rm a x) y) computes isPerm (xs.erase av) ys
  have hrm : ∃ N, ∀ f ≥ N,
      evalOpt f w e (rmT aT xT) = some (enc (xs.erase av)) :=
    corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e aT xT av ha hx
  have hR : ∃ N, ∀ f ≥ N, evalOpt f w e (permT (rmT aT xT) yT)
      = some (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil) :=
    corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons (xs.erase av) ys e (rmT aT xT) yT hrm hy
  -- the replayed statement at e: implies-truthy; antecedent truthy → equal truthy
  have hEq : ∃ N, ∀ f ≥ N, evalOpt f w e
      (equalT (permT xT (consT aT yT)) (permT (rmT aT xT) yT))
      = some (Logic.equal
          (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
          (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil)) :=
    conv_builtin2 w e { name := "EQUAL" } _ _ _ _ _ (by decide) h_no_equal
      hL hR (callBuiltin_equal _ _)
  have hImp : ∃ N, ∀ f ≥ N, evalOpt f w e perm_consFormula
      = some (Logic.implies SExpr.t
          (Logic.equal
            (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
            (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil))) :=
    conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
      h_no_implies hP hEq (callBuiltin_implies _ _)
  -- decode: the replayed statement's truthiness pins implies ≠ nil → = t → equal truthy
  obtain ⟨Nm, hm⟩ := hreplayed e
  have hne : Logic.implies SExpr.t
      (Logic.equal
        (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
        (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil))
      ≠ SExpr.nil := by
    obtain ⟨NI, hI⟩ := hImp
    obtain ⟨v, hv, hvne⟩ := hm (max Nm NI) (by omega)
    have : v = Logic.implies SExpr.t _ :=
      Option.some.inj ((hI (max Nm NI) (by omega)) ▸ hv.symm.trans rfl)
    exact this ▸ hvne
  have hIt := implies_t_of_ne_nil hne
  have hQt : Logic.toBool (Logic.equal
      (bif xs.isPerm (av :: ys) then SExpr.t else SExpr.nil)
      (bif (xs.erase av).isPerm ys then SExpr.t else SExpr.nil)) = true :=
    truthy_of_implies_t hIt rfl
  -- Bool-cond injectivity: t ≠ nil discriminates
  exact bool_of_cond_eq (eq_of_equal_truthy hQt)

/-! ## The remaining perm-book native entries (lifter sprint 2026-07-06)

Each consumes its theorem's UNCONDITIONAL driver replayed statement at exactly one seam
(`hreplayed`) and decodes through the `corr_*` simulation layer with the
Lifting decode kit (`replayed_pins_ne_nil` / `bool_of_cond_eq` /
`conv_and_conds` / `replayed_peel_guard`). -/

private def bS : Symbol := { package := "ACL2", name := "B" }
private def bT : SExpr := .atom (.symbol { name := "B" })
private def zS : Symbol := { package := "ACL2", name := "Z" }
private def zT : SExpr := .atom (.symbol { name := "Z" })

def perm_symmetricFormula : SExpr := impliesT (permT xT yT) (permT yT xT)

/-- perm-symmetric, natively: `isPerm` is symmetric. -/
theorem perm_symmetric_native_of_replayed (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_symmetricFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys : List SExpr) (hp : xs.isPerm ys = true) :
    ys.isPerm xs = true := by
  let e : Env := (({} : Env).insert yS (enc ys)).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert yS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = (({} : Env).insert yS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hA := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs ys e xT yT hx hy
  have hC := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons ys xs e yT xT hy hx
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hA hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hp]; rfl))

def memb_rmFormula : SExpr := impliesT (membT aT (rmT bT xT)) (membT aT xT)

/-- memb-rm, natively: membership survives erasing another element. -/
theorem memb_rm_native_of_replayed (w : World)
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env memb_rmFormula = some v ∧ v ≠ SExpr.nil)
    (av bv : SExpr) (xs : List SExpr)
    (hmem : (xs.erase bv).contains av = true) :
    xs.contains av = true := by
  let e : Env := ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
    re_val_var_get w e { name := "B" } bv (by
      show e.get? bS = some bv
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hrm := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons xs e bT xT bv hb hx
  have hA := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
    (xs.erase bv) e aT (rmT bT xT) av ha hrm
  have hC := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
    xs e aT xT av ha hx
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hA hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hmem]; rfl))

def comm_rmFormula : SExpr := equalT (rmT aT (rmT bT xT)) (rmT bT (rmT aT xT))

/-- comm-rm, natively: erasures commute (a LIST equality, decoded via `enc`
    injectivity). -/
theorem comm_rm_native_of_replayed (w : World)
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env comm_rmFormula = some v ∧ v ≠ SExpr.nil)
    (av bv : SExpr) (xs : List SExpr) :
    (xs.erase bv).erase av = (xs.erase av).erase bv := by
  let e : Env := ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
    re_val_var_get w e { name := "B" } bv (by
      show e.get? bS = some bv
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hL := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons (xs.erase bv) e aT (rmT bT xT) av ha
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e bT xT bv hb hx)
  have hR := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons (xs.erase av) e bT (rmT aT xT) bv hb
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e aT xT av ha hx)
  have hEq := conv_builtin2 w e { name := "EQUAL" } _ _ _ _ _ (by decide)
    h_no_equal hL hR (callBuiltin_equal _ _)
  exact enc_inj (eq_of_equal_truthy (toBool_true_of_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hEq)))

def perm_membFormula : SExpr :=
  impliesT (ifT (permT xT yT) (membT aT xT) qNil) (membT aT yT)

/-- perm-memb, natively: membership transports across `isPerm`. -/
theorem perm_memb_native_of_replayed (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_membFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) (hmem : xs.contains av = true) :
    ys.contains av = true := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hAnd := conv_and_conds w e (permT xT yT) (membT aT xT)
    (xs.isPerm ys) (xs.contains av)
    (corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons xs ys e xT yT hx hy)
    (corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
      xs e aT xT av ha hx)
  have hC := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car h_no_cdr
    ys e aT yT av ha hy
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hAnd hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hb : (xs.isPerm ys && xs.contains av) = true := by rw [hp, hmem]; rfl
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hb]; rfl))

def perm_rmFormula : SExpr :=
  impliesT (permT xT yT) (permT (rmT aT xT) (rmT aT yT))

/-- perm-rm, natively: `isPerm` is preserved by erasing the same element. -/
theorem perm_rm_native_of_replayed (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_rmFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr) (hp : xs.isPerm ys = true) :
    (xs.erase av).isPerm (ys.erase av) = true := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hA := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs ys e xT yT hx hy
  have hC := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons (xs.erase av) (ys.erase av) e
    (rmT aT xT) (rmT aT yT)
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e aT xT av ha hx)
    (corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      ys e aT yT av ha hy)
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hA hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hp]; rfl))

def perm_transitiveFormula : SExpr :=
  impliesT (ifT (permT xT yT) (permT yT zT) qNil) (permT xT zT)

/-- perm-transitive, natively: `isPerm` is transitive. -/
theorem perm_transitive_native_of_replayed (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_transitiveFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys zs : List SExpr)
    (hxy : xs.isPerm ys = true) (hyz : ys.isPerm zs = true) :
    xs.isPerm zs = true := by
  let e : Env := ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hz : ∃ N, ∀ f ≥ N, evalOpt f w e zT = some (enc zs) :=
    re_val_var_get w e { name := "Z" } (enc zs) (by
      show e.get? zS = some (enc zs)
      rw [show e = ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hAnd := conv_and_conds w e (permT xT yT) (permT yT zT)
    (xs.isPerm ys) (ys.isPerm zs)
    (corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons xs ys e xT yT hx hy)
    (corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons ys zs e yT zT hy hz)
  have hC := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs zs e xT zT hx hz
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hAnd hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hb : (xs.isPerm ys && ys.isPerm zs) = true := by rw [hxy, hyz]; rfl
  exact bool_true_of_cond_truthy
    (truthy_of_implies_t hIt (by rw [cond_t_of_true hb]; rfl))

private abbrev booleanpT (x : SExpr) : SExpr := app1 "BOOLEANP" x

/-- The `defequiv`-generated obligation, macroexpanded exactly as ACL2's
    Goal input clause states it (audit #3 verified this byte-for-byte
    against the log's :INPUTCLAUSE). -/
def perm_equivFormula : SExpr :=
  ifT (booleanpT (permT xT yT))
    (ifT (permT xT xT)
      (ifT (impliesT (permT xT yT) (permT yT xT))
        (impliesT (ifT (permT xT yT) (permT yT zT) qNil) (permT xT zT))
        qNil)
      qNil)
    qNil

/-- perm-is-an-equivalence, natively — the genuinely NEW conjunct is
    REFLEXIVITY (the symmetric/transitive conjuncts have their own
    theorems): peel the `booleanp` guard (type-absorbed), then the `(perm
    x x)` guard IS the native fact. -/
theorem perm_refl_native_of_replayed (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_booleanp : w.defs.get? ({ name := "BOOLEANP" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_equivFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) : xs.isPerm xs = true := by
  let e : Env := ((({} : Env).insert zS (enc [])).insert yS (enc [])).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert zS (enc [])).insert yS (enc [])).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc []) :=
    re_val_var_get w e { name := "Y" } (enc []) (by
      show e.get? yS = some (enc [])
      rw [show e = ((({} : Env).insert zS (enc [])).insert yS (enc [])).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- guard 1: (booleanp (perm x y)) computes to t = bif true (type-absorbed)
  have hpxy := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs [] e xT yT hx hy
  have hG1 : ∃ N, ∀ f ≥ N, evalOpt f w e (booleanpT (permT xT yT))
      = some (bif true then SExpr.t else SExpr.nil) := by
    have h := conv_builtin1 w e { name := "BOOLEANP" } (permT xT yT)
      (bif xs.isPerm [] then SExpr.t else SExpr.nil)
      (Logic.booleanp (bif xs.isPerm [] then SExpr.t else SExpr.nil))
      (by decide) h_no_booleanp hpxy (callBuiltin_booleanp _)
    rw [booleanp_cond] at h
    exact h
  obtain ⟨_, hrest⟩ := replayed_peel_guard (hreplayed e) hG1
  -- guard 2: (perm x x) — its Bool IS the reflexivity fact
  have hG2 := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs xs e xT xT hx hx
  exact (replayed_peel_guard hrest hG2).1

/-- The idiomatic corollary over `List.Perm`: a member can be moved across —
    `a ∈ xs → (xs ~ a :: ys ↔ xs.erase a ~ ys)`. -/
theorem perm_cons_native_perm_of_replayed (w : World)
    (h_perm : w.defs.get? perm_sym = some ([xS, yS], permBody))
    (h_memb : w.defs.get? memb_sym = some ([aS, xS], membBody))
    (h_rm : w.defs.get? rm_sym = some ([eS, xS], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env,
      ∃ N, ∀ f, f ≥ N → ∃ v,
        evalOpt f w env perm_consFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs ys : List SExpr) (hmem : av ∈ xs) :
    xs.Perm (av :: ys) ↔ (xs.erase av).Perm ys := by
  have h := perm_cons_native_of_replayed w h_perm h_memb h_rm h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_cons h_no_implies hreplayed av xs ys
    (by simpa [List.contains_iff_mem] using hmem)
  constructor
  · intro hp
    exact List.isPerm_iff.mp (h ▸ List.isPerm_iff.mpr hp)
  · intro hp
    exact List.isPerm_iff.mp (h ▸ List.isPerm_iff.mpr hp)

end ACL2.Worlds.Perm

