/-
  Replay/Lemmas/TpClosure — the TP prover's RETURN-PATH composition lemma
  and the per-corollary-CLASS value-closure facts it consumes (TP-replay
  arc increment 1, 2026-08-12).

  The split is deliberate. `convP_builtin2` is the SHAPE move: a return-path
  application of a registered primitive carries the corollary predicate from
  its arguments to the application, for an ARBITRARY predicate `P`, given
  that the primitive's value function preserves `P`. That preservation is
  the only class-specific content, and it lives here as one lemma per
  (corollary class, primitive) pair — a statement about the LIFTED emitted
  corollary itself, never about any particular function.
-/
import ACL2Lean.Replay.Lemmas.Discharge

namespace ACL2.Replay

open ACL2

/-! ## The return-path composition move -/

/-- The UNCONSTRAINED argument obligation (TP-replay arc increment 2,
    2026-08-13). A constructor closure need not constrain every argument:
    `CONSP` of a `CONS` holds whatever the arguments are, and `TRUE-LISTP`
    of a `CONS` constrains only the TAIL. The unconstrained positions carry
    this trivial predicate, so a `ConvToP … TpArgAny` is exactly plain
    evaluability (`convP_any`) — the walk's existing convergence machinery,
    with no type content added Lean-side. -/
def TpArgAny : SExpr → Prop := fun _ => True

/-- An unconstrained argument position: plain convergence IS the
    obligation. -/
theorem convP_any {w : World} {env : Env} {t : SExpr}
    (h : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v) :
    ConvToP w env t TpArgAny := by
  obtain ⟨N, v, hv⟩ := h
  exact ⟨v, trivial, N, hv⟩

/-- A 2-ary registered BUILTIN on the TP return path: the value predicate
    carries from the arguments to the application. `g`/`hg` are the
    primitive's total value function and its `callBuiltin` characterization
    (the `dpBinary` rfl lemma); `hcl` is the corollary class's CLOSURE fact
    for that primitive. The TP analogue of `conv_builtin2_ex`.

    `Pa`/`Pb` are the PER-ARGUMENT obligations, which are NOT in general
    `P`: the driver reads them off the closure's registered ARG-OBLIGATION
    PROFILE (`TpArgProfile`) and passes `TpArgAny` at every unconstrained
    position. -/
theorem convP_builtin2 (w : World) (env : Env) (s : Symbol) (a b : SExpr)
    (g : SExpr → SExpr → SExpr) (P Pa Pb : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_no : w.defs.get? s = none)
    (hg : ∀ u v, callBuiltin s.name [u, v] = some (g u v))
    (hcl : ∀ u v, Pa u → Pb v → P (g u v))
    (ha : ConvToP w env a Pa) (hb : ConvToP w env b Pb) :
    ConvToP w env
      (.cons (.atom (.symbol s)) (.cons a (.cons b .nil))) P := by
  obtain ⟨av, hPa, ha'⟩ := ha
  obtain ⟨bv, hPb, hb'⟩ := hb
  exact ⟨g av bv, hcl av bv hPa hPb,
    conv_builtin2 w env s a b av bv (g av bv) h_ns h_no ha' hb' (hg av bv)⟩

/-! ## Corollary-class closure facts

A class is named for the EMITTED corollary shape it lifts (the recognizer
lives with the prover, `tpCorClass?`). `NON-NEGATIVE-INTEGER` is ACL2's
`(IF (INTEGERP (f …)) (NOT (< (f …) '0)) 'NIL)` — `:BASICTS 7`,
`*ts-non-negative-integer*` — value-lifted by `dpValExpr`, i.e. EXACTLY the
`P` the prover builds for that corollary (`bif`/`cond`-shaped `IF`, `Logic`
primitives, the quoted `'0` reflected). `dp_nonneg_int_of_tp` is the
forward decode of that same predicate; `nonNegIntCor_of_nat` is its
converse. -/

/-- The lifted `NON-NEGATIVE-INTEGER` corollary holds of every Nat-image
    integer atom — the converse of `dp_nonneg_int_of_tp`. -/
theorem nonNegIntCor_of_nat (n : Nat) :
    (bif Logic.toBool (Logic.integerp (.atom (.number (.int (n : Int)))))
     then Logic.not
       (Logic.lt (.atom (.number (.int (n : Int)))) (.atom (.number (.int 0))))
     else SExpr.nil) = SExpr.t := by
  simp [Logic.integerp, Logic.toBool, Logic.not, Logic.lt, Logic.toRat,
    if_neg (show ¬((n : Int) < 0) by omega)]

/-- CLOSURE, `NON-NEGATIVE-INTEGER` × `BINARY-+`: the emitted corollary's
    lifted predicate is preserved by ACL2 addition. This is the whole
    Lean-side content of the TP prover's `BINARY-+` return-path arm —
    ACL2's emitted leaf verdict says the leaf's type-set is covered by the
    corollary, and this says our value model agrees. -/
theorem nonNegIntCor_closed_plus (u v : SExpr)
    (hu : (bif Logic.toBool (Logic.integerp u)
           then Logic.not (Logic.lt u (.atom (.number (.int 0))))
           else SExpr.nil) = SExpr.t)
    (hv : (bif Logic.toBool (Logic.integerp v)
           then Logic.not (Logic.lt v (.atom (.number (.int 0))))
           else SExpr.nil) = SExpr.t) :
    (bif Logic.toBool (Logic.integerp (Logic.plus u v))
     then Logic.not (Logic.lt (Logic.plus u v) (.atom (.number (.int 0))))
     else SExpr.nil) = SExpr.t := by
  obtain ⟨m, rfl⟩ := dp_nonneg_int_of_tp hu
  obtain ⟨n, rfl⟩ := dp_nonneg_int_of_tp hv
  rw [logic_plus_int, show (m : Int) + (n : Int) = ((m + n : Nat) : Int) by omega]
  exact nonNegIntCor_of_nat (m + n)

/-! ### The CONSTRUCTOR classes (TP-replay arc increment 2, 2026-08-13)

`CONSP` is ACL2's `*ts-cons*` (`:BASICTS 3072` = proper ∪ improper cons)
and `TRUE-LISTP` is `*ts-true-list*` (`1152` = proper-cons ∪ nil); both are
emitted as BARE corollaries — `(CONSP (f …))` / `(TRUE-LISTP (f …))` — so
the lifted `P` is just the `Logic` recognizer at the value. Their `CONS`
closures differ exactly in their ARG-OBLIGATION PROFILE: every cons is a
cons (no obligation on either argument), while a cons is a true-list iff
its TAIL is (the head arbitrary). -/

/-- CLOSURE, `CONSP` × `CONS`, profile `neither`: a `CONS` is a `CONSP`
    whatever its arguments are. The arguments carry only `TpArgAny` —
    the walk still has to CONVERGE them, but nothing about their type is
    used or claimed. -/
theorem conspCor_closed_cons (u v : SExpr)
    (_hu : TpArgAny u) (_hv : TpArgAny v) :
    Logic.consp (SExpr.cons u v) = SExpr.t := rfl

/-- CLOSURE, `TRUE-LISTP` × `CONS`, profile `sndOnly`: consing onto a
    true-list gives a true-list; the HEAD is unconstrained (`TpArgAny`).
    `Logic.trueListp` recurses straight into the tail, so the emitted
    corollary's own lifted predicate is what carries. -/
theorem trueListpCor_closed_cons (u v : SExpr) (_hu : TpArgAny u)
    (hv : Logic.trueListp v = SExpr.t) :
    Logic.trueListp (SExpr.cons u v) = SExpr.t := hv

/-! ## The CALLEE-TP return path (TP-replay arc increment 3, 2026-08-13)

A return path may END in a call to ANOTHER function — `SORTFN1`'s
`(SORTFN1-INSERT (CAR X) (SORTFN1 (CDR X)))`, or the `BINARY-+` summand
`(HOW-MANY-SMALLER (CAR X) (CDR X))` inside `BNEXT-SIZE`'s leaf. The
value fact at such a position is the CALLEE's OWN emitted type
prescription, proved by the same prover recursively; nothing about the
callee is assumed or derived here. -/

/-- The CALLEE-TP position move: the call CONVERGES (the plain totality
    walk, which is what the callee's admission licenses), and the
    callee's own type-prescription fact — a statement about ANY value
    the call converges to (`mkTpHypType`'s shape) — supplies `P` there.
    `P` is the OUTER corollary's predicate; the driver composes the
    callee's predicate into it via the registered class implication (or
    the identity, when the classes coincide). -/
theorem convP_of_conv_ex {w : World} {env : Env} {t : SExpr}
    {P : SExpr → Prop}
    (h : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v)
    (hP : ∀ v, (∃ N, ∀ f ≥ N, evalOpt f w env t = some v) → P v) :
    ConvToP w env t P := by
  obtain ⟨N, v, hv⟩ := h
  exact ⟨v, hP v ⟨N, hv⟩, N, hv⟩

/-! ## The 3-ARY assemblies (TP-replay arc increment 4, 2026-08-13)

`Discharge.lean` carries the arity 1 and 2 `tp_*` family; the arity-3
MIRRORS live here, in the TP arc's own module (Discharge is close to the
weight ratchet's norm). Nothing new is claimed at arity 3: each statement
is the arity-3 image of its 2-ary twin (`convP_defn_2`,
`tp_hyp_2_of_body`, `tp_2_rec`, `tp_2_rec_snd`), and the
argument-strictness pair is MOVED (not copied) from
`Imported/ExecGen.lean`, which defined but never cited it. -/

/-- 3-ary argument STRICTNESS at one fuel step. -/
theorem evalOpt_app3_args (f : Nat) (w : World) (env : Env)
    (s : Symbol) (a1 a2 a3 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
      = some v) :
    (∃ u, evalOpt f w env a1 = some u) ∧
    (∃ u, evalOpt f w env a2 = some u) ∧
    (∃ u, evalOpt f w env a3 = some u) := by
  rw [show evalOpt (f + 1) w env
        (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
        = evalOptStep (evalOpt f) w env
            (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
        from rfl] at h
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
    | some u2 =>
      cases hu3 : evalOpt f w env a3 with
      | none => simp [List.mapM, List.mapM.loop, hu1, hu2, hu3] at h
      | some u3 => exact ⟨⟨u1, rfl⟩, ⟨u2, rfl⟩, ⟨u3, rfl⟩⟩

/-- 3-ary argument strictness, convergence form. -/
theorem conv_args3_of_conv_app (w : World) (env : Env) (s : Symbol)
    (a1 a2 a3 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
      = some v) :
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a1 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a2 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a3 = some u) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨conv_fix ⟨N, fun f _ => ?_⟩, conv_fix ⟨N, fun f _ => ?_⟩,
          conv_fix ⟨N, fun f _ => ?_⟩⟩
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).1
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).2.1
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).2.2

/-- A defined 3-ary call inherits the body's predicate (the 3-ary
    self-call inside the TP walk). -/
theorem convP_defn_3 (w : World) (env : Env) (s : Symbol)
    (arg1 arg2 arg3 av1 av2 av3 : SExpr)
    (formal1 formal2 formal3 : Symbol) (body : SExpr) (P : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (h3 : ∃ N, ∀ f ≥ N, evalOpt f w env arg3 = some av3)
    (hbody : ConvToP w
      (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body P) :
    ConvToP w env
      (.cons (.atom (.symbol s))
        (.cons arg1 (.cons arg2 (.cons arg3 .nil)))) P := by
  obtain ⟨v, hP, hv⟩ := hbody
  exact ⟨v, hP, conv_defn_3 w env s arg1 arg2 arg3 av1 av2 av3
    formal1 formal2 formal3 body v h_ns h_def h1 h2 h3 hv⟩

/-- The TP-HYPOTHESIS assembly, 3-ary (`mkTpHypType`'s shape at arity 3):
    argument strictness recovers the argument values, the walk pins ONE
    convergent value with `P`, determinism identifies them. -/
theorem tp_hyp_3_of_body (w : World) (s : Symbol)
    (formal1 formal2 formal3 : Symbol) (body : SExpr) (P : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (hbody : ∀ av1 av2 av3 : SExpr,
      ConvToP w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
        body P) :
    ∀ (env' : Env) (a0 a1 a2 v : SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w env'
        (.cons (.atom (.symbol s))
          (.cons a0 (.cons a1 (.cons a2 .nil)))) = some v) →
      P v := by
  intro env' a0 a1 a2 v h
  obtain ⟨⟨N0, u0, h0⟩, ⟨N1, u1, h1⟩, ⟨N2, u2, h2⟩⟩ :=
    conv_args3_of_conv_app w env' s a0 a1 a2 v h_ns h
  obtain ⟨u, hPu, hu⟩ := hbody u0 u1 u2
  have happ := conv_defn_3 w env' s a0 a1 a2 u0 u1 u2
    formal1 formal2 formal3 body u h_ns h_def ⟨N0, h0⟩ ⟨N1, h1⟩ ⟨N2, h2⟩ hu
  exact (val_unique h happ) ▸ hPu

/-- The TP body induction at arity 3, measure on the FIRST formal. -/
theorem tp_3_rec_mu (μ : SExpr → Nat)
    (formal1 formal2 formal3 : Symbol) (body : SExpr)
    (w : World) (P : SExpr → Prop)
    (step : ∀ av1 : SExpr,
      (∀ bv : SExpr, μ bv < μ av1 → ∀ cv dv : SExpr,
        ConvToP w (bindArgs [formal1, formal2, formal3] [bv, cv, dv])
          body P) →
      ∀ av2 av3 : SExpr,
        ConvToP w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
          body P) :
    ∀ av1 av2 av3 : SExpr,
      ConvToP w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
        body P :=
  measure_strong_induction_val μ
    (fun av1 => ∀ av2 av3,
      ConvToP w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
        body P)
    step

/-- The TP body induction at arity 3, measure on the SECOND formal (the
    `(fn x e)` shape — `ALL-REL`/`FILTER`). -/
theorem tp_3_rec_snd_mu (μ : SExpr → Nat)
    (formal1 formal2 formal3 : Symbol) (body : SExpr)
    (w : World) (P : SExpr → Prop)
    (step : ∀ av2 : SExpr,
      (∀ cv : SExpr, μ cv < μ av2 → ∀ bv dv : SExpr,
        ConvToP w (bindArgs [formal1, formal2, formal3] [bv, cv, dv])
          body P) →
      ∀ av1 av3 : SExpr,
        ConvToP w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
          body P) :
    ∀ av1 av2 av3 : SExpr,
      ConvToP w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
        body P :=
  fun av1 av2 av3 =>
    measure_strong_induction_val μ
      (fun av2 => ∀ av1 av3,
        ConvToP w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
          body P)
      step av2 av1 av3

/-- CLASS IMPLICATION, `CONSP` ⇒ `CONSP`-or-`NIL`: a callee whose emitted
    corollary is the BARE `(CONSP (g …))` (`*ts-cons*`, 3072) satisfies
    the weaker consp-or-nil `IF` corollary (`*ts-cons*` ∪ `*ts-nil*`,
    3200) the caller's own type prescription states. This is the whole
    Lean-side content of a cross-class callee step: both corollaries are
    EMITTED, and this says our value model agrees that one implies the
    other. The driver additionally recompute-checks the mask containment
    3072 ⊆ 3200 against the same `TpCorClass.tsMask` data. -/
theorem conspOrNilCor_of_conspCor (v : SExpr) (h : Logic.consp v = SExpr.t) :
    (bif Logic.toBool (Logic.consp v) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t := by
  rw [h]; rfl

/-! ## The ARGS-VALUED corollary (TP-replay arc increment 5, 2026-08-13)

`BINARY-APPEND`/`APP` are prescribed by ACL2 as
`(IF (CONSP (fn X Y)) 'T (EQUAL (fn X Y) Y))` — the else-disjunct names a
FORMAL, so the lifted predicate is indexed by that argument's VALUE
(`mkTpHypTypeAv`'s shape). The class's Lean-side content is three facts:
its `CONS` closure, the fact AT the residue argument itself (the `Y`
return leaf ACL2 enumerates with the unknown verdict `-1`, covered by the
EQUALITY disjunct rather than by any type-set), and the implication into
the value-only classes a CALLER's own prescription may need. -/

/-- CLOSURE, args-valued × `CONS`, profile `neither`: a `CONS` takes the
    corollary's `CONSP` disjunct whatever its arguments and whatever the
    residue argument's value `y` is. -/
theorem conspOrArgCor_closed_cons (y u v : SExpr)
    (_hu : TpArgAny u) (_hv : TpArgAny v) :
    (bif Logic.toBool (Logic.consp (SExpr.cons u v)) then SExpr.t
     else Logic.equal (SExpr.cons u v) y) = SExpr.t := rfl

/-- The args-valued corollary AT its residue argument: the return leaf that
    IS the formal `Y` takes the EQUALITY disjunct, by reflexivity of
    `Logic.equal`. This is why the leaf's emitted verdict (`-1`, unknown)
    needs no mask check — the corollary covers that leaf by its equality
    disjunct, not by a type-set. -/
theorem conspOrArgCor_at_arg (y : SExpr) :
    (bif Logic.toBool (Logic.consp y) then SExpr.t
     else Logic.equal y y) = SExpr.t := by
  cases h : Logic.toBool (Logic.consp y) with
  | true => rfl
  | false => exact logic_equal_self y

/-- CLOSURE, `CONSP`-or-`NIL` × `CONS`, profile `neither` (needed by the
    args-valued CALLEE step, which walks the residue ARGUMENT under the
    CALLER's own predicate). -/
theorem conspOrNilCor_closed_cons (u v : SExpr)
    (_hu : TpArgAny u) (_hv : TpArgAny v) :
    (bif Logic.toBool (Logic.consp (SExpr.cons u v)) then SExpr.t
     else Logic.equal (SExpr.cons u v) SExpr.nil) = SExpr.t := rfl

/-- CLASS IMPLICATION (args-valued form), args-valued ⇒ `CONSP`-or-`NIL`:
    the callee's value is a cons OR it IS the residue argument's value `y`
    — so the caller's consp-or-nil prescription holds of it as soon as it
    holds of `y`. The `y` premise is NOT assumed: the driver proves it by
    walking the residue ARGUMENT under the caller's own predicate (the
    same machinery, no new class content). `REV`'s
    `(APP (REV (CDR X)) (CONS (CAR X) 'NIL))` leaf is the customer. -/
theorem conspOrNilCor_of_conspOrArgCor (y v : SExpr)
    (hy : (bif Logic.toBool (Logic.consp y) then SExpr.t
           else Logic.equal y SExpr.nil) = SExpr.t)
    (h : (bif Logic.toBool (Logic.consp v) then SExpr.t
          else Logic.equal v y) = SExpr.t) :
    (bif Logic.toBool (Logic.consp v) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t := by
  cases hv : Logic.toBool (Logic.consp v) with
  | true => rfl
  | false =>
    rw [hv] at h
    simp only [cond_false] at h ⊢
    have hvy : v = y := Logic.eq_of_equal_ne_nil (by rw [h]; simp)
    subst hvy
    rw [hv] at hy
    simp only [cond_false] at hy
    exact hy

/-- A value with the predicate plus its convergence IS the strengthened
    convergence (the args-valued residue-leaf arm's assembly). -/
theorem convP_of_val {w : World} {env : Env} {t : SExpr} {P : SExpr → Prop}
    {v : SExpr} (hP : P v)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env t = some v) : ConvToP w env t P :=
  ⟨v, hP, h⟩

/-- Transport a `ConvToP` onto an ALREADY-PINNED convergence value
    (determinism): the walk's value and the driver's lifted value are the
    same value, so the predicate holds of the latter. -/
theorem convP_at_val {w : World} {env : Env} {t : SExpr} {P : SExpr → Prop}
    {u : SExpr} (h : ConvToP w env t P)
    (hu : ∃ N, ∀ f ≥ N, evalOpt f w env t = some u) : P u := by
  obtain ⟨v, hP, hv⟩ := h
  exact (val_unique hu hv) ▸ hP

/-- The TP body induction at arity 2 with an ARGUMENT-INDEXED predicate
    (measure on the first formal): the exact `tp_2_rec_mu` statement with `P`
    depending on the argument values, as the args-valued corollary's
    lifted predicate does. -/
theorem tp_2_rec_av_mu (μ : SExpr → Nat)
    (formal1 formal2 : Symbol) (body : SExpr) (w : World)
    (P : SExpr → SExpr → SExpr → Prop)
    (step : ∀ av1 : SExpr,
      (∀ bv : SExpr, μ bv < μ av1 → ∀ cv : SExpr,
        ConvToP w (bindArgs [formal1, formal2] [bv, cv]) body (P bv cv)) →
      ∀ av2 : SExpr,
        ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body
          (P av1 av2)) :
    ∀ av1 av2 : SExpr,
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body (P av1 av2) :=
  measure_strong_induction_val μ
    (fun av1 => ∀ av2,
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body (P av1 av2))
    step

/-- The ARGS-VALUED TP-hypothesis assembly, 2-ary — exactly
    `mkTpHypTypeAv`'s conclusion at arity 2. Unlike the value-only twin
    this needs no argument strictness: the argument VALUES are premises,
    so the body walk applies at them directly and determinism identifies
    the application's value with the body's. -/
theorem tp_hyp_2_av_of_body (w : World) (s : Symbol)
    (formal1 formal2 : Symbol) (body : SExpr)
    (P : SExpr → SExpr → SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (hbody : ∀ av1 av2 : SExpr,
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body (P av1 av2)) :
    ∀ (env' : Env) (a0 a1 u0 u1 v : SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w env' a0 = some u0) →
      (∃ N, ∀ f ≥ N, evalOpt f w env' a1 = some u1) →
      (∃ N, ∀ f ≥ N, evalOpt f w env'
        (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil))) = some v) →
      P u0 u1 v := by
  intro env' a0 a1 u0 u1 v h0 h1 h
  obtain ⟨u, hPu, hu⟩ := hbody u0 u1
  have happ := conv_defn_2 w env' s a0 a1 u0 u1 formal1 formal2 body u
    h_ns h_def h0 h1 hu
  exact (val_unique h happ) ▸ hPu

/-! ## The HYPOTHESIS-CARRYING assemblies (T1+2 sprint P5b, 2026-08-16)

ACL2 stores CONDITIONAL type-prescription rules — `BINARY-APPEND` carries
the boot-strap `TRUE-LISTP-APPEND`,
`(IMPLIES (TRUE-LISTP B) (TRUE-LISTP (BINARY-APPEND A B)))`, alongside its
weak definitional rule (the fork's `:ALL-TPS` channel emits both, each with
its own hypotheses and its own context-refined `:LEAVES`). Consuming one
means carrying its hypotheses through the body induction: `H` is the
hypothesis conjunction lifted at the ARGUMENT VALUES, exactly as `P` is the
conclusion lifted at the application's value.

Nothing class-specific is claimed here — `H` is an arbitrary predicate on
the argument values, and the driver builds it from the EMITTED hypotheses.
Both statements are the `tp_2_rec_mu` / `tp_hyp_2_of_body` shapes with that
premise threaded through. -/

/-- The TP body induction at arity 2 with a HYPOTHESIS on the argument
    values (measure on the first formal). The IH carries `H` at ITS
    argument values, so a self-call must re-establish it — which is what
    makes the hypothesis honest rather than assumed. -/
theorem tp_2_rec_hyp_mu (μ : SExpr → Nat)
    (formal1 formal2 : Symbol) (body : SExpr) (w : World)
    (P : SExpr → Prop) (H : SExpr → SExpr → Prop)
    (step : ∀ av1 : SExpr,
      (∀ bv : SExpr, μ bv < μ av1 → ∀ cv : SExpr, H bv cv →
        ConvToP w (bindArgs [formal1, formal2] [bv, cv]) body P) →
      ∀ av2 : SExpr, H av1 av2 →
        ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P) :
    ∀ av1 av2 : SExpr, H av1 av2 →
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P :=
  measure_strong_induction_val μ
    (fun av1 => ∀ av2, H av1 av2 →
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P)
    step

/-- The HYPOTHESIS-CARRYING TP assembly, 2-ary: the conditional stored
    rule's statement — given the argument values, the hypothesis at them,
    and any value the call converges to, the conclusion predicate holds of
    that value. Argument strictness is not needed (the argument values are
    premises); determinism identifies the application's value with the
    body's. -/
theorem tp_hyp_2_cond_of_body (w : World) (s : Symbol)
    (formal1 formal2 : Symbol) (body : SExpr)
    (P : SExpr → Prop) (H : SExpr → SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (hbody : ∀ av1 av2 : SExpr, H av1 av2 →
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P) :
    ∀ (env' : Env) (a0 a1 u0 u1 v : SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w env' a0 = some u0) →
      (∃ N, ∀ f ≥ N, evalOpt f w env' a1 = some u1) →
      H u0 u1 →
      (∃ N, ∀ f ≥ N, evalOpt f w env'
        (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil))) = some v) →
      P v := by
  intro env' a0 a1 u0 u1 v h0 h1 hH h
  obtain ⟨u, hPu, hu⟩ := hbody u0 u1 hH
  have happ := conv_defn_2 w env' s a0 a1 u0 u1 formal1 formal2 body u
    h_ns h_def h0 h1 hu
  exact (val_unique h happ) ▸ hPu

end ACL2.Replay
