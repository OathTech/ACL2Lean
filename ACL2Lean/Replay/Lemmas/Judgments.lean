/-
  Replay/Lemmas/Judgments — section-aligned positional slice of the former
  EvalLemmas monolith (perf arc, 2026-08-07): MOVE-ONLY; the cut points
  are the file's own section-header layer boundaries, which sit in def-before-use
  order, so the import chain IS the dependency order.
-/
import ACL2Lean.Replay.Lemmas.Discharge

namespace ACL2.Replay

open ACL2

/-! ## The R-parameterized rewrite judgment (G1, binding invariant L2)

ACL2's rewriter is generic over equivalence relations (geneqv); the preprocess
chain runs under IFF, so its `(if X 't 'nil) ⇒ X` simplifications are
iff-only, not value-preserving. `EvRel R` is the rewrite judgment over an
ABSTRACT value relation — `Eq` (the convergent eval-equality) and `SIff`
(ACL2's iff) are the first two instances; user equivalence relations land as
further instances with congruence lemmas indexed by
(function, position, R-in, R-out), mirroring ACL2's congruence runes. Note
the COLLAPSE rows of that table: an iff-related test or `not` argument makes
the surrounding term eval-EQUAL (the lazy `if` consults only `toBool`). -/

/-- Value-level truthiness equivalence — ACL2's `iff` on values. -/
def SIff (u v : SExpr) : Prop := (u = SExpr.nil) ↔ (v = SExpr.nil)

theorem siff_refl (u : SExpr) : SIff u u := Iff.rfl

theorem siff_trans {u v x : SExpr} (h1 : SIff u v) (h2 : SIff v x) : SIff u x :=
  Iff.trans h1 h2

/-- The R-parameterized rewrite judgment: both sides CONVERGE, values
    R-related. `EvRel Eq` strengthens the bare eval-equality chain form by
    convergence (every replay step is convergence-backed anyway). -/
def EvRel (R : SExpr → SExpr → Prop) (w : World) (env : Env) (a b : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, ∃ u v,
    evalOpt f w env a = some u ∧ evalOpt f w env b = some v ∧ R u v

theorem evrel_trans {R : SExpr → SExpr → Prop}
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {w : World} {env : Env} {a b c : SExpr}
    (h1 : EvRel R w env a b) (h2 : EvRel R w env b c) : EvRel R w env a c := by
  obtain ⟨n1, h1⟩ := h1; obtain ⟨n2, h2⟩ := h2
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨u, v, hau, hbv, huv⟩ := h1 f (by omega)
  obtain ⟨v', x, hbv', hcx, hvx⟩ := h2 f (by omega)
  have hvv' : v = v' := Option.some.inj (hbv.symm.trans hbv')
  exact ⟨u, x, hau, hcx, htrans huv (by rw [hvv']; exact hvx)⟩

/-- A (convergent) eval-equality chain is an `EvRel R` for reflexive R —
    the injection of today's equal-steps into an iff composite. -/
theorem evrel_of_fuel_eq {R : SExpr → SExpr → Prop} (hrefl : ∀ x, R x x)
    {w : World} {env : Env} {a b v : SExpr}
    (hab : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some v) : EvRel R w env a b := by
  obtain ⟨n1, h1⟩ := hab; obtain ⟨n2, h2⟩ := hb
  refine ⟨n1 + n2, fun f hf => ?_⟩
  exact ⟨v, v, (h1 f (by omega)).trans (h2 f (by omega)), h2 f (by omega), hrefl v⟩

/-- The `PREPROCESS/IF-IFF` node: `(if A 't 'nil) ⇒ A` under IFF. The lhs's
    value is `t`/`nil` by A's truthiness — iff-related to A's own value but
    NOT equal to it (A may be truthy-non-t). -/
theorem evrel_siff_if_t_nil (w : World) (env : Env) (A vA : SExpr)
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w env A = some vA) :
    EvRel SIff w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons A (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
            .nil)))) A := by
  obtain ⟨N, hA⟩ := hA
  refine ⟨N + 2, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hAg := hA g (by omega)
  by_cases hv : vA = SExpr.nil
  · refine ⟨SExpr.nil, vA, ?_, hA (g + 1) (by omega), by simp [SIff, hv]⟩
    rw [evalOpt_if_false g w env A _ _ (by rw [hAg, hv])]
    obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
    simp [evalOpt, evalOptStep, Symbol.isNamed]
  · refine ⟨SExpr.t, vA, ?_, hA (g + 1) (by omega), by simp [SIff, hv, SExpr.t]⟩
    rw [evalOpt_if_true g w env A _ _ vA hAg (toBool_true_of_ne_nil hv)]
    obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
    simp [evalOpt, evalOptStep, Symbol.isNamed]

/-- Congruence (if, THEN-position, R-in → R-out = R): needs the test's and the
    OTHER branch's convergence (the untaken branch's value relates by
    reflexivity). Works uniformly for every reflexive R — one lemma serves the
    whole table column. -/
theorem evrel_if_then_congr {R : SExpr → SExpr → Prop} (hrefl : ∀ x, R x x)
    {w : World} {env : Env} {c thn thn' els vc vEls : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (hels : ∃ N, ∀ f ≥ N, evalOpt f w env els = some vEls)
    (hthn : EvRel R w env thn thn') :
    EvRel R w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil))))
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn' (.cons els .nil)))) := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hels⟩ := hels; obtain ⟨n3, hthn⟩ := hthn
  refine ⟨n1 + n2 + n3 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hcg := hc g (by omega)
  by_cases hv : vc = SExpr.nil
  · refine ⟨vEls, vEls, ?_, ?_, hrefl vEls⟩
    · rw [evalOpt_if_false g w env c thn els (by rw [hcg, hv])]
      exact hels g (by omega)
    · rw [evalOpt_if_false g w env c thn' els (by rw [hcg, hv])]
      exact hels g (by omega)
  · obtain ⟨u, v, hu, hv', huv⟩ := hthn g (by omega)
    refine ⟨u, v, ?_, ?_, huv⟩
    · rw [evalOpt_if_true g w env c thn els vc hcg (toBool_true_of_ne_nil hv)]
      exact hu
    · rw [evalOpt_if_true g w env c thn' els vc hcg (toBool_true_of_ne_nil hv)]
      exact hv'

/-- Congruence (if, ELSE-position, R-in → R-out = R). -/
theorem evrel_if_else_congr {R : SExpr → SExpr → Prop} (hrefl : ∀ x, R x x)
    {w : World} {env : Env} {c thn els els' vc vThn : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (hthn : ∃ N, ∀ f ≥ N, evalOpt f w env thn = some vThn)
    (hels : EvRel R w env els els') :
    EvRel R w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil))))
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els' .nil)))) := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hthn⟩ := hthn; obtain ⟨n3, hels⟩ := hels
  refine ⟨n1 + n2 + n3 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hcg := hc g (by omega)
  by_cases hv : vc = SExpr.nil
  · obtain ⟨u, v, hu, hv', huv⟩ := hels g (by omega)
    refine ⟨u, v, ?_, ?_, huv⟩
    · rw [evalOpt_if_false g w env c thn els (by rw [hcg, hv])]; exact hu
    · rw [evalOpt_if_false g w env c thn els' (by rw [hcg, hv])]; exact hv'
  · refine ⟨vThn, vThn, ?_, ?_, hrefl vThn⟩
    · rw [evalOpt_if_true g w env c thn els vc hcg (toBool_true_of_ne_nil hv)]
      exact hthn g (by omega)
    · rw [evalOpt_if_true g w env c thn els' vc hcg (toBool_true_of_ne_nil hv)]
      exact hthn g (by omega)

/-- COLLAPSE row (if, TEST-position, SIff-in → Eq-out): iff-related tests make
    the surrounding ifs eval-EQUAL — the lazy `if` consults only `toBool`. -/
theorem evrel_if_test_siff_collapse {w : World} {env : Env} {c c' thn els : SExpr}
    (hcc' : EvRel SIff w env c c') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c' (.cons thn (.cons els .nil)))) := by
  obtain ⟨n1, hcc'⟩ := hcc'
  refine ⟨n1 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨u, v, hu, hv, huv⟩ := hcc' g (by omega)
  by_cases hnu : u = SExpr.nil
  · rw [evalOpt_if_false g w env c thn els (by rw [hu, hnu]),
        evalOpt_if_false g w env c' thn els (by rw [hv, Iff.mp huv hnu])]
  · rw [evalOpt_if_true g w env c thn els u hu (toBool_true_of_ne_nil hnu),
        evalOpt_if_true g w env c' thn els v hv
          (toBool_true_of_ne_nil (fun hnv => hnu (Iff.mpr huv hnv)))]

/-- SIff toBool transport: truthiness-equivalent values have equal `toBool`. -/
theorem siff_toBool_eq {u v : SExpr} (h : SIff u v) :
    Logic.toBool u = Logic.toBool v := by
  cases u <;> cases v <;> simp_all [SIff, Logic.toBool]

/-- The OR-SHAPE normalization (G1 rung 1, inc-2): `(if a a b) ⇒ (if a 't b)`
    is IFF-only — when `a` is truthy the sides value `va` vs `t` (truthiness
    agrees); when nil both take `b`. The `rewrite-if-finish` collapse the
    fork now labels `:EQUIV IFF` (p3-conj-mid-literal). -/
theorem evrel_siff_if_or_shape (w : World) (env : Env) (a b va vb : SExpr)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some vb) :
    EvRel SIff w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons a (.cons a (.cons b .nil))))
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons a (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons b .nil)))) := by
  obtain ⟨n1, ha⟩ := ha; obtain ⟨n2, hb⟩ := hb
  refine ⟨n1 + n2 + 2, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hag := ha g (by omega)
  by_cases hv : va = SExpr.nil
  · refine ⟨vb, vb, ?_, ?_, siff_refl vb⟩
    · rw [evalOpt_if_false g w env a a b (by rw [hag, hv])]
      exact hb g (by omega)
    · rw [evalOpt_if_false g w env a _ b (by rw [hag, hv])]
      exact hb g (by omega)
  · refine ⟨va, SExpr.t, ?_, ?_, by simp [SIff, hv, SExpr.t]⟩
    · rw [evalOpt_if_true g w env a a b va hag (toBool_true_of_ne_nil hv)]
      exact ha g (by omega)
    · rw [evalOpt_if_true g w env a _ b va hag (toBool_true_of_ne_nil hv)]
      obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
      simp [evalOpt, evalOptStep, Symbol.isNamed]

/-- The OR-COLLAPSE BRIDGE (G1 rung 1, inc-2b): rewrite-if replaced the
    then-branch — the UNREWRITTEN test's copy `A` — by `'T` with no
    recorded step; with the test's own recorded chain `eval A = eval X`
    re-composed on the then-copy, the collapse is an SIff step: truthy `X`
    values the sides `vX` vs `t` (truthiness agrees), nil `X` takes `B` on
    both. -/
theorem evrel_siff_if_or_bridge (w : World) (env : Env) (X A B vX vB : SExpr)
    (hAX : ∃ N, ∀ f ≥ N, evalOpt f w env A = evalOpt f w env X)
    (hX : ∃ N, ∀ f ≥ N, evalOpt f w env X = some vX)
    (hB : ∃ N, ∀ f ≥ N, evalOpt f w env B = some vB) :
    EvRel SIff w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons X (.cons A (.cons B .nil))))
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons X (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons B .nil)))) := by
  obtain ⟨n1, hAX⟩ := hAX; obtain ⟨n2, hX⟩ := hX; obtain ⟨n3, hB⟩ := hB
  refine ⟨n1 + n2 + n3 + 2, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hXg := hX g (by omega)
  by_cases hv : vX = SExpr.nil
  · refine ⟨vB, vB, ?_, ?_, siff_refl vB⟩
    · rw [evalOpt_if_false g w env X A B (by rw [hXg, hv])]
      exact hB g (by omega)
    · rw [evalOpt_if_false g w env X _ B (by rw [hXg, hv])]
      exact hB g (by omega)
  · refine ⟨vX, SExpr.t, ?_, ?_, by simp [SIff, hv, SExpr.t]⟩
    · rw [evalOpt_if_true g w env X A B vX hXg (toBool_true_of_ne_nil hv)]
      rw [hAX g (by omega)]
      exact hX g (by omega)
    · rw [evalOpt_if_true g w env X _ B vX hXg (toBool_true_of_ne_nil hv)]
      obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
      simp [evalOpt, evalOptStep, Symbol.isNamed]

/-- COLLAPSE row (implies, CONSEQUENT position, SIff-in → Eq-out):
    `implies` consults only its arguments' truthiness, so an iff-related
    consequent makes the applications eval-EQUAL — the boolean-consumer
    sibling of the if-test collapse. -/
theorem evrel_implies_arg2_siff_collapse {w : World} {env : Env}
    {h c c' vh : SExpr}
    (hNo : w.defs.get? { name := "IMPLIES" } = none)
    (hh : ∃ N, ∀ f ≥ N, evalOpt f w env h = some vh)
    (hcc' : EvRel SIff w env c c') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IMPLIES" }))
        (.cons h (.cons c .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IMPLIES" }))
        (.cons h (.cons c' .nil))) := by
  obtain ⟨n1, hh⟩ := hh; obtain ⟨n2, hcc'⟩ := hcc'
  refine ⟨n1 + n2 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨u, v, hcu, hcv, huv⟩ := hcc' g (by omega)
  rw [evalOpt_builtin_2 g w env { name := "IMPLIES" } h c vh u
        (by simp [Symbol.isNamed]) hNo (hh g (by omega)) hcu,
      evalOpt_builtin_2 g w env { name := "IMPLIES" } h c' vh v
        (by simp [Symbol.isNamed]) hNo (hh g (by omega)) hcv,
      callBuiltin_implies, callBuiltin_implies,
      logic_implies_cond, logic_implies_cond, siff_toBool_eq huv]

/-- COLLAPSE row (implies, ANTECEDENT position, SIff-in → Eq-out). -/
theorem evrel_implies_arg1_siff_collapse {w : World} {env : Env}
    {h h' c vc : SExpr}
    (hNo : w.defs.get? { name := "IMPLIES" } = none)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (hhh' : EvRel SIff w env h h') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IMPLIES" }))
        (.cons h (.cons c .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IMPLIES" }))
        (.cons h' (.cons c .nil))) := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hhh'⟩ := hhh'
  refine ⟨n1 + n2 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨u, v, hhu, hhv, huv⟩ := hhh' g (by omega)
  rw [evalOpt_builtin_2 g w env { name := "IMPLIES" } h c u vc
        (by simp [Symbol.isNamed]) hNo hhu (hc g (by omega)),
      evalOpt_builtin_2 g w env { name := "IMPLIES" } h' c v vc
        (by simp [Symbol.isNamed]) hNo hhv (hc g (by omega)),
      callBuiltin_implies, callBuiltin_implies,
      logic_implies_cond, logic_implies_cond, siff_toBool_eq huv]

/-- Transport a NIL value across an SIff chain (both endpoints pinned) —
    the spine's falsity bridge for an IFF literal chain (G1 inc-2b). -/
theorem siff_val_nil_transport {w : World} {env : Env} {a b va vb : SExpr}
    (hab : EvRel SIff w env a b)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some vb)
    (hnil : va = SExpr.nil) : vb = SExpr.nil := by
  obtain ⟨n1, hab⟩ := hab; obtain ⟨n2, ha⟩ := ha; obtain ⟨n3, hb⟩ := hb
  obtain ⟨u, v, hau, hbv, huv⟩ := hab (n1 + n2 + n3) (by omega)
  have hu : u = va := Option.some.inj (hau.symm.trans (ha (n1 + n2 + n3) (by omega)))
  have hv : v = vb := Option.some.inj (hbv.symm.trans (hb (n1 + n2 + n3) (by omega)))
  rw [hu, hv] at huv
  exact huv.mp hnil

/-- The reverse transport: a truthy chain-END value makes the START truthy
    (the SIff contrapositive; the conjunction composer's close). -/
theorem siff_val_ne_nil_transport {w : World} {env : Env} {a b va vb : SExpr}
    (hab : EvRel SIff w env a b)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some vb)
    (hvb : vb ≠ SExpr.nil) : va ≠ SExpr.nil := by
  obtain ⟨n1, hab⟩ := hab; obtain ⟨n2, ha⟩ := ha; obtain ⟨n3, hb⟩ := hb
  obtain ⟨u, v, hau, hbv, huv⟩ := hab (n1 + n2 + n3) (by omega)
  have hu : u = va := Option.some.inj (hau.symm.trans (ha (n1 + n2 + n3) (by omega)))
  have hv : v = vb := Option.some.inj (hbv.symm.trans (hb (n1 + n2 + n3) (by omega)))
  rw [hu, hv] at huv
  exact fun hva => hvb (huv.mp hva)

/-- MODUS PONENS at the value level: a truthy `Logic.implies` with a truthy
    antecedent has a truthy consequent (the rule:<thm> discharge's
    hypothesis-consumption step). -/
theorem implies_value_mp {vA vB : SExpr}
    (h : Logic.implies vA vB ≠ SExpr.nil) (hvA : vA ≠ SExpr.nil) :
    vB ≠ SExpr.nil := by
  rw [logic_implies_cond] at h
  rw [toBool_true_of_ne_nil hvA] at h
  intro hB
  rw [hB] at h
  simp [Logic.toBool] at h

/-- An `and`-antecedent's value (`(if A B 'nil)` lifted) is truthy when both
    parts are (the two-hypothesis rule antecedent). -/
theorem and_value_ne_nil {vA vB : SExpr}
    (hvA : vA ≠ SExpr.nil) (hvB : vB ≠ SExpr.nil) :
    cond (Logic.toBool vA) vB SExpr.nil ≠ SExpr.nil := by
  rw [toBool_true_of_ne_nil hvA]
  exact hvB

/-- `Logic.implies` is boolean-valued (the chain-start head fact). -/
theorem logic_implies_boolean (p q : SExpr) :
    Logic.implies p q = SExpr.t ∨ Logic.implies p q = SExpr.nil := by
  rw [logic_implies_cond]
  cases Logic.toBool p <;> cases Logic.toBool q <;> simp

/-- The rewrite-equal boolean CASE-RESTRUCTURING identity (fork-batch
    item 1's consumer): `(EQUAL p q)` with `q` TWO-VALUED equals
    `(IF q (EQUAL p 'T) (IF p 'NIL 'T))` at the value level. -/
theorem logic_equal_case_split (vp vq : SExpr)
    (hq : vq = SExpr.t ∨ vq = SExpr.nil) :
    Logic.equal vp vq
      = cond (Logic.toBool vq) (Logic.equal vp SExpr.t)
          (cond (Logic.toBool vp) SExpr.nil SExpr.t) := by
  rcases hq with h | h <;> subst h
  · simp [Logic.toBool]
  · by_cases hp : vp = SExpr.nil
    · subst hp; simp [Logic.equal, Logic.toBool]
    · have h1 : (vp == SExpr.nil) = false := by simp [hp]
      simp [Logic.equal, Logic.toBool, h1]

/-- A truthy `Logic.booleanp` pins its argument two-valued (the
    equivalence-rune own-position congruence's boolean pin — the defequiv
    booleanp conjunct applied at each R-application). -/
theorem booleanp_truthy_cases {v : SExpr}
    (h : Logic.booleanp v ≠ SExpr.nil) : v = SExpr.t ∨ v = SExpr.nil := by
  by_cases ht : v == SExpr.t <;> by_cases hn : v == SExpr.nil <;>
    simp_all [Logic.booleanp]

/-- Two boolean values with mutually-implied truthiness are EQUAL — the
    equivalence-rune own-position congruence's closing step: the R
    applications at the original and R-rewritten argument are both boolean
    (defequiv conjunct 1) and each truthy iff the other (sym + trans), so
    their VALUES coincide. -/
theorem boolean_biimpl_eq {va vb : SExpr}
    (ha : va = SExpr.t ∨ va = SExpr.nil) (hb : vb = SExpr.t ∨ vb = SExpr.nil)
    (hfwd : va ≠ SExpr.nil → vb ≠ SExpr.nil)
    (hbwd : vb ≠ SExpr.nil → va ≠ SExpr.nil) : va = vb := by
  have htn : SExpr.t ≠ SExpr.nil := by decide
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb
  · rfl
  · exact absurd rfl (hfwd htn)
  · exact absurd rfl (hbwd htn)
  · rfl

/-! ## The truthiness judgment `EvTrue` (G2)

ACL2's notion of clause/theorem truth is *the term is non-nil*; the exact-t
form is strictly stronger (they coincide only on boolean-valued terms, and
the exact-t mirror is false-as-stated for non-boolean formulas). G2 states
the CLAUSE and MIRROR judgments as `EvTrue`; exact-t facts survive at the
VALUE level and inject at the clause boundary (`evtrue_of_eq_t`). The
quantifier shape matches `EvRel` (∃N∀f∃v), so the G1 iff layer transports
`EvTrue` directly (`evtrue_of_evrel_siff`) with no boolean-valuedness side
condition. Design + decision log:
`docs/plans/2026-06-11_g2-evtrue-migration.md`. -/

/-- ACL2's clause/theorem truth: the term eventually converges to a NON-NIL
    value. -/
def EvTrue (w : World) (env : Env) (t : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, ∃ v, evalOpt f w env t = some v ∧ v ≠ SExpr.nil

/-- `(consp (cons a b)) = t` — the syntactic-cons disjunct evidence. -/
theorem logic_consp_cons_t (a b : SExpr) :
    Logic.consp (SExpr.cons a b) = SExpr.t := rfl

/-- Type-set DISJOINTNESS decode (G1 rung 1, inc-2): a cons can never
    `equal` a non-cons — the value fact behind ACL2's
    `(:TYPE-SET-EQUALITY NIL)` verdict `(equal x 'c) ⇒ 'nil` when the
    clause context types `x` as a cons and `'c` is an atom. -/
theorem logic_equal_nil_of_consp_t_nil {v c : SExpr}
    (hv : Logic.consp v = SExpr.t) (hc : Logic.consp c = SExpr.nil) :
    Logic.equal v c = SExpr.nil := by
  cases v with
  | cons x y =>
    cases c with
    | cons a b => simp [Logic.consp, SExpr.t] at hc
    | nil => simp [Logic.equal]
    | atom a => simp [Logic.equal]
  | nil => simp [Logic.consp, SExpr.t] at hv
  | atom a => simp [Logic.consp, SExpr.t] at hv

/-- The DISJUNCTIVE-CONS TP decode, 2 disjuncts (G1 arc 2026-07-29): a
    truthy args-valued TP fact `(if (consp v) 't (equal v y))` with `y`
    provably a cons forces `(consp v) = t` — either disjunct makes `v` a
    cons (the second by the `equal` decode). Consumes the emitted
    BINARY-APPEND-class corollary at a `recognizer/true` node; exactly
    ACL2's type-set leaf union under the cited TP rune. -/
theorem logic_consp_t_of_tp_disj2 {v y : SExpr}
    (h : (bif Logic.toBool (Logic.consp v) then SExpr.t
          else Logic.equal v y) = SExpr.t)
    (hy : Logic.consp y = SExpr.t) :
    Logic.consp v = SExpr.t := by
  by_cases hc : Logic.toBool (Logic.consp v) = true
  · cases v with
    | cons a b => exact logic_consp_cons_t a b
    | nil => simp [Logic.consp, Logic.toBool] at hc
    | atom a => simp [Logic.consp, Logic.toBool] at hc
  · rw [Bool.not_eq_true] at hc
    rw [hc, cond_false] at h
    have hveq : v = y := Logic.eq_of_equal_ne_nil (by rw [h]; simp [SExpr.t])
    rw [hveq]; exact hy

/-- The 3-disjunct sibling (the MERGE2 shape:
    `(if (consp v) 't (if (equal v x) 't (equal v y)))` — result is a cons,
    or one of two argument values, each provably a cons). -/
theorem logic_consp_t_of_tp_disj3 {v x y : SExpr}
    (h : (bif Logic.toBool (Logic.consp v) then SExpr.t
          else bif Logic.toBool (Logic.equal v x) then SExpr.t
               else Logic.equal v y) = SExpr.t)
    (hx : Logic.consp x = SExpr.t) (hy : Logic.consp y = SExpr.t) :
    Logic.consp v = SExpr.t := by
  by_cases hc : Logic.toBool (Logic.consp v) = true
  · cases v with
    | cons a b => exact logic_consp_cons_t a b
    | nil => simp [Logic.consp, Logic.toBool] at hc
    | atom a => simp [Logic.consp, Logic.toBool] at hc
  · rw [Bool.not_eq_true] at hc
    rw [hc, cond_false] at h
    by_cases he : Logic.toBool (Logic.equal v x) = true
    · have hne : Logic.equal v x ≠ SExpr.nil := fun hnil => by
        rw [hnil] at he; simp [Logic.toBool] at he
      rw [Logic.eq_of_equal_ne_nil hne]; exact hx
    · rw [Bool.not_eq_true] at he
      rw [he, cond_false] at h
      have hveq : v = y := Logic.eq_of_equal_ne_nil (by rw [h]; simp [SExpr.t])
      rw [hveq]; exact hy

/-- A truthy `(consp v)` walk fact makes `endp v` NIL — the CONSP/ENDP
    duality at the VALUE level (audit F1, sorting arc 2026-07-29: the
    recorded route's ruler peel consumes emitted `(ENDP …)` rulers against
    the translated body's `(CONSP …)` branch facts). -/
theorem logic_endp_nil_of_consp_toBool {v : SExpr}
    (h : Logic.toBool (Logic.consp v) = true) :
    Logic.endp v = SExpr.nil := by
  cases v <;> simp_all [Logic.endp, Logic.consp, Logic.toBool]

/-- Cast a convergence to nil along a value equation (the recorded-
    termination ruler peel: the walk's `toBool = false` fact decodes to the
    test's nil value). -/
theorem conv_nil_of_conv_eq {w : World} {env : Env} {t v : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env t = some v) (hv : v = SExpr.nil) :
    ∃ N, ∀ f ≥ N, evalOpt f w env t = some SExpr.nil := hv ▸ h

/-- Exact-t injection at the clause boundary: a value-pinned `= some t` fact
    IS truthiness. Every existing exact-t producer enters the `EvTrue` layer
    through this single lemma. -/
theorem evtrue_of_eq_t {w : World} {env : Env} {a : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = some SExpr.t) : EvTrue w env a := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, fun f hf => ⟨SExpr.t, h f hf, by simp [SExpr.t]⟩⟩

/-- Transport `EvTrue` BACKWARDS along an iff chain: `a` iff-rewrites to `b`
    and `b` is true, so `a` is true. Replaces the deleted G1-interim
    end-game (backward truth transport + the boolean-head strengthening) —
    truthiness is the statement now, so no strengthening is needed. -/
theorem evtrue_of_evrel_siff {w : World} {env : Env} {a b : SExpr}
    (hab : EvRel SIff w env a b) (hb : EvTrue w env b) : EvTrue w env a := by
  obtain ⟨n1, hab⟩ := hab; obtain ⟨n2, hb⟩ := hb
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨u, v, hau, hbv, huv⟩ := hab f (by omega)
  obtain ⟨v', hbv', hnv'⟩ := hb f (by omega)
  have : v = v' := Option.some.inj (hbv.symm.trans hbv')
  exact ⟨u, hau, fun hnu => hnv' (this ▸ Iff.mp huv hnu)⟩

/-- A pinned value under `EvTrue` is non-nil (the last-literal leaf fact:
    the clause fact + the literal's value characterization give `.truthy`
    uniformly — `.exactT` is gone, D9). -/
theorem ne_nil_of_evtrue_conv {w : World} {env : Env} {a va : SExpr}
    (ht : EvTrue w env a)
    (hconv : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va) : va ≠ SExpr.nil := by
  obtain ⟨n1, ht⟩ := ht; obtain ⟨n2, hconv⟩ := hconv
  obtain ⟨v, hav, hnv⟩ := ht (n1 + n2) (by omega)
  have : v = va := Option.some.inj (hav.symm.trans (hconv (n1 + n2) (by omega)))
  exact this ▸ hnv

/-- A TRUE term is iff-equivalent to `'t` (D10): the honest chain-step form
    of a verdict-only discharge node — `EvTrue lhs` composes in the SIff lane
    instead of being strengthened to an eval-equality with `'t` (which held
    only for boolean-valued clauses). -/
theorem evrel_siff_qt_of_evtrue {w : World} {env : Env} {a : SExpr}
    (ha : EvTrue w env a) :
    EvRel SIff w env a
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) := by
  obtain ⟨N, ha⟩ := ha
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨u, hau, hnu⟩ := ha (g + 1) (by omega)
  refine ⟨u, SExpr.t, hau, ?_, by simp [SIff, hnu, SExpr.t]⟩
  exact evalOpt_quote g w env SExpr.t

/-- `EvTrue '\''NIL` is absurd — the empty disjunction's ex-falso decode
    (the SINGLETON spine arm, G1 inc-2c). -/
theorem evtrue_quote_nil_false {w : World} {env : Env}
    (h : EvTrue w env (.cons (.atom (.symbol { name := "QUOTE" }))
      (.cons .nil .nil))) : False := by
  obtain ⟨N, h⟩ := h
  obtain ⟨v, hv, hnv⟩ := h (N + 1) (by omega)
  exact hnv (Option.some.inj (hv.symm.trans (evalOpt_quote N w env SExpr.nil)))

/-- Extract the REST of a disjunction from its `EvTrue` when the head literal
    is valued nil — the induction scaffold's per-case peel, fixed to the
    disjoin shape `(if c 't rest)`. -/
theorem evtrue_extract_else {w : World} {env : Env} {c rest : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some SExpr.nil)
    (hif : EvTrue w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons rest .nil))))) : EvTrue w env rest := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hif⟩ := hif
  refine ⟨n1 + n2 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨v, hifv, hnv⟩ := hif (g + 1) (by omega)
  rw [evalOpt_if_false g w env c _ rest (hc g (by omega))] at hifv
  exact ⟨v, evalOpt_fuel_mono g w env rest v hifv, hnv⟩

/-- The REVERSE of `evtrue_extract_else`: re-INTRODUCE a leading disjunct
    whose test converges to nil. The induction add-literal-dedup bridge
    (sorting arc 2026-07-28): a pushed literal deduped into an earlier
    ruling/IH occurrence is peeled WITH that occurrence, so the leaf's
    remaining disjunction is the deduped SUFFIX — this re-wraps it back to
    the FULL pushed instance using the very nil fact the peel used. -/
theorem evtrue_intro_else {w : World} {env : Env} {c rest : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some SExpr.nil)
    (hrest : EvTrue w env rest) :
    EvTrue w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons rest .nil)))) := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hrest⟩ := hrest
  refine ⟨n1 + n2 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨v, hv, hnv⟩ := hrest g (by omega)
  rw [evalOpt_if_false g w env c _ rest (hc g (by omega))]
  exact ⟨v, hv, hnv⟩

/-- A TRUE term's negation converges to nil (the step case's IH literal:
    `EvTrue ihInst` pins `(not ihInst) ⇒ nil` WITHOUT pinning the IH's own
    value — `Logic.not v = nil` for every non-nil `v`). -/
theorem conv_not_nil_of_evtrue {w : World} {env : Env} {X : SExpr}
    (h_noshadow : w.defs.get? { name := "NOT" } = none)
    (hX : EvTrue w env X) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "NOT" })) (.cons X .nil))
      = some SExpr.nil := by
  obtain ⟨N, hX⟩ := hX
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨v, hv, hnv⟩ := hX g (by omega)
  rw [evalOpt_builtin_1 g w env { name := "NOT" } X v
    (by simp [Symbol.isNamed]) h_noshadow hv]
  rw [callBuiltin_not, not_nil_of_truthy hnv]

/-- The DUAL of `conv_not_nil_of_evtrue`: a nil argument makes `(not X)`
    converge to `t` (the multi-clause bridge's neg-leaf converter). -/
theorem conv_not_t_of_conv_nil {w : World} {env : Env} {X : SExpr}
    (h_noshadow : w.defs.get? { name := "NOT" } = none)
    (hX : ∃ N, ∀ f ≥ N, evalOpt f w env X = some SExpr.nil) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "NOT" })) (.cons X .nil))
      = some SExpr.t := by
  obtain ⟨N, hX⟩ := hX
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_builtin_1 g w env { name := "NOT" } X SExpr.nil
    (by simp [Symbol.isNamed]) h_noshadow (hX g (by omega))]
  rw [callBuiltin_not]
  rfl

/-- Transport `EvTrue` backwards along an EVAL-EQUALITY chain (the
    equal-steps composition entering the truthiness judgment). The two sides
    may sit at DIFFERENT envs — the IH bridge's `evalOpt_substTerm_subst1`
    relates the goal env to the IH-instantiation env. -/
theorem evtrue_of_fuel_eq {w : World} {env env' : Env} {a b : SExpr}
    (hab : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env' b)
    (hb : EvTrue w env' b) : EvTrue w env a := by
  obtain ⟨n1, hab⟩ := hab; obtain ⟨n2, hb⟩ := hb
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨v, hbv, hnv⟩ := hb f (by omega)
  exact ⟨v, (hab f (by omega)).trans hbv, hnv⟩

/-- Drop a FALSIFIED leading disjunct: `EvTrue (IF c 'T r)` with the test
    converging to nil is `EvTrue r` (the generalize type-restriction
    head-drop — msort arc, 2026-07-19). -/
theorem evtrue_tail_of_if_head_nil {w : World} {env : Env} {c t r : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some SExpr.nil)
    (h : EvTrue w env (.cons (.atom (.symbol { name := "IF" }))
          (.cons c (.cons t (.cons r .nil))))) : EvTrue w env r := by
  obtain ⟨Nc, hc⟩ := hc
  obtain ⟨Nh, hh⟩ := h
  refine ⟨Nc + Nh, fun f hf => ?_⟩
  obtain ⟨v, hv, hnv⟩ := hh (f + 1) (by omega)
  rw [evalOpt_if_false f w env c t r (hc f (by omega))] at hv
  exact ⟨v, hv, hnv⟩

/-- `not` of an exact-t value is nil (restriction-literal falsification). -/
theorem not_of_eq_t {x : SExpr} (h : x = SExpr.t) :
    Logic.not x = SExpr.nil := by subst h; rfl

/-- The converse: a pinned non-nil value IS `EvTrue` (the positive-literal
    fallback of the clausify walk — truthiness anywhere in the spine, D9). -/
theorem evtrue_of_conv_ne_nil {w : World} {env : Env} {a va : SExpr}
    (hconv : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va)
    (hne : va ≠ SExpr.nil) : EvTrue w env a := by
  obtain ⟨N, hconv⟩ := hconv
  exact ⟨N, fun f hf => ⟨va, hconv f hf, hne⟩⟩

/-- The LINEAR-rule premise fact (2b): from the `linear:` hypothesis
    instance (`EvTrue h → EvTrue (EQUAL l r)`) and the three terms'
    pinned values, the DP-obligation premise `(IF h (EQUAL l r) 'T)`'s
    value is `t` — cond-shaped exactly like a TP corollary, so the
    INT-VIEW lift consumes it unchanged. `hnd`: EQUAL is undefined in
    the world (no-shadow; `by decide` at the concrete world). -/
theorem linear_premise_fact {w : World} {env : Env} {h l r vh vl vr : SExpr}
    (hnd : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hyp : EvTrue w env h → EvTrue w env
      (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons l (.cons r .nil))))
    (ph : ∃ N, ∀ f ≥ N, evalOpt f w env h = some vh)
    (pl : ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl)
    (pr : ∃ N, ∀ f ≥ N, evalOpt f w env r = some vr) :
    cond (Logic.toBool vh) (Logic.equal vl vr) SExpr.t = SExpr.t := by
  cases hb : Logic.toBool vh with
  | false => rfl
  | true =>
    have hne : vh ≠ SExpr.nil := fun hnil => by
      rw [hnil] at hb; exact absurd hb (by decide)
    have hc := hyp (evtrue_of_conv_ne_nil ph hne)
    have hpe := conv_builtin2 w env { name := "EQUAL" } l r vl vr
      (Logic.equal vl vr) (by decide) hnd pl pr (callBuiltin_equal vl vr)
    have hne2 := ne_nil_of_evtrue_conv hc hpe
    show Logic.equal vl vr = SExpr.t
    rcases logic_equal_t_or_nil vl vr with ht | hn
    · exact ht
    · exact absurd hn hne2

/-- The RULE-content premise fact (2c): from a boolean-strengthened
    stored-rule hypothesis instance (`EvTrue h → eval l ≐ eval 'T`) and
    the two terms' pinned values, the DP-obligation premise
    `(IF h (EQUAL l 'T) 'T)`'s value is `t` — the `linear_premise_fact`
    twin for `rule:` content (lhs ⇒ 'T shapes: TRUE-LISTP-RM /
    ORDEREDP-RM). -/
theorem rule_premise_fact {w : World} {env : Env} {h l vh vl : SExpr}
    (hyp : EvTrue w env h → ∃ N, ∀ f ≥ N,
      evalOpt f w env l = evalOpt f w env
        (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons SExpr.t .nil)))
    (ph : ∃ N, ∀ f ≥ N, evalOpt f w env h = some vh)
    (pl : ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl) :
    cond (Logic.toBool vh) (Logic.equal vl SExpr.t) SExpr.t = SExpr.t := by
  cases hb : Logic.toBool vh with
  | false => rfl
  | true =>
    have hne : vh ≠ SExpr.nil := fun hnil => by
      rw [hnil] at hb; exact absurd hb (by decide)
    obtain ⟨N1, hEq⟩ := hyp (evtrue_of_conv_ne_nil ph hne)
    obtain ⟨N2, hpl⟩ := pl
    obtain ⟨N3, hqt⟩ := re_val_quote w env SExpr.t
    have hvl : vl = SExpr.t := by
      have h1 := hpl (N1 + N2 + N3) (by omega)
      have h2 := hEq (N1 + N2 + N3) (by omega)
      have h3 := hqt (N1 + N2 + N3) (by omega)
      exact Option.some.inj ((h1.symm.trans h2).trans h3)
    rw [hvl]
    rfl

/-- The EQUIVREFL premise fact (2c): a stored :EQUIVALENCE rule's reflexivity
    instance `(R u u)` is TRUE, so the double-negation premise
    `(NOT (NOT (R u u)))` lifts to `t` at the pinned value. Double-negation
    (not truthiness-as-`= t`) because `EvTrue` alone gives only `≠ nil` —
    the obligation's TP booleanp cell then forces `= T` inside the fact,
    exactly ACL2's tau composition (refl content + recognizer booleanness). -/
theorem equivrefl_premise_fact {w : World} {env : Env} {a va : SExpr}
    (ht : EvTrue w env a)
    (pa : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va) :
    Logic.not (Logic.not va) = SExpr.t := by
  have hne := ne_nil_of_evtrue_conv ht pa
  cases va with
  | nil => exact absurd rfl hne
  | atom a => rfl
  | cons a b => rfl

/-- The `EvTrue` spine combinator (D9): VALUE-characterized convergence of the
    test and truth of the branch selected by EITHER case of `cv` (both
    implications supplied; the proof case-splits on `cv = nil`). One lemma
    serves `replayClauseSpine`, the clausify-bridge positive walk, and the
    discharge spine; an exact-t branch enters via `evtrue_of_eq_t`. -/
theorem evtrue_dp_if_split (w : World) (env : Env) (c t e cv : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (hthen : cv ≠ .nil → EvTrue w env t)
    (helse : cv = .nil → EvTrue w env e) :
    EvTrue w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))) := by
  obtain ⟨Nc, hc⟩ := hc
  by_cases hcv : cv = .nil
  · obtain ⟨Ne, he⟩ := helse hcv
    refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨v, hev, hnv⟩ := he g (by omega)
    exact ⟨v, by
      rw [evalOpt_if_false g w env c t e (hcv ▸ hc g (by omega))]; exact hev, hnv⟩
  · obtain ⟨Nt, ht⟩ := hthen hcv
    refine ⟨max Nc Nt + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨v, htv, hnv⟩ := ht g (by omega)
    exact ⟨v, by
      rw [evalOpt_if_true g w env c t e cv (hc g (by omega))
        (toBool_true_of_ne_nil hcv)]; exact htv, hnv⟩

/-- Extract `integerp v = t` from a TRUE type-prescription corollary of the
    standard `(IF (INTEGERP v) … 'NIL)` shape (lifted: `cond (toBool (integerp v))
    X nil = t`): the recognizer is two-valued, and a false test would make the
    cond `nil ≠ t`. -/
theorem tp_cond_integerp_t (v X : SExpr)
    (h : cond (Logic.toBool (Logic.integerp v)) X SExpr.nil = SExpr.t) :
    Logic.integerp v = SExpr.t := by
  match v with
  | .atom (.number (.int _)) => rfl
  | .atom (.number (.rational _ _ _)) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.symbol _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.keyword _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.char _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.string _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .nil => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .cons _ _ => simp [Logic.integerp, Logic.toBool, SExpr.t] at h

/-- A variable's value at an `insert`-updated env (the IH instantiation env). -/
theorem re_val_var_insert (w : World) (env : Env) (s : Symbol) (v : SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (env.insert s v) (.atom (.symbol s)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w _ s v (by simp)⟩

/-- Two value characterizations across an eval-equality pin the SAME value (the
    spine's bridge from a literal's pre-rewrite falsity to its post-rewrite form). -/
theorem val_eq_of_eval_eq {a b : Nat → Option SExpr} {u v : SExpr}
    (hab : ∃ N, ∀ f ≥ N, a f = b f)
    (ha : ∃ N, ∀ f ≥ N, a f = some u) (hb : ∃ N, ∀ f ≥ N, b f = some v) : u = v := by
  obtain ⟨n1, h1⟩ := hab; obtain ⟨n2, h2⟩ := ha; obtain ⟨n3, h3⟩ := hb
  have := ((h2 (n1+n2+n3) (by omega)).symm.trans (h1 (n1+n2+n3) (by omega))).trans
    (h3 (n1+n2+n3) (by omega))
  exact Option.some.inj this

/-- Weaken a value-characterized convergence to the v-existential form
    (`proveConv`'s shape, consumed by `re_equal_self` etc.). -/
theorem conv_vfix_of_val {w : World} {env : Env} {a v : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = some v) :
    ∃ N, ∃ v', ∀ f ≥ N, evalOpt f w env a = some v' := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, v, h⟩

/-- Extract the integer witness from a true `integerp` value fact (the TP bridge:
    the lifted type-prescription gives `Logic.integerp v = t`; recognizers like
    `acl2-numberp` need the int shape). -/
theorem logic_integerp_int (v : SExpr) (h : Logic.integerp v = SExpr.t) :
    ∃ k : Int, v = .atom (.number (.int k)) := by
  match v with
  | .atom (.number (.int k)) => exact ⟨k, rfl⟩
  | .atom (.number (.rational _ _ _)) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.symbol _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.keyword _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.char _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.string _) => simp [Logic.integerp, SExpr.t] at h
  | .nil => simp [Logic.integerp, SExpr.t] at h
  | .cons _ _ => simp [Logic.integerp, SExpr.t] at h

/-- The rewrite-if EQUAL-NIL test normalization (sorting-completion-2
    Class A, ORDEREDP-MEMB): `(IF (EQUAL 'NIL c) a b) ≡ (IF c b a)` —
    ACL2 strips an equal-nil test and SWAPS the branches, unrecorded.
    Needs EQUAL unshadowed. -/
theorem re_if_equal_nil_test_swap (w : World) (env : Env) (c a b : SExpr)
    (hNoEq : w.defs.get? ({ name := "EQUAL" } : Symbol) = none) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons .nil .nil))
                (.cons c .nil)))
            (.cons a (.cons b .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons c (.cons b (.cons a .nil)))) := by
  by_cases hconv : ∃ vc N, evalOpt N w env c = some vc
  · obtain ⟨vc, N, hN⟩ := hconv
    refine ⟨N + 3, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    obtain ⟨g'', rfl⟩ : ∃ g'', g' = g'' + 1 := ⟨g' - 1, by omega⟩
    have hc1 : evalOpt (g'' + 1) w env c = some vc :=
      evalOpt_ge_fuel N _ w env c vc hN (by omega)
    have hc2 : evalOpt (g'' + 2) w env c = some vc :=
      evalOpt_ge_fuel N _ w env c vc hN (by omega)
    have hq : evalOpt (g'' + 1) w env
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
        = some SExpr.nil := evalOpt_quote g'' w env .nil
    have hinner : evalOpt (g'' + 2) w env
        (.cons (.atom (.symbol { name := "EQUAL" }))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
            (.cons .nil .nil))
            (.cons c .nil))) = some (Logic.equal SExpr.nil vc) := by
      rw [evalOpt_builtin_2 (g'' + 1) w env { name := "EQUAL" } _ c
        SExpr.nil vc (by decide) hNoEq hq hc1]
      rfl
    by_cases hb : vc = SExpr.nil
    · subst hb
      have ht : Logic.equal SExpr.nil SExpr.nil = SExpr.t := by
        simp [Logic.equal]
      rw [ht] at hinner
      rw [evalOpt_if_true (g'' + 2) w env _ a b SExpr.t hinner
            (by simp [Logic.toBool]),
          evalOpt_if_false (g'' + 2) w env c b a hc2]
    · have hnil : Logic.equal SExpr.nil vc = SExpr.nil := by
        simp only [Logic.equal, beq_iff_eq]
        rw [if_neg (fun h => hb h.symm)]
      rw [hnil] at hinner
      rw [evalOpt_if_false (g'' + 2) w env _ a b hinner,
          evalOpt_if_true (g'' + 2) w env c b a vc hc2
            (by cases vc <;> simp_all [Logic.toBool])]
  · have hnone : ∀ M, evalOpt M w env c = none := by
      intro M
      rcases h : evalOpt M w env c with _ | vc
      · rfl
      · exact absurd ⟨vc, M, h⟩ hconv
    refine ⟨2, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hinner : ∀ M, evalOpt M w env
        (.cons (.atom (.symbol { name := "EQUAL" }))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
            (.cons .nil .nil))
            (.cons c .nil))) = none := by
      intro M
      cases M with
      | zero => rfl
      | succ M' =>
        show evalOptStep (evalOpt M') w env _ = none
        unfold evalOptStep
        simp only [Symbol.isNamed, SExpr.toList?]
        cases hM : evalOpt M' w env
            (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)) with
        | none => simp [hM, hnone M']
        | some v => simp [hM, hnone M']
    show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
    unfold evalOptStep
    simp only [Symbol.isNamed, SExpr.toList?]
    simp [hinner g, hnone g]

/-- `rewrite-if`'s SWAPPED-P normalization (rewrite.lisp:17726-37):
    when the rewritten if-TEST has the negation shape `(IF c 'NIL 'T)`, ACL2
    strips it and SWAPS the branches before descending — unconditionally, and
    never recorded as a step (subsequent branch bkptrs simply refer to the
    swapped orientation). The chain walker applies this bridge
    deterministically when a path frame descends into such an if. -/
theorem re_if_neg_test_swap (w : World) (env : Env) (c a b : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons c
                (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                    (.cons SExpr.t .nil)) .nil))))
            (.cons a (.cons b .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons b (.cons a .nil)))) := by
  by_cases hconv : ∃ vc N, evalOpt N w env c = some vc
  · obtain ⟨vc, N, hN⟩ := hconv
    refine ⟨N + 3, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    obtain ⟨g'', rfl⟩ : ∃ g'', g' = g'' + 1 := ⟨g' - 1, by omega⟩
    have hc1 : evalOpt (g'' + 1) w env c = some vc :=
      evalOpt_ge_fuel N _ w env c vc hN (by omega)
    have hc2 : evalOpt (g'' + 2) w env c = some vc :=
      evalOpt_ge_fuel N _ w env c vc hN (by omega)
    by_cases hb : Logic.toBool vc = true
    · -- inner test truthy ⇒ inner if = 'NIL ⇒ outer takes b; RHS test truthy ⇒ b
      have hinner : evalOpt (g'' + 2) w env
          (.cons (.atom (.symbol { name := "IF" }))
            (.cons c
              (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                  (.cons SExpr.t .nil)) .nil)))) = some SExpr.nil := by

        rw [evalOpt_if_true (g'' + 1) w env c _ _ vc hc1 hb]
        exact evalOpt_quote g'' w env .nil
      rw [evalOpt_if_false (g'' + 2) w env _ a b hinner,
          evalOpt_if_true (g'' + 2) w env c b a vc hc2 hb]
    · have hvnil : vc = SExpr.nil := by
        cases vc <;> simp_all [Logic.toBool]
      subst hvnil
      -- inner test nil ⇒ inner if = 'T ⇒ outer takes a; RHS test nil ⇒ a
      have hinner : evalOpt (g'' + 2) w env
          (.cons (.atom (.symbol { name := "IF" }))
            (.cons c
              (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                  (.cons SExpr.t .nil)) .nil)))) = some SExpr.t := by
        rw [evalOpt_if_false (g'' + 1) w env c _ _ hc1]
        exact evalOpt_quote g'' w env SExpr.t
      rw [evalOpt_if_true (g'' + 2) w env _ a b SExpr.t hinner (by simp [Logic.toBool]),
          evalOpt_if_false (g'' + 2) w env c b a hc2]
  · -- `c` diverges at every fuel: both sides are `none`
    have hnone : ∀ M, evalOpt M w env c = none := by
      intro M
      rcases h : evalOpt M w env c with _ | vc
      · rfl
      · exact absurd ⟨vc, M, h⟩ hconv
    refine ⟨2, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hinner : evalOpt (g' + 1) w env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons c
            (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil)) .nil)))) = none := by
      show evalOptStep (evalOpt g') w env _ = none
      unfold evalOptStep
      simp only [Symbol.isNamed, SExpr.toList?]
      show (evalOpt g' w env c).bind _ = none
      rw [hnone g']; rfl
    show evalOptStep (evalOpt (g' + 1)) w env _ = evalOptStep (evalOpt (g' + 1)) w env _
    unfold evalOptStep
    simp only [Symbol.isNamed, SExpr.toList?]
    show (evalOpt (g' + 1) w env _).bind _ = (evalOpt (g' + 1) w env c).bind _
    rw [hinner, hnone (g' + 1)]; rfl

/-- Arg-order symmetry of an EQUAL application: `Logic.equal` is symmetric and
    argument evaluation is jointly strict, so the whole application is
    orientation-independent. Bridges ACL2's `one-way-unify1` EQUAL special
    case — a rule whose lhs is `(EQUAL p q)` may match a target equality
    COMMUTED (the CAR-APPEND class). -/
theorem re_equal_comm (w : World) (env : Env) (a b : SExpr)
    (hno : w.defs.get? { name := "EQUAL" } = none) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "EQUAL" })) (.cons b (.cons a .nil))) := by
  by_cases ha : ∃ va N, evalOpt N w env a = some va
  · by_cases hb : ∃ vb N, evalOpt N w env b = some vb
    · obtain ⟨va, Na, hva⟩ := ha
      obtain ⟨vb, Nb, hvb⟩ := hb
      refine ⟨max Na Nb + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have ha' : evalOpt g w env a = some va :=
        evalOpt_ge_fuel Na g w env a va hva (by omega)
      have hb' : evalOpt g w env b = some vb :=
        evalOpt_ge_fuel Nb g w env b vb hvb (by omega)
      rw [evalOpt_builtin_2 g w env _ a b va vb (by decide) hno ha' hb',
          evalOpt_builtin_2 g w env _ b a vb va (by decide) hno hb' ha',
          callBuiltin_equal, callBuiltin_equal, logic_equal_comm va vb]
    · -- b diverges: both sides are none (joint strictness)
      have hnone : ∀ M, evalOpt M w env b = none := by
        intro M
        rcases h : evalOpt M w env b with _ | vb
        · rfl
        · exact absurd ⟨vb, M, h⟩ hb
      refine ⟨1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
      unfold evalOptStep
      simp only [Symbol.isNamed, SExpr.toList?]
      simp [List.mapM, List.mapM.loop, hnone g]
  · -- a diverges: both sides are none (joint strictness)
    have hnone : ∀ M, evalOpt M w env a = none := by
      intro M
      rcases h : evalOpt M w env a with _ | va
      · rfl
      · exact absurd ⟨va, M, h⟩ ha
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
    unfold evalOptStep
    simp only [Symbol.isNamed, SExpr.toList?]
    simp [List.mapM, List.mapM.loop, hnone g]

/-- Nat-valued twin of `Logic.len` — the DP leaf tactic's bridge from stuck
    `Logic.len` applications to omega-visible nonnegative integers (the
    `SExpr.consCount` pattern from the decrease prover). -/
def lenNat : SExpr → Nat
  | .cons _ b => lenNat b + 1
  | _ => 0

/-- `Logic.len` computes `lenNat` as an int atom. NOT `@[simp]` — consumed
    only by the DP leaf tactic's explicit simp set, so the driver's structural
    `Logic.len` values (the builtin TP pin route, `gz_def_len` unfolds) are
    untouched elsewhere. -/
theorem logic_len_eq_lenNat (x : SExpr) :
    Logic.len x = .atom (.number (.int (lenNat x))) := by
  induction x with
  | cons a b _ ihb =>
    have h : Logic.len (SExpr.cons a b)
        = .atom (.number (.int (Logic.toInt (Logic.len b) + 1))) := rfl
    rw [h, ihb]
    simp only [lenNat, Logic.toInt]
    congr 3
  | nil => simp [Logic.len, lenNat]
  | atom a => simp [Logic.len, lenNat]

/-! LEN decrease walk (P3, bsort — BNEXT's `:MEASURE (LEN X)`): the
    `lenNat` mirrors of the Count library's decrease lemmas, consumed by
    `chainLtLen` in `Totality.lean`. -/

/-- cdr strictly decreases `lenNat` under consp evidence. -/
theorem lenNat_cdr_lt_of_consp {x : SExpr}
    (h : Logic.toBool (Logic.consp x) = true) :
    lenNat (Logic.cdr x) < lenNat x := by
  cases x with
  | nil => simp [Logic.consp, Logic.toBool] at h
  | atom a => simp [Logic.consp, Logic.toBool] at h
  | cons a b => simp [Logic.cdr, lenNat]

/-- cdr never increases `lenNat` (cdr of a non-cons is nil, length 0). -/
theorem lenNat_cdr_le (x : SExpr) : lenNat (Logic.cdr x) ≤ lenNat x := by
  cases x <;> simp [Logic.cdr, lenNat]

/-- Re-consing ANY car onto a cdr PRESERVES `lenNat` — the length-measure
    fact `consCount` cannot have (car contents are invisible to length),
    and exactly BNEXT's swap call site `(CONS (CAR X) (CDR (CDR X)))`. -/
theorem lenNat_cons_cdr_eq_of_consp (a : SExpr) {w : SExpr}
    (h : Logic.toBool (Logic.consp w) = true) :
    lenNat (Logic.cons a (Logic.cdr w)) = lenNat w := by
  cases w with
  | nil => simp [Logic.consp, Logic.toBool] at h
  | atom x => simp [Logic.consp, Logic.toBool] at h
  | cons c d => simp [Logic.cons, Logic.cdr, lenNat]

/-- `Logic.len` never returns a cons (the recognizer/false class in
    admission trees of LEN-based measures — BNEXT's `:MEASURE (LEN X)`;
    the same emitted-corollary gate as the integerp twin below applies at
    the consumer). -/
theorem logic_consp_len_nil (x : SExpr) :
    Logic.consp (Logic.len x) = SExpr.nil := by
  rw [logic_len_eq_lenNat]; rfl

/-- `Logic.len` is a natural (the NATP-COMPOUND-RECOGNIZER class in the
    same admission trees: a length is a nonnegative integer). -/
theorem logic_natp_len_t (x : SExpr) :
    Logic.natp (Logic.len x) = SExpr.t := by
  rw [logic_len_eq_lenNat]
  simp [Logic.natp]

/-- CONSP-nil from a fn's lifted nonneg-int TP-corollary fact (the
    recognizer/false world-fn route, audit 2026-08-07 S3): the corollary
    known `= t` pins the value to an integer, and no integer is a cons. -/
theorem logic_consp_nil_of_int_tp_fact {v : SExpr}
    (hfact : cond (Logic.toBool (Logic.integerp v))
        (Logic.not (Logic.lt v (SExpr.atom (.number (.int 0)))))
        SExpr.nil
      = SExpr.t) :
    Logic.consp v = SExpr.nil := by
  match v with
  | .atom (.number (.int _)) => simp [Logic.consp]
  | .atom (.number (.rational _ _ _)) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.symbol _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.keyword _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.char _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.string _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .nil => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .cons _ _ => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact

/-- NATP from a WORLD fn's lifted nonneg-int TP-corollary fact (the
    compound-recognizer world-fn route — BNEXT-SIZE): the corollary
    `(IF (INTEGERP app) (NOT (< app '0)) 'NIL)` lifted at the value and
    known `= t` pins the value to a nonnegative integer. -/
theorem logic_natp_t_of_int_tp_fact {v : SExpr}
    (hfact : cond (Logic.toBool (Logic.integerp v))
        (Logic.not (Logic.lt v (SExpr.atom (.number (.int 0)))))
        SExpr.nil
      = SExpr.t) :
    Logic.natp v = SExpr.t := by
  match v with
  | .atom (.number (.int k)) =>
    have hk : ¬ k < 0 := fun hk => by
      simp [Logic.toBool, Logic.not, Logic.lt, Logic.toRat, hk, SExpr.t] at hfact
    have hk' : k ≥ 0 := by omega
    simp [Logic.natp, hk']
  | .atom (.number (.rational _ _ _)) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.symbol _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.keyword _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.char _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .atom (.string _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .nil => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  | .cons _ _ => simp [Logic.integerp, Logic.toBool, SExpr.t] at hfact
  -- (Resurrected 2026-08-07: killed in the drift round as
  -- consumer-less; the R2 emitted-data gate is now its consumer —
  -- the item-9 world-fn route unparks.)

/-- `Logic.len` is always an ACL2 integer — the kernel-checked counterpart of
    LEN's ground-zero `:TYPE-PRESCRIPTION` corollary
    `(IF (INTEGERP (LEN X)) (NOT (< (LEN X) '0)) 'NIL)`. The builtin TP pin
    route (`pinTermOpaques`) applies it ONLY after matching that emitted
    corollary shape, so the type fact is still consumed from ACL2's emission,
    with the proof supplied by the trusted core (LEN is a builtin —
    `Logic.len` IS its semantics here). -/
theorem logic_len_integerp (x : SExpr) : Logic.integerp (Logic.len x) = SExpr.t := by
  cases x with
  | cons a b => simp [Logic.len]
  | nil => simp [Logic.len]
  | atom a => simp [Logic.len]

/-- Value-characterized convergence of an `if` INSIDE a literal: the value is
    `cond (toBool cv) tv ev` (both branches must converge — their values are
    needed whichever way the test goes, since the DP fact reasons over all
    variable values). -/
theorem re_val_if (w : World) (env : Env) (c t e cv tv ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w env t = some tv)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w env e = some ev) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = some (cond (Logic.toBool cv) tv ev) := by
  obtain ⟨Nc, hc⟩ := hc; obtain ⟨Nt, ht⟩ := ht; obtain ⟨Ne, he⟩ := he
  refine ⟨max Nc (max Nt Ne) + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  by_cases hcv : Logic.toBool cv = true
  · rw [evalOpt_if_true g w env c t e cv (hc g (by omega)) hcv, ht g (by omega), hcv]
    rfl
  · have hnil : cv = .nil := by cases cv <;> simp_all [Logic.toBool]
    have htb : Logic.toBool cv = false := by simp [hnil, Logic.toBool]
    rw [evalOpt_if_false g w env c t e (hnil ▸ hc g (by omega)), he g (by omega), htb]
    rfl

/-- `if` convergence: all three parts converging makes the `if` converge (to the
    branch the test selects — existential, the analyzer doesn't need which). -/
theorem re_conv_if (w : World) (env : Env) (c t e : SExpr)
    (hc : ∃ N, ∃ cv, ∀ f ≥ N, evalOpt f w env c = some cv)
    (ht : ∃ N, ∃ tv, ∀ f ≥ N, evalOpt f w env t = some tv)
    (he : ∃ N, ∃ ev, ∀ f ≥ N, evalOpt f w env e = some ev) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = some v := by
  obtain ⟨Nc, cv, hc⟩ := hc
  obtain ⟨Nt, tv, ht⟩ := ht
  obtain ⟨Ne, ev, he⟩ := he
  obtain ⟨N, h⟩ := re_val_if w env c t e cv tv ev ⟨Nc, hc⟩ ⟨Nt, ht⟩ ⟨Ne, he⟩
  exact ⟨N, cond (Logic.toBool cv) tv ev, h⟩

/-- The value identity behind rewrite-equal's built-in NIL normalization:
    `(equal nil v)` and `(if v nil t)` compute the same value. -/
theorem logic_equal_nil_eq_ite (v : SExpr) :
    Logic.equal .nil v = (bif Logic.toBool v then .nil else .t) := by
  cases v with
  | nil => rfl
  | atom a => simp [Logic.equal, Logic.toBool]
  | cons a b => simp [Logic.equal, Logic.toBool]

/-- `(if x 'nil 't)` converges to `(bif toBool vx then nil else t)` given `x`
    converges to `vx` — the value-characterized form of ACL2's `(not x)`. -/
theorem re_val_if_nil_t (w : World) (env : Env) (x vx : SExpr)
    (hx : ∃ N, ∀ f ≥ N, evalOpt f w env x = some vx) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) .nil))))
      = some (bif Logic.toBool vx then .nil else .t) := by
  obtain ⟨N, hN⟩ := hx
  refine ⟨N + 2, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  by_cases hb : Logic.toBool vx = true
  · rw [evalOpt_if_true g w env _ _ _ vx (hN g (by omega)) hb, hb]
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact evalOpt_quote g' w env .nil
  · have hnil : vx = .nil := by
      cases vx with
      | nil => rfl
      | atom a => simp [Logic.toBool] at hb
      | cons a b => simp [Logic.toBool] at hb
    rw [evalOpt_if_false g w env _ _ _ (hnil ▸ hN g (by omega)),
        Bool.of_not_eq_true hb]
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact evalOpt_quote g' w env SExpr.t

/-- rewrite-equal's built-in NIL normalization, LEFT form (rewrite.lisp:18089,
    unconditional/syntactic): `(equal 'nil x) ≡ (if x 'nil 't)`, fuel-robust,
    given `x` converges and `equal` is unshadowed. -/
theorem re_equal_nil_norm_l (w : World) (env : Env) (x : SExpr)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hxe : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env x = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons x .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) .nil)))) := by
  obtain ⟨N, vx, hN⟩ := hxe
  have hx : ∃ M, ∀ f ≥ M, evalOpt f w env x = some vx := ⟨N, hN⟩
  have hl := conv_builtin2 w env { name := "EQUAL" }
    (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)) x
    .nil vx (Logic.equal .nil vx)
    (by simp [Symbol.isNamed]) h_no_equal (re_val_quote w env .nil) hx
    (callBuiltin_equal .nil vx)
  have hr := re_val_if_nil_t w env x vx hx
  exact fuel_eq_of_conv hl hr (logic_equal_nil_eq_ite vx)

/-- if-interp's call-stack fold `(equal (equal a b) 't) = (equal a b)`
    (rewrite.lisp:3791-3793) — sound because `Logic.equal` is two-valued. -/
theorem logic_equal_equal_t_r (a b : SExpr) :
    Logic.equal (Logic.equal a b) SExpr.t = Logic.equal a b := by
  by_cases h : (a == b) = true <;> simp [Logic.equal, h, SExpr.t]

/-- Mirrored: `(equal 't (equal a b)) = (equal a b)` (rewrite.lisp:3785-3789). -/
theorem logic_equal_equal_t_l (a b : SExpr) :
    Logic.equal SExpr.t (Logic.equal a b) = Logic.equal a b := by
  rw [logic_equal_comm]
  exact logic_equal_equal_t_r a b

/-- rewrite-equal's built-in EQUALITYP normalization (rewrite.lisp:18093,
    unconditional/syntactic): `(equal (equal a b) r) ≡
    (if (equal a b) (equal r 't) (if r 'nil 't))` — sound because
    `Logic.equal` is two-valued. Fuel-robust, given the parts converge. -/
theorem re_equal_equalityp_norm (w : World) (env : Env) (a b r : SExpr)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hae : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env a = some v)
    (hbe : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env b = some v)
    (hre : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env r = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons r .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil)) .nil)))
            (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
                  .nil)))) .nil)))) := by
  obtain ⟨Na, va, hNa⟩ := hae
  obtain ⟨Nb, vb, hNb⟩ := hbe
  obtain ⟨Nr, vr, hNr⟩ := hre
  have hns : Symbol.isNamed { name := "EQUAL" } "QUOTE" = false ∧
             Symbol.isNamed { name := "EQUAL" } "IF" = false ∧
             Symbol.isNamed { name := "EQUAL" } "LET" = false ∧
             Symbol.isNamed { name := "EQUAL" } "LET*" = false := by
    simp [Symbol.isNamed]
  have hin : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
      = some (Logic.equal va vb) :=
    conv_builtin2 w env { name := "EQUAL" } a b va vb (Logic.equal va vb)
      hns h_no_equal ⟨Na, hNa⟩ ⟨Nb, hNb⟩ (callBuiltin_equal va vb)
  have hl : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons r .nil)))
      = some (Logic.equal (Logic.equal va vb) vr) :=
    conv_builtin2 w env { name := "EQUAL" } _ r (Logic.equal va vb) vr _
      hns h_no_equal hin ⟨Nr, hNr⟩ (callBuiltin_equal (Logic.equal va vb) vr)
  by_cases hcase : (va == vb) = true
  · have heqt : Logic.equal va vb = SExpr.t := by simp [Logic.equal, hcase]
    have hthen : ∃ N, ∀ f ≥ N, evalOpt f w env
        (.cons (.atom (.symbol { name := "EQUAL" }))
          (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
            (.cons SExpr.t .nil)) .nil)))
        = some (Logic.equal vr SExpr.t) :=
      conv_builtin2 w env { name := "EQUAL" } r _ vr SExpr.t _
        hns h_no_equal ⟨Nr, hNr⟩ (re_val_quote w env SExpr.t)
        (callBuiltin_equal vr SExpr.t)
    have hr := conv_if_true w env
      (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
      (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons SExpr.t .nil)) .nil)))
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
            .nil))))
      SExpr.t (Logic.equal vr SExpr.t) (heqt ▸ hin) (by decide) hthen
    refine fuel_eq_of_conv hl hr ?_
    rw [heqt, logic_equal_comm]
  · have heqn : Logic.equal va vb = SExpr.nil := by simp [Logic.equal, hcase]
    have hr' := re_val_if_nil_t w env r vr ⟨Nr, hNr⟩
    have hr : ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil)) .nil)))
            (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
                  .nil)))) .nil))))
        = some (bif Logic.toBool vr then .nil else .t) := by
      obtain ⟨Nc, hc⟩ := heqn ▸ hin
      obtain ⟨Ne, he⟩ := hr'
      refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [evalOpt_if_false g w env _ _ _ (hc g (by omega))]
      exact he g (by omega)
    refine fuel_eq_of_conv hl hr ?_
    rw [heqn]
    exact logic_equal_nil_eq_ite vr

/-- rewrite-equal's built-in NIL normalization, RIGHT form (rewrite.lisp:18091):
    `(equal x 'nil) ≡ (if x 'nil 't)`. -/
theorem re_equal_nil_norm_r (w : World) (env : Env) (x : SExpr)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hxe : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env x = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)) .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) .nil)))) := by
  obtain ⟨N, vx, hN⟩ := hxe
  have hx : ∃ M, ∀ f ≥ M, evalOpt f w env x = some vx := ⟨N, hN⟩
  have hl := conv_builtin2 w env { name := "EQUAL" }
    x (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
    vx .nil (Logic.equal vx .nil)
    (by simp [Symbol.isNamed]) h_no_equal hx (re_val_quote w env .nil)
    (callBuiltin_equal vx .nil)
  have hr := re_val_if_nil_t w env x vx hx
  refine fuel_eq_of_conv hl hr ?_
  rw [← logic_equal_nil_eq_ite vx]
  exact logic_equal_comm vx .nil


/-! ## The recorded-termination (μ-generic) totality pack — sorting arc
    2026-07-28. Strong induction over an arbitrary Nat measure (design
    I1: the measure is Lean bookkeeping, appearing in no statement); the
    INTERPRETED count as that measure (definite description; the allowed
    Classical.choice); the transport/decode lemmas consuming the REPLAYED
    admission waterfall's O< facts against the byte-checked ground-zero
    shapes. -/

private def intAtom (n : Int) : SExpr := .atom (.number (.int n))

/-- Strong induction over an ARBITRARY Nat measure (μ is Lean bookkeeping —
    design I1; the recorded-termination route instantiates the interpreted
    ACL2-COUNT). -/
theorem measure_strong_induction_val (μ : SExpr → Nat) (P : SExpr → Prop)
    (step : ∀ x, (∀ y, μ y < μ x → P y) → P x) : ∀ x, P x := by
  intro x
  generalize h : μ x = n
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih => exact step x (fun y hy => ih (μ y) (h ▸ hy) y rfl)

theorem totality_1_rec_mu (μ : SExpr → Nat)
    (w : World) (s : Symbol) (formal : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (step : ∀ av : SExpr,
      (∀ bv : SExpr, μ bv < μ av →
        ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [bv]) body = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∀ (env' : Env) (a0 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env' (.cons (.atom (.symbol s)) (.cons a0 .nil)) = some v := by
  have hbody := measure_strong_induction_val μ
    (fun av => ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal] [av]) body = some v) step
  exact totality_1_of_body w s formal body h_ns h_def hbody

theorem totality_2_rec_mu (μ : SExpr → Nat)
    (w : World) (s : Symbol) (formal1 formal2 : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (step : ∀ av1 : SExpr,
      (∀ bv : SExpr, μ bv < μ av1 → ∀ cv : SExpr,
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal1, formal2] [bv, cv]) body = some v) →
      ∀ av2 : SExpr,
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env'
          (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil))) = some v := by
  have hbody := measure_strong_induction_val μ
    (fun av1 => ∀ av2, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) step
  exact totality_2_of_body w s formal1 formal2 body h_ns h_def
    (fun av1 av2 => hbody av1 av2)

theorem totality_2_rec_mu_snd (μ : SExpr → Nat)
    (w : World) (s : Symbol) (formal1 formal2 : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (step : ∀ av2 : SExpr,
      (∀ cv : SExpr, μ cv < μ av2 → ∀ bv : SExpr,
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal1, formal2] [bv, cv]) body = some v) →
      ∀ av1 : SExpr,
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env'
          (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil))) = some v := by
  have hbody := measure_strong_induction_val μ
    (fun av2 => ∀ av1, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) step
  exact totality_2_of_body w s formal1 formal2 body h_ns h_def
    (fun av1 av2 => hbody av2 av1)

/-- LEFT conjunct of an IF-encoded conjunction: `EvTrue (IF A B 'NIL)` needs
    `A` truthy (the nil-else would otherwise be the value). `A`'s own
    convergence is required to name the branch. -/
theorem evtrue_and_left {w : World} {env : Env} {A B va : SExpr}
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w env A = some va)
    (h : EvTrue w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons A (.cons B
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
            .nil))))) :
    va ≠ SExpr.nil := by
  intro hva
  obtain ⟨Na, ha⟩ := hA; obtain ⟨N, hN⟩ := h
  obtain ⟨v, hv, hnv⟩ := hN (max Na N + 2) (by omega)
  rw [evalOpt_if_false (max Na N + 1) w env A B _
    (hva ▸ ha (max Na N + 1) (by omega))] at hv
  rw [evalOpt_quote (max Na N) w env .nil] at hv
  exact hnv ((Option.some.injEq _ _).mp hv).symm

/-- RIGHT conjunct of an IF-encoded conjunction: `EvTrue (IF A B 'NIL)` with
    `A` converging truthy IS `EvTrue B`. -/
theorem evtrue_and_right {w : World} {env : Env} {A B va : SExpr}
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w env A = some va)
    (hva : Logic.toBool va = true)
    (h : EvTrue w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons A (.cons B
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
            .nil))))) :
    EvTrue w env B := by
  obtain ⟨Na, ha⟩ := hA; obtain ⟨N, hN⟩ := h
  refine ⟨max Na N, fun f hf => ?_⟩
  obtain ⟨v, hv, hnv⟩ := hN (f + 1) (by omega)
  rw [evalOpt_if_true f w env A B _ va (ha f (by omega)) hva] at hv
  exact ⟨v, hv, hnv⟩

/-- Convergence values are unique (fuel monotonicity + determinism). -/
theorem conv_unique {w : World} {env : Env} {t v v' : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env t = some v)
    (h' : ∃ N, ∀ f ≥ N, evalOpt f w env t = some v') : v = v' := by
  obtain ⟨N, hN⟩ := h; obtain ⟨N', hN'⟩ := h'
  have h1 := hN (max N N') (le_max_left _ _)
  have h2 := hN' (max N N') (le_max_right _ _)
  rw [h1] at h2; exact (Option.some.injEq _ _).mp h2

/-- The count fn applied to the QUOTED value, in the empty env, converges to
    the integer `n` — the defining relation of `interpCount`. -/
def InterpCountConv (w : World) (cnt : Symbol) (v : SExpr) (n : Nat) : Prop :=
  ∃ N, ∀ f ≥ N,
    evalOpt f w {}
      (.cons (.atom (.symbol cnt))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil))
          .nil))
    = some (intAtom n)

open scoped Classical in
/-- The INTERPRETED-count bookkeeping measure: the Nat the world's count fn
    computes on the quoted value in the empty env (definite description —
    the measure appears in no statement, design I1; `Classical.choice` is
    in the allowed axiom trio), 0 where none exists. -/
noncomputable def interpCount (w : World) (cnt : Symbol) (v : SExpr) : Nat :=
  if h : ∃ n : Nat, InterpCountConv w cnt v n then h.choose else 0

/-- QUOTE convergence at a KNOWN value (the `re_conv_quote` shape with the
    value exposed). -/
theorem conv_quote_val (w : World) (env : Env) (v : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)) = some v :=
  ⟨1, fun f _ => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w env v⟩

/-- Extract the BODY convergence from a 1-ary app convergence (the inverse
    direction of `conv_defn_1`; `evalOpt_defn_1` is an equation). -/
theorem conv_body_of_app1 {w : World} {env : Env} {s formal : Symbol}
    {arg av body v : SExpr}
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (happ : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons arg .nil)) = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v := by
  obtain ⟨Na, ha⟩ := harg; obtain ⟨Np, hp⟩ := happ
  refine ⟨max Na Np, fun f hf => ?_⟩
  have h1 := hp (f + 1) (by omega)
  rw [evalOpt_defn_1 f w env s arg av formal body h_ns h_def
    (ha f (by omega))] at h1
  exact h1

/-- TRANSPORT a 1-ary app's convergence to the QUOTED-value form at the
    empty env: the body evaluation is env-independent. With the value an
    integer (from the fn's TP), this is exactly `InterpCountConv`. -/
theorem interpCountConv_of_app1 {w : World} {env : Env} {cnt formal : Symbol}
    {t vt body : SExpr} {n : Nat}
    (h_ns : cnt.isNamed "QUOTE" = false ∧ cnt.isNamed "IF" = false ∧
            cnt.isNamed "LET" = false ∧ cnt.isNamed "LET*" = false)
    (h_def : w.defs.get? cnt = some ([formal], body))
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w env t = some vt)
    (happ : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol cnt)) (.cons t .nil))
        = some (intAtom n)) :
    InterpCountConv w cnt vt n := by
  have hb := conv_body_of_app1 h_ns h_def ht happ
  exact conv_defn_1 w {} cnt
    (.cons (.atom (.symbol { name := "QUOTE" })) (.cons vt .nil)) vt
    formal body (intAtom n) h_ns h_def (conv_quote_val w {} vt) hb

/-! The O< decode on integer atoms, against the BYTE-CHECKED emitted
    ground-zero shapes (the driver validates the world's entries equal these
    literals by kernel decision before applying the lemma). -/

def oltXSym : Symbol := { name := "X" }
def oltYSym : Symbol := { name := "Y" }

/-- The emitted ground-zero `O-FINP` body: `(IF (CONSP X) 'NIL 'T)`. -/
def oFinpBodyShape : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" }))
        (.cons (.atom (.symbol oltXSym)) .nil))
      (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
            (.cons SExpr.t .nil))
          .nil)))

/-- The emitted ground-zero `O<` body, parameterized by its (unexercised on
    integer atoms) ordinal else-arm: `(IF (O-FINP X) (IF (O-FINP Y) (< X Y)
    'T) <elseBr>)`. The driver byte-checks the world's entry against this
    shape (with the world's own else-arm) by kernel decision. -/
def oLtBodyShapeWith (elseBr : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "O-FINP" }))
        (.cons (.atom (.symbol oltXSym)) .nil))
      (.cons (.cons (.atom (.symbol { name := "IF" }))
          (.cons (.cons (.atom (.symbol { name := "O-FINP" }))
              (.cons (.atom (.symbol oltYSym)) .nil))
            (.cons (.cons (.atom (.symbol { name := "<" }))
                (.cons (.atom (.symbol oltXSym))
                  (.cons (.atom (.symbol oltYSym)) .nil)))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                  (.cons SExpr.t .nil))
                .nil))))
        (.cons elseBr .nil)))

/-- `o-finp` of an ATOM value is `t` (via the byte-checked body). -/
theorem conv_ofinp_atom {w : World} {env : Env} {arg av : SExpr}
    (hnoConsp : w.defs.get? { name := "CONSP" } = none)
    (hdefF : w.defs.get? { name := "O-FINP" } = some ([oltXSym], oFinpBodyShape))
    (hatom : Logic.consp av = SExpr.nil)
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "O-FINP" })) (.cons arg .nil))
        = some SExpr.t := by
  have hX : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [oltXSym] [av]) (.atom (.symbol oltXSym)) = some av :=
    re_val_var_get w _ oltXSym av (bindArgs_single_get_self oltXSym av)
  have hconsp := conv_builtin1 w (bindArgs [oltXSym] [av]) { name := "CONSP" }
    (.atom (.symbol oltXSym)) av (Logic.consp av) (by decide) hnoConsp hX
    (callBuiltin_consp av)
  rw [hatom] at hconsp
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [oltXSym] [av]) oFinpBodyShape = some SExpr.t := by
    obtain ⟨Nc, hc⟩ := hconsp
    refine ⟨Nc + 2, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show evalOpt (g + 1) w _ (.cons (.atom (.symbol { name := "IF" })) _) = _
    rw [evalOpt_if_false g w _ _ _ _ (hc g (by omega))]
    obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
    exact evalOpt_quote g2 w _ SExpr.t
  exact conv_defn_1 w env { name := "O-FINP" } arg av oltXSym oFinpBodyShape
    SExpr.t (by decide) hdefF harg hbody

theorem logic_lt_int_ne_nil_iff (m n : Int) :
    (Logic.lt (intAtom m) (intAtom n) ≠ SExpr.nil) ↔ m < n := by
  simp [intAtom, Logic.lt, Logic.toRat, SExpr.t]

/-- The O< DECODE on integer atoms: `EvTrue (O< a b)` with both arguments
    converging to integers, against the byte-checked `O<`/`O-FINP` shapes,
    IS the integer ordering. -/
theorem olt_int_decode {w : World} {env : Env} {a b elseBr : SExpr} {m n : Int}
    (hnoLt : w.defs.get? { name := "<" } = none)
    (hnoConsp : w.defs.get? { name := "CONSP" } = none)
    (hdefF : w.defs.get? { name := "O-FINP" } = some ([oltXSym], oFinpBodyShape))
    (hdefO : w.defs.get? { name := "O<" }
      = some ([oltXSym, oltYSym], oLtBodyShapeWith elseBr))
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some (intAtom m))
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some (intAtom n))
    (hev : EvTrue w env
      (.cons (.atom (.symbol { name := "O<" })) (.cons a (.cons b .nil)))) :
    m < n := by
  have hneXY : oltXSym ≠ oltYSym := by decide
  set envB := bindArgs [oltXSym, oltYSym] [intAtom m, intAtom n] with henvB
  have hX : ∃ N, ∀ f ≥ N,
      evalOpt f w envB (.atom (.symbol oltXSym)) = some (intAtom m) :=
    re_val_var_get w _ oltXSym _ (bindArgs_pair_get_fst oltXSym oltYSym _ _)
  have hY : ∃ N, ∀ f ≥ N,
      evalOpt f w envB (.atom (.symbol oltYSym)) = some (intAtom n) :=
    re_val_var_get w _ oltYSym _ (bindArgs_pair_get_snd oltXSym oltYSym _ _ hneXY)
  have hFinX := conv_ofinp_atom hnoConsp hdefF (by simp [intAtom, Logic.consp]) hX
  have hFinY := conv_ofinp_atom hnoConsp hdefF (by simp [intAtom, Logic.consp]) hY
  have hlt := conv_builtin2 w envB { name := "<" } (.atom (.symbol oltXSym))
    (.atom (.symbol oltYSym)) (intAtom m) (intAtom n)
    (Logic.lt (intAtom m) (intAtom n)) (by decide) hnoLt hX hY
    (callBuiltin_lt (intAtom m) (intAtom n))
  have hinner := conv_if_true w envB _ _
    (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
    SExpr.t _ hFinY (by simp [Logic.toBool]) hlt
  have houter := conv_if_true w envB _ _ elseBr SExpr.t _ hFinX
    (by simp [Logic.toBool]) hinner
  have happ := conv_defn_2 w env { name := "O<" } a b (intAtom m) (intAtom n)
    oltXSym oltYSym _ (Logic.lt (intAtom m) (intAtom n)) (by decide) hdefO ha hb houter
  have hne := ne_nil_of_evtrue_conv hev happ
  exact (logic_lt_int_ne_nil_iff m n).mp hne

theorem interpCount_eq {w : World} {cnt : Symbol} {v : SExpr} {n : Nat}
    (h : InterpCountConv w cnt v n) :
    interpCount w cnt v = n := by
  have hx : ∃ m : Nat, InterpCountConv w cnt v m := ⟨n, h⟩
  rw [interpCount, dif_pos hx]
  have hspec := hx.choose_spec
  have hv := conv_unique hspec h
  simp only [intAtom, SExpr.atom.injEq, Atom.number.injEq, Number.int.injEq] at hv
  omega


/-- The ONE-SHOT interpreted-count decrease decode (recorded-termination
    route): from the REPLAYED admission waterfall's `O<` fact over two
    count applications, their convergences (the count fn's totality), and
    the count fn's standard nonneg-int TP (partially applied at each
    argument), conclude the `interpCount` ordering the μ-generic strong
    induction consumes. All shape obligations (the count fn's arity-1
    entry, the `O<`/`O-FINP` ground-zero bodies) are BYTE-CHECKED by the
    driver before application. -/
theorem interp_decrease_decode {w : World} {env : Env} {cnt : Symbol}
    {formal : Symbol} {cntBody : SExpr} {tσ tm vσ vm elseBr : SExpr}
    (h_ns : cnt.isNamed "QUOTE" = false ∧ cnt.isNamed "IF" = false ∧
            cnt.isNamed "LET" = false ∧ cnt.isNamed "LET*" = false)
    (h_def : w.defs.get? cnt = some ([formal], cntBody))
    (hnoLt : w.defs.get? { name := "<" } = none)
    (hnoConsp : w.defs.get? { name := "CONSP" } = none)
    (hdefF : w.defs.get? { name := "O-FINP" } = some ([oltXSym], oFinpBodyShape))
    (hdefO : w.defs.get? { name := "O<" }
      = some ([oltXSym, oltYSym], oLtBodyShapeWith elseBr))
    (hσ : ∃ N, ∀ f ≥ N, evalOpt f w env tσ = some vσ)
    (hm : ∃ N, ∀ f ≥ N, evalOpt f w env tm = some vm)
    (hcσ : ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol cnt)) (.cons tσ .nil)) = some v)
    (hcm : ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol cnt)) (.cons tm .nil)) = some v)
    (htpσ : ∀ v : SExpr,
      (∃ N, ∀ f ≥ N,
        evalOpt f w env (.cons (.atom (.symbol cnt)) (.cons tσ .nil)) = some v) →
      (bif Logic.toBool (Logic.integerp v)
       then Logic.not (Logic.lt v (.atom (.number (.int 0))))
       else SExpr.nil) = SExpr.t)
    (htpm : ∀ v : SExpr,
      (∃ N, ∀ f ≥ N,
        evalOpt f w env (.cons (.atom (.symbol cnt)) (.cons tm .nil)) = some v) →
      (bif Logic.toBool (Logic.integerp v)
       then Logic.not (Logic.lt v (.atom (.number (.int 0))))
       else SExpr.nil) = SExpr.t)
    (hev : EvTrue w env
      (.cons (.atom (.symbol { name := "O<" }))
        (.cons (.cons (.atom (.symbol cnt)) (.cons tσ .nil))
          (.cons (.cons (.atom (.symbol cnt)) (.cons tm .nil)) .nil)))) :
    interpCount w cnt vσ < interpCount w cnt vm := by
  obtain ⟨Nσ, cσ, hcσ'⟩ := hcσ
  obtain ⟨Nm, cm, hcm'⟩ := hcm
  have hconvσ : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol cnt)) (.cons tσ .nil)) = some cσ :=
    ⟨Nσ, hcσ'⟩
  have hconvm : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol cnt)) (.cons tm .nil)) = some cm :=
    ⟨Nm, hcm'⟩
  obtain ⟨nσ, rfl⟩ := dp_nonneg_int_of_tp (htpσ cσ hconvσ)
  obtain ⟨nm, rfl⟩ := dp_nonneg_int_of_tp (htpm cm hconvm)
  have hicσ := interpCount_eq (interpCountConv_of_app1 h_ns h_def hσ hconvσ)
  have hicm := interpCount_eq (interpCountConv_of_app1 h_ns h_def hm hconvm)
  have hlt := olt_int_decode hnoLt hnoConsp hdefF hdefO hconvσ hconvm hev
  rw [hicσ, hicm]
  omega


/-! ## 3-ary totality (sorting arc 2026-07-29 — FILTER/ALL-REL/REL) -/

theorem bindArgs_triple_get_fst (f1 f2 f3 : Symbol) (v1 v2 v3 : SExpr) :
    (bindArgs [f1, f2, f3] [v1, v2, v3]).get? f1 = some v1 := by
  show ((({} : Env).insert f3 v3 |>.insert f2 v2 |>.insert f1 v1)).get? f1
    = some v1
  simp

theorem bindArgs_triple_get_snd (f1 f2 f3 : Symbol) (v1 v2 v3 : SExpr)
    (h12 : f1 ≠ f2) :
    (bindArgs [f1, f2, f3] [v1, v2, v3]).get? f2 = some v2 := by
  show ((({} : Env).insert f3 v3 |>.insert f2 v2 |>.insert f1 v1)).get? f2
    = some v2
  simp [Ne.symm h12]

theorem bindArgs_triple_get_thd (f1 f2 f3 : Symbol) (v1 v2 v3 : SExpr)
    (h13 : f1 ≠ f3) (h23 : f2 ≠ f3) :
    (bindArgs [f1, f2, f3] [v1, v2, v3]).get? f3 = some v3 := by
  show ((({} : Env).insert f3 v3 |>.insert f2 v2 |>.insert f1 v1)).get? f3
    = some v3
  simp [Ne.symm h13, Ne.symm h23]

/-- A 3-ary defined call converges when its arguments and its body (at the
    argument values) converge — ∃N∃v walk form. -/
theorem conv_defn_3_ex (w : World) (env : Env) (s : Symbol)
    (formal1 formal2 formal3 : Symbol) (body arg1 arg2 arg3 av1 av2 av3 : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (h3 : ∃ N, ∀ f ≥ N, evalOpt f w env arg3 = some av3)
    (hbody : ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body
        = some v) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 (.cons arg3 .nil))))
        = some v := by
  obtain ⟨Nb, v, hb⟩ := hbody
  obtain ⟨N, h⟩ := conv_defn_3 w env s arg1 arg2 arg3 av1 av2 av3
    formal1 formal2 formal3 body v h_ns h_def h1 h2 h3 ⟨Nb, hb⟩
  exact ⟨N, v, h⟩

theorem totality_3_of_body (w : World) (s : Symbol)
    (formal1 formal2 formal3 : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (hbody : ∀ av1 av2 av3 : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body
        = some v) :
    ∀ (env' : Env) (a0 a1 a2 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a2 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env'
          (.cons (.atom (.symbol s))
            (.cons a0 (.cons a1 (.cons a2 .nil)))) = some v := by
  intro env' a0 a1 a2 h0 h1 h2
  obtain ⟨N0, av1, h0'⟩ := h0
  obtain ⟨N1, av2, h1'⟩ := h1
  obtain ⟨N2, av3, h2'⟩ := h2
  exact conv_defn_3_ex w env' s formal1 formal2 formal3 body a0 a1 a2
    av1 av2 av3 h_ns h_def ⟨N0, h0'⟩ ⟨N1, h1'⟩ ⟨N2, h2'⟩ (hbody av1 av2 av3)

/-- 3-ary RECURSIVE totality, measured on the SECOND formal (FILTER/ALL-REL:
    `(fn x e)` recursing on `x`); the other two argument values are
    universally quantified INSIDE the induction. μ-generic (design I1). -/
theorem totality_3_rec_snd_mu (μ : SExpr → Nat)
    (w : World) (s : Symbol) (formal1 formal2 formal3 : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (step : ∀ av2 : SExpr,
      (∀ bv : SExpr, μ bv < μ av2 → ∀ av1 av3 : SExpr,
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, bv, av3])
            body = some v) →
      ∀ av1 av3 : SExpr,
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
          body = some v) :
    ∀ (env' : Env) (a0 a1 a2 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a2 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env'
          (.cons (.atom (.symbol s))
            (.cons a0 (.cons a1 (.cons a2 .nil)))) = some v := by
  have hbody := measure_strong_induction_val μ
    (fun av2 => ∀ av1 av3, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body
        = some v) step
  exact totality_3_of_body w s formal1 formal2 formal3 body h_ns h_def
    (fun av1 av2 av3 => hbody av2 av1 av3)



/-- The AND-shape value decode (inc-2a conjunction composer): a nil
    conjunction value with a TRUTHY left conjunct forces the right conjunct
    nil. -/
theorem cond_true_nil_forces_r {b : Bool} {r : SExpr}
    (h : cond b r SExpr.nil = SExpr.nil) (hb : b = true) : r = SExpr.nil := by
  subst hb; simpa using h


/-- `cond` under a proved-true test IS its then-branch (the conjunction
    composer's last-literal value decode). -/
theorem cond_true_val {b : Bool} (r e : SExpr) (hb : b = true) :
    cond b r e = r := by subst hb; rfl

end ACL2.Replay
