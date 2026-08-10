/-
  Replay/Lemmas/DescentExt — the equal-descent restructure arc's lemma
  family (module-size norm: new lemma families get their own module).
-/
import ACL2Lean.Replay.Lemmas.Judgments

namespace ACL2.Replay

open ACL2

/-- The `<`-headed LINEAR-rule premise fact (equal-descent restructure
    arc, charter item 3): `linear_premise_fact`'s twin for INEQUALITY
    conclusions — the emitted snapshot legitimately carries local
    inequality-headed :LINEAR rules (fork-batch item 1's wider snapshot;
    HOW-MANY-BAD-PAIRS-BNEXT's rule feeding termination:BSORT's decrease
    obligation is the first consumer). -/
theorem linear_premise_fact_lt {w : World} {env : Env} {h l r vh vl vr : SExpr}
    (hnd : w.defs.get? ({ name := "<" } : Symbol) = none)
    (hyp : EvTrue w env h → EvTrue w env
      (.cons (.atom (.symbol { name := "<" }))
        (.cons l (.cons r .nil))))
    (ph : ∃ N, ∀ f ≥ N, evalOpt f w env h = some vh)
    (pl : ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl)
    (pr : ∃ N, ∀ f ≥ N, evalOpt f w env r = some vr) :
    cond (Logic.toBool vh) (Logic.lt vl vr) SExpr.t = SExpr.t := by
  cases hb : Logic.toBool vh with
  | false => rfl
  | true =>
    have hne : vh ≠ SExpr.nil := fun hnil => by
      rw [hnil] at hb; exact absurd hb (by decide)
    have hc := hyp (evtrue_of_conv_ne_nil ph hne)
    have hpe := conv_builtin2 w env { name := "<" } l r vl vr
      (Logic.lt vl vr) (by decide) hnd pl pr (callBuiltin_lt vl vr)
    have hne2 := ne_nil_of_evtrue_conv hc hpe
    show Logic.lt vl vr = SExpr.t
    rcases logic_lt_t_or_nil vl vr with ht | hn
    · exact ht
    · exact absurd hn hne2

/-- The RULE-content premise fact for EVG-output rules (the tau-basis
    consumer, fork-batch item I): from a stored-rule hypothesis instance
    concluding an eval-equality with a QUOTED constant (`EvTrue h →
    eval l ≐ eval 'c` — NOT-MEMB-IMPLIES-HOW-MANY-IS-0's `(HOW-MANY A X)
    ⇒ '0` shape) and the two pinned values, the DP-obligation premise
    `(IF h (EQUAL l 'c) 'T)`'s value is `t` — `rule_premise_fact`
    generalized from `'T` to an arbitrary quoted payload. -/
theorem rule_premise_fact_evg {w : World} {env : Env} {h l c vh vl : SExpr}
    (hyp : EvTrue w env h → ∃ N, ∀ f ≥ N,
      evalOpt f w env l = evalOpt f w env
        (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons c .nil)))
    (ph : ∃ N, ∀ f ≥ N, evalOpt f w env h = some vh)
    (pl : ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl) :
    cond (Logic.toBool vh) (Logic.equal vl c) SExpr.t = SExpr.t := by
  cases hb : Logic.toBool vh with
  | false => rfl
  | true =>
    have hne : vh ≠ SExpr.nil := fun hnil => by
      rw [hnil] at hb; exact absurd hb (by decide)
    obtain ⟨N1, hEq⟩ := hyp (evtrue_of_conv_ne_nil ph hne)
    obtain ⟨N2, hpl⟩ := pl
    obtain ⟨N3, hqt⟩ := re_val_quote w env c
    have hvl : vl = c := by
      have h1 := hpl (N1 + N2 + N3) (by omega)
      have h2 := hEq (N1 + N2 + N3) (by omega)
      have h3 := hqt (N1 + N2 + N3) (by omega)
      exact Option.some.inj ((h1.symm.trans h2).trans h3)
    rw [hvl]
    exact Logic.equal_self c

end ACL2.Replay
