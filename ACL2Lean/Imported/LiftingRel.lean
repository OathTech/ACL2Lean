import ACL2Lean.Imported.Lifting

/-!
  THE RELATIONAL DECODE COMBINATORS — the `<` / `≤` / conjunction siblings
  of `Lifting.native_of_replayed_equal`.

  Its own module per the module-size norm: `Imported/Lifting.lean` carries
  the EQUATIONAL spine (`Conv`/`Rep`/`Implements` + the equational ender)
  and is at the size ceiling; this is a new LEMMA FAMILY, so it gets a
  sibling.

  WHY THIS EXISTS. Until now the decode family was EQUAL-ONLY: every
  waypoint ended at `native_of_replayed_equal`, so any corpus row whose
  conclusion is a COMPARISON or a CONJUNCTION had no ender at all and was
  decode-blocked regardless of how green its replay was. The three shapes
  here are read off what ACL2 actually emits:

  - `(< a b)`                     — the strict comparison, verbatim;
  - `(NOT (< b a))`               — what ACL2's `<=` macroexpands to
                                    (03-linear's LEN2-NONNEG is emitted as
                                    `:TFORMULA (NOT (< (LEN2 X) '0))`);
  - `(IF A B 'NIL)`               — what ACL2's `AND` macroexpands to
                                    (15-nested-induction's NESTED-INDUCTION
                                    is emitted as
                                    `:TFORMULA (IF (EQUAL …) (EQUAL …) 'NIL)`).

  Each combinator is the SAME shape as `native_of_replayed_equal`: the
  replayed statement's truthiness plus a representation of each side,
  yielding the NATIVE fact. Nothing here decides anything — the replayed
  statement is consumed at exactly one point and a wrong-shaped one is a
  TYPE ERROR at that point (`Tests/LiftingRelProbes.lean` pins that).

  THE COMPARISONS ARE `intRep`-ONLY, deliberately. `Logic.lt` is ACL2's
  full rational comparison; the native fact `x < y` at `Int` is sound for
  it only because both sides are pinned to INTEGER atoms by `intRep`. A
  `Rep`-generic version would have to carry an order on the represented
  type and an agreement lemma — build it when a row needs it, not before.
-/

open ACL2 ACL2.Replay

namespace ACL2.Lifting

/-! ## Term builders + `callBuiltin` bridges -/

/-- `(< a b)`. -/
abbrev ltT (a b : SExpr) : SExpr := app2 "<" a b
/-- `(not a)`. -/
abbrev notT (a : SExpr) : SExpr := app1 "NOT" a
/-- The macroexpanded `(and a b)` — ACL2 emits `(IF a b 'NIL)`. -/
abbrev andT (a b : SExpr) : SExpr := appIf a b qNilT

/-! ## The convergence kit for the new heads -/

/-- `(< a b)` converges to the SYMBOLIC `Logic.lt` of the values. -/
theorem conv_ltT (w : World) (e : Env) (a b av bv : SExpr)
    (h_no : w.defs.get? ({ name := "<" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (ltT a b) = some (Logic.lt av bv) :=
  conv_builtin2 w e { name := "<" } a b av bv _ (by decide) h_no ha hb
    (callBuiltin_lt _ _)

/-- `(not a)` converges to the SYMBOLIC `Logic.not` of the value. -/
theorem conv_notT (w : World) (e : Env) (a av : SExpr)
    (h_no : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (notT a) = some (Logic.not av) :=
  conv_builtin1 w e { name := "NOT" } a av _ (by decide) h_no ha
    (callBuiltin_not _)

/-! ## Value-level readings of `Logic.lt` at integer atoms -/

/-- `Logic.lt` at two INTEGER atoms is the integer comparison (both
    denominators are `1`, so the cross-multiplied test IS `m < n`). -/
theorem logic_lt_int (m n : Int) :
    Logic.lt (intRep.enc m) (intRep.enc n)
      = if m < n then SExpr.t else SExpr.nil := by
  simp [Logic.lt, Logic.toRat, intRep]

/-- A truthy `(< m n)` at integer atoms IS `m < n` — the `<` decode's
    value-level ender. -/
theorem lt_of_lt_truthy {m n : Int}
    (h : Logic.toBool (Logic.lt (intRep.enc m) (intRep.enc n)) = true) :
    m < n := by
  rw [logic_lt_int] at h
  by_cases hmn : m < n
  · exact hmn
  · rw [if_neg hmn] at h; exact absurd h (by decide)

/-- A truthy `(not (< m n))` at integer atoms IS `n ≤ m` — the `≤`
    decode's value-level ender (ACL2 has no `<=` in the logic: `(<= a b)`
    macroexpands to `(not (< b a))`). -/
theorem le_of_not_lt_truthy {m n : Int}
    (h : Logic.toBool (Logic.not (Logic.lt (intRep.enc m) (intRep.enc n)))
      = true) : n ≤ m := by
  rw [logic_lt_int] at h
  by_cases hmn : m < n
  · rw [if_pos hmn] at h; exact absurd h (by decide)
  · omega

/-! ## The ENDERS — the `native_of_replayed_equal` siblings -/

/-- THE `<` DECODE: a replayed TRUE `(< lhs rhs)` statement plus an
    INTEGER representation of each side yields the NATIVE `<`. The exact
    shape of `native_of_replayed_equal`, with `Logic.lt`'s two-valuedness
    in place of `equal`'s. -/
theorem native_of_replayed_lt (w : World) (e : Env) (lhs rhs : SExpr)
    (x y : Int)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (hL : Conv w e lhs (intRep.enc x)) (hR : Conv w e rhs (intRep.enc y))
    (hreplayed : EvTrue w e (ltT lhs rhs)) : x < y :=
  lt_of_lt_truthy (toBool_true_of_ne_nil
    (ne_nil_of_evtrue_conv hreplayed (conv_ltT w e lhs rhs _ _ h_no_lt hL hR)))

/-- THE `≤` DECODE: a replayed TRUE `(NOT (< lhs rhs))` statement — the
    macroexpansion of ACL2's `(<= rhs lhs)` — plus an INTEGER
    representation of each side yields the NATIVE `≤`. Note the ARGUMENT
    ORDER: the conclusion is `y ≤ x`, mirroring the swap the
    macroexpansion performs, so a consumer reads its `lhs`/`rhs` straight
    off the emitted `(< …)` term. -/
theorem native_of_replayed_le (w : World) (e : Env) (lhs rhs : SExpr)
    (x y : Int)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (hL : Conv w e lhs (intRep.enc x)) (hR : Conv w e rhs (intRep.enc y))
    (hreplayed : EvTrue w e (notT (ltT lhs rhs))) : y ≤ x :=
  le_of_not_lt_truthy (toBool_true_of_ne_nil
    (ne_nil_of_evtrue_conv hreplayed
      (conv_notT w e (ltT lhs rhs) _ h_no_not
        (conv_ltT w e lhs rhs _ _ h_no_lt hL hR))))

/-! ## The conjunction split -/

/-- THE CONJUNCTION SPLIT: a replayed TRUE macroexpanded `(and A B)` —
    i.e. `(IF A B 'NIL)` — makes BOTH conjuncts replayed-true, so each is
    then decoded by the ordinary combinators.

    Both directions of the `if` are needed: if `A` were nil the whole term
    would converge to `'NIL`, contradicting the replayed statement's
    truthiness; with `A` truthy the term IS `B`, which inherits it. -/
theorem replayed_split_and (w : World) (e : Env) (A B av bv : SExpr)
    (hA : Conv w e A av) (hB : Conv w e B bv)
    (hreplayed : EvTrue w e (andT A B)) :
    EvTrue w e A ∧ EvTrue w e B := by
  have havne : av ≠ SExpr.nil := by
    intro hnil
    subst hnil
    exact ne_nil_of_evtrue_conv hreplayed
      (conv_if_false' w e A B qNilT SExpr.nil hA (re_val_quote w e SExpr.nil))
      rfl
  have hbvne : bv ≠ SExpr.nil :=
    ne_nil_of_evtrue_conv hreplayed
      (conv_if_true w e A B qNilT av bv hA (toBool_true_of_ne_nil havne) hB)
  obtain ⟨Na, ha⟩ := hA
  obtain ⟨Nb, hb⟩ := hB
  exact ⟨⟨Na, fun f hf => ⟨av, ha f hf, havne⟩⟩,
         ⟨Nb, fun f hf => ⟨bv, hb f hf, hbvne⟩⟩⟩

/-- THE `and` DECODE, both conjuncts EQUATIONAL: a replayed TRUE
    macroexpanded `(and (equal l1 r1) (equal l2 r2))` yields BOTH native
    equalities. Built from `replayed_split_and` plus two applications of
    `native_of_replayed_equal` — the conjuncts may sit in DIFFERENT
    represented types (15-nested-induction's two conjuncts are both
    integer-valued, but nothing here couples them). -/
theorem native_of_replayed_and {γ δ : Type} (w : World) (e : Env)
    (rγ : Rep γ) (rδ : Rep δ)
    (l1 r1 l2 r2 : SExpr) (x1 y1 : γ) (x2 y2 : δ)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hL1 : Conv w e l1 (rγ.enc x1)) (hR1 : Conv w e r1 (rγ.enc y1))
    (hL2 : Conv w e l2 (rδ.enc x2)) (hR2 : Conv w e r2 (rδ.enc y2))
    (hreplayed : EvTrue w e (andT (equalT l1 r1) (equalT l2 r2))) :
    x1 = y1 ∧ x2 = y2 :=
  let hs := replayed_split_and w e (equalT l1 r1) (equalT l2 r2) _ _
    (conv_equalT w e l1 r1 _ _ h_no_equal hL1 hR1)
    (conv_equalT w e l2 r2 _ _ h_no_equal hL2 hR2) hreplayed
  ⟨native_of_replayed_equal w e rγ l1 r1 x1 y1 h_no_equal hL1 hR1 hs.1,
   native_of_replayed_equal w e rδ l2 r2 x2 y2 h_no_equal hL2 hR2 hs.2⟩

/-! ## The IMPLIES peel — extracted, not new

The `(IMPLIES hyp concl)` glue below was written out verbatim FOUR times
in the waypoint layer (`Imported/Rev.lean`'s APP-NIL and REV-REV,
`Imported/RuleApp.lean`'s two rows) before this extraction. It is the
step every CONDITIONAL row takes: the antecedent converges to `t` at the
encoded instance (a machinery-side enc-image fact), so the replayed
implication's truthiness passes to the consequent's value. -/

/-- THE PEEL, as a REPLAYED-STATEMENT TRANSFORMER: given the antecedent
    converges to `t` (a machinery-side enc-image fact) and the consequent
    converges at all, a replayed TRUE `(implies hyp concl)` IS a replayed
    TRUE `concl`.

    Stating it this way — `EvTrue … → EvTrue …` rather than "…→ a truthy
    value" — is what makes EVERY conditional row reduce to the
    UNCONDITIONAL combinator: the decode of a `(IMPLIES h C)` row is the
    decode of `C` composed with this, whatever `C`'s shape is. -/
theorem replayed_of_replayed_implies (w : World) (e : Env)
    (hyp concl cv : SExpr)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hH : Conv w e hyp SExpr.t) (hC : Conv w e concl cv)
    (hreplayed : EvTrue w e (impliesT hyp concl)) : EvTrue w e concl := by
  have hne : cv ≠ SExpr.nil :=
    (Logic.toBool_eq_true cv).mp (truthy_of_implies_t
      (implies_t_of_ne_nil (ne_nil_of_evtrue_conv hreplayed
        (conv_impliesT w e hyp concl SExpr.t cv h_no_implies hH hC))) rfl)
  obtain ⟨N, hN⟩ := hC
  exact ⟨N, fun f hf => ⟨cv, hN f hf, hne⟩⟩

/-- THE CONDITIONAL `<` DECODE: a replayed TRUE
    `(implies hyp (< lhs rhs))` whose antecedent converges to `t` at the
    encoded instance. The corpus's `<`-conclusion rows are conditional
    (03-linear's LEN2-CDR-SMALLER is `(IMPLIES (CONSP X) (< …))`), so this
    is the form they consume — and it is literally the unconditional
    ender composed with the peel, no new content. -/
theorem native_of_replayed_lt_of_implies (w : World) (e : Env)
    (hyp lhs rhs : SExpr) (x y : Int)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hH : Conv w e hyp SExpr.t)
    (hL : Conv w e lhs (intRep.enc x)) (hR : Conv w e rhs (intRep.enc y))
    (hreplayed : EvTrue w e (impliesT hyp (ltT lhs rhs))) : x < y :=
  native_of_replayed_lt w e lhs rhs x y h_no_lt hL hR
    (replayed_of_replayed_implies w e hyp (ltT lhs rhs) _ h_no_implies hH
      (conv_ltT w e lhs rhs _ _ h_no_lt hL hR) hreplayed)

end ACL2.Lifting
