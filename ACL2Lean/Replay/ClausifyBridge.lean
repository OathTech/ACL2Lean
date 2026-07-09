/-
  G3 Fragment B — the clausify bridge as a once-proved lemma.

  `clausifyPure` is the PURE fragment of ACL2's `clausify-input1` (the
  recompute-and-validate twin of the recorded checkpoints — validation
  stays in the driver); `disjoinTerm` is ACL2's `disjoin`. The bridge
  lemma `clausifyPure_sound` (to come, built on Fragment A's `dpLiftF`)
  replaces the per-leaf `peelClause`/`walkPosT`/`val*` walkers: ONE mutual
  structural induction proving that the output clause's truth gives the
  input's truth (pos) / falsity (neg).

  Fragment-local per invariant L1; world-parametric per L3. Design:
  docs/plans/2026-06-12_g3-consolidations.md (D-B1..3).
-/
import ACL2Lean.Replay.DpLift

namespace ACL2.Replay

open ACL2

/-- `(quote t)`, the result an equal-self literal reduces to. -/
def quoteT : SExpr := .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)

/-- `(quote nil)`. -/
def quoteNil : SExpr := .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)

/-- ACL2's `disjoin` of a literal list: `(if l₁ 't (if l₂ 't … lₖ))`; a singleton
    is the literal itself; the empty clause is `'nil` (false). -/
def disjoinTerm : List SExpr → SExpr
  | [] => .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)
  | [l] => l
  | l :: rest =>
    .cons (.atom (.symbol { name := "IF" }))
      (.cons l (.cons quoteT (.cons (disjoinTerm rest) .nil)))

/-- ACL2's `dumb-negate-lit`, two of its four arms (strip a `not`, else
    wrap). The other two arms (quote-fold `'nil`↔`'t`, `(equal x 'nil)` →
    `x`) are pure too but not mirrored; a log taking them diverges from this
    recomputation and hard-fails at `bridgeClausify`'s record validation.
    ACL2 strips `(not x)` by exact symbol while we strip by NAME (any
    package); the bridge lemma handles the wrong-package case vacuously and
    the record check catches any behavioral divergence. -/
def dumbNegateLit (t : SExpr) : SExpr :=
  match t with
  | .cons (.atom (.symbol ns)) (.cons _ .nil) =>
    if ns.name == "NOT" then
      match t with
      | .cons _ (.cons inner .nil) => inner
      | _ => t
    else .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
  | _ => .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)

/-- The PURE fragment of `clausify-input1` (no `expand-and-or`; sub-clauses
    joined by plain `++` where ACL2's `disjoin-clauses`/`add-literal` may
    also dedupe or detect complementary pairs): `pos` is ACL2's `bool`.
    Recomputed for the walk and VALIDATED against the recorded checkpoints —
    any divergence (an expansion fired, a literal merged, an unmirrored
    `dumb-negate-lit` arm) hard-fails upstream. -/
def clausifyPure (t : SExpr) (pos : Bool) : List SExpr :=
  if t == (if pos then quoteNil else quoteT) then []
  else match t with
  | .cons (.atom (.symbol ifS)) (.cons t1 (.cons t2 (.cons t3 .nil))) =>
    if ifS.name == "IF" then
      if pos then
        if t3 == quoteT then clausifyPure t1 false ++ clausifyPure t2 true
        else if t2 == quoteT then clausifyPure t1 true ++ clausifyPure t3 true
        else [t]
      else
        if t3 == quoteNil then clausifyPure t1 false ++ clausifyPure t2 false
        else if t2 == quoteNil then clausifyPure t1 true ++ clausifyPure t3 false
        else [dumbNegateLit t]
    else if pos then [t] else [dumbNegateLit t]
  | _ => if pos then [t] else [dumbNegateLit t]

/-! ## The disjoin characterization ladder (design doc, Fragment B helpers) -/

/-- The empty clause's disjunction (`(quote nil)`) is never true. -/
theorem not_evtrue_disjoin_nil (w : World) (env : Env) :
    ¬ EvTrue w env (disjoinTerm []) := by
  intro h
  obtain ⟨N, h⟩ := h
  obtain ⟨v, hv, hnv⟩ := h (N + 1) (by omega)
  have hq : evalOpt (N + 1) w env (disjoinTerm []) = some SExpr.nil :=
    evalOpt_quote N w env SExpr.nil
  exact hnv (Option.some.inj (hv.symm.trans hq))

/-- `EvTrue` of `(quote t)` (the spine's then-branch). -/
theorem evtrue_quoteT (w : World) (env : Env) : EvTrue w env quoteT :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact ⟨SExpr.t, evalOpt_quote g w env SExpr.t, by simp [SExpr.t]⟩⟩

/-- The UNIFORM cons characterization: a disjunction headed by a converging
    literal is true iff the literal is truthy or the rest is true.
    (`disjoinTerm`'s singleton special case dissolves: for `rest = []` the
    right disjunct is refuted by `not_evtrue_disjoin_nil`.) -/
theorem evtrue_disjoin_cons (w : World) (env : Env) (l : SExpr)
    (rest : List SExpr) (vl : SExpr)
    (hconv : ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl) :
    EvTrue w env (disjoinTerm (l :: rest)) ↔
      (vl ≠ SExpr.nil ∨ EvTrue w env (disjoinTerm rest)) := by
  cases rest with
  | nil =>
    constructor
    · intro h
      exact Or.inl (ne_nil_of_evtrue_conv h hconv)
    · rintro (hne | habs)
      · exact evtrue_of_conv_ne_nil hconv hne
      · exact absurd habs (not_evtrue_disjoin_nil w env)
  | cons r rs =>
    constructor
    · intro h
      by_cases hv : vl = SExpr.nil
      · exact Or.inr (evtrue_extract_else (hv ▸ hconv) h)
      · exact Or.inl hv
    · rintro (hne | hrest)
      · exact evtrue_dp_if_split w env l quoteT (disjoinTerm (r :: rs)) vl
          hconv (fun _ => evtrue_quoteT w env) (fun h0 => absurd h0 hne)
      · exact evtrue_dp_if_split w env l quoteT (disjoinTerm (r :: rs)) vl
          hconv (fun _ => evtrue_quoteT w env) (fun _ => hrest)

/-- Split a true disjoined APPEND into a true side (needs the left
    literals' convergences to walk the spine). -/
theorem evtrue_disjoin_append_elim (w : World) (env : Env) :
    ∀ (xs ys : List SExpr),
      (∀ l ∈ xs, ∃ vl, ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl) →
      EvTrue w env (disjoinTerm (xs ++ ys)) →
      EvTrue w env (disjoinTerm xs) ∨ EvTrue w env (disjoinTerm ys)
  | [], _, _, h => Or.inr (by simpa using h)
  | l :: xs, ys, hconv, h => by
    obtain ⟨vl, hvl⟩ := hconv l List.mem_cons_self
    rw [List.cons_append,
        evtrue_disjoin_cons w env l (xs ++ ys) vl hvl] at h
    rcases h with hne | hrest
    · exact Or.inl ((evtrue_disjoin_cons w env l xs vl hvl).mpr (Or.inl hne))
    · rcases evtrue_disjoin_append_elim w env xs ys
        (fun l' hl' => hconv l' (List.mem_cons_of_mem _ hl')) hrest with h1 | h2
      · exact Or.inl ((evtrue_disjoin_cons w env l xs vl hvl).mpr (Or.inr h1))
      · exact Or.inr h2

/-! ## The literal-liftability induction (every clause literal lifts when
the input does — feeds the literal convergences of the main theorem). -/

/-- Symbols with different names are BEq-distinct. -/
theorem symbol_beq_false_of_name_ne {a b : Symbol} (h : a.name ≠ b.name) :
    (a == b) = false := by
  cases hab : a == b
  · rfl
  · exact absurd (congrArg Symbol.name (eq_of_beq hab)) h

/-- BEq-distinct symbols from full inequality. -/
theorem symbol_beq_false_of_ne {a b : Symbol} (h : a ≠ b) :
    (a == b) = false := by
  cases hab : a == b
  · rfl
  · exact absurd (eq_of_beq hab) h

/-- A POS leaf `[t]`: the literal is the input itself. -/
theorem lifts_leaf_pos {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (t : SExpr)
    (hl : (dpLiftF vars opq t).isSome) :
    ∀ l ∈ [t], (dpLiftF vars opq l).isSome := by
  intro l hmem
  rw [List.mem_singleton.mp hmem]
  exact hl

/-- `dumbNegateLit` characterized: either the wrap `(not t)`, or the strip
    of a unary `not`-NAMED application. -/
theorem dumbNegateLit_eq (t : SExpr) :
    dumbNegateLit t = notT t ∨
    ∃ ns x, t = .cons (.atom (.symbol ns)) (.cons x .nil) ∧
      ns.isNamed "NOT" = true ∧ dumbNegateLit t = x := by
  rcases t with _ | a | ⟨hd, tl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · rcases hd with _ | a' | _
    · exact Or.inl rfl
    · rcases a' with ns | _ | _ | _ | _
      · rcases tl with _ | _ | ⟨x, tl2⟩
        · exact Or.inl rfl
        · exact Or.inl rfl
        · rcases tl2 with _ | _ | _
          · by_cases hname : ns.name = "NOT"
            · exact Or.inr ⟨ns, x, rfl, by simp [Symbol.isNamed, hname],
                by simp [dumbNegateLit, hname]⟩
            · exact Or.inl (by simp [dumbNegateLit, hname])
          · exact Or.inl rfl
          · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl  -- .char-headed cons: not a `not`-application
    · exact Or.inl rfl

/-- A NEG leaf `[dumbNegateLit t]`: the strip arm inverts the `not` (or is
    vacuous for a wrong-package `not`-named head); the wrap arm introduces
    one. -/
theorem lifts_leaf_neg {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true) (t : SExpr)
    (hl : (dpLiftF vars opq t).isSome) :
    ∀ l ∈ [dumbNegateLit t], (dpLiftF vars opq l).isSome := by
  intro l hmem
  rw [List.mem_singleton.mp hmem]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  rcases dumbNegateLit_eq t with hwrap | ⟨ns, x, hshape, hname, hstrip⟩
  · rw [hwrap]
    exact Option.isSome_iff_exists.mpr ⟨_, dpLiftF_not_intro hwf hv⟩
  · rw [hstrip]
    subst hshape
    by_cases hfull : ns = ({ name := "NOT" } : Symbol)
    · subst hfull
      obtain ⟨xv, hxv, _⟩ := dpLiftF_not_inv hwf hv
      exact Option.isSome_iff_exists.mpr ⟨xv, hxv⟩
    · -- wrong-package not: the lift premise is refutable
      exfalso
      have hnn : ns.name = "NOT" := by simpa [Symbol.isNamed] using hname
      have hnone : dpLiftF vars opq
          (.cons (.atom (.symbol ns)) (x.cons SExpr.nil)) = none :=
        dpLiftF_app_none_of_banned_name hwf (x.cons SExpr.nil)
          (by simp [Symbol.isNamed, hnn, dpLiftHeads])
          (symbol_beq_false_of_name_ne (by simp [hnn]))
          (symbol_beq_false_of_name_ne (by simp [hnn]))
          (by
            cases hpkg : ns.package == "ACL2"
            · simp
            · exact absurd (by
                have hp : ns.package = "ACL2" := eq_of_beq hpkg
                cases ns
                simp_all) hfull)
      rw [hnone] at hv
      cases hv

/-- The vacuous-case refuter, packaged: an if-NAMED head that is not the
    default-package `if` cannot lift. -/
theorem dpLiftF_ifname_none {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    {ifS : Symbol} (args : SExpr) (hnn : ifS.name = "IF")
    (hfull : ifS ≠ ({ name := "IF" } : Symbol)) :
    dpLiftF vars opq (.cons (.atom (.symbol ifS)) args) = none :=
  dpLiftF_app_none_of_banned_name hwf args
    (by simp [Symbol.isNamed, hnn])
    (symbol_beq_false_of_name_ne (by simp [hnn]))
    (symbol_beq_false_of_ne hfull)
    (by simp [hnn, dpLiftHeads])

theorem clausifyPure_lifts {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true) :
    ∀ t pos, (dpLiftF vars opq t).isSome →
      ∀ l ∈ clausifyPure t pos, (dpLiftF vars opq l).isSome := by
  intro t pos
  induction t, pos using clausifyPure.induct with
  | case1 t pos hguard =>
    intro _ l hmem
    rw [clausifyPure.eq_def] at hmem
    simp [hguard] at hmem
  | case2 ifS t1 t2 t3 hname ht3 houter ih2 ih1 =>
    intro hl l hmem
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain ⟨cv, tv, ev, hcv, htv, hev, _⟩ := dpLiftF_if_inv hwf hv
      rw [clausifyPure.eq_def] at hmem
      simp [ht3] at hmem
      obtain ⟨-, h | h⟩ := hmem
      · exact ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) l h
      · exact ih1 (Option.isSome_iff_exists.mpr ⟨tv, htv⟩) l h
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case3 ifS t1 t2 t3 hname hnt3 ht2 houter ih2 ih1 =>
    intro hl l hmem
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain ⟨cv, tv, ev, hcv, htv, hev, _⟩ := dpLiftF_if_inv hwf hv
      rw [clausifyPure.eq_def] at hmem
      simp [hnt3, ht2] at hmem
      obtain ⟨-, h | h⟩ := hmem
      · exact ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) l h
      · exact ih1 (Option.isSome_iff_exists.mpr ⟨ev, hev⟩) l h
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case4 ifS t1 t2 t3 hname hnt3 hnt2 houter =>
    intro hl l hmem
    rw [clausifyPure.eq_def] at hmem
    simp [hname, hnt3, hnt2] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact hl
  | case5 pos ifS t1 t2 t3 hname hnpos ht3 houter ih2 ih1 =>
    intro hl l hmem
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain ⟨cv, tv, ev, hcv, htv, hev, _⟩ := dpLiftF_if_inv hwf hv
      rw [clausifyPure.eq_def] at hmem
      simp [hnpos, ht3] at hmem
      obtain ⟨-, h | h⟩ := hmem
      · exact ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) l h
      · exact ih1 (Option.isSome_iff_exists.mpr ⟨tv, htv⟩) l h
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case6 pos ifS t1 t2 t3 hname hnpos hnt3 ht2 houter ih2 ih1 =>
    intro hl l hmem
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain ⟨cv, tv, ev, hcv, htv, hev, _⟩ := dpLiftF_if_inv hwf hv
      rw [clausifyPure.eq_def] at hmem
      simp [hnpos, hnt3, ht2] at hmem
      obtain ⟨-, h | h⟩ := hmem
      · exact ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) l h
      · exact ih1 (Option.isSome_iff_exists.mpr ⟨ev, hev⟩) l h
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case7 pos ifS t1 t2 t3 hname hnpos hnt3 hnt2 houter =>
    intro hl l hmem
    rw [clausifyPure.eq_def] at hmem
    simp [hname, hnpos, hnt3, hnt2] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact lifts_leaf_neg hwf _ hl _ (List.mem_singleton.mpr rfl)
  | case8 ifS t1 t2 t3 hnname houter =>
    intro hl l hmem
    rw [clausifyPure.eq_def] at hmem
    simp [hnname] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact hl
  | case9 pos ifS t1 t2 t3 hnname hnpos houter =>
    intro hl l hmem
    rw [clausifyPure.eq_def] at hmem
    simp [hnname, hnpos] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact lifts_leaf_neg hwf _ hl _ (List.mem_singleton.mpr rfl)
  | case10 t hnshape houter =>
    intro hl l hmem
    rw [clausifyPure.eq_def] at hmem
    split at hmem
    · simp at hmem
      obtain ⟨-, rfl⟩ := hmem
      exact hl
    · exact absurd rfl (by assumption)
  | case11 t pos houter hnpos hnshape =>
    intro hl l hmem
    rw [clausifyPure.eq_def] at hmem
    simp only [houter, if_false, Bool.false_eq_true] at hmem
    split at hmem
    · exact absurd (by assumption) hnpos
    · simp at hmem
      obtain ⟨-, rfl⟩ := hmem
      exact lifts_leaf_neg hwf _ hl _ (List.mem_singleton.mpr rfl)

/-! ## THE BRIDGE LEMMA (Fragment B's product) -/

/-- The bridge's per-mode conclusion: pos = the input is TRUE; neg = the
    input converges to nil (its falsity). -/
def ClausifyGoal (w : World) (env : Env) (t : SExpr) : Bool → Prop
  | true => EvTrue w env t
  | false => ∃ N, ∀ f ≥ N, evalOpt f w env t = some SExpr.nil

/-- The NEG leaf: a true `dumbNegateLit t` makes `t` converge to nil. -/
theorem sound_neg_leaf (w : World) (env : Env)
    {vars : List (Symbol × SExpr)} {opq : List (SExpr × SExpr)}
    (hvars : ∀ q ∈ vars,
      ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol q.1)) = some q.2)
    (hopq : ∀ p ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hns : dpNoShadow w) (hwf : dpOpqWF opq = true) (t : SExpr)
    (hl : (dpLiftF vars opq t).isSome)
    (hdis : EvTrue w env (dumbNegateLit t)) :
    ∃ N, ∀ f ≥ N, evalOpt f w env t = some SExpr.nil := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  rcases dumbNegateLit_eq t with hwrap | ⟨ns, x, hshape, hname, hstrip⟩
  · -- wrap arm: EvTrue (not t) pins Logic.not v ≠ nil, so v = nil
    rw [hwrap] at hdis
    have hnotconv := dpLiftF_sound w env vars opq hvars hopq hns _ _
      (dpLiftF_not_intro hwf hv)
    have hne := ne_nil_of_evtrue_conv hdis hnotconv
    have hvnil := arg_nil_of_not_truthy hne
    exact hvnil ▸ dpLiftF_sound w env vars opq hvars hopq hns t v hv
  · -- strip arm: t = (not x); a true x makes (not x) nil
    rw [hstrip] at hdis
    subst hshape
    by_cases hfull : ns = ({ name := "NOT" } : Symbol)
    · subst hfull
      -- after the strip rewrite, the hypothesis IS x's truth; the goal IS
      -- the not-application's nil convergence
      exact conv_not_nil_of_evtrue (hns "NOT" (by simp [dpLiftHeads])) hdis
    · exfalso
      have hnn : ns.name = "NOT" := by simpa [Symbol.isNamed] using hname
      have hnone : dpLiftF vars opq
          (.cons (.atom (.symbol ns)) (x.cons SExpr.nil)) = none :=
        dpLiftF_app_none_of_banned_name hwf (x.cons SExpr.nil)
          (by simp [Symbol.isNamed, hnn, dpLiftHeads])
          (symbol_beq_false_of_name_ne (by simp [hnn]))
          (symbol_beq_false_of_name_ne (by simp [hnn]))
          (by
            cases hpkg : ns.package == "ACL2"
            · simp
            · exact absurd (by
                have hp : ns.package = "ACL2" := eq_of_beq hpkg
                cases ns
                simp_all) hfull)
      rw [hnone] at hv
      cases hv

/-- The DUAL NEG leaf: a nil-converging `dumbNegateLit t` makes `t` TRUE
    (the multi-clause bridge's converter, mirroring `sound_neg_leaf`). -/
theorem neg_leaf_false_sound (w : World) (env : Env)
    {vars : List (Symbol × SExpr)} {opq : List (SExpr × SExpr)}
    (hvars : ∀ q ∈ vars,
      ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol q.1)) = some q.2)
    (hopq : ∀ p ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hns : dpNoShadow w) (hwf : dpOpqWF opq = true) (t : SExpr)
    (hl : (dpLiftF vars opq t).isSome)
    (hnil : ∃ N, ∀ f ≥ N, evalOpt f w env (dumbNegateLit t) = some SExpr.nil) :
    EvTrue w env t := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  have sound := dpLiftF_sound w env vars opq hvars hopq hns
  rcases dumbNegateLit_eq t with hwrap | ⟨ns, x, hshape, hname, hstrip⟩
  · -- wrap arm: (not t) converges nil, so Logic.not v = nil, so v ≠ nil
    rw [hwrap] at hnil
    have hnotconv := sound _ _ (dpLiftF_not_intro hwf hv)
    have hnotnil : Logic.not v = SExpr.nil := val_unique hnotconv hnil
    exact evtrue_of_conv_ne_nil (sound t v hv) (logic_not_nil_ne v hnotnil)
  · -- strip arm: t = (not x); a nil x makes (not x) converge to t
    rw [hstrip] at hnil
    subst hshape
    by_cases hfull : ns = ({ name := "NOT" } : Symbol)
    · subst hfull
      have ht := conv_not_t_of_conv_nil
        (hns "NOT" (by simp [dpLiftHeads])) hnil
      exact evtrue_of_conv_ne_nil ht (by simp [SExpr.t])
    · exfalso
      have hnn : ns.name = "NOT" := by simpa [Symbol.isNamed] using hname
      have hnone : dpLiftF vars opq
          (.cons (.atom (.symbol ns)) (x.cons SExpr.nil)) = none :=
        dpLiftF_app_none_of_banned_name hwf (x.cons SExpr.nil)
          (by simp [Symbol.isNamed, hnn, dpLiftHeads])
          (symbol_beq_false_of_name_ne (by simp [hnn]))
          (symbol_beq_false_of_name_ne (by simp [hnn]))
          (by
            cases hpkg : ns.package == "ACL2"
            · simp
            · exact absurd (by
                have hp : ns.package = "ACL2" := eq_of_beq hpkg
                cases ns
                simp_all) hfull)
      rw [hnone] at hv
      cases hv

/-- The multi-clause bridge's CONJUNCTION lemma: when EVERY literal of
    `clausifyPure t pos` converges to nil, `t` satisfies the OPPOSITE goal —
    pos-mode literals all false ⟹ `t` is nil; NEG-mode literals all false ⟹
    `t` is TRUE. The `pos = false` instance is the multi-output clausify
    composition: ACL2's ¬-clause pass lists the ways `t` can fail, and the
    per-literal split clauses (proved separately) refute each. -/
theorem clausifyAllFalse_sound (w : World) (env : Env)
    {vars : List (Symbol × SExpr)} {opq : List (SExpr × SExpr)}
    (hvars : ∀ q ∈ vars,
      ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol q.1)) = some q.2)
    (hopq : ∀ p ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hns : dpNoShadow w) (hwf : dpOpqWF opq = true) :
    ∀ t pos, (dpLiftF vars opq t).isSome →
      (∀ L ∈ clausifyPure t pos,
        ∃ N, ∀ f ≥ N, evalOpt f w env L = some SExpr.nil) →
      ClausifyGoal w env t (!pos) := by
  have sound := dpLiftF_sound w env vars opq hvars hopq hns
  intro t pos
  induction t, pos using clausifyPure.induct with
  | case1 t pos hguard =>
    intro _ _
    -- t IS the mode's trivial constant: 'nil (pos) is nil; 't (neg) is true
    have hteq := eq_of_beq hguard
    cases pos
    · subst hteq
      show EvTrue w env quoteT
      exact evtrue_quoteT w env
    · subst hteq
      show ∃ N, ∀ f ≥ N, evalOpt f w env quoteNil = some SExpr.nil
      exact ⟨1, fun f hf => by
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        exact evalOpt_quote g w env SExpr.nil⟩
  | case2 ifS t1 t2 t3 hname ht3 houter ih2 ih1 =>
    intro hl hnil
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t3 = quoteT := eq_of_beq ht3
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : ev = SExpr.t :=
        Option.some.inj (hev.symm.trans (dpLiftF_quote hwf SExpr.t))
      rw [clausifyPure.eq_def] at hnil
      simp only [hname, ht3, if_true] at hnil
      have hL := fun l hl => hnil l (List.mem_append_left _ hl)
      have hR := fun l hl => hnil l (List.mem_append_right _ hl)
      -- t1 true (its neg literals all false), t2 nil (its pos literals all
      -- false): v = cond (toBool cv) tv 't with cv ≠ nil → v = tv = nil
      have hcvne : cv ≠ SExpr.nil :=
        ne_nil_of_evtrue_conv
          (ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL) (sound t1 cv hcv)
      obtain ⟨N2, hN2⟩ := ih1 (Option.isSome_iff_exists.mpr ⟨tv, htv⟩) hR
      have htvnil : tv = SExpr.nil := val_unique (sound t2 tv htv) ⟨N2, hN2⟩
      have hvnil : v = SExpr.nil := by
        rw [hveq, toBool_true_of_ne_nil hcvne, htvnil]
        rfl
      have hc := sound _ v hv
      rw [hvnil] at hc
      exact hc
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case3 ifS t1 t2 t3 hname hnt3 ht2 houter ih2 ih1 =>
    intro hl hnil
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t2 = quoteT := eq_of_beq ht2
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : tv = SExpr.t :=
        Option.some.inj (htv.symm.trans (dpLiftF_quote hwf SExpr.t))
      rw [clausifyPure.eq_def] at hnil
      simp only [hname, hnt3, ht2, if_true] at hnil
      have hL := fun l hl => hnil l (List.mem_append_left _ hl)
      have hR := fun l hl => hnil l (List.mem_append_right _ hl)
      -- t1 nil, t3 nil: v = cond (toBool cv) 't ev = ev = nil
      obtain ⟨N1, hN1⟩ := ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL
      have hcvnil : cv = SExpr.nil := val_unique (sound t1 cv hcv) ⟨N1, hN1⟩
      obtain ⟨N2, hN2⟩ := ih1 (Option.isSome_iff_exists.mpr ⟨ev, hev⟩) hR
      have hevnil : ev = SExpr.nil := val_unique (sound t3 ev hev) ⟨N2, hN2⟩
      have hvnil : v = SExpr.nil := by
        rw [hveq, hcvnil, hevnil]
        rfl
      have hc := sound _ v hv
      rw [hvnil] at hc
      exact hc
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case4 ifS t1 t2 t3 hname hnt3 hnt2 houter =>
    intro hl hnil
    have hlist : clausifyPure ((SExpr.atom (Atom.symbol ifS)).cons
        (t1.cons (t2.cons (t3.cons SExpr.nil)))) true
        = [(SExpr.atom (Atom.symbol ifS)).cons
            (t1.cons (t2.cons (t3.cons SExpr.nil)))] := by
      rw [clausifyPure.eq_def]
      simp [hname, hnt3, hnt2]
      simpa using houter
    exact hnil _ (hlist ▸ List.mem_singleton_self _)
  | case5 pos ifS t1 t2 t3 hname hnpos ht3 houter ih2 ih1 =>
    intro hl hnil
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t3 = quoteNil := eq_of_beq ht3
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : ev = SExpr.nil :=
        Option.some.inj (hev.symm.trans (dpLiftF_quote hwf SExpr.nil))
      rw [clausifyPure.eq_def] at hnil
      simp only [houter, hname, ht3, if_true] at hnil
      have hL := fun l hl => hnil l (List.mem_append_left _ hl)
      have hR := fun l hl => hnil l (List.mem_append_right _ hl)
      -- t1 true, t2 true: v = cond (toBool cv) tv nil with cv ≠ nil → v = tv ≠ nil
      have hcvne : cv ≠ SExpr.nil :=
        ne_nil_of_evtrue_conv
          (ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL) (sound t1 cv hcv)
      have htvne : tv ≠ SExpr.nil :=
        ne_nil_of_evtrue_conv
          (ih1 (Option.isSome_iff_exists.mpr ⟨tv, htv⟩) hR) (sound t2 tv htv)
      have hvne : v ≠ SExpr.nil := by
        rw [hveq, toBool_true_of_ne_nil hcvne]
        simpa using htvne
      exact evtrue_of_conv_ne_nil (sound _ v hv) hvne
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case6 pos ifS t1 t2 t3 hname hnpos hnt3 ht2 houter ih2 ih1 =>
    intro hl hnil
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t2 = quoteNil := eq_of_beq ht2
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : tv = SExpr.nil :=
        Option.some.inj (htv.symm.trans (dpLiftF_quote hwf SExpr.nil))
      rw [clausifyPure.eq_def] at hnil
      simp only [houter, hname, hnt3, ht2, if_true] at hnil
      have hL := fun l hl => hnil l (List.mem_append_left _ hl)
      have hR := fun l hl => hnil l (List.mem_append_right _ hl)
      -- t1 nil, t3 true: v = cond (toBool cv) nil ev = ev ≠ nil
      obtain ⟨N1, hN1⟩ := ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL
      have hcvnil : cv = SExpr.nil := val_unique (sound t1 cv hcv) ⟨N1, hN1⟩
      have hevne : ev ≠ SExpr.nil :=
        ne_nil_of_evtrue_conv
          (ih1 (Option.isSome_iff_exists.mpr ⟨ev, hev⟩) hR) (sound t3 ev hev)
      have hvne : v ≠ SExpr.nil := by
        rw [hveq, hcvnil]
        simpa using hevne
      exact evtrue_of_conv_ne_nil (sound _ v hv) hvne
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case7 pos ifS t1 t2 t3 hname hnpos hnt3 hnt2 houter =>
    intro hl hnil
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    have hlist : clausifyPure ((SExpr.atom (Atom.symbol ifS)).cons
        (t1.cons (t2.cons (t3.cons SExpr.nil)))) false
        = [dumbNegateLit ((SExpr.atom (Atom.symbol ifS)).cons
            (t1.cons (t2.cons (t3.cons SExpr.nil))))] := by
      rw [clausifyPure.eq_def]
      simp [hname, hnt3, hnt2]
      simpa using houter
    exact neg_leaf_false_sound w env hvars hopq hns hwf _ hl
      (hnil _ (hlist ▸ List.mem_singleton_self _))
  | case8 ifS t1 t2 t3 hnname houter =>
    intro hl hnil
    have hlist : clausifyPure ((SExpr.atom (Atom.symbol ifS)).cons
        (t1.cons (t2.cons (t3.cons SExpr.nil)))) true
        = [(SExpr.atom (Atom.symbol ifS)).cons
            (t1.cons (t2.cons (t3.cons SExpr.nil)))] := by
      rw [clausifyPure.eq_def]
      simp [hnname]
      simpa using houter
    exact hnil _ (hlist ▸ List.mem_singleton_self _)
  | case9 pos ifS t1 t2 t3 hnname hnpos houter =>
    intro hl hnil
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    have hlist : clausifyPure ((SExpr.atom (Atom.symbol ifS)).cons
        (t1.cons (t2.cons (t3.cons SExpr.nil)))) false
        = [dumbNegateLit ((SExpr.atom (Atom.symbol ifS)).cons
            (t1.cons (t2.cons (t3.cons SExpr.nil))))] := by
      rw [clausifyPure.eq_def]
      simp [hnname]
      simpa using houter
    exact neg_leaf_false_sound w env hvars hopq hns hwf _ hl
      (hnil _ (hlist ▸ List.mem_singleton_self _))
  | case10 t hnshape houter =>
    intro hl hnil
    have hlist : clausifyPure t true = [t] := by
      rw [clausifyPure.eq_def]
      have houter' : (t == quoteNil) = false := by simpa using houter
      simp only [reduceIte, houter', Bool.false_eq_true, if_false]
    exact hnil _ (hlist ▸ List.mem_singleton_self _)
  | case11 t pos houter hnpos hnshape =>
    intro hl hnil
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    have hlist : clausifyPure t false = [dumbNegateLit t] := by
      rw [clausifyPure.eq_def]
      have houter' : (t == quoteT) = false := by simpa using houter
      simp only [houter', Bool.false_eq_true, if_false]
    exact neg_leaf_false_sound w env hvars hopq hns hwf _ hl
      (hnil _ (hlist ▸ List.mem_singleton_self _))

/-- G3 Fragment B, THE BRIDGE LEMMA (once-proved; replaces the per-leaf
    `peelClause`/`walkPosT`/`val*` walkers): a true output clause gives the
    clausify input's truth (pos) / falsity (neg). World-parametric (L3);
    premised on Fragment A's lift fact (D-B1) and the key well-formedness
    (D-B4). -/
theorem clausifyPure_sound (w : World) (env : Env)
    {vars : List (Symbol × SExpr)} {opq : List (SExpr × SExpr)}
    (hvars : ∀ q ∈ vars,
      ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol q.1)) = some q.2)
    (hopq : ∀ p ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hns : dpNoShadow w) (hwf : dpOpqWF opq = true) :
    ∀ t pos, (dpLiftF vars opq t).isSome →
      EvTrue w env (disjoinTerm (clausifyPure t pos)) →
      ClausifyGoal w env t pos := by
  have sound := dpLiftF_sound w env vars opq hvars hopq hns
  have litconvs : ∀ (u : SExpr) (b : Bool), (dpLiftF vars opq u).isSome →
      ∀ l ∈ clausifyPure u b, ∃ vl, ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl :=
    fun u b hu l hl => by
      obtain ⟨vl, hvl⟩ :=
        Option.isSome_iff_exists.mp (clausifyPure_lifts hwf u b hu l hl)
      exact ⟨vl, sound l vl hvl⟩
  intro t pos
  induction t, pos using clausifyPure.induct with
  | case1 t pos hguard =>
    intro _ hdis
    rw [clausifyPure.eq_def] at hdis
    simp only [hguard, if_true] at hdis
    exact absurd hdis (not_evtrue_disjoin_nil w env)
  | case2 ifS t1 t2 t3 hname ht3 houter ih2 ih1 =>
    intro hl hdis
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t3 = quoteT := eq_of_beq ht3
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : ev = SExpr.t :=
        Option.some.inj (hev.symm.trans (dpLiftF_quote hwf SExpr.t))
      rw [clausifyPure.eq_def] at hdis
      simp only [hname, ht3, if_true] at hdis
      rcases evtrue_disjoin_append_elim w env _ _
        (litconvs t1 false (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩)) hdis
        with hL | hR
      · -- t1 false ⇒ cv = nil ⇒ v = 't
        obtain ⟨N1, hN1⟩ := ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL
        have hcvnil : cv = SExpr.nil :=
          val_unique (sound t1 cv hcv) ⟨N1, hN1⟩
        have hvt : v = SExpr.t := by
          rw [hveq, hcvnil]
          rfl
        exact evtrue_of_conv_ne_nil (hvt ▸ sound _ v hv) (by simp [SExpr.t])
      · -- t2 true ⇒ tv ≠ nil ⇒ v ≠ nil either way
        have htvne : tv ≠ SExpr.nil :=
          ne_nil_of_evtrue_conv
            (ih1 (Option.isSome_iff_exists.mpr ⟨tv, htv⟩) hR) (sound t2 tv htv)
        have hvne : v ≠ SExpr.nil := by
          rw [hveq]
          cases Logic.toBool cv
          · simp [SExpr.t]
          · simpa using htvne
        exact evtrue_of_conv_ne_nil (sound _ v hv) hvne
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case3 ifS t1 t2 t3 hname hnt3 ht2 houter ih2 ih1 =>
    intro hl hdis
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t2 = quoteT := eq_of_beq ht2
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : tv = SExpr.t :=
        Option.some.inj (htv.symm.trans (dpLiftF_quote hwf SExpr.t))
      rw [clausifyPure.eq_def] at hdis
      simp only [hname, hnt3, ht2, if_true] at hdis
      rcases evtrue_disjoin_append_elim w env _ _
        (litconvs t1 true (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩)) hdis
        with hL | hR
      · -- t1 true ⇒ cv ≠ nil ⇒ v = 't
        have hcvne : cv ≠ SExpr.nil :=
          ne_nil_of_evtrue_conv
            (ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL) (sound t1 cv hcv)
        have hvt : v = SExpr.t := by
          rw [hveq, toBool_true_of_ne_nil hcvne]
          rfl
        exact evtrue_of_conv_ne_nil (hvt ▸ sound _ v hv) (by simp [SExpr.t])
      · -- t3 true ⇒ ev ≠ nil ⇒ v ≠ nil either way
        have hevne : ev ≠ SExpr.nil :=
          ne_nil_of_evtrue_conv
            (ih1 (Option.isSome_iff_exists.mpr ⟨ev, hev⟩) hR) (sound t3 ev hev)
        have hvne : v ≠ SExpr.nil := by
          rw [hveq]
          cases Logic.toBool cv
          · simpa using hevne
          · simp [SExpr.t]
        exact evtrue_of_conv_ne_nil (sound _ v hv) hvne
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case4 ifS t1 t2 t3 hname hnt3 hnt2 houter =>
    intro hl hdis
    rw [clausifyPure.eq_def] at hdis
    simp [hname, hnt3, hnt2] at hdis
    rw [if_neg (show ¬((SExpr.atom (Atom.symbol ifS)).cons
      (t1.cons (t2.cons (t3.cons SExpr.nil))) = quoteNil) by
        simpa using houter)] at hdis
    exact hdis
  | case5 pos ifS t1 t2 t3 hname hnpos ht3 houter ih2 ih1 =>
    intro hl hdis
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t3 = quoteNil := eq_of_beq ht3
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : ev = SExpr.nil :=
        Option.some.inj (hev.symm.trans (dpLiftF_quote hwf SExpr.nil))
      rw [clausifyPure.eq_def] at hdis
      simp only [houter, hname, ht3, if_true] at hdis
      rcases evtrue_disjoin_append_elim w env _ _
        (litconvs t1 false (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩)) hdis
        with hL | hR
      · -- t1 false ⇒ cv = nil ⇒ v = nil
        obtain ⟨N1, hN1⟩ := ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL
        have hcvnil : cv = SExpr.nil :=
          val_unique (sound t1 cv hcv) ⟨N1, hN1⟩
        have hvnil : v = SExpr.nil := by
          rw [hveq, hcvnil]
          rfl
        have hc := sound _ v hv
        rw [hvnil] at hc
        exact hc
      · -- t2 false ⇒ tv = nil ⇒ v = nil either way
        obtain ⟨N2, hN2⟩ := ih1 (Option.isSome_iff_exists.mpr ⟨tv, htv⟩) hR
        have htvnil : tv = SExpr.nil :=
          val_unique (sound t2 tv htv) ⟨N2, hN2⟩
        have hvnil : v = SExpr.nil := by
          rw [hveq, htvnil]
          cases Logic.toBool cv <;> rfl
        have hc := sound _ v hv
        rw [hvnil] at hc
        exact hc
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case6 pos ifS t1 t2 t3 hname hnpos hnt3 ht2 houter ih2 ih1 =>
    intro hl hdis
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    by_cases hfull : ifS = ({ name := "IF" } : Symbol)
    · subst hfull
      obtain rfl : t2 = quoteNil := eq_of_beq ht2
      obtain ⟨cv, tv, ev, hcv, htv, hev, hveq⟩ := dpLiftF_if_inv hwf hv
      obtain rfl : tv = SExpr.nil :=
        Option.some.inj (htv.symm.trans (dpLiftF_quote hwf SExpr.nil))
      rw [clausifyPure.eq_def] at hdis
      simp only [houter, hname, hnt3, ht2, if_true] at hdis
      rcases evtrue_disjoin_append_elim w env _ _
        (litconvs t1 true (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩)) hdis
        with hL | hR
      · -- t1 true ⇒ cv ≠ nil ⇒ v = nil (the then-branch is 'nil)
        have hcvne : cv ≠ SExpr.nil :=
          ne_nil_of_evtrue_conv
            (ih2 (Option.isSome_iff_exists.mpr ⟨cv, hcv⟩) hL) (sound t1 cv hcv)
        have hvnil : v = SExpr.nil := by
          rw [hveq, toBool_true_of_ne_nil hcvne]
          rfl
        have hc := sound _ v hv
        rw [hvnil] at hc
        exact hc
      · -- t3 false ⇒ ev = nil ⇒ v = nil either way
        obtain ⟨N2, hN2⟩ := ih1 (Option.isSome_iff_exists.mpr ⟨ev, hev⟩) hR
        have hevnil : ev = SExpr.nil :=
          val_unique (sound t3 ev hev) ⟨N2, hN2⟩
        have hvnil : v = SExpr.nil := by
          rw [hveq, hevnil]
          cases Logic.toBool cv <;> rfl
        have hc := sound _ v hv
        rw [hvnil] at hc
        exact hc
    · rw [dpLiftF_ifname_none hwf _ (by simpa using hname) hfull] at hv
      cases hv
  | case7 pos ifS t1 t2 t3 hname hnpos hnt3 hnt2 houter =>
    intro hl hdis
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    rw [clausifyPure.eq_def] at hdis
    simp [hname, hnt3, hnt2] at hdis
    rw [if_neg (show ¬((SExpr.atom (Atom.symbol ifS)).cons
      (t1.cons (t2.cons (t3.cons SExpr.nil))) = quoteT) by
        simpa using houter)] at hdis
    exact sound_neg_leaf w env hvars hopq hns hwf _ hl hdis
  | case8 ifS t1 t2 t3 hnname houter =>
    intro hl hdis
    rw [clausifyPure.eq_def] at hdis
    simp [hnname] at hdis
    rw [if_neg (show ¬((SExpr.atom (Atom.symbol ifS)).cons
      (t1.cons (t2.cons (t3.cons SExpr.nil))) = quoteNil) by
        simpa using houter)] at hdis
    exact hdis
  | case9 pos ifS t1 t2 t3 hnname hnpos houter =>
    intro hl hdis
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    rw [clausifyPure.eq_def] at hdis
    simp [hnname] at hdis
    rw [if_neg (show ¬((SExpr.atom (Atom.symbol ifS)).cons
      (t1.cons (t2.cons (t3.cons SExpr.nil))) = quoteT) by
        simpa using houter)] at hdis
    exact sound_neg_leaf w env hvars hopq hns hwf _ hl hdis
  | case10 t hnshape houter =>
    intro hl hdis
    rw [clausifyPure.eq_def] at hdis
    split at hdis
    · -- the leaf arm with the outer guard retained
      have houter' : (t == quoteNil) = false := by simpa using houter
      rw [houter'] at hdis
      simp only [Bool.false_eq_true, if_false] at hdis
      exact hdis
    · exact absurd rfl (by assumption)
  | case11 t pos houter hnpos hnshape =>
    intro hl hdis
    have hposf : pos = false := by simpa using hnpos
    subst hposf
    rw [clausifyPure.eq_def] at hdis
    split at hdis
    · exact absurd (by assumption : false = true) (by decide)
    · have houter' : (t == quoteT) = false := by simpa using houter
      rw [houter'] at hdis
      simp only [Bool.false_eq_true, if_false] at hdis
      exact sound_neg_leaf w env hvars hopq hns hwf _ hl hdis

end ACL2.Replay
