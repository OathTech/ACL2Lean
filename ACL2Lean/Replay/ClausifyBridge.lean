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
def quoteT : SExpr := .cons (.atom (.symbol { name := "quote" })) (.cons SExpr.t .nil)

/-- `(quote nil)`. -/
def quoteNil : SExpr := .cons (.atom (.symbol { name := "quote" })) (.cons .nil .nil)

/-- ACL2's `disjoin` of a literal list: `(if l₁ 't (if l₂ 't … lₖ))`; a singleton
    is the literal itself; the empty clause is `'nil` (false). -/
def disjoinTerm : List SExpr → SExpr
  | [] => .cons (.atom (.symbol { name := "quote" })) (.cons .nil .nil)
  | [l] => l
  | l :: rest =>
    .cons (.atom (.symbol { name := "if" }))
      (.cons l (.cons quoteT (.cons (disjoinTerm rest) .nil)))

/-- ACL2's `dumb-negate-lit` (the pure fragment: strip a `not`, else wrap). -/
def dumbNegateLit (t : SExpr) : SExpr :=
  match t with
  | .cons (.atom (.symbol ns)) (.cons _ .nil) =>
    if ns.name == "not" then
      match t with
      | .cons _ (.cons inner .nil) => inner
      | _ => t
    else .cons (.atom (.symbol { name := "not" })) (.cons t .nil)
  | _ => .cons (.atom (.symbol { name := "not" })) (.cons t .nil)

/-- The PURE fragment of `clausify-input1` (no `expand-and-or`): `pos` is
    ACL2's `bool`. Recomputed for the walk and VALIDATED against the recorded
    checkpoints — divergence (an expansion fired) hard-fails upstream. -/
def clausifyPure (t : SExpr) (pos : Bool) : List SExpr :=
  if t == (if pos then quoteNil else quoteT) then []
  else match t with
  | .cons (.atom (.symbol ifS)) (.cons t1 (.cons t2 (.cons t3 .nil))) =>
    if ifS.name == "if" then
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
      ns.isNamed "not" = true ∧ dumbNegateLit t = x := by
  rcases t with _ | a | ⟨hd, tl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · rcases hd with _ | a' | _
    · exact Or.inl rfl
    · rcases a' with ns | _ | _ | _
      · rcases tl with _ | _ | ⟨x, tl2⟩
        · exact Or.inl rfl
        · exact Or.inl rfl
        · rcases tl2 with _ | _ | _
          · by_cases hname : ns.name = "not"
            · exact Or.inr ⟨ns, x, rfl, by simp [Symbol.isNamed, hname],
                by simp [dumbNegateLit, hname]⟩
            · exact Or.inl (by simp [dumbNegateLit, hname])
          · exact Or.inl rfl
          · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
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
    by_cases hfull : ns = ({ name := "not" } : Symbol)
    · subst hfull
      obtain ⟨xv, hxv, _⟩ := dpLiftF_not_inv hwf hv
      exact Option.isSome_iff_exists.mpr ⟨xv, hxv⟩
    · -- wrong-package not: the lift premise is refutable
      exfalso
      have hnn : ns.name = "not" := by simpa [Symbol.isNamed] using hname
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
    {ifS : Symbol} (args : SExpr) (hnn : ifS.name = "if")
    (hfull : ifS ≠ ({ name := "if" } : Symbol)) :
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
    by_cases hfull : ifS = ({ name := "if" } : Symbol)
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
    by_cases hfull : ifS = ({ name := "if" } : Symbol)
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
    by_cases hfull : ifS = ({ name := "if" } : Symbol)
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
    by_cases hfull : ifS = ({ name := "if" } : Symbol)
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

end ACL2.Replay
