import ACL2Lean.Replay.DpLift

namespace ACL2.Replay
open ACL2

/-- `(quote t)`, the result an equal-self literal reduces to. -/
def quoteT : SExpr := .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)

/-- `(quote nil)`. -/
def quoteNil : SExpr := .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)

/-- `(EQUAL x y)` shape. -/
abbrev equalAppCB (x y : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "EQUAL" })) (.cons x (.cons y .nil))

/-- ACL2's primitive literal negation: NOT stripping and equality with
quoted NIL on either side. Quote folding remains a checked frontier.
The existing NOT-by-name behavior is retained; its wrong-package case
cannot lift under the bridge's well-formedness premise. -/
def dumbNegateLit (t : SExpr) : SExpr :=
  match t with
  | .cons (.atom (.symbol ns)) (.cons x .nil) =>
    if ns.name == "NOT" then x else notT t
  | .cons (.atom (.symbol es)) (.cons x (.cons y .nil)) =>
    if es == ({name := "EQUAL"} : Symbol) then
      if y == quoteNil then x else if x == quoteNil then y else notT t
    else notT t
  | _ => notT t

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

/-- The syntactic arms used by the checked clausifier. -/
theorem dumbNegateLit_eq (t : SExpr) :
    dumbNegateLit t = notT t ∨
    (∃ ns x, t = .cons (.atom (.symbol ns)) (.cons x .nil) ∧
      ns.isNamed "NOT" = true ∧ dumbNegateLit t = x) ∨
    (∃ x, t = equalAppCB x quoteNil ∧ dumbNegateLit t = x) ∨
    (∃ x, t = equalAppCB quoteNil x ∧ dumbNegateLit t = x) := by
  rcases t with _ | a | ⟨hd, tl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · rcases hd with _ | a' | _
    · exact Or.inl rfl
    · rcases a' with ns | _ | _ | _ | _
      · rcases tl with _ | _ | ⟨x, tl2⟩
        · exact Or.inl rfl
        · exact Or.inl rfl
        · rcases tl2 with _ | _ | ⟨y, tl3⟩
          · by_cases hname : ns.name = "NOT"
            · exact Or.inr (Or.inl ⟨ns, x, rfl, by simp [Symbol.isNamed, hname],
                by simp [dumbNegateLit, hname]⟩)
            · exact Or.inl (by simp [dumbNegateLit, hname])
          · exact Or.inl rfl
          · rcases tl3 with _ | _ | _
            · by_cases he : ns = ({name := "EQUAL"} : Symbol)
              · subst ns
                by_cases hy : y = quoteNil
                · subst y
                  exact Or.inr (Or.inr (Or.inl ⟨x, rfl, by simp [dumbNegateLit]⟩))
                · by_cases hx : x = quoteNil
                  · subst x
                    exact Or.inr (Or.inr (Or.inr ⟨y, rfl, by simp [dumbNegateLit, hy]⟩))
                  · exact Or.inl (by simp [dumbNegateLit, hy, hx])
              · exact Or.inl (by simp [dumbNegateLit, he])
            · exact Or.inl rfl
            · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inl rfl

theorem dpLiftF_prim2 {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    (n : String) (x y : SExpr)
    (hban : ((({ name := n } : Symbol)).isNamed "QUOTE" ||
             (({ name := n } : Symbol)).isNamed "IF" ||
             dpLiftHeads.contains n) = true)
    (hnq : ((({ name := n } : Symbol)) == { name := "QUOTE" }) = false)
    (hnif : ((({ name := n } : Symbol)) == { name := "IF" }) = false)
    (hprim : ((({ name := n } : Symbol)).package == "ACL2" &&
              dpLiftHeads.contains n) = true) :
    dpLiftF vars opq
        (.cons (.atom (.symbol { name := n })) (.cons x (.cons y .nil)))
      = (dpLiftF vars opq x).bind (fun xv =>
          (dpLiftF vars opq y).bind (fun yv => callBuiltin n [xv, yv])) := by
  rw [dpLiftF.eq_def, dpOpqWF_find_banned opq hwf _ hban]
  simp only [hnq, hnif, hprim, if_true, if_false, Bool.false_eq_true]
  cases hx : dpLiftF vars opq x <;> cases hy : dpLiftF vars opq y <;> rfl

private theorem dpLiftF_equal_inv {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    {x y v : SExpr} (h : dpLiftF vars opq (equalAppCB x y) = some v) :
    ∃ xv yv, dpLiftF vars opq x = some xv ∧ dpLiftF vars opq y = some yv ∧
      v = Logic.equal xv yv := by
  rw [dpLiftF_prim2 hwf "EQUAL" x y (by decide) (by decide) (by decide) (by decide)] at h
  obtain ⟨xv, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨yv, hy, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨xv, yv, hx, hy, ?_⟩
  simpa using (Option.some.inj h).symm

/-- Literal negation preserves liftability and reverses truth. The stripped
value need not be Boolean, so the interface states truth rather than value
identity. All three negative-leaf bridges consume this shared fact. -/
theorem dumbNegateLit_lift {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    {t v : SExpr} (hv : dpLiftF vars opq t = some v) :
    ∃ nv, dpLiftF vars opq (dumbNegateLit t) = some nv ∧ (nv = .nil ↔ v ≠ .nil) := by
  rcases dumbNegateLit_eq t with hwrap | ⟨ns, x, hshape, hname, hstrip⟩ |
      ⟨x, hshape, hstrip⟩ | ⟨x, hshape, hstrip⟩
  · rw [hwrap]
    exact ⟨Logic.not v, dpLiftF_not_intro hwf hv, ⟨logic_not_nil_ne v, not_nil_of_truthy⟩⟩
  · rw [hstrip]
    subst hshape
    by_cases hfull : ns = ({name := "NOT"} : Symbol)
    · subst ns
      obtain ⟨xv, hxv, rfl⟩ := dpLiftF_not_inv hwf hv
      refine ⟨xv, hxv, ?_⟩
      constructor
      · rintro rfl
        decide
      · exact nil_of_logic_not_ne_nil
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
  · rw [hstrip]
    subst hshape
    obtain ⟨xv, zv, hx, hz, rfl⟩ := dpLiftF_equal_inv hwf hv
    have hzero : zv = .nil := by simpa only [quoteNil, dpLiftF_quote hwf, Option.some.injEq] using hz.symm
    subst zv
    exact ⟨xv, hx, (Logic.equal_ne_nil_iff xv .nil).symm⟩
  · rw [hstrip]
    subst hshape
    obtain ⟨zv, xv, hz, hx, rfl⟩ := dpLiftF_equal_inv hwf hv
    have hzero : zv = .nil := by simpa only [quoteNil, dpLiftF_quote hwf, Option.some.injEq] using hz.symm
    subst zv
    refine ⟨xv, hx, ?_⟩
    rw [Logic.equal_ne_nil_iff]
    exact eq_comm

/-- Every negative leaf lifts when its input does. -/
theorem lifts_leaf_neg {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true) (t : SExpr)
    (hl : (dpLiftF vars opq t).isSome) :
    ∀ l ∈ [dumbNegateLit t], (dpLiftF vars opq l).isSome := by
  intro l hmem
  rw [List.mem_singleton.mp hmem]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨nv, hn, _⟩ := dumbNegateLit_lift hwf hv
  exact Option.isSome_iff_exists.mpr ⟨nv, hn⟩

/-- A true negated literal makes the input converge to NIL. -/
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
  obtain ⟨nv, hn, hflip⟩ := dumbNegateLit_lift hwf hv
  have hne := ne_nil_of_evtrue_conv hdis (dpLiftF_sound w env vars opq hvars hopq hns _ _ hn)
  have hvnil : v = .nil := by
    by_contra h
    exact hne (hflip.mpr h)
  exact hvnil ▸ dpLiftF_sound w env vars opq hvars hopq hns t v hv

/-- A false negated literal makes the input true. -/
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
  obtain ⟨nv, hn, hflip⟩ := dumbNegateLit_lift hwf hv
  have hnv := val_unique (dpLiftF_sound w env vars opq hvars hopq hns _ _ hn) hnil
  exact evtrue_of_conv_ne_nil (dpLiftF_sound w env vars opq hvars hopq hns t v hv) (hflip.mp hnv)

end ACL2.Replay
