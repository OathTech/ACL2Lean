/-
  G3 Fragment A — the DP value lift as a VERIFIED PURE FUNCTION.

  `dpLiftF` computes the lifted `Logic`-primitive value of a clause term over
  the env's variable values and a pinned-opaque assoc list — the pure twin of
  the driver's `dpValExpr` meta-walker, with the SAME fixed primitive table
  and the SAME frontiers (an unknown head returns `none`; the caller
  hard-fails exactly as the walker did). `dpLiftF_sound` is the once-proved
  soundness lemma (G3: the walker's per-node `mkAppM` proof chains are
  replaced by ONE lemma instantiation over a kernel-computable function).

  D-A4: primitive/special heads are recognized by FULL symbol equality
  against the default-package (`ACL2`) symbols — a non-ACL2-package `if`/
  `car`/… occurrence is a FRONTIER (`none`), not a lift. (The walker
  de-facto rejected those too: its lemma applications only unify at the
  default-package symbols; the whole corpus is ACL2-package.)

  Fragment-local per invariant L1 (own function, own lemma, composes at the
  convergence-judgment layer); world-parametric per L3 (the world enters
  only through the no-shadow premises). Design + decisions:
  docs/plans/2026-06-12_g3-consolidations.md.
-/
import ACL2Lean.Replay.EvalLemmas

namespace ACL2.Replay

open ACL2

/-- The DP-lift primitive heads (the FIXED table — mirrors the driver's
    `dpUnary`/`dpBinary`; anything else with a symbol head is opaque). -/
def dpLiftHeads : List String :=
  ["not", "zp", "consp", "integerp", "acl2-numberp", "true-listp", "car",
   "cdr", "equal", "<", "binary-+", "binary-*", "cons", "implies", "iff"]

/-- The DP value lift (G3 Fragment A): opaque application values from `opq`
    (syntactic `==` lookup, checked FIRST — the walker's order), variable
    values from `env` (with ACL2's t/nil self-evaluation for unbound symbols,
    mirroring `evalOpt`'s variable case exactly), `quote` transparent, `if`
    STRICT in both branches (the walker's value-characterized form:
    `cond (toBool cv) tv ev`), and the fixed primitive table via
    `callBuiltin` (alignment with the evaluator by construction). An unknown
    shape is `none` — the FRONTIER, not a default: the caller hard-fails on
    it exactly as `dpValExpr` did. -/
def dpLiftF (env : Env) (opq : List (SExpr × SExpr)) (t : SExpr) :
    Option SExpr :=
  match opq.find? (fun p => p.1 == t) with
  | some p => some p.2
  | none =>
    match t with
    | .atom (.symbol s) =>
      match env.get? s with
      | some v => some v
      | none => if s.isNamed "t" then some SExpr.t else some SExpr.nil
    | .cons (.atom (.symbol fs)) args =>
      if fs == { name := "quote" } then
        match args with
        | .cons v .nil => some v
        | _ => none
      else if fs == { name := "if" } then
        match args with
        | .cons c (.cons thn (.cons els .nil)) => do
          let cv ← dpLiftF env opq c
          let tv ← dpLiftF env opq thn
          let ev ← dpLiftF env opq els
          some (cond (Logic.toBool cv) tv ev)
        | _ => none
      else if fs.package == "ACL2" && dpLiftHeads.contains fs.name then
        match args with
        | .cons a .nil => do
          let av ← dpLiftF env opq a
          callBuiltin fs.name [av]
        | .cons a (.cons b .nil) => do
          let av ← dpLiftF env opq a
          let bv ← dpLiftF env opq b
          callBuiltin fs.name [av, bv]
        | _ => none
      else none
    | _ => none

/-- Every DP-lift head NAME is none of the evaluator's special-form names
    (the fixed table is closed: one `decide`). -/
theorem dpLiftHeads_not_special :
    ∀ n ∈ dpLiftHeads,
      ((n == "quote") = false) ∧ ((n == "if") = false) ∧
      ((n == "let") = false) ∧ ((n == "let*") = false) := by decide

/-- G3 Fragment A, THE soundness lemma (once-proved; replaces the walker's
    per-node proof chains): a `dpLiftF` value is the term's eventual
    evaluation, given the opaque convergences and that the world shadows no
    primitive head. World-parametric (L3). -/
theorem dpLiftF_sound (w : World) (env : Env) (opq : List (SExpr × SExpr))
    (hopq : ∀ p ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hns : ∀ n ∈ dpLiftHeads, w.defs.get? { name := n } = none) :
    ∀ t v, dpLiftF env opq t = some v →
      ∃ N, ∀ f ≥ N, evalOpt f w env t = some v := by
  intro t
  induction t using dpLiftF.induct (env := env) (opq := opq) with
  | case1 t p hfind =>
    -- opaque hit: the value is the pinned one; convergence from `hopq`
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    obtain rfl := Option.some.inj h
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred : p.1 == t := by simpa using List.find?_some hfind
    exact eq_of_beq hpred ▸ hopq p hmem
  | case2 s v0 hget hfind =>
    -- bound variable
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hget] at h
    obtain rfl := Option.some.inj h
    exact ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w env s _ hget⟩
  | case3 s hget hT hfind =>
    -- unbound, self-evaluating `t`
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hget, hT, if_true] at h
    obtain rfl := Option.some.inj h
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [evalOpt, evalOptStep, hget, hT]
  | case4 s hget hnT hfind =>
    -- unbound, nil-evaluating
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hget, hnT] at h
    obtain rfl := Option.some.inj h
    exact ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var_unbound g w env s hget (by simpa using hnT)⟩
  | case5 fs hq v0 hfind =>
    -- well-formed quote
    obtain rfl : fs = { name := "quote" } := eq_of_beq hq
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [BEq.rfl, if_true] at h
    obtain rfl := Option.some.inj h
    exact ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_quote g w env _⟩
  | case6 fs args hq hmal hfind =>
    -- malformed quote: the lift is `none` (frontier)
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hq, if_true] at h
    cases h
  | case7 fs hnq hif c thn els hfind ih3 ih2 ih1 =>
    -- well-formed if: strict both-branch lift, `re_val_if`
    obtain rfl : fs = { name := "if" } := eq_of_beq hif
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hif, if_true] at h
    obtain ⟨cv, hcv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tv, htv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ev, hev, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    exact re_val_if w env c thn els cv tv ev (ih3 _ hcv) (ih2 _ htv) (ih1 _ hev)
  | case8 fs args hnq hif hmal hfind =>
    -- malformed if
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hif, if_true] at h
    split at h <;> first | cases h | simp_all
  | case9 fs hnq hnif hprim a hfind ih1 =>
    -- unary primitive via callBuiltin
    have hsplit := hprim
    simp only [Bool.and_eq_true] at hsplit
    obtain ⟨hpkg, hcont⟩ := hsplit
    obtain ⟨pkg, name⟩ := fs
    obtain rfl : pkg = "ACL2" := eq_of_beq hpkg
    have hmem : name ∈ dpLiftHeads := by
      simpa using hcont
    obtain ⟨h1, h2, h3, h4⟩ := dpLiftHeads_not_special name hmem
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hnif, hprim, if_true] at h
    obtain ⟨av, hav, hcb⟩ := Option.bind_eq_some_iff.mp h
    exact conv_builtin1 w env _ a av v
      ⟨by simpa [Symbol.isNamed] using h1, by simpa [Symbol.isNamed] using h2,
       by simpa [Symbol.isNamed] using h3, by simpa [Symbol.isNamed] using h4⟩
      (hns name hmem) (ih1 _ hav) hcb
  | case10 fs hnq hnif hprim a b hfind ih2 ih1 =>
    -- binary primitive via callBuiltin
    have hsplit := hprim
    simp only [Bool.and_eq_true] at hsplit
    obtain ⟨hpkg, hcont⟩ := hsplit
    obtain ⟨pkg, name⟩ := fs
    obtain rfl : pkg = "ACL2" := eq_of_beq hpkg
    have hmem : name ∈ dpLiftHeads := by
      simpa using hcont
    obtain ⟨h1, h2, h3, h4⟩ := dpLiftHeads_not_special name hmem
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hnif, hprim, if_true] at h
    obtain ⟨av, hav, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bv, hbv, hcb⟩ := Option.bind_eq_some_iff.mp h
    exact conv_builtin2 w env _ a b av bv v
      ⟨by simpa [Symbol.isNamed] using h1, by simpa [Symbol.isNamed] using h2,
       by simpa [Symbol.isNamed] using h3, by simpa [Symbol.isNamed] using h4⟩
      (hns name hmem) (ih2 _ hav) (ih1 _ hbv) hcb
  | case11 fs args hnq hnif hprim hmal1 hmal2 hfind =>
    -- primitive with malformed arity
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hnif, hprim, if_true] at h
    split at h <;> cases h
  | case12 fs args hnq hnif hnprim hfind =>
    -- unknown head: frontier
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hnif, hnprim] at h
    cases h
  | case13 t hfind hnatom hncons =>
    -- non-symbol shapes: frontier
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    rcases t with _ | a | ⟨hd, tl⟩
    · cases h
    · rcases a with s | _ | _ | _
      · exact absurd rfl (hnatom s)
      all_goals cases h
    · rcases hd with _ | a' | _
      · cases h
      · rcases a' with s' | _ | _ | _
        · exact absurd rfl (hncons s' tl)
        all_goals cases h
      · cases h

end ACL2.Replay
