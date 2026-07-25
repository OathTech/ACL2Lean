/-
  G3 Fragment A — the DP value lift as a VERIFIED PURE FUNCTION.

  `dpLiftF` computes the lifted `Logic`-primitive value of a clause term over
  explicit VARIABLE and OPAQUE value assoc lists — the pure twin of the
  driver's `dpValExpr` meta-walker, with the SAME fixed primitive table (an
  unknown head returns `none`; the caller hard-fails exactly as the walker
  did). ONE deliberate asymmetry (S2, 2026-07-25): `dpValExpr` additionally
  beta-reduces translated-`let` LAMBDA applications; `dpLiftF` does not (the
  reduct is not a structural subterm, so a lambda arm is a termination-design
  question this verified function has not taken on). The DP-leaf path guards
  the gap by NAME — `dpLiftProof` frontiers a lambda-bearing leaf before the
  reduction check (`Driver/Discharge.lean`), so the divergence error there
  still means a real defect. `dpLiftF_sound` is the once-proved soundness
  lemma (G3: the walker's per-node `mkAppM` proof chains are replaced by ONE
  lemma instantiation).

  D-A4: primitive/special heads are recognized by FULL symbol equality
  against the default-package (`ACL2`) symbols — a non-ACL2-package `if`/
  `car`/… occurrence is a FRONTIER (`none`), not a lift. (For `if` the old
  walker behaved the same — `re_val_if` only unifies at the default-package
  symbol — but for primitives it dispatched by NAME (`conv_builtin1/2` take
  an arbitrary symbol), so this is a deliberate frontier NARROWING:
  fail-closed, and the whole corpus is ACL2-package so the golden table is
  unaffected.)

  D-A5 (discovered at consumer wiring): variables take their values from an
  explicit assoc list `vars` — NOT from an `Env` parameter — because the
  harness's env is a QUANTIFIED FVAR: `env.get?` would be symbolically
  stuck, while assoc lookup over CONCRETE keys reduces even with symbolic
  (fvar) VALUES embedded, so the driver discharges the
  `dpLiftF vars opq t = some v` fact by `Eq.refl`/defeq. The lemma's
  premise ties each entry to its variable's convergence; a variable absent
  from `vars` is a frontier (`none`).

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
  ["NOT", "ZP", "CONSP", "INTEGERP", "ACL2-NUMBERP", "RATIONALP",
   "TRUE-LISTP", "CAR", "CDR", "SYMBOLP", "STRINGP", "BOOLEANP", "NFIX",
   "FIX", "LEN", "ENDP", "ATOM", "EQUAL", "<", "LEXORDER", "BINARY-+",
   "BINARY-*", "CONS", "IMPLIES", "IFF"]

/-- The DP value lift (G3 Fragment A): opaque application values from `opq`
    (syntactic `==` lookup, checked FIRST — the walker's order), variable
    values from `vars` (D-A5), `quote` transparent, `if` STRICT in both
    branches (the walker's value-characterized form:
    `cond (toBool cv) tv ev`), and the fixed primitive table via
    `callBuiltin` (alignment with the evaluator by construction). An unknown
    shape is `none` — the FRONTIER, not a default: the caller hard-fails on
    it exactly as `dpValExpr` did. -/
def dpLiftF (vars : List (Symbol × SExpr)) (opq : List (SExpr × SExpr))
    (t : SExpr) : Option SExpr :=
  match opq.find? (fun p => p.1 == t) with
  | some p => some p.2
  | none =>
    match t with
    | .atom (.symbol s) =>
      match vars.find? (fun q => q.1 == s) with
      | some q => some q.2
      | none => none
    | .cons (.atom (.symbol fs)) args =>
      if fs == { name := "QUOTE" } then
        match args with
        | .cons v .nil => some v
        | _ => none
      else if fs == { name := "IF" } then
        match args with
        | .cons c (.cons thn (.cons els .nil)) => do
          let cv ← dpLiftF vars opq c
          let tv ← dpLiftF vars opq thn
          let ev ← dpLiftF vars opq els
          some (cond (Logic.toBool cv) tv ev)
        | _ => none
      else if fs.package == "ACL2" && dpLiftHeads.contains fs.name then
        match args with
        | .cons a .nil => do
          let av ← dpLiftF vars opq a
          callBuiltin fs.name [av]
        | .cons a (.cons b .nil) => do
          let av ← dpLiftF vars opq a
          let bv ← dpLiftF vars opq b
          callBuiltin fs.name [av, bv]
        | _ => none
      else none
    | _ => none

/-- Every DP-lift head NAME is none of the evaluator's special-form names
    (the fixed table is closed: one `decide`). -/
theorem dpLiftHeads_not_special :
    ∀ n ∈ dpLiftHeads,
      ((n == "QUOTE") = false) ∧ ((n == "IF") = false) ∧
      ((n == "LET") = false) ∧ ((n == "LET*") = false) := by decide

/-- The world shadows none of the DP-lift primitive heads — DECIDABLE, so
    the driver discharges it with one kernel `decide` per world. -/
def dpNoShadow (w : World) : Prop :=
  ∀ n ∈ dpLiftHeads, w.defs.get? { name := n } = none

instance (w : World) : Decidable (dpNoShadow w) := by
  unfold dpNoShadow; infer_instance

/-- G3 Fragment A, THE soundness lemma (once-proved; replaces the walker's
    per-node proof chains): a `dpLiftF` value is the term's eventual
    evaluation, given the variable and opaque convergences and that the
    world shadows no primitive head. World-parametric (L3). -/
theorem dpLiftF_sound (w : World) (env : Env)
    (vars : List (Symbol × SExpr)) (opq : List (SExpr × SExpr))
    (hvars : ∀ q ∈ vars,
      ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol q.1)) = some q.2)
    (hopq : ∀ p ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hns : dpNoShadow w) :
    ∀ t v, dpLiftF vars opq t = some v →
      ∃ N, ∀ f ≥ N, evalOpt f w env t = some v := by
  intro t
  induction t using dpLiftF.induct (vars := vars) (opq := opq) with
  | case1 t p hfind =>
    -- opaque hit: the value is the pinned one; convergence from `hopq`
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    obtain rfl := Option.some.inj h
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred : p.1 == t := by simpa using List.find?_some hfind
    exact eq_of_beq hpred ▸ hopq p hmem
  | case2 s q hfindv hfind =>
    -- variable hit: convergence from `hvars`
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hfindv] at h
    obtain rfl := Option.some.inj h
    have hmem := List.mem_of_find?_eq_some hfindv
    have hpred : q.1 == s := by simpa using List.find?_some hfindv
    exact eq_of_beq hpred ▸ hvars q hmem
  | case3 s hfindv hfind =>
    -- variable miss: frontier
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hfindv] at h
    cases h
  | case4 fs hq v0 hfind =>
    -- well-formed quote
    obtain rfl : fs = { name := "QUOTE" } := eq_of_beq hq
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [BEq.rfl, if_true] at h
    obtain rfl := Option.some.inj h
    exact ⟨1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_quote g w env _⟩
  | case5 fs args hq hmal hfind =>
    -- malformed quote: the lift is `none` (frontier)
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hq, if_true] at h
    cases h
  | case6 fs hnq hif c thn els hfind ih3 ih2 ih1 =>
    -- well-formed if: strict both-branch lift, `re_val_if`
    obtain rfl : fs = { name := "IF" } := eq_of_beq hif
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hif, if_true] at h
    obtain ⟨cv, hcv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tv, htv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ev, hev, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    exact re_val_if w env c thn els cv tv ev (ih3 _ hcv) (ih2 _ htv) (ih1 _ hev)
  | case7 fs args hnq hif hmal hfind =>
    -- malformed if
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hif, if_true] at h
    split at h <;> first | cases h | simp_all
  | case8 fs hnq hnif hprim a hfind ih1 =>
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
  | case9 fs hnq hnif hprim a b hfind ih2 ih1 =>
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
  | case10 fs args hnq hnif hprim hmal1 hmal2 hfind =>
    -- primitive with malformed arity
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hnif, hprim, if_true] at h
    split at h <;> cases h
  | case11 fs args hnq hnif hnprim hfind =>
    -- unknown head: frontier
    intro v h
    rw [dpLiftF.eq_def, hfind] at h
    simp only [hnq, hnif, hnprim] at h
    cases h
  | case12 t hfind hnatom hncons =>
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

/-! ## Lift-fact extraction (Fragment B's interface, D-B4)

The clausify bridge recurses through `if`-structure and `not`-wraps; to
thread the lift premise it needs (a) opaque keys to be genuine USER-FN
applications — never special forms or table primitives (matching
`collectOpaques`' construction; DECIDABLE, one check per leaf) — and
(b) inversion/introduction lemmas for the `if` and `not` arms. -/

/-- An opaque key must be an application whose head NAME is neither a
    special form's nor a table primitive's (NAME-based, any package —
    matching `collectOpaques`' name-based collection, D-B4 refined). -/
def dpOpqKeyOk : SExpr → Bool
  | .cons (.atom (.symbol fs)) _ =>
    !(fs.isNamed "QUOTE") && !(fs.isNamed "IF") &&
    !(dpLiftHeads.contains fs.name)
  | _ => false

/-- All opaque keys well-formed (decidable; the driver checks it once per
    leaf alongside `dpNoShadow`). -/
def dpOpqWF (opq : List (SExpr × SExpr)) : Bool :=
  opq.all (fun p => dpOpqKeyOk p.1)

/-- The `if` term shape. -/
abbrev ifT (c thn els : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil)))

/-- The `not` term shape. -/
abbrev notT (x : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "NOT" })) (.cons x .nil)

/-- A banned-NAME application is never an opaque key under WF. -/
theorem dpOpqWF_find_banned (opq : List (SExpr × SExpr))
    (hwf : dpOpqWF opq = true) {fs : Symbol} (args : SExpr)
    (hban : (fs.isNamed "QUOTE" || fs.isNamed "IF" ||
             dpLiftHeads.contains fs.name) = true) :
    opq.find? (fun p => p.1 == .cons (.atom (.symbol fs)) args) = none := by
  cases hfind : opq.find? (fun p => p.1 == .cons (.atom (.symbol fs)) args) with
  | none => rfl
  | some p =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred : p.1 == .cons (.atom (.symbol fs)) args := by
      simpa using List.find?_some hfind
    have hkey := List.all_eq_true.mp hwf p hmem
    rw [eq_of_beq hpred] at hkey
    simp only [dpOpqKeyOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hkey
    obtain ⟨⟨h1, h2⟩, h3⟩ := hkey
    simp only [h1, h2, Bool.false_or] at hban
    exact absurd hban (by simpa using h3)

/-- An if-term is never an opaque key under WF. -/
theorem dpOpqWF_find_if (opq : List (SExpr × SExpr))
    (hwf : dpOpqWF opq = true) (c thn els : SExpr) :
    opq.find? (fun p => p.1 == ifT c thn els) = none :=
  dpOpqWF_find_banned opq hwf _ (by decide)

/-- A not-term is never an opaque key under WF. -/
theorem dpOpqWF_find_not (opq : List (SExpr × SExpr))
    (hwf : dpOpqWF opq = true) (x : SExpr) :
    opq.find? (fun p => p.1 == notT x) = none :=
  dpOpqWF_find_banned opq hwf _ (by decide)

/-- A (default-package) quote-term lifts transparently under WF. -/
theorem dpLiftF_quote {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true) (x : SExpr) :
    dpLiftF vars opq
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons x .nil)) = some x := by
  rw [dpLiftF.eq_def, dpOpqWF_find_banned opq hwf _ (by decide)]
  simp

/-- A banned-NAME head that is NOT the default-package special/primitive
    cannot lift at all (the structural arms all miss and WF bans the key) —
    the refuter for the wrong-package vacuous cases in the clausify
    induction (D-B4). -/
theorem dpLiftF_app_none_of_banned_name {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    {fs : Symbol} (args : SExpr)
    (hban : (fs.isNamed "QUOTE" || fs.isNamed "IF" ||
             dpLiftHeads.contains fs.name) = true)
    (hnq : (fs == { name := "QUOTE" }) = false)
    (hnif : (fs == { name := "IF" }) = false)
    (hnprim : (fs.package == "ACL2" && dpLiftHeads.contains fs.name) = false) :
    dpLiftF vars opq (.cons (.atom (.symbol fs)) args) = none := by
  rw [dpLiftF.eq_def, dpOpqWF_find_banned opq hwf args hban]
  simp [hnq, hnif]
  intro hpkg hmem
  simp [hpkg, hmem] at hnprim

/-- INVERT a lifted if: the three components lift, and the value is the
    `cond` of theirs. -/
theorem dpLiftF_if_inv {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    {c thn els v : SExpr}
    (h : dpLiftF vars opq (ifT c thn els) = some v) :
    ∃ cv tv ev, dpLiftF vars opq c = some cv ∧
      dpLiftF vars opq thn = some tv ∧ dpLiftF vars opq els = some ev ∧
      v = cond (Logic.toBool cv) tv ev := by
  rw [dpLiftF.eq_def, dpOpqWF_find_if opq hwf c thn els] at h
  simp only [show (({ name := "IF" } : Symbol) == { name := "QUOTE" }) = false
    from by decide, BEq.rfl, if_true, if_false, Bool.false_eq_true] at h
  obtain ⟨cv, hcv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tv, htv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ev, hev, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨cv, tv, ev, hcv, htv, hev, (Option.some.inj h).symm⟩

/-- INTRODUCE a lifted not: a lifted argument gives the wrap's lift. -/
theorem dpLiftF_not_intro {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    {x xv : SExpr} (h : dpLiftF vars opq x = some xv) :
    dpLiftF vars opq (notT x) = some (Logic.not xv) := by
  rw [dpLiftF.eq_def, dpOpqWF_find_not opq hwf x]
  simp only [show (({ name := "NOT" } : Symbol) == { name := "QUOTE" }) = false
      from by decide,
    show (({ name := "NOT" } : Symbol) == { name := "IF" }) = false
      from by decide,
    show (({ name := "NOT" } : Symbol).package == "ACL2" &&
      dpLiftHeads.contains ({ name := "NOT" } : Symbol).name) = true
      from by decide,
    if_true, if_false, Bool.false_eq_true]
  rw [h]
  rfl

/-- INVERT a lifted not: the argument lifts, and the value is `Logic.not`
    of its. -/
theorem dpLiftF_not_inv {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    {x v : SExpr} (h : dpLiftF vars opq (notT x) = some v) :
    ∃ xv, dpLiftF vars opq x = some xv ∧ v = Logic.not xv := by
  rw [dpLiftF.eq_def, dpOpqWF_find_not opq hwf x] at h
  simp only [show (({ name := "NOT" } : Symbol) == { name := "QUOTE" }) = false
      from by decide,
    show (({ name := "NOT" } : Symbol) == { name := "IF" }) = false
      from by decide,
    show (({ name := "NOT" } : Symbol).package == "ACL2" &&
      dpLiftHeads.contains ({ name := "NOT" } : Symbol).name) = true
      from by decide,
    if_true, if_false, Bool.false_eq_true] at h
  obtain ⟨xv, hxv, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨xv, hxv, ?_⟩
  simpa using (Option.some.inj h).symm

end ACL2.Replay
