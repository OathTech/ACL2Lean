/-
  WORLD TRANSPORT (perf arc phase 2 item 1, 2026-08-17) — the consumer
  face of the D2 metatheorem `evalOpt_world_mono` (EvalOpt.lean, proven
  2026-07-10, zero consumers until now; design
  docs/plans/2026-07-10_external-knowledge-design.md §D2/§D7).

  A dependency book's replayed statement lives over ITS OWN world `w1`;
  a consumer replays over an extension `w2 ⊇ w1`. `evalOpt_world_mono`
  transfers convergence facts forward under two side conditions:

  - `hext` — every `w1` def present byte-identically in `w2`;
  - `hnew` — no `w2`-only def SHADOWS a name `w1` dispatched via
    `callBuiltin` (world-first dispatch would send the two evaluations
    down different routes).

  Both are ∀-over-`Symbol` statements, so neither is directly decidable.
  This module reduces each to a per-world-pair DECIDABLE check plus — for
  `hnew` — a FINITE list of per-name `callBuiltin` facts:

  - `worldExtendsCheck` (a fold over `w1.defs.entries`) ⟹ `hext`;
  - `newKeysCoverCheck` (every `w2` key is a `w1` key or in a concrete
    `news` list) + `NoBuiltins news` ⟹ `hnew`.

  THE hnew RECONCILIATION (settled at build time, 2026-08-17): the T1+2
  sprint's P3c rejected this transport because `callBuiltin`'s 55-arm
  match cannot produce equation lemmas — its splitter generation dies at
  a FIXED 200k-heartbeat whnf budget that `set_option maxHeartbeats 0`
  does NOT lift (re-demonstrated on this branch). That failure is real
  but confined to the GENERIC route (`∀ name ∉ builtinNames, …`). The
  DEMAND-scoped route needs no equation lemma at all: for each CONCRETE
  non-builtin name, `∀ args, callBuiltin "N" args = none` is closed by
  `rfl` — kernel whnf reduces the match on a concrete name with the args
  still abstract (the compiled decision tree splits on the name column
  first). The new names of a world pair are a finite concrete set, so
  `hnew` is dischargeable name-by-name without ever unfolding
  `callBuiltin` under an abstract name. (A5's reading of §D7 — "hnew
  from facts the drivers already build" — is vindicated in mechanism:
  the same concrete-world kernel-decide style as `proveNoShadow`, though
  the facts themselves are new, not the per-world no-shadow facts.)

  The meta-level builders that apply these lemmas per book pair live in
  `Replay/Runner.lean` (`crossBookRegistry`) and the coverage harness.
-/
import ACL2Lean.Replay.Lemmas.Judgments

namespace ACL2.Replay

open ACL2

/-! ## DefMap spine lemmas -/

/-- A `DefMap.get?` hit's key-value pair is an entry (assoc-list spine of
    `get?.go`; `Symbol`'s `BEq` is lawful). -/
private theorem mem_entries_of_go_eq_some {s : Symbol}
    {v : List Symbol × SExpr} :
    ∀ {l : List (Symbol × (List Symbol × SExpr))},
      DefMap.get?.go s l = some v → (s, v) ∈ l := by
  intro l
  induction l with
  | nil => intro h; simp [DefMap.get?.go] at h
  | cons p rest ih =>
    intro h
    by_cases hk : p.1 == s
    · rw [DefMap.get?.go, if_pos hk] at h
      obtain rfl := eq_of_beq hk
      cases h
      exact List.mem_cons_self ..
    · rw [DefMap.get?.go, if_neg hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- `DefMap.get?` unfolded to its spine (the `let rec` body). -/
private theorem get?_eq_go (m : DefMap) (s : Symbol) :
    m.get? s = DefMap.get?.go s m.entries := rfl

/-! ## The decidable per-pair side conditions -/

/-- Side condition 1 (per world pair, decidable): every `w1` def is
    present BYTE-IDENTICALLY in `w2` — the same check as
    `Runner.worldIncludes`, in `decide` form so a kernel proof of
    `= true` is available on concrete worlds. -/
def worldExtendsCheck (w1 w2 : World) : Bool :=
  w1.defs.entries.all fun kv => decide (w2.defs.get? kv.1 = some kv.2)

/-- Side condition 2's decidable cover (per world pair + a concrete
    `news` list): every `w2` def key is a `w1` key or listed in `news`.
    (`news` is intended as exactly the `w2`-only keys; the lemma only
    needs the cover direction.) -/
def newKeysCoverCheck (w1 w2 : World) (news : List Symbol) : Bool :=
  w2.defs.entries.all fun kv =>
    w1.defs.contains kv.1 || news.contains kv.1

/-- The finite per-name residue of `hnew`: each listed (new, concrete)
    name makes `callBuiltin` fall through to `none` on every argument
    list. On a concrete non-builtin name each conjunct is closed by
    `rfl` (see the module header — the P3c reconciliation). -/
def NoBuiltins : List Symbol → Prop
  | [] => True
  | s :: rest => (∀ args, callBuiltin s.name args = none) ∧ NoBuiltins rest

/-- `NoBuiltins` introduction, nil (meta-builder anchor). -/
theorem noBuiltins_nil : NoBuiltins [] := trivial

/-- `NoBuiltins` introduction, cons (meta-builder step). -/
theorem noBuiltins_cons {s : Symbol} {l : List Symbol}
    (h : ∀ args, callBuiltin s.name args = none) (t : NoBuiltins l) :
    NoBuiltins (s :: l) := ⟨h, t⟩

private theorem noBuiltins_spec {l : List Symbol} (h : NoBuiltins l) :
    ∀ s ∈ l, ∀ args, callBuiltin s.name args = none := by
  induction l with
  | nil => intro s hs; cases hs
  | cons a rest ih =>
    intro s hs
    cases hs with
    | head => exact h.1
    | tail _ hs => exact ih h.2 s hs

/-! ## The bridges: decidable checks ⟹ the metatheorem's side conditions -/

/-- `worldExtendsCheck` reflects to `evalOpt_world_mono`'s `hext`. -/
theorem hext_of_worldExtendsCheck {w1 w2 : World}
    (h : worldExtendsCheck w1 w2 = true) :
    ∀ s d, w1.defs.get? s = some d → w2.defs.get? s = some d := by
  intro s d hget
  rw [get?_eq_go] at hget
  have hm : (s, d) ∈ w1.defs.entries := mem_entries_of_go_eq_some hget
  have := List.all_eq_true.mp h _ hm
  exact of_decide_eq_true this

/-- `newKeysCoverCheck` + the finite `NoBuiltins` facts reflect to
    `evalOpt_world_mono`'s `hnew`. -/
theorem hnew_of_cover {w1 w2 : World} {news : List Symbol}
    (hcov : newKeysCoverCheck w1 w2 news = true)
    (hnb : NoBuiltins news) :
    ∀ s, w1.defs.get? s = none →
      w2.defs.get? s = none ∨ ∀ args, callBuiltin s.name args = none := by
  intro s hs
  cases hg : w2.defs.get? s with
  | none => exact .inl rfl
  | some d =>
    refine .inr ?_
    rw [get?_eq_go] at hg
    have hm : (s, d) ∈ w2.defs.entries := mem_entries_of_go_eq_some hg
    have hdisj := List.all_eq_true.mp hcov _ hm
    rcases Bool.or_eq_true .. |>.mp hdisj with hc | hn
    · exact absurd hc (by simp [DefMap.contains, hs])
    · exact noBuiltins_spec hnb s (by simpa using hn)

/-! ## The transport -/

/-- WORLD TRANSPORT at the judgment level: `EvTrue` transfers along a
    checked world extension — `evalOpt_world_mono` with both side
    conditions in their per-pair decidable/finite form. Fuel-shape
    preserving (the metatheorem is per-fuel), so the `∃N∀f` statement
    transfers with the same `N`. Stated `∀ env t` so ONE constant per
    (consumer, dependency) world pair serves every transported
    statement of that pair. -/
theorem evtrue_transport {w1 w2 : World} {news : List Symbol}
    (hinc : worldExtendsCheck w1 w2 = true)
    (hcov : newKeysCoverCheck w1 w2 news = true)
    (hnb : NoBuiltins news) :
    ∀ (env : Env) (t : SExpr), EvTrue w1 env t → EvTrue w2 env t := by
  intro env t h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨v, hv, hnn⟩ := hN f hf
  exact ⟨v, evalOpt_world_mono (hext_of_worldExtendsCheck hinc)
    (hnew_of_cover hcov hnb) f env t v hv, hnn⟩

end ACL2.Replay
