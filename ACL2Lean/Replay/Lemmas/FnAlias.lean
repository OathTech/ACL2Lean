import ACL2Lean.Replay.Lemmas.Core

/-! # Fn-alias commutation (Phase 3 2c — the R7b a1 route)

The functional-instantiation "apply at a model" move needs one new
semantic fact: evaluating a term over an ALIAS WORLD (the base world
extended with fresh definitions binding the constrained names to the
instances' bodies) agrees with evaluating the FN-SUBSTITUTED term over
the base world.  Two lemmas:

- `evalOpt_fnfree_agree` (A): a term with NO non-quoted occurrence of
  the alias names evaluates IDENTICALLY (same fuel) in both worlds —
  the extra definitions are never consulted.  Fuel induction mirroring
  `evalOptStep_mono`'s case skeleton.
- `evalOpt_fnalias_transport` (B): a CONVERGING evaluation over the
  alias world transports to the base world on the `substFnCalls` image
  (one direction — all `EvTrue` consumers need).  Strong fuel
  induction; the alias-call case composes (A) on the alias body with
  the `evalOpt_substTerm_substN` variable-substitution bridge.

`substFnCalls` (ACL2's `sublis-fn` semantics) lives HERE — total and
structural, so the kernel can reason about it — and is consumed by the
driver through the `ACL2.Replay` namespace (it moved from
Driver/NodeCore/Ctx, which the Lemmas layer cannot import). -/

namespace ACL2.Replay

open ACL2

mutual

/-- Apply a FUNCTIONAL substitution: each application of a substituted
    fn `(fn a₁ … aₙ)` becomes the lambda body with formals replaced by
    the (recursively substituted) arguments.  QUOTE bodies are DATA and
    are never descended (load-bearing for the transport lemma).  An
    arity mismatch or improper argument spine leaves the application
    head unsubstituted (the caller's verbatim cross-check then fails
    closed). -/
def substFnCalls (σ : List (Symbol × List Symbol × SExpr)) :
    SExpr → SExpr
  | .cons (.atom (.symbol fs)) args =>
    if fs.name == "QUOTE" then .cons (.atom (.symbol fs)) args
    else
      let args' := substFnList σ args
      match σ.find? (fun (fn, _, _) => fn == fs) with
      | some (_, formals, body) =>
        match args'.toList? with
        | some actuals =>
          if formals.length == actuals.length then
            substTerm formals actuals body
          else .cons (.atom (.symbol fs)) args'
        | none => .cons (.atom (.symbol fs)) args'
      | none => .cons (.atom (.symbol fs)) args'
  | .cons a b => .cons (substFnCalls σ a) (substFnList σ b)
  | t => t

/-- The argument-spine map for `substFnCalls` (structural twin). -/
def substFnList (σ : List (Symbol × List Symbol × SExpr)) :
    SExpr → SExpr
  | .cons a d => .cons (substFnCalls σ a) (substFnList σ d)
  | t => t

end

/-- No non-quoted occurrence of any of `names` (conservative: any
    symbol position outside QUOTE bodies counts). -/
def fnFreeTerm (names : List Symbol) : SExpr → Bool
  | .cons (.atom (.symbol q)) args =>
    if q.name == "QUOTE" then true
    else !names.contains q && fnFreeTerm names args
  | .cons a b => fnFreeTerm names a && fnFreeTerm names b
  | .atom (.symbol s) => !names.contains s
  | _ => true

/-- Every definition body of `w` is `fnFreeTerm names`. -/
def aliasFreeWorld (names : List Symbol) (w : World) : Bool :=
  w.defs.entries.all fun (_, _, body) => fnFreeTerm names body

/-- `DefMap.get?.go = some` finds its binding among the entries (keyed
    by a `==`-equal symbol). -/
theorem defMap_get?_go_mem {s : Symbol} {v : List Symbol × SExpr} :
    ∀ (l : List (Symbol × (List Symbol × SExpr))),
      DefMap.get?.go s l = some v → ∃ k, (k, v) ∈ l ∧ (k == s) = true
  | [], h => by simp [DefMap.get?.go] at h
  | (k, v') :: rest, h => by
    by_cases hk : (k == s) = true
    · refine ⟨k, ?_, hk⟩
      rw [DefMap.get?.go, if_pos hk] at h
      simp at h
      simp [h]
    · rw [DefMap.get?.go, if_neg hk] at h
      obtain ⟨k', hm, hks⟩ := defMap_get?_go_mem rest h
      exact ⟨k', List.mem_cons_of_mem _ hm, hks⟩

/-- `DefMap.get? = some` finds its binding among the entries. -/
theorem defMap_get?_mem {m : DefMap} {s : Symbol}
    {v : List Symbol × SExpr} (h : m.get? s = some v) :
    ∃ k, (k, v) ∈ m.entries ∧ (k == s) = true :=
  defMap_get?_go_mem m.entries h

end ACL2.Replay
