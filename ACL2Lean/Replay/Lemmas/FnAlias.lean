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

/-- No occurrence of any of `names`, anywhere — a UNIFORM structural
    traversal (deliberately conservative: quoted DATA also counts, which
    keeps every proof a plain congruence; a world/term that quotes an
    alias name fails the decidable precondition loudly at composition
    time rather than needing a quote-aware induction here). -/
def fnFreeTerm (names : List Symbol) : SExpr → Bool
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

/-- Elements of a proper spine inherit `fnFreeTerm`. -/
theorem fnFree_toList?_mem {names : List Symbol} :
    ∀ {argsE : SExpr} {l : List SExpr},
      fnFreeTerm names argsE = true → argsE.toList? = some l →
      ∀ a ∈ l, fnFreeTerm names a = true := by
  intro argsE
  induction argsE with
  | nil => intro l _ hl a ha; simp [SExpr.toList?] at hl; simp [hl] at ha
  | atom _ => intro l _ hl; simp [SExpr.toList?] at hl
  | cons x d ihx ihd =>
    intro l hfree hl a ha
    simp only [fnFreeTerm, Bool.and_eq_true] at hfree
    simp only [SExpr.toList?] at hl
    match hd : d.toList? with
    | none => rw [hd] at hl; simp at hl
    | some dl =>
      rw [hd] at hl; simp at hl
      subst hl
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact hfree.1
      · exact ihd hfree.2 hd a hmem

/-- `mapM` congruence under pointwise agreement on members. -/
theorem mapM_eq_of_mem {f g : SExpr → Option SExpr} :
    ∀ (l : List SExpr), (∀ a ∈ l, f a = g a) →
      l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: rest, h => by
    simp only [List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_eq_of_mem rest (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- Abstract fold+bind congruence: pointwise-equal step and body
    functions give equal folds (no matcher identity involved — the
    callers instantiate F/F' with the GOAL's own functions). -/
theorem foldlM_bind_congr {α : Type} (F F' : Env → SExpr → Option Env)
    (B B' : Env → Option α) :
    ∀ (l : List SExpr),
      (∀ acc b, b ∈ l → F' acc b = F acc b) →
      (∀ acc, B' acc = B acc) →
      ∀ acc, (l.foldlM F' acc).bind B' = (l.foldlM F acc).bind B
  | [], _, hbody, acc => by
    exact hbody acc
  | b :: rest, hstep, hbody, acc => by
    simp only [List.foldlM_cons,
      hstep acc b (List.mem_cons_self ..)]
    cases F acc b with
    | none => rfl
    | some acc' =>
      exact foldlM_bind_congr F F' B B' rest
        (fun a c hc => hstep a c (List.mem_cons_of_mem _ hc)) hbody acc'

/-- `do`-bind on a literal `some`: congruence by definitional unfolding
    (the type-class bind on `some a` IS `f a`). -/
theorem some_bind_congr {α β : Type} (a : α) {f g : α → Option β}
    (h : f a = g a) :
    (do let x ← some a; f x) = (do let x ← some a; g x) := h

/-- LEMMA A — alias-free evaluation invariance, POINTWISE in fuel: a
    term free of the alias names evaluates identically over the alias
    world and the base world (the extra definitions are never
    consulted), provided every base-world body is also alias-free. -/
theorem evalOpt_fnfree_agree (names : List Symbol) (w w' : World)
    (hagree : ∀ s : Symbol, names.contains s = false →
      w'.defs.get? s = w.defs.get? s)
    (hw : aliasFreeWorld names w = true) :
    ∀ (f : Nat) (env : Env) (t : SExpr), fnFreeTerm names t = true →
      evalOpt f w' env t = evalOpt f w env t
  | 0, _, _, _ => rfl
  | f + 1, env, t, hfree => by
    have IH := evalOpt_fnfree_agree names w w' hagree hw f
    show evalOptStep (evalOpt f) w' env t = evalOptStep (evalOpt f) w env t
    match t with
    | .nil | .atom (.number _) | .atom (.string _)
    | .atom (.keyword _) | .atom (.char _) | .atom (.symbol _) => rfl
    | .cons (.atom (.number _)) _ | .cons (.atom (.string _)) _
    | .cons (.atom (.keyword _)) _ | .cons (.atom (.char _)) _
    | .cons .nil _ => rfl
    | .cons (.cons .nil _) _ | .cons (.cons (.atom (.number _)) _) _
    | .cons (.cons (.atom (.string _)) _) _
    | .cons (.cons (.atom (.keyword _)) _) _
    | .cons (.cons (.atom (.char _)) _) _
    | .cons (.cons (.cons _ _) _) _ => rfl
    | .cons (.cons (.atom (.symbol lam)) .nil) _
    | .cons (.cons (.atom (.symbol lam)) (.atom _)) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ .nil)) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ (.atom _))) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.cons _ _)))) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.atom _)))) _ => rfl
    | .cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) argsExpr =>
      simp only [fnFreeTerm, Bool.and_eq_true] at hfree
      simp only [evalOptStep_cons_lam]
      by_cases hlam : lam.isNamed "LAMBDA" = true
      case neg => rw [if_neg hlam, if_neg hlam]
      case pos =>
        rw [if_pos hlam, if_pos hlam]
        match hfl : lamFormals? formalsE, hal : argsExpr.toList? with
        | some formals, some args =>
          dsimp
          rw [mapM_eq_of_mem args (fun a ha =>
            IH env a (fnFree_toList?_mem hfree.2 hal a ha))]
          cases hmap : args.mapM (fun a => evalOpt f w env a) with
          | none => rfl
          | some argVals =>
            dsimp only [Option.bind]
            by_cases hlen : formals.length = argVals.length
            · simp only [hlen, if_true]
              exact IH (bindArgsOver env formals argVals) lamBody
                hfree.1.2.2.1
            · simp only [hlen, if_false]
        | none, some _ => rfl
        | none, none => rfl
        | some _, none => rfl
    | .cons (.atom (.symbol s)) argsExpr =>
      simp only [fnFreeTerm, Bool.and_eq_true] at hfree
      simp only [evalOptStep_cons_symbol]
      by_cases hq : s.isNamed "QUOTE" = true
      · rw [if_pos hq, if_pos hq]
      · rw [if_neg hq, if_neg hq]
        by_cases hif : s.isNamed "IF" = true
        · rw [if_pos hif, if_pos hif]
          match hal : argsExpr.toList? with
          | some [c, tt, e] =>
            dsimp only []
            have hels := fnFree_toList?_mem hfree.2 hal
            rw [IH env c (hels c (by simp)),
              IH env tt (hels tt (by simp)),
              IH env e (hels e (by simp))]
          | some [] => rfl
          | some [_] => rfl
          | some [_, _] => rfl
          | some (_ :: _ :: _ :: _ :: _) => rfl
          | none => rfl
        · rw [if_neg hif, if_neg hif]
          by_cases hlet : (s.isNamed "LET" || s.isNamed "LET*") = true
          · rw [if_pos hlet, if_pos hlet]
            match hal : argsExpr.toList? with
            | some [bindings, body] =>
              dsimp only []
              have hels := fnFree_toList?_mem hfree.2 hal
              match hbl : bindings.toList? with
              | some bList =>
                dsimp only []
                have hbels := fnFree_toList?_mem
                  (hels bindings (by simp)) hbl
                have hbody := hels body (by simp)
                refine foldlM_bind_congr _ _ _ _ bList ?_
                  (fun acc => IH acc body hbody) env
                intro acc b hb
                match hbt : SExpr.toList? b with
                | some [SExpr.atom (Atom.symbol var), valExpr] =>
                  dsimp only []
                  have hvF : fnFreeTerm names valExpr = true :=
                    fnFree_toList?_mem (hbels b hb) hbt valExpr (by simp)
                  rw [IH (if s.isNamed "LET*" then acc else env)
                    valExpr hvF]
                | some [] => dsimp only []
                | some [_] => simp
                | some (_ :: _ :: _ :: _) => simp
                | none => dsimp only []
                | some [SExpr.nil, _] => dsimp only []
                | some [SExpr.cons _ _, _] => dsimp only []
                | some [SExpr.atom (Atom.number _), _] => dsimp only []
                | some [SExpr.atom (Atom.string _), _] => dsimp only []
                | some [SExpr.atom (Atom.keyword _), _] => dsimp only []
                | some [SExpr.atom (Atom.char _), _] => dsimp only []
              | none => dsimp only []
            | some [] => dsimp only []
            | some [_] => dsimp only []
            | some (_ :: _ :: _ :: _) => dsimp only []
            | none => dsimp only []
          · rw [if_neg hlet, if_neg hlet]
            match hal : argsExpr.toList? with
            | some args =>
              try dsimp only []
              rw [mapM_eq_of_mem args (fun a ha =>
                IH env a (fnFree_toList?_mem hfree.2 hal a ha))]
              cases hmap : args.mapM (fun a => evalOpt f w env a) with
              | none => rfl
              | some argVals =>
                refine some_bind_congr argVals ?_
                dsimp only []
                have hs : names.contains s = false := by
                  cases hns : names.contains s with
                  | false => rfl
                  | true => rw [hns] at hfree; simp at hfree
                rw [hagree s hs]
                match hget : w.defs.get? s with
                | some (formals, body) =>
                  dsimp only []
                  by_cases hlen : formals.length = argVals.length
                  · simp only [hlen, if_true]
                    have hbF : fnFreeTerm names body = true := by
                      obtain ⟨k, hmem, _⟩ := defMap_get?_mem hget
                      exact List.all_eq_true.mp hw _ hmem
                    exact IH (bindArgs formals argVals) body hbF
                  · simp only [hlen, if_false]
                | none => rfl
            | none => rfl

/-! ## Auxiliaries for the β-expansion transport (Lemma B′) -/

/-- `substFnList` commutes with proper-spine listing. -/
theorem substFnList_toList? (σ : List (Symbol × List Symbol × SExpr)) :
    ∀ (argsE : SExpr),
      (substFnList σ argsE).toList?
        = (argsE.toList?).map (List.map (substFnCalls σ))
  | .nil => rfl
  | .atom a => rfl
  | .cons x d => by
    simp only [substFnList, SExpr.toList?, substFnList_toList? σ d]
    cases d.toList? with
    | none => rfl
    | some l => rfl

mutual

/-- Lambda-formals safety: no lambda application inside `t` binds a
    formal named by the substitution (a substituted formal list would
    corrupt the binder).  QUOTE bodies are data and skipped. -/
def substSafe (names : List Symbol) : SExpr → Bool
  | .cons (.atom (.symbol q)) args =>
    if q.name == "QUOTE" then true else substSafeSpine names args
  | .cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    if lam.isNamed "LAMBDA" then
      (match lamFormals? formalsE with
       | some formals => formals.all (fun x => !names.contains x)
       | none => false)
      && substSafe names lamBody && substSafeSpine names argsExpr
    else false
  | .cons a b => substSafe names a && substSafeSpine names b
  | _ => true

/-- Spine twin of `substSafe`. -/
def substSafeSpine (names : List Symbol) : SExpr → Bool
  | .cons a d => substSafe names a && substSafeSpine names d
  | _ => true

end

end ACL2.Replay
