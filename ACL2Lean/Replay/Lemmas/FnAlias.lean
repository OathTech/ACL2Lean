import ACL2Lean.Replay.Lemmas.Judgments

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
  | .cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- a LAMBDA application (translated `let`): the FORMALS position is a
    -- binder, never descended (ACL2's sublis-fn semantics — fn symbols
    -- and variables are separate namespaces, so no capture is possible);
    -- the body and actuals are substituted
    .cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons (substFnCalls σ lamBody) .nil)))
      (substFnList σ argsExpr)
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

/-- `mapM = some` forces equal lengths. -/
theorem mapM_some_length {f : SExpr → Option SExpr} :
    ∀ {l : List SExpr} {vs : List SExpr}, l.mapM f = some vs →
      l.length = vs.length
  | [], vs, h => by simp_all
  | a :: rest, vs, h => by
    cases hf : f a with
    | none => simp [List.mapM_cons, hf] at h
    | some v =>
      cases hr : rest.mapM f with
      | none => simp [List.mapM_cons, hf, hr] at h
      | some rvs =>
        simp [List.mapM_cons, hf, hr] at h
        subst h
        simp [mapM_some_length hr]

/-- `mapM = some` gives the per-element equations along the zip. -/
theorem mapM_some_zip {f : SExpr → Option SExpr} :
    ∀ {l : List SExpr} {vs : List SExpr}, l.mapM f = some vs →
      ∀ p ∈ l.zip vs, f p.1 = some p.2
  | [], vs, h => by simp_all
  | a :: rest, vs, h => by
    cases hf : f a with
    | none => simp [List.mapM_cons, hf] at h
    | some v =>
      cases hr : rest.mapM f with
      | none => simp [List.mapM_cons, hf, hr] at h
      | some rvs =>
        simp [List.mapM_cons, hf, hr] at h
        subst h
        intro p hp
        rcases List.mem_cons.mp (by simpa [List.zip_cons_cons] using hp)
          with rfl | hmem
        · exact hf
        · exact mapM_some_zip hr p hmem

/-- LEMMA B′ — single-world β-EXPANSION transport: a converging
    evaluation over the alias world transports to the `substFnCalls`
    image IN THE SAME WORLD (composing with Lemma A on the alias-free
    image then crosses to the base world).  Non-alias definition bodies
    are untouched by the substitution, so NO conditions on the world's
    other content are needed; `WellScoped t` excludes surface LET/LET*
    (Core.lean's predicate) and `substSafe` protects lambda binders. -/
theorem evalOpt_fnexpand_transport
    (σ : List (Symbol × List Symbol × SExpr)) (w' : World)
    (hσdef : ∀ e ∈ σ, w'.defs.get? e.1 = some (e.2.1, e.2.2))
    (hσns : ∀ e ∈ σ, (e.1.isNamed "QUOTE" || e.1.isNamed "IF" ||
      e.1.isNamed "LET" || e.1.isNamed "LET*" ||
      e.1.isNamed "LAMBDA") = false)
    (hσws : ∀ e ∈ σ, WellScoped e.2.2 = true)
    (hσcl : ∀ e ∈ σ, (freeVars e.2.2).all (fun x => e.2.1.contains x) = true) :
    ∀ (F : Nat) (env : Env) (t : SExpr) (v : SExpr),
      WellScoped t = true →
      evalOpt F w' env t = some v →
      ∃ N, ∀ f ≥ N, evalOpt f w' env (substFnCalls σ t) = some v
  | 0, _, _, _, _, h => by simp [evalOpt] at h
  | F + 1, env, t, v, hws, h => by
    have IH := evalOpt_fnexpand_transport σ w' hσdef hσns hσws hσcl F
    rw [show evalOpt (F+1) w' env t
        = evalOptStep (evalOpt F) w' env t from rfl] at h
    match t with
    | .nil | .atom (.number _) | .atom (.string _)
    | .atom (.keyword _) | .atom (.char _) | .atom (.symbol _) =>
      exact ⟨1, fun f hf => by
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        exact h⟩
    | .cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) argsExpr =>
      -- translated let: WellScoped supplies the invariants
      obtain ⟨hlam, ⟨lformals, hform, hclosed⟩, hbws, hspineWs⟩ :=
        WellScoped_lam_parts hws
      simp only [evalOptStep_cons_lam, hlam, if_true, hform] at h
      revert h
      match hal : argsExpr.toList? with
      | none => intro h; exact absurd h (by simp)
      | some args =>
        dsimp only []
        intro h
        cases hmap : args.mapM (fun a => evalOpt F w' env a) with
        | none => rw [hmap] at h; exact absurd h (by simp)
        | some argVals =>
          rw [hmap] at h
          by_cases hlen : lformals.length = argVals.length
          case neg =>
            rw [show ((some argVals >>= fun argVals =>
              if lformals.length = argVals.length then
                evalOpt F w' (bindArgsOver env lformals argVals) lamBody
              else none) : Option SExpr)
              = if lformals.length = argVals.length then
                evalOpt F w' (bindArgsOver env lformals argVals) lamBody
              else none from rfl, if_neg hlen] at h
            exact absurd h (by simp)
          case pos =>
            rw [show ((some argVals >>= fun argVals =>
              if lformals.length = argVals.length then
                evalOpt F w' (bindArgsOver env lformals argVals) lamBody
              else none) : Option SExpr)
              = if lformals.length = argVals.length then
                evalOpt F w' (bindArgsOver env lformals argVals) lamBody
              else none from rfl, if_pos hlen] at h
            -- the substituted term: the dedicated lambda arm keeps the
            -- binder; body and actuals are substituted — conv_lam
            -- reassembles from the IHs
            have hargs' : (substFnList σ argsExpr).toList?
                = some (args.map (substFnCalls σ)) := by
              rw [substFnList_toList?, hal]; rfl
            have hlenA : (args.map (substFnCalls σ)).length
                = argVals.length := by
              simpa using mapM_some_length (f := fun a => evalOpt F w' env a) hmap
            have hconv : ∀ p ∈ (args.map (substFnCalls σ)).zip argVals,
                ∃ N, ∀ f ≥ N, evalOpt f w' env p.1 = some p.2 := by
              intro p hp
              rw [List.zip_map_left] at hp
              obtain ⟨⟨a, u⟩, hmem, rfl⟩ := List.mem_map.mp hp
              have haw : WellScoped a = true :=
                WellScoped_of_mem_spine hal hspineWs a
                  (List.of_mem_zip hmem).1
              exact IH env a u haw (mapM_some_zip hmap (a, u) hmem)
            have hbody : ∃ N, ∀ f ≥ N, evalOpt f w'
                (bindArgsOver env lformals argVals)
                (substFnCalls σ lamBody) = some v :=
              IH (bindArgsOver env lformals argVals) lamBody v hbws h
            exact conv_lam w' env lam formalsE (substFnCalls σ lamBody)
              (substFnList σ argsExpr) lformals (args.map (substFnCalls σ))
              argVals v hlam hform hargs' hlenA hlen hconv hbody
    | .cons (.atom (.symbol s)) argsExpr =>
      by_cases hq : s.isNamed "QUOTE" = true
      case pos =>
        -- QUOTE: the guard leaves the whole term; the step ignores rec
        have hid : substFnCalls σ (.cons (.atom (.symbol s)) argsExpr)
            = .cons (.atom (.symbol s)) argsExpr := by
          rw [substFnCalls, if_pos (show (s.name == "QUOTE") = true from hq)]
        rw [hid]
        simp only [evalOptStep_cons_symbol, if_pos hq] at h
        exact ⟨1, fun f hf => by
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
          show evalOptStep (evalOpt g) w' env _ = some v
          simp only [evalOptStep_cons_symbol, if_pos hq]
          exact h⟩
      case neg =>
      have hqf : s.isNamed "QUOTE" = false := Bool.eq_false_iff.mpr hq
      obtain ⟨hlet, hlam2, hspineWs⟩ := WellScoped_sym_parts hws hqf
      have hqname : ¬((s.name == "QUOTE") = true) := by
        simpa [Symbol.isNamed] using hq
      by_cases hif : s.isNamed "IF" = true
      case pos =>
        -- IF: recompose branchwise; assembled by hand (the step
        -- dispatches on isNamed, so no literal-symbol coupling)
        simp only [evalOptStep_cons_symbol, if_neg hq, if_pos hif] at h
        have hfind : σ.find? (fun e => e.1 == s) = none := by
          rw [List.find?_eq_none]
          intro e he hbeq
          have := hσns e he
          rw [eq_of_beq hbeq] at this
          simp [hif] at this
        revert h
        match hal : argsExpr.toList? with
        | some [c, tt, e] =>
          dsimp only []
          intro h
          have hels := WellScoped_of_mem_spine hal hspineWs
          cases hc : evalOpt F w' env c with
          | none => rw [hc] at h; exact absurd h (by simp)
          | some cv =>
            rw [hc] at h
            replace h : (if Logic.toBool cv then evalOpt F w' env tt
                else evalOpt F w' env e) = some v := h
            have hid : substFnCalls σ (.cons (.atom (.symbol s)) argsExpr)
                = .cons (.atom (.symbol s))
                    (substFnList σ argsExpr) := by
              rw [substFnCalls, if_neg hqname]
              dsimp only []
              rw [hfind]
            rw [hid]
            obtain ⟨Nc, hcC⟩ := IH env c cv (hels c (by simp)) hc
            have hargs' : (substFnList σ argsExpr).toList?
                = some [substFnCalls σ c, substFnCalls σ tt,
                        substFnCalls σ e] := by
              rw [substFnList_toList?, hal]; rfl
            cases htb : Logic.toBool cv with
            | true =>
              rw [if_pos htb] at h
              obtain ⟨Nt, htC⟩ := IH env tt v (hels tt (by simp)) h
              refine ⟨max Nc Nt + 1, fun f hf => ?_⟩
              obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
              show evalOptStep (evalOpt g) w' env _ = some v
              simp only [evalOptStep_cons_symbol, if_neg hq, if_pos hif,
                hargs']
              rw [hcC g (by omega)]
              have hbr : (if Logic.toBool cv then
                  evalOpt g w' env (substFnCalls σ tt)
                else evalOpt g w' env (substFnCalls σ e)) = some v := by
                rw [if_pos htb]
                exact htC g (by omega)
              exact hbr
            | false =>
              rw [if_neg (by rw [htb]; simp)] at h
              obtain ⟨Ne, heC⟩ := IH env e v (hels e (by simp)) h
              refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
              obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
              show evalOptStep (evalOpt g) w' env _ = some v
              simp only [evalOptStep_cons_symbol, if_neg hq, if_pos hif,
                hargs']
              rw [hcC g (by omega)]
              have hbr : (if Logic.toBool cv then
                  evalOpt g w' env (substFnCalls σ tt)
                else evalOpt g w' env (substFnCalls σ e)) = some v := by
                rw [if_neg (by rw [htb]; simp)]
                exact heC g (by omega)
              exact hbr
        | some [] => intro h; exact absurd h (by simp)
        | some [_] => intro h; exact absurd h (by simp)
        | some [_, _] => intro h; exact absurd h (by simp)
        | some (_ :: _ :: _ :: _ :: _) => intro h; exact absurd h (by simp)
        | none => intro h; exact absurd h (by simp)
      case neg =>
        -- general application: alias / defined / builtin
        simp only [evalOptStep_cons_symbol, if_neg hq, if_neg hif,
          if_neg (by simp [Bool.or_eq_true] at hlet ⊢; exact hlet :
            ¬((s.isNamed "LET" || s.isNamed "LET*") = true))] at h
        revert h
        match hal : argsExpr.toList? with
        | none => intro h; exact absurd h (by simp)
        | some args =>
          dsimp only []
          intro h
          have hels := WellScoped_of_mem_spine hal hspineWs
          cases hmap : args.mapM (fun a => evalOpt F w' env a) with
          | none => rw [hmap] at h; exact absurd h (by simp)
          | some argVals =>
            rw [hmap] at h
            replace h : (match w'.defs.get? s with
              | some (formals, body) =>
                if formals.length = argVals.length then
                  evalOpt F w' (bindArgs formals argVals) body
                else none
              | none => callBuiltin s.name argVals) = some v := h
            have hlenAV : args.length = argVals.length :=
              mapM_some_length (f := fun a => evalOpt F w' env a) hmap
            have hspine' : (substFnList σ argsExpr).toList?
                = some (args.map (substFnCalls σ)) := by
              rw [substFnList_toList?, hal]; rfl
            have hconvArgs : ∀ p ∈ (args.map (substFnCalls σ)).zip argVals,
                ∃ N, ∀ f ≥ N, evalOpt f w' env p.1 = some p.2 := by
              intro p hp
              rw [List.zip_map_left] at hp
              obtain ⟨⟨a, u⟩, hmem, rfl⟩ := List.mem_map.mp hp
              exact IH env a u (hels a (List.of_mem_zip hmem).1)
                (mapM_some_zip hmap (a, u) hmem)
            match hσf : σ.find? (fun e => e.1 == s) with
            | some (fn, formals, body) =>
              -- THE ALIAS CALL: β-expand through the substN bridge
              have hmem := List.mem_of_find?_eq_some hσf
              have hfs : fn = s := eq_of_beq (by
                have := List.find?_some hσf; simpa using this)
              subst hfs
              have hget : w'.defs.get? fn = some (formals, body) :=
                hσdef _ hmem
              rw [hget] at h
              replace h : (if formals.length = argVals.length then
                  evalOpt F w' (bindArgs formals argVals) body
                else none) = some v := h
              by_cases hlen2 : formals.length = argVals.length
              case neg => rw [if_neg hlen2] at h; exact absurd h (by simp)
              rw [if_pos hlen2] at h
              have hid : substFnCalls σ (.cons (.atom (.symbol fn)) argsExpr)
                  = substTerm formals (args.map (substFnCalls σ)) body := by
                rw [substFnCalls, if_neg hqname]
                dsimp only []
                rw [hσf, hspine']
                dsimp only []
                rw [if_pos (by
                  simp [hlen2, ← hlenAV])]
              rw [hid]
              obtain ⟨Ns, hsub⟩ := evalOpt_substTerm_substN w' env formals
                (args.map (substFnCalls σ)) argVals body (hσws _ hmem)
                (by simpa using hlenAV) hconvArgs
              have hcl : ∀ x ∈ freeVars body, x ∈ formals := by
                intro x hx
                have := List.all_eq_true.mp (hσcl _ hmem) x hx
                simpa [List.contains_iff_exists_mem_beq] using this
              have henvbr : ∀ n, evalOpt n w'
                  (bindArgsOver env formals argVals) body
                  = evalOpt n w' (bindArgs formals argVals) body := by
                intro n
                refine evalOpt_freevar_congr w' n _ _ body (hσws _ hmem)
                  (fun x hx => ?_)
                have hxf := hcl x hx
                show evalOptStep _ _ _ _ = evalOptStep _ _ _ _
                simp only [evalOptStep]
                rw [bindArgs_eq_bindArgsOver_empty formals argVals,
                  bindArgsOver_get_of_mem x formals argVals hlen2 hxf env ∅]
              refine ⟨max Ns F, fun f hf => ?_⟩
              rw [hsub f (by omega), henvbr f]
              exact evalOpt_ge_fuel F f w' _ body v h (by omega)
            | none =>
              -- non-alias: rebuilt application; body/builtin untouched
              have hid : substFnCalls σ (.cons (.atom (.symbol s)) argsExpr)
                  = .cons (.atom (.symbol s)) (substFnList σ argsExpr) := by
                rw [substFnCalls, if_neg hqname]
                dsimp only []
                rw [hσf]
              rw [hid]
              obtain ⟨Nm, hm⟩ := mapM_conv_of_zip w' env
                (args.map (substFnCalls σ)) argVals
                (by simpa using hlenAV) hconvArgs
              match hget : w'.defs.get? s with
              | some (formals, body) =>
                rw [hget] at h
                replace h : (if formals.length = argVals.length then
                    evalOpt F w' (bindArgs formals argVals) body
                  else none) = some v := h
                by_cases hlen2 : formals.length = argVals.length
                case neg => rw [if_neg hlen2] at h; exact absurd h (by simp)
                rw [if_pos hlen2] at h
                refine ⟨max Nm F + 1, fun f hf => ?_⟩
                obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                show evalOptStep (evalOpt g) w' env _ = some v
                simp only [evalOptStep_cons_symbol, if_neg hq, if_neg hif,
                  if_neg (by simp [Bool.or_eq_true] at hlet ⊢; exact hlet :
                    ¬((s.isNamed "LET" || s.isNamed "LET*") = true)),
                  hspine']
                try dsimp only []
                rw [hm g (by omega), hget]
                replace : (if formals.length = argVals.length then
                    evalOpt g w' (bindArgs formals argVals) body
                  else none) = some v := by
                  rw [if_pos hlen2]
                  exact evalOpt_ge_fuel F g w' _ body v h (by omega)
                exact this
              | none =>
                rw [hget] at h
                replace h : callBuiltin s.name argVals = some v := h
                refine ⟨Nm + 1, fun f hf => ?_⟩
                obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                show evalOptStep (evalOpt g) w' env _ = some v
                simp only [evalOptStep_cons_symbol, if_neg hq, if_neg hif,
                  if_neg (by simp [Bool.or_eq_true] at hlet ⊢; exact hlet :
                    ¬((s.isNamed "LET" || s.isNamed "LET*") = true)),
                  hspine']
                try dsimp only []
                rw [hm g (by omega), hget]
                exact h
    | .cons (.atom (.number _)) _ | .cons (.atom (.string _)) _
    | .cons (.atom (.keyword _)) _ | .cons (.atom (.char _)) _
    | .cons .nil _ => exact absurd h (by simp [evalOptStep])
    | .cons (.cons .nil _) _ | .cons (.cons (.atom (.number _)) _) _
    | .cons (.cons (.atom (.string _)) _) _
    | .cons (.cons (.atom (.keyword _)) _) _
    | .cons (.cons (.atom (.char _)) _) _
    | .cons (.cons (.cons _ _) _) _ => exact absurd h (by simp [evalOptStep])
    | .cons (.cons (.atom (.symbol lam)) .nil) _
    | .cons (.cons (.atom (.symbol lam)) (.atom _)) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ .nil)) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ (.atom _))) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.cons _ _)))) _
    | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.atom _)))) _ =>
      exact absurd hws (by simp [WellScoped])

/-- THE R7b COMPOSITION at the `EvTrue` level: an alias-world truth
    transports to the base world on the substituted image — B′ inside
    the alias world, then Lemma A across (the image must be alias-free,
    which the composition site checks by `decide`).  This is the
    semantic content of ACL2's functional-instantiation step, made
    kernel-checked. -/
theorem evtrue_fnalias (σ : List (Symbol × List Symbol × SExpr))
    (w w' : World)
    (hσdef : ∀ e ∈ σ, w'.defs.get? e.1 = some (e.2.1, e.2.2))
    (hσns : ∀ e ∈ σ, (e.1.isNamed "QUOTE" || e.1.isNamed "IF" ||
      e.1.isNamed "LET" || e.1.isNamed "LET*" ||
      e.1.isNamed "LAMBDA") = false)
    (hσws : ∀ e ∈ σ, WellScoped e.2.2 = true)
    (hσcl : ∀ e ∈ σ, (freeVars e.2.2).all (fun x => e.2.1.contains x) = true)
    (hagree : ∀ s : Symbol, (σ.map (·.1)).contains s = false →
      w'.defs.get? s = w.defs.get? s)
    (hw : aliasFreeWorld (σ.map (·.1)) w = true)
    (t : SExpr) (hws : WellScoped t = true)
    (hfree : fnFreeTerm (σ.map (·.1)) (substFnCalls σ t) = true)
    (env : Env) (h : EvTrue w' env t) :
    EvTrue w env (substFnCalls σ t) := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨v, hv, hne⟩ := hN N (Nat.le_refl _)
  obtain ⟨N', h'⟩ := evalOpt_fnexpand_transport σ w' hσdef hσns hσws hσcl
    N env t v hws hv
  refine ⟨N', fun f hf => ⟨v, ?_, hne⟩⟩
  rw [← evalOpt_fnfree_agree (σ.map (·.1)) w w' hagree hw f env
    (substFnCalls σ t) hfree]
  exact h' f hf

/-! ## The alias-world constructor (composition-site plumbing)

`evtrue_fnalias`'s `hσdef`/`hagree` hypotheses quantify over all
symbols, so a composition site cannot `decide` them; built through
`withAliases`, both come out CONSTRUCTIVELY. -/

/-- `get?` over a filtered-out foreign key is unchanged. -/
theorem defMap_get?_go_filter (s s' : Symbol) (hne : (s' == s) = false) :
    ∀ (l : List (Symbol × (List Symbol × SExpr))),
      DefMap.get?.go s' (l.filter (fun kv => kv.1 != s))
        = DefMap.get?.go s' l
  | [] => rfl
  | (k, v) :: rest => by
    rw [List.filter_cons]
    by_cases hk : (k != s) = true
    · rw [if_pos (by simpa using hk)]
      by_cases hks : (k == s') = true
      · rw [DefMap.get?.go, if_pos hks, DefMap.get?.go, if_pos hks]
      · rw [DefMap.get?.go, if_neg hks, DefMap.get?.go, if_neg hks]
        exact defMap_get?_go_filter s s' hne rest
    · rw [if_neg (by simpa using hk)]
      have hkeq : k = s := by simpa [bne] using hk
      have hks : (k == s') = false := by
        subst hkeq
        cases hb : (k == s') with
        | false => rfl
        | true => rw [eq_of_beq hb] at hne; simp at hne
      rw [DefMap.get?.go, if_neg (by simp [hks])]
      exact defMap_get?_go_filter s s' hne rest

/-- `DefMap.insert` affects only its key. -/
theorem defMap_get?_insert (m : DefMap) (s s' : Symbol)
    (v : List Symbol × SExpr) :
    (m.insert s v).get? s' = if s' == s then some v else m.get? s' := by
  show DefMap.get?.go s' ((s, v) :: m.entries.filter (fun kv => kv.1 != s))
    = _
  by_cases h : (s' == s) = true
  · rw [if_pos h, DefMap.get?.go, if_pos (by
      rw [eq_of_beq h]; simp)]
  · rw [if_neg h, DefMap.get?.go, if_neg (by
      cases hb : (s == s') with
      | false => simp
      | true => rw [eq_of_beq hb] at h; simp at h)]
    exact defMap_get?_go_filter s s'
      (by cases hb : (s' == s) <;> simp_all) m.entries

/-- Extend a world with alias definitions (head entry wins). -/
def World.withAliases (w : World) :
    List (Symbol × List Symbol × SExpr) → World
  | [] => w
  | e :: rest =>
    let w' := World.withAliases w rest
    { w' with defs := w'.defs.insert e.1 (e.2.1, e.2.2) }

/-- Off the alias names, `withAliases` changes nothing. -/
theorem withAliases_agree (w : World) :
    ∀ (σ : List (Symbol × List Symbol × SExpr)) (s : Symbol),
      (σ.map (·.1)).contains s = false →
      (World.withAliases w σ).defs.get? s = w.defs.get? s
  | [], _, _ => rfl
  | e :: rest, s, h => by
    have hs : (s == e.1) = false := by
      simp [List.contains_cons] at h
      cases hb : (s == e.1) with
      | false => rfl
      | true => rw [show s = e.1 from eq_of_beq hb] at h; simp at h
    show ((World.withAliases w rest).defs.insert e.1 _).get? s = _
    rw [defMap_get?_insert, if_neg (by simp [hs])]
    refine withAliases_agree w rest s ?_
    simp [List.contains_cons] at h
    simpa using h.2

/-- Each alias entry is defined in the extension (given DISTINCT names). -/
theorem withAliases_get (w : World) :
    ∀ (σ : List (Symbol × List Symbol × SExpr)),
      (σ.map (·.1)).Nodup →
      ∀ e ∈ σ, (World.withAliases w σ).defs.get? e.1
        = some (e.2.1, e.2.2)
  | [], _, e, he => absurd he (by simp)
  | e0 :: rest, hnd, e, he => by
    rcases List.mem_cons.mp he with rfl | hmem
    · show ((World.withAliases w rest).defs.insert e.1 _).get? e.1 = _
      rw [defMap_get?_insert, if_pos (by simp)]
    · have hne : (e.1 == e0.1) = false := by
        have h0 := (List.nodup_cons.mp hnd).1
        cases hb : (e.1 == e0.1) with
        | false => rfl
        | true =>
          have : e0.1 ∈ rest.map (·.1) := by
            rw [← eq_of_beq hb]
            exact List.mem_map_of_mem hmem
          exact absurd this h0
      show ((World.withAliases w rest).defs.insert e0.1 _).get? e.1 = _
      rw [defMap_get?_insert, if_neg (by simp [hne])]
      exact withAliases_get w rest (List.nodup_cons.mp hnd).2 e hmem

end ACL2.Replay
