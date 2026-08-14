/-
  Driver/NodeCore/Recognizer — positional slice of the former NodeCore
  monolith (perf arc 3a, 2026-08-07): MOVE-ONLY; the boundaries are the
  file's own def-before-use order, so the import chain IS the
  dependency order.
-/
import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Recognizer fact `∃N∀f≥N, eval term = some verdict` (verdict the node's recorded
    `(quote t)`/`(quote nil)` value). Sources, in order: a fact pinned in the ctx by
    the scaffold/spine (e.g. `(consp x)` under a case hypothesis); the
    `acl2-numberp`-of-pinned-int recipe (the TP bridge); a structurally-computing
    value (e.g. `consp (cons …) = t`, where the cast is definitional). -/
partial def replayRecognizer (cfg : ReplayConfig) (ctx : ReplayCtx)
    (term : SExpr) (verdict : SExpr)
    -- the STEP's recorded :TYPESET when called from a recognizer node
    -- (audit 2026-08-07 S4 — the exact value ACL2 consulted); none on
    -- recursive/self calls (gate falls back to the emitted :BASICTS).
    (stepTs : Option Int := none)
    -- the node's cited (:TYPE-PRESCRIPTION <name>) runes — the tpthm
    -- route's BUG-023 anchor (theorem-classed TP rules; defun-TP names
    -- simply have no tpthm offer and fall through to the tp: routes)
    (citedTpThms : List String := []) : MetaM Expr := do
  let verdictE := reflectSExpr verdict
  if let some (v, p) := ctx.val? term then
    unless ← isDefEq v verdictE do
      throwError "replayRecognizer: pinned value of {repr term} ≠ verdict {repr verdict}"
    return p
  -- spine falsity facts: the literal IS this recognizer (verdict nil), or wraps it
  -- in (not …) (the literal's falsity makes the recognizer non-nil → t, by its
  -- two-valued range).
  if let some hNil := ctx.litFactByTerm? term then
    unless verdict == SExpr.nil do
      throwError "replayRecognizer: spine says {repr term} is nil but verdict is {repr verdict}"
    let p ← ctxValProof cfg ctx term
    let v ← ctxValExpr cfg ctx term
    return ← mkAppM ``re_val_cast
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hNil]
  -- not-literal elimination, searched over the term AND its true-listp
  -- CONS-peels (each peel definitional on the value side — see
  -- `trueListpConsPeels`): the spine's (not REC)-falsity fact at any peel
  -- depth discharges the original recognizer.
  let notOf (t : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
  let hit? := (trueListpConsPeels term).findSome? fun c =>
    (ctx.litFactByTerm? (notOf c)).map (c, ·)
  if let some (cterm, hNil) := hit? then
    match cterm with
    | .cons (.atom (.symbol rs)) _ =>
      -- TWO-VALUED recognizer registry: the spine's (not REC)-falsity fact
      -- forces REC ≠ nil, and a boolean-range lemma lifts that to = t. Each
      -- entry pairs the recognizer's trusted-core lift with its proved
      -- ne-nil→t lemma; an unlisted recognizer stays a named frontier.
      let entry? : Option (Name × Name) :=
        if rs.name == "CONSP" then
          some (``Logic.consp, ``logic_consp_ne_nil_t)
        else if rs.name == "TRUE-LISTP" then
          some (``Logic.trueListp, ``logic_trueListp_ne_nil_t)
        else if rs.name == "INTEGERP" then
          some (``Logic.integerp, ``logic_integerp_ne_nil_t)
        else none
      let some (liftC, neLemma) := entry?
        | throwError "replayRecognizer: not-literal elimination has no \
                      two-valued entry for {rs.name} (frontier)"
      unless verdict == SExpr.t do
        throwError "replayRecognizer: not-literal elimination of {rs.name} \
                    needs verdict t (got {repr verdict})"
      let v ← ctxValExpr cfg ctx cterm      -- <lift> xv, at the hit peel
      unless v.isAppOfArity liftC 1 do
        throwError "replayRecognizer: value of {repr cterm} is not ({liftC} _)"
      let xv := v.appArg!
      let hne ← mkAppM ``logic_not_nil_ne #[v, hNil]
      let hT ← mkAppM neLemma #[xv, hne]
      -- proof/value of the ORIGINAL term; its value is DEFEQ to the peel's
      -- (trueListp's cons match-arm), so the cast composes.
      let p ← ctxValProof cfg ctx term
      return ← mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hT]
    | _ => throwError "replayRecognizer: not-literal over a non-application"
  -- registered derivation ATOM-from-CONSP-false — ACL2's typeset resolution
  -- of `(ATOM u) ⇒ 'T` from CONSP-false evidence (originally the FALSE
  -- branch of an if on `(CONSP u)`; the ingredient now comes through the
  -- type-set walker's unified falsity channels).
  if let .cons (.atom (.symbol rs)) (.cons u .nil) := term then
    if rs.name == "ATOM" then
      let conspU : SExpr :=
        .cons (.atom (.symbol { name := "CONSP" })) (.cons u .nil)
      if let some hNil ← typeSetWalk cfg ctx (.isNil conspU) then
        unless verdict == SExpr.t do
          throwError "replayRecognizer: (ATOM _) under false-(CONSP _) \
                      evidence needs verdict t (got {repr verdict})"
        let ctxU ← pinTermOpaques cfg cfg.envExpr ctx conspU
        let vC ← ctxValExpr cfg ctxU conspU
        unless vC.isAppOfArity ``Logic.consp 1 do
          throwError "replayRecognizer: derived value of {repr conspU} is \
                      not (Logic.consp _)"
        let vu := vC.appArg!
        let hT ← mkAppM ``logic_atom_of_consp_nil #[vu, hNil]
        let v ← ctxValExpr cfg ctx term
        unless ← isDefEq v (mkApp (mkConst ``Logic.atom) vu) do
          throwError "replayRecognizer: value of {repr term} does not match the \
                      branch fact's (Logic.atom _) instance"
        let p ← ctxValProof cfg ctx term
        return ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hT]
  match term with
  | .cons (.atom (.symbol rs)) (.cons z .nil) =>
    if rs.name == "ACL2-NUMBERP" then
      let pin? ← match ctx.val? z with
        | some p => pure (some p)
        | none => builtinIntVal? cfg ctx z   -- gz-builtin TP route (e.g. LEN)
      let some (vz, pz) := pin?
        | throwError "replayRecognizer: acl2-numberp argument {repr z} has no pinned value"
      let k ← intValExpr? vz
      unless verdict == SExpr.t do
        throwError "replayRecognizer: acl2-numberp of a pinned int must have verdict t"
      let hNo ← proveNoShadow cfg { name := "ACL2-NUMBERP" }
      mkAppM ``re_acl2_numberp_int #[cfg.worldExpr, cfg.envExpr, reflectSExpr z, k, hNo, pz]
    -- RECOGNIZER-VIA-TYPE-PRESCRIPTION: `(REC (fn args))` ⇒ t where the verdict
    -- comes from `fn`'s EMITTED :TYPE-PRESCRIPTION whose corollary is exactly
    -- `(REC (fn formals))` (e.g. `(CONSP (INSERT E X))` for INSERT — ACL2 tags
    -- this node `type-prescription:<fn>`). The value of `(REC (fn args))` is
    -- `<REC-lift> vz` on `fn`'s opaque pinned value `vz`, which will NOT reduce
    -- to t; the TP hypothesis is what discharges it. Consumed, not inferred —
    -- exactly the source ACL2 records. (fn must be a user application with a
    -- matching TP corollary; anything else falls through to the general case.)
    else if let .cons (.atom (.symbol fs)) argsSpine := z then
      if let some (_, cor, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name) then
        let some (formals, _) := cfg.worldVal.defs.get? fs
          | throwError "replayRecognizer: {fs.name} not defined in the world"
        let args := (argsSpine.toList?).getD []
        let inst := ACL2.Replay.substTerm formals args cor
        -- REGISTERED TP-LATTICE derivation (recognizer/false via TP): ACL2's
        -- type-set closes `(CONSP app) ⇒ 'NIL` from the fn's TP whose TYPE
        -- part is `(INTEGERP app)` (the standard corollary encoding
        -- `(IF (INTEGERP app) <bound> 'NIL)`) — type-bit disjointness, the
        -- trusted-core theorem `logic_consp_nil_of_tp_integerp`. Consumed,
        -- not inferred: the node's recorded runes cite the TP (e.g.
        -- `(CONSP (ACL2-COUNT …)) ⇒ 'NIL` in admission waterfalls).
        let intTpShape : Bool := match inst with
          | .cons (.atom (.symbol ifS))
              (.cons (.cons (.atom (.symbol intS)) (.cons z' .nil))
                (.cons _ (.cons elseB .nil))) =>
            ifS.name == "IF" && intS.name == "INTEGERP" && z' == z
              && elseB == quoteNil
          | _ => false
        let latticeRoute :=
          rs.name == "CONSP" && verdict == SExpr.nil && intTpShape
        -- otherwise the corollary, instantiated at the actual args, must BE
        -- this term (so the TP fact proves exactly this recognizer's verdict).
        unless formals.length == args.length ∧
               ((inst == term ∧ verdict == SExpr.t) ∨ latticeRoute) do
          throwError "replayRecognizer: TP corollary of {fs.name} ({repr cor}) \
                      does not match {repr term} ⇒ {repr verdict} (frontier)"
        let some (vz, convz) := ctx.val? z
          | throwError "replayRecognizer: {repr z} has no pinned value (TP recognizer, frontier)"
        -- fact : <lifted corollary at args>[appPat ↦ vz] = t  =  (REC-lift vz) = t
        let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
          ++ (args.map reflectSExpr).toArray ++ #[vz, convz])
        let hVerdict ← if latticeRoute then
            mkAppM ``logic_consp_nil_of_tp_integerp #[fact]
          else pure fact
        let p ← ctxValProof cfg ctx term
        let v ← ctxValExpr cfg ctx term
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hVerdict]
      else
        let p ← ctxValProof cfg ctx term
        let v ← ctxValExpr cfg ctx term
        if ← isDefEq v verdictE then
          mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p,
              ← mkEqRefl verdictE]
        else if let some (_, cor, tpHyp) :=
            ctx.tpHypsAv.find? (fun (nm, _, _) => nm == fs.name) then
          -- REGISTERED ARGS-VALUED-TP derivation (recognizer/true,
          -- disjunctive-cons class; G1 arc 2026-07-29): fn's emitted TP
          -- corollary is `(IF (CONSP appPat) 'T (EQUAL appPat formalₖ))`
          -- (the BINARY-APPEND shape) and the k-th ACTUAL's value is a
          -- CONS — either disjunct forces CONSP, exactly ACL2's type-set
          -- leaf union under the cited TP rune. Consumed, not inferred.
          let some (formals, _) := cfg.worldVal.defs.get? fs
            | throwError "replayRecognizer: {fs.name} not defined in the world"
          let args := (argsSpine.toList?).getD []
          unless formals.length == args.length do
            throwError "replayRecognizer: args-valued TP — arity mismatch on {fs.name}"
          let appPat : SExpr :=
            .cons (.atom (.symbol fs))
              ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
          -- the corollary's disjunct chain: (IF (CONSP appPat) 'T rest)
          -- with rest = (EQUAL appPat formal) | (IF (EQUAL appPat formal)
          -- 'T rest') — collect the disjunct formals in order
          let rec disjFormals : SExpr → Option (List Symbol)
            | .cons (.atom (.symbol eqS))
                (.cons ap2 (.cons (.atom (.symbol fv)) .nil)) =>
              if eqS.name == "EQUAL" && ap2 == appPat then some [fv] else none
            | .cons (.atom (.symbol ifS))
                (.cons (.cons (.atom (.symbol eqS))
                    (.cons ap2 (.cons (.atom (.symbol fv)) .nil)))
                  (.cons qt' (.cons rest .nil))) =>
              if ifS.name == "IF" && eqS.name == "EQUAL" && ap2 == appPat
                  && qt' == quoteT then
                (disjFormals rest).map (fv :: ·)
              else none
            | _ => none
          let fvs? : Option (List Symbol) := match cor with
            | .cons (.atom (.symbol ifS))
                (.cons (.cons (.atom (.symbol cS)) (.cons ap .nil))
                  (.cons qt (.cons rest .nil))) =>
              if ifS.name == "IF" && cS.name == "CONSP" && ap == appPat
                  && qt == quoteT then disjFormals rest
              else none
            | _ => none
          let some fvs := fvs?
            | throwError "replayRecognizer: args-valued TP corollary of {fs.name} \
                ({repr cor}) is not the disjunctive-cons shape (frontier)"
          unless rs.name == "CONSP" && verdict == SExpr.t do
            throwError "replayRecognizer: args-valued TP of {fs.name} supports only \
                (CONSP _) ⇒ 'T (got {repr term} ⇒ {repr verdict}, frontier)"
          let argVals ← args.mapM (ctxValExpr cfg ctx ·)
          let argConvs ← args.mapM (ctxValProof cfg ctx ·)
          -- per-disjunct consp evidence: the actual's value is a SYNTACTIC
          -- cons, or the clause context holds `(consp arg)` (a (not (consp
          -- arg))-falsity fact or a positive branch fact) — exactly the
          -- type-alist entries ACL2's type-set consults for the leaf union
          let evidence ← fvs.mapM fun fv => do
            let some k := formals.findIdx? (· == fv)
              | throwError "replayRecognizer: args-valued TP of {fs.name} — \
                  disjunct var {fv.name} is not a formal"
            let some vk := argVals[k]?
              | throwError "replayRecognizer: args-valued TP — no value for arg {k}"
            let some argk := args[k]?
              | throwError "replayRecognizer: args-valued TP — no arg {k}"
            match ← typeSetWalk cfg ctx (.isConspT argk) with
            | some h => pure h
            | none =>
              throwError "replayRecognizer: args-valued TP of {fs.name} — \
                  no consp evidence for disjunct arg {repr argk} (frontier)"
          let some (vz, convz) := ctx.val? z
            | throwError "replayRecognizer: {repr z} has no pinned value \
                (args-valued TP recognizer, frontier)"
          let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
            ++ (args.map reflectSExpr).toArray ++ argVals.toArray
            ++ #[vz] ++ argConvs.toArray ++ #[convz])
          let hVerdict ← match evidence with
            | [e1] => mkAppM ``logic_consp_t_of_tp_disj2 #[fact, e1]
            | [e1, e2] => mkAppM ``logic_consp_t_of_tp_disj3 #[fact, e1, e2]
            | _ => throwError "replayRecognizer: args-valued TP of {fs.name} — \
                {evidence.length} disjuncts unsupported (frontier)"
          unless ← isDefEq v (mkApp (mkConst ``Logic.consp) vz) do
            throwError "replayRecognizer: value of {repr term} does not match \
                (Logic.consp _) on the pinned application value"
          mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hVerdict]
        else
          -- REGISTERED BUILTIN-RANGE derivation: ACL2's type-set knows each
          -- primitive's return type natively (`type-set-binary-+` …), so a
          -- recognizer verdict on a BUILTIN application is the primitive's
          -- RANGE — a trusted-core theorem, keyed (recognizer, builtin head).
          -- The value is opaque-argument-blocked (`Logic.plus vz …` does not
          -- reduce), which is exactly why the range fact is a lemma.
          let range? : Option Name :=
            if rs.name == "CONSP" && verdict == SExpr.nil
                && fs.name == "BINARY-+" then
              some ``logic_consp_plus_nil
            else none
          match range? with
          | some lem =>
            unless v.isAppOfArity ``Logic.consp 1
                && v.appArg!.isAppOfArity ``Logic.plus 2 do
              throwError "replayRecognizer: value of {repr term} does not match \
                          the registered builtin-range shape (frontier)"
            let arg := v.appArg!
            let h ← mkAppM lem #[arg.appFn!.appArg!, arg.appArg!]
            mkAppM ``re_val_cast
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, h]
          | none =>
            -- TRUE-LISTP/CDR closure (sorting-completion-2 Class A,
            -- ORDERED-PERMS): (TRUE-LISTP (CDR u)) ⇒ 'T from an in-scope
            -- TRUTHY true-listp fact on u (a false `(not (true-listp u))`
            -- lit/seg/branch fact) — ACL2's type-set closure, value-level
            -- (`logic_trueListp_cdr_t`).
            if rs.name == "TRUE-LISTP" && verdict == SExpr.t
                && fs.name == "CDR" then do
              let .cons _ (.cons (.cons _ (.cons u .nil)) .nil) := term
                | throwError "replayRecognizer: TRUE-LISTP/CDR closure — \
                    unexpected term shape {repr term}"
              let tlpU : SExpr := .cons (.atom (.symbol { name := "TRUE-LISTP" }))
                (.cons u .nil)
              let ctxU ← pinTermOpaques cfg cfg.envExpr ctx tlpU
              let vTlpU ← ctxValExpr cfg ctxU tlpU
              let sources := falsitySources ctxU
              -- EQUATION-transport evidence (the observed ORDERED-PERMS
              -- route): u equation-equals (CONS a d) via a false
              -- (NOT (EQUAL …)) fact, and d carries the truthy true-listp
              -- fact (the elim RESTRICTION literal) — trueListp vu then
              -- reduces to trueListp vd definitionally.
              let hT ← do
                match ← typeSetWalk cfg ctxU (.isTruthy tlpU) with
                | some hne => mkAppM ``logic_trueListp_cdr_t #[hne]
                | none => do
                  -- CONS-fact route (the hoisted `tlpCons` demand): a false
                  -- `(NOT (TRUE-LISTP (CONS a w)))` fact on the recognizer's
                  -- inner term w = (CDR u) — `trueListp (cons a w)` IS
                  -- `trueListp w` definitionally, and two-valuedness gives
                  -- the 'T verdict (ORDERED-PERMS Subgoal *1/7'5').
                  let wT : SExpr := .cons (.atom (.symbol { name := "CDR" }))
                    (.cons u .nil)
                  let mut viaCons? : Option Expr := none
                  for (st, hf) in sources do
                    if viaCons?.isNone then
                      let inner? : Option SExpr :=
                        match st with
                        | .cons (.atom (.symbol ns))
                            (.cons (.cons (.atom (.symbol rs2))
                              (.cons (.cons (.atom (.symbol cs))
                                (.cons a2 (.cons d2 .nil))) .nil)) .nil) =>
                          if ns.name == "NOT" && rs2.name == "TRUE-LISTP" &&
                              cs.name == "CONS" && d2 == wT then
                            some (.cons (.atom (.symbol { name := "CONS" }))
                              (.cons a2 (.cons d2 .nil)))
                          else none
                        | _ => none
                      if let some consT := inner? then do
                        let tlpC : SExpr :=
                          .cons (.atom (.symbol { name := "TRUE-LISTP" }))
                            (.cons consT .nil)
                        let ctxC ← pinTermOpaques cfg cfg.envExpr ctxU tlpC
                        let vTlpC ← ctxValExpr cfg ctxC tlpC
                        if ← isDefEq (← inferType hf)
                            (← mkEq (mkApp (mkConst ``Logic.not) vTlpC)
                              (mkConst ``SExpr.nil)) then
                          let hne ← mkAppM ``logic_not_nil_ne #[vTlpC, hf]
                          viaCons? := some (← mkAppM
                            ``logic_trueListp_ne_nil_t #[vTlpC.appArg!, hne])
                  if let some h := viaCons? then pure h else do
                  let mut viaEq? : Option Expr := none
                  for (st, hf) in sources do
                    if viaEq?.isNone then
                      let eqSides? : Option (SExpr × SExpr) := do
                        let .cons (.atom (.symbol ns))
                            (.cons (.cons (.atom (.symbol eqS))
                              (.cons p (.cons q .nil))) .nil) := st | none
                        guard (ns.name == "NOT" && eqS.name == "EQUAL")
                        if q == u then some (p, q)
                        else if p == u then some (q, p)
                        else none
                      if let some (c, _) := eqSides? then
                        if let .cons (.atom (.symbol cS))
                            (.cons a2 (.cons d2 .nil)) := c then
                          if cS.name == "CONS" then do
                            let notTlpD : SExpr :=
                              .cons (.atom (.symbol { name := "NOT" }))
                                (.cons (.cons
                                  (.atom (.symbol { name := "TRUE-LISTP" }))
                                  (.cons d2 .nil)) .nil)
                            let tlpD : SExpr :=
                              .cons (.atom (.symbol { name := "TRUE-LISTP" }))
                                (.cons d2 .nil)
                            let ctxD ← pinTermOpaques cfg cfg.envExpr ctxU
                              (.cons (.atom (.symbol { name := "CONS" }))
                                (.cons a2 (.cons d2 .nil)))
                            let vTlpD ← ctxValExpr cfg ctxD tlpD
                            let mut hD? : Option Expr := none
                            for (st2, hf2) in sources do
                              if hD?.isNone && st2 == notTlpD then
                                if ← isDefEq (← inferType hf2)
                                    (← mkEq (mkApp (mkConst ``Logic.not) vTlpD)
                                      (mkConst ``SExpr.nil)) then
                                  hD? := some hf2
                            if let some hfD := hD? then do
                              let pq : SExpr :=
                                .cons (.atom (.symbol { name := "EQUAL" }))
                                  (.cons c (.cons u .nil))
                              -- the fact's own equality orientation
                              let stEq := match st with
                                | .cons _ (.cons e .nil) => e
                                | _ => pq
                              let ctxE ← pinTermOpaques cfg cfg.envExpr ctxD stEq
                              let vPQ ← ctxValExpr cfg ctxE stEq
                              if ← isDefEq (← inferType hf)
                                  (← mkEq (mkApp (mkConst ``Logic.not) vPQ)
                                    (mkConst ``SExpr.nil)) then
                                let hneEq ← mkAppM ``logic_not_nil_ne #[vPQ, hf]
                                let heq ← mkAppM ``Logic.eq_of_equal_ne_nil
                                  #[hneEq]  -- vp = vq (record orientation)
                                -- orient to vu = v(CONS a d)
                                let .cons _ (.cons pT (.cons _ .nil)) := stEq
                                  | pure ()
                                let heqU ← if pT == u then pure heq
                                  else mkAppM ``Eq.symm #[heq]
                                let vd ← ctxValExpr cfg ctxE d2
                                let va ← ctxValExpr cfg ctxE a2
                                let _ := va
                                -- trueListp vu = trueListp (cons va vd)
                                --             ≡ trueListp vd (defeq)
                                -- trueListp vu = trueListp (cons va vd)
                                -- ≡ trueListp vd (defeq); ≠ nil from d
                                let hcong ← mkAppM ``congrArg
                                  #[mkConst ``Logic.trueListp, heqU]
                                let hDne ← mkAppM ``logic_not_nil_ne
                                  #[vTlpD, hfD]
                                let _ := vd
                                viaEq? := some (← mkAppM ``ne_of_eq_of_ne
                                  #[hcong, hDne])
                  match viaEq? with
                  | some h => mkAppM ``logic_trueListp_cdr_t #[h]
                  | none =>
                    throwError "replayRecognizer: TRUE-LISTP/CDR closure — no \
                        truthy true-listp fact for {repr u} in scope \
                        (direct, cons-fact, or equation-transport; frontier)"
              unless vTlpU.isAppOfArity ``Logic.trueListp 1 do
                throwError "replayRecognizer: value of {repr tlpU} is not \
                    (Logic.trueListp _)"
              unless ← isDefEq v (mkApp (mkConst ``Logic.trueListp)
                  (mkApp (mkConst ``Logic.cdr) vTlpU.appArg!)) do
                throwError "replayRecognizer: value of {repr term} does not \
                    match (Logic.trueListp (Logic.cdr _))"
              mkAppM ``re_val_cast
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE,
                  p, hT]
            else if rs.name == "CONSP" && verdict == SExpr.t then do
              -- CONSP closure (sorting-completion-2, ORDERED-PERMS):
              -- `deriveConspT` — syntactic-cons value, clause evidence,
              -- IF-branch split, or (CDR u)-of-a-proper-list
              let .cons _ (.cons w .nil) := term
                | throwError "replayRecognizer: CONSP closure — \
                    unexpected term shape {repr term}"
              let ctxU ← pinTermOpaques cfg cfg.envExpr ctx term
              let some hT ← typeSetWalk cfg ctxU (.isConspT w)
                | throwError "replayRecognizer: CONSP closure — no consp \
                    derivation for {repr w} in scope (frontier)"
              let vW ← ctxValExpr cfg (← pinTermOpaques cfg cfg.envExpr ctxU w) w
              unless ← isDefEq v (mkApp (mkConst ``Logic.consp) vW) do
                throwError "replayRecognizer: value of {repr term} does not \
                    match (Logic.consp _)"
              mkAppM ``re_val_cast
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE,
                  p, hT]
            else if rs.name == "CONSP" && verdict == SExpr.nil &&
                ((cfg.gzTpBasicTs.lookup fs.name).isSome ||
                 (builtinRecogFacts.find? (fun e => e.1 == fs.name)).isSome) then do
              -- R2 gate (audit 2026-08-07 S3: the guard is now
              -- DATA-DRIVEN — emitted TP presence, not the lemma
              -- table's keys; the gate runs FIRST with the step's
              -- recorded :TYPESET when present).
              recogVerdictGate cfg fs.name "CONSP" false stepTs
              -- BUILTIN never-a-cons (BNEXT-SIZE route layer 3: the
              -- recognizer/false class in admission trees of LEN-based
              -- measures — (CONSP (LEN X)) ⇒ 'NIL). The trusted-core
              -- consp-nil lemma applies at the composed value, GATED on
              -- the fn's EMITTED nonneg-int TP corollary.
              let .cons _ (.cons inner .nil) := term
                | throwError "replayRecognizer: internal — non-unary \
                    recognizer at the builtin arm"
              let .cons _ (.cons innerArg .nil) := inner
                | throwError "replayRecognizer: {fs.name} not \
                    applied to exactly one arg: {repr inner}"
              let ctxB ← pinTermOpaques cfg cfg.envExpr ctx innerArg
              let hT ← match builtinRecogFacts.find? (fun e => e.1 == fs.name) with
                | some (_, conspLem, _) =>
                  -- BUILTIN route: trusted-core value lemma, anchored to
                  -- the emitted corollary shape.
                  let some cor := cfg.gzTps.lookup fs.name
                    | throwError "replayRecognizer: builtin {fs.name}'s TP \
                        corollary not emitted (type facts from ACL2 — \
                        emission gap)"
                  let .cons _ (.cons (.cons _ (.cons app _)) _) := cor
                    | throwError "replayRecognizer: {fs.name} corollary \
                        destructure failed: {repr cor}"
                  unless cor == intTpCorollary app do
                    throwError "replayRecognizer: {fs.name}'s emitted \
                        corollary drifted from the nonneg-int shape: \
                        {repr cor}"
                  let vArg ← ctxValExpr cfg ctxB innerArg
                  mkAppM conspLem #[vArg]
                | none =>
                  -- WORLD-fn route (audit 2026-08-07 S3, the compound
                  -- arm's twin): the consp-nil fact from the fn's BOUND
                  -- tp: hypothesis via logic_consp_nil_of_int_tp_fact.
                  let ctxB2 ← pinTermOpaques cfg cfg.envExpr ctxB inner
                  let some (_, cor, tpHyp) :=
                      ctxB2.tpHyps.find? (fun (n, _, _) => n == fs.name)
                    | throwError "replayRecognizer: {fs.name} passed the \
                        emitted-data gate but has neither a trusted-core \
                        value lemma nor a bound tp: hypothesis (frontier)"
                  let some (formals, _) := cfg.worldVal.defs.get? fs
                    | throwError "replayRecognizer: {fs.name} has a tp: \
                        hypothesis but is not in the world (internal)"
                  let args := [innerArg]
                  unless formals.length == args.length do
                    throwError "replayRecognizer: {fs.name} arity \
                        mismatch (frontier)"
                  let inst := ACL2.Replay.substTerm formals args cor
                  unless inst == intTpCorollary inner do
                    throwError "replayRecognizer: {fs.name}'s \
                        instantiated corollary {repr inst} is not the \
                        nonneg-int shape at {repr inner} (frontier)"
                  let some (vz, convz) := ctxB2.val? inner
                    | throwError "replayRecognizer: {repr inner} has no \
                        pinned value (totality hypothesis missing?)"
                  let hFact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
                    ++ (args.map reflectSExpr).toArray ++ #[vz, convz])
                  mkAppM ``logic_consp_nil_of_int_tp_fact #[hFact]
              let pB ← ctxValProof cfg ctxB term
              let vB ← ctxValExpr cfg ctxB term
              mkAppM ``re_val_cast
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, vB,
                  verdictE, pB, hT]
            else if let some (spec, hypV) := citedTpThms.findSome? (fun tn =>
                ctx.tpThmHyps.find? (fun (s, _) => s.name == tn)) then do
              -- TP-CLASSED THEOREM route (tpthm sub-arc 2026-08-04,
              -- RESURRECTED at the final close-out — the FIRST :CLASSES
              -- consumer; killed at 910785a for lacking a green consumer,
              -- now reachable): the node's ttree cites a
              -- (:TYPE-PRESCRIPTION <defthm>) rune naming a theorem, not a
              -- defun admission TP (RM has none; TRUE-LISTP-RM is
              -- `:CLASSES :TYPE-PRESCRIPTION`). Match the theorem's
              -- conclusion against the recognizer term (no σ is emitted
              -- for type-set rule applications; one-way matching is
              -- deterministic and recompute-checked), relieve the hyp
              -- instance from the clause context, MP, and pin the exact
              -- verdict by the recognizer's trusted-core two-valued
              -- range. Anchored per BUG-023: CITED runes only.
              let (hyp?, concl) := match spec.formula with
                | .cons (.atom (.symbol imp)) (.cons h (.cons c .nil)) =>
                  if imp.name == "IMPLIES" then (some h, c)
                  else (none, spec.formula)
                | f => (none, f)
              let some σ := matchPattern? concl term
                | throwError "replayRecognizer/tpthm: {spec.name}'s \
                    conclusion {repr concl} does not match {repr term} \
                    (frontier)"
              let σvars := σ.map (·.1)
              let σterms := σ.map (·.2)
              unless ACL2.Replay.substTerm σvars σterms concl == term do
                throwError "replayRecognizer/tpthm: match recompute failed \
                    (internal)"
              unless (ACL2.Replay.freeVars spec.formula).all
                  (σvars.contains ·) do
                throwError "replayRecognizer/tpthm: {spec.name} has free \
                    variables outside the conclusion match (frontier — \
                    free-variable TP hyps)"
              unless verdict == SExpr.t do
                throwError "replayRecognizer/tpthm: verdict {repr verdict} \
                    ≠ 'T (frontier)"
              let (hInst, ctx1) ← instantiateEvTrueHypAt cfg ctx hypV
                σvars σterms spec.formula
              let instF := ACL2.Replay.substTerm σvars σterms spec.formula
              let ctx2 ← pinTermOpaques cfg cfg.envExpr ctx1 instF
              let hFne ← mkAppM ``ne_nil_of_evtrue_conv
                #[hInst, ← ctxValProof cfg ctx2 instF]
              let (hCne, ctxF) ← match hyp? with
                | none => pure (hFne, ctx2)
                | some h => do
                  let hσ := ACL2.Replay.substTerm σvars σterms h
                  let notH : SExpr := .cons
                    (.atom (.symbol { name := "NOT" })) (.cons hσ .nil)
                  let ctx3 ← pinTermOpaques cfg cfg.envExpr ctx2 hσ
                  let vH ← ctxValExpr cfg ctx3 hσ
                  -- litFactByTermChecked? already scans litFacts THEN
                  -- segFacts with a per-candidate type check; an unchecked
                  -- segFacts fallback would re-open the cross-env-context
                  -- hole that helper closes (tpthm audit F1 — a dead arm
                  -- deleted)
                  let hit ← ctx3.litFactByTermChecked? notH
                    (← mkEq (mkApp (mkConst ``Logic.not) vH)
                      (mkConst ``SExpr.nil))
                  let some hNotNil := hit
                    | throwError "replayRecognizer/tpthm: {spec.name}'s hyp \
                        instance {repr hσ} has no (not …)-falsity fact in \
                        scope (frontier)"
                  let hne ← mkAppM ``logic_not_nil_ne #[vH, hNotNil]
                  pure (← mkAppM ``implies_value_mp #[hFne, hne], ctx3)
              -- exact-'T pin: the recognizer's TRUSTED-CORE two-valued
              -- range (same registry as dischargeRuleHyp's routeBool)
              let coreBool? : Option (Name × Name) :=
                if rs.name == "TRUE-LISTP" then
                  some (``Logic.trueListp, ``logic_trueListp_ne_nil_t)
                else if rs.name == "CONSP" then
                  some (``Logic.consp, ``logic_consp_ne_nil_t)
                else none
              let some (liftC, neLemma) := coreBool?
                | throwError "replayRecognizer/tpthm: {rs.name} has no \
                    trusted-core two-valued range registered (frontier)"
              let vC ← ctxValExpr cfg ctxF term
              unless vC.isAppOfArity liftC 1 do
                throwError "replayRecognizer/tpthm: value of {repr term} \
                    is not ({liftC} _)"
              let hT ← mkAppM neLemma #[vC.appArg!, hCne]
              mkAppM ``re_val_cast
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, vC,
                  verdictE, ← ctxValProof cfg ctxF term, hT]
            else
              throwError "replayRecognizer: value of {repr term} does not reduce to {repr verdict} \
                        (no TP hypothesis for {fs.name}; cited TP runes \
                        {citedTpThms})"
    else
      let p ← ctxValProof cfg ctx term
      let v ← ctxValExpr cfg ctx term
      if ← isDefEq v verdictE then
        let hv ← mkEqRefl verdictE
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hv]
      else if rs.name == "CONSP" && verdict == SExpr.t then do
        -- CONSP of a variable/simple inner resolved from the clause context
        -- (ORDERED-PERMS: (CONSP B) ⇒ 'T from the truthy-(CDR B) evidence)
        let .cons _ (.cons w .nil) := term
          | throwError "replayRecognizer: CONSP closure — unexpected term \
              shape {repr term}"
        let ctxU ← pinTermOpaques cfg cfg.envExpr ctx term
        let some hT ← typeSetWalk cfg ctxU (.isConspT w)
          | throwError "replayRecognizer: CONSP closure — no consp \
              derivation for {repr w} in scope (frontier); lit \
              {repr (ctxU.litFacts.map (·.2.1))}; seg \
              {repr (ctxU.segFacts.map (·.1))}; branch \
              {repr (ctxU.branchFacts.map (fun (t,_,sg,_) => (t, sg)))}"
        let vW ← ctxValExpr cfg (← pinTermOpaques cfg cfg.envExpr ctxU w) w
        unless ← isDefEq v (mkApp (mkConst ``Logic.consp) vW) do
          throwError "replayRecognizer: value of {repr term} does not \
              match (Logic.consp _)"
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hT]
      else
        throwError "replayRecognizer: value of {repr term} does not reduce to {repr verdict}"
  | _ => throwError "replayRecognizer: not a recognizer application: {repr term}"

/-- A node's R-PAYLOAD (the R-parameterized rewrite lane, option M
    2026-08-14): what a node contributes when its recorded chain ENDS
    under a user equivalence `rel` instead of `equal`. The node's own
    claim then splits in two — an eval-EQUALITY `eval lhs = eval a`
    (the returned `Expr`), and the relation fact `hR : EvTrue w env
    (rel a b)` with `b` the node's recorded rhs. There is no eval
    equality between `a` and `b`; the payload must be COLLAPSED at the
    enclosing congruence frame (`collapseAtCongruenceFrame`) before it
    can compose with anything, and every consumer that cannot collapse
    it hard-fails on `some`. -/
structure RPayload where
  /-- The equivalence relation's fn symbol (`PERM`, `SAME-LEN2`, …). -/
  rel : Symbol
  /-- The R-step's sides: `hR : EvTrue w env (rel a b)`. `a` is where
      the returned eval-equality lands; `b` is the node's recorded rhs. -/
  a : SExpr
  b : SExpr
  /-- `EvTrue w env (rel a b)` — from a clause literal's falsity (the
      solidify class) or a stored R-rule instance (the with-lemma class);
      never assumed. -/
  hR : Expr

/-- The node-level recursion interface (WP2 Stage 2): the knot's entry
    points as a record, so node recipes are top-level defs taking `rec`
    instead of members of one `mutual` block (new recipes land additively).
    Tied ONCE below (`replayNode`/`replayRewrites` — the public names and
    signatures are unchanged from the pre-WP2 mutual). -/
structure NodeRec where
  /-- `replayNode` — the per-node rune dispatcher. `some payload` = the
      node's recorded chain ended under a user equivalence (see
      `RPayload`); the `Expr` then proves `eval lhs = eval payload.a`,
      NOT `eval lhs = eval rhs`. -/
  node : ReplayConfig → ReplayCtx → ProofNode → MetaM (Expr × Option RPayload)
  /-- `replayRewrites` — the chain walker (the strip machinery and the
      write-only `depth` retired with gstack-coordinate emission —
      fold-back audit 2026-07-31 V7). -/
  rewrites : ReplayConfig → ReplayCtx → SExpr → List ProofNode →
    MetaM (Option (Expr × Bool) × SExpr)

/-- Bridge rewrite-equal's built-in NIL NORMALIZATION (rewrite.lisp:18089-92,
    unconditional/syntactic — ACL2 never records it): a chain-end mismatch of
    EXACTLY the shape `(EQUAL 'NIL x)` / `(EQUAL x 'NIL)` (reached) vs
    `(IF x 'NIL 'T)` (recorded), SAME `x`. Returns the fuel-eq chain
    `eval reached ≡ eval recorded`, or `none` when the shapes don't match
    (the caller's fail-closed mismatch error stands). -/
def bridgeEqualNilNorm (cfg : ReplayConfig) (ctx : ReplayCtx)
    (reached recorded : SExpr) : MetaM (Option Expr) := do
  let eqT (a b : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil))
  -- the if-interp call-stack fold, L-orientation (rewrite.lisp:3791-3793,
  -- the PCE tower's residue; RESURRECTED at the final close-out — killed
  -- at 910785a, its consumer now reachable): reached
  -- (EQUAL 'T (EQUAL a b)) vs recorded (EQUAL a b)
  if let .cons (.atom (.symbol re2)) (.cons a (.cons b .nil)) := recorded then
    if re2.name == "EQUAL" && reached == eqT quoteT recorded then
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx recorded
      let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
      let va ← ctxValExpr cfg ctx a
      let vb ← ctxValExpr cfg ctx b
      let ha ← ctxValProof cfg ctx a
      let hb ← ctxValProof cfg ctx b
      return some (← mkAppM ``re_equal_t_fold_l
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b,
          va, vb, hNoEq, ha, hb])
  -- the BOOLEAN-TP fold (the PCE tower's residue; RESURRECTED, same
  -- round): reached (EQUAL p 'T) vs recorded p, where p's fn carries an
  -- emitted BOOLEAN TP corollary `(IF (EQUAL p 'T) 'T (EQUAL p 'NIL))`
  -- — two-valuedness makes the fold a value identity (consumed, not
  -- inferred).
  if reached == eqT recorded quoteT then
    if let .cons (.atom (.symbol fs)) argsSpine := recorded then
      if let some (_, cor, tpHyp) :=
          ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) then do
        let some (formals, _) := cfg.worldVal.defs.get? fs | return none
        let args := (argsSpine.toList?).getD []
        if formals.length == args.length then do
          let inst := ACL2.Replay.substTerm formals args cor
          let expected : SExpr :=
            .cons (.atom (.symbol { name := "IF" }))
              (.cons (eqT recorded quoteT)
                (.cons quoteT (.cons (eqT recorded quoteNil) .nil)))
          if inst == expected then do
            let ctx ← pinTermOpaques cfg cfg.envExpr ctx recorded
            let some (vp, convp) := ctx.val? recorded | return none
            let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
              ++ (args.map reflectSExpr).toArray ++ #[vp, convp])
            let hveq ← mkAppM ``logic_equal_t_self_of_boolean_tp #[fact]
            let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
            let hp ← ctxValProof cfg ctx recorded
            let hOuter ← mkAppM ``conv_builtin2
              #[cfg.worldExpr, cfg.envExpr,
                reflectSymbol { name := "EQUAL" }, reflectSExpr recorded,
                reflectSExpr quoteT, vp, mkConst ``SExpr.t,
                mkApp2 (mkConst ``Logic.equal) vp (mkConst ``SExpr.t),
                ← proveNotSpecial { name := "EQUAL" }, hNoEq, hp,
                ← mkAppM ``re_val_quote
                  #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t],
                ← mkAppM ``callBuiltin_equal #[vp, mkConst ``SExpr.t]]
            return some (← mkAppM ``fuel_eq_of_conv #[hOuter, hp, hveq])
  let .cons (.atom (.symbol ifS)) (.cons x (.cons thn (.cons els .nil))) := recorded
    | return none
  unless ifS.name == "IF" do return none
  -- the NIL forms: recorded (IF x 'NIL 'T)
  if thn == quoteNil && els == quoteT then
    let some lem :=
        (if reached == eqT quoteNil x then some ``re_equal_nil_norm_l
         else if reached == eqT x quoteNil then some ``re_equal_nil_norm_r
         else none) | return none
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx x
    let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
    let hx ← proveConv cfg cfg.envExpr ctx x
    return some (← mkAppM lem #[cfg.worldExpr, cfg.envExpr, reflectSExpr x, hNoEq, hx])
  -- the EQUALITYP form (rewrite.lisp:18093): reached (EQUAL (EQUAL a b) r),
  -- recorded (IF (EQUAL a b) (EQUAL r 'T) (IF r 'NIL 'T))
  let .cons (.atom (.symbol xeS)) (.cons a (.cons b .nil)) := x | return none
  unless xeS.name == "EQUAL" do return none
  let .cons (.atom (.symbol thS)) (.cons r (.cons rtq .nil)) := thn | return none
  unless thS.name == "EQUAL" && rtq == quoteT do return none
  unless els == .cons (.atom (.symbol { name := "IF" }))
      (.cons r (.cons quoteNil (.cons quoteT .nil))) do return none
  unless reached == eqT x r do return none
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx reached
  let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
  let ha ← proveConv cfg cfg.envExpr ctx a
  let hb ← proveConv cfg cfg.envExpr ctx b
  let hr ← proveConv cfg cfg.envExpr ctx r
  return some (← mkAppM ``re_equal_equalityp_norm
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, reflectSExpr r,
      hNoEq, ha, hb, hr])

/-- `bridgeEqualNilNorm` at DEPTH: descend the UNIQUE-difference path of
    reached vs recorded (same head/arity along it), bridge the mismatching
    subterm, and lift through the common frames (sorting-completion-2,
    ORDERED-PERMS Subgoal *1/2'5' literal 4: the normalization fires INSIDE
    an if-finish/combined branch after the 'NIL substitution). More than one
    differing child at any level → `none` (the caller's fail-closed
    mismatch error stands). -/
partial def bridgeEqualNilNormDeep (cfg : ReplayConfig) (ctx : ReplayCtx)
    (reached recorded : SExpr) : MetaM (Option Expr) := do
  if let some h ← bridgeEqualNilNorm cfg ctx reached recorded then
    return some h
  let .cons (.atom (.symbol f1)) args1 := reached | return none
  let .cons (.atom (.symbol f2)) args2 := recorded | return none
  unless f1 == f2 && f1.name != "QUOTE" do return none
  let some l1 := args1.toList? | return none
  let some l2 := args2.toList? | return none
  unless l1.length == l2.length do return none
  let diffs := (l1.zip l2).zipIdx.filter fun ((x, y), _) => x != y
  let [((x, y), i)] := diffs | return none
  let some inner ← bridgeEqualNilNormDeep cfg ctx x y | return none
  let st : PathStep := { fn := f1, arity := l1.length, argIdx := i,
                         siblings := l1.eraseIdx i }
  return some (← applyStep cfg.worldExpr cfg.envExpr st x y inner)

/-- Lift one rewrite-if SWAPPED-P normalization step
    (`re_if_neg_test_swap`) from position `steps` (where `sub =
    (IF (IF c 'NIL 'T) a b)` sits inside `root`) to the root:
    `eval root ≡ eval root[steps ↦ swapped]`. Shared by
    `bridgeIfNegTestSwap` and the if-finish joint normalization
    (`normalizeSwapsToward`). -/
def liftNegTestSwap (cfg : ReplayConfig) (steps : List PathStep)
    (root sub c a b swapped : SExpr) : MetaM (Expr × SExpr) := do
  let mut inner ← mkAppM ``re_if_neg_test_swap
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr a, reflectSExpr b]
  let mut curL := sub
  let mut curR := swapped
  for st in steps.reverse do
    inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
    curL := rebuild st curL
    curR := rebuild st curR
  unless curL == root do
    throwError "liftNegTestSwap: reconstructed {repr curL} ≠ {repr root}"
  return (inner, curR)

/-- The EQUAL-NIL variant of `liftNegTestSwap` (sorting-completion-2
    Class A): `(IF (EQUAL 'NIL c) a b) ⇒ (IF c b a)` via
    `re_if_equal_nil_test_swap` (EQUAL unshadowed — kernel-decided). -/
def liftEqualNilTestSwap (cfg : ReplayConfig) (steps : List PathStep)
    (root sub c a b swapped : SExpr) : MetaM (Expr × SExpr) := do
  let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
  let mut inner ← mkAppM ``re_if_equal_nil_test_swap
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr a,
      reflectSExpr b, hNoEq]
  let mut curL := sub
  let mut curR := swapped
  for st in steps.reverse do
    inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
    curL := rebuild st curL
    curR := rebuild st curR
  unless curL == root do
    throwError "liftEqualNilTestSwap: reconstructed {repr curL} ≠ {repr root}"
  return (inner, curR)

/-- The rewrite-if SWAPPED-P bridge (rewrite.lisp:17726-37): walk `rel` from
    `start`; when the rewritten test of an if has the negation shape
    `(IF c 'NIL 'T)`, ACL2 strips the negation and SWAPS the branches before
    descending — unconditionally and without recording a step (subsequent
    branch bkptrs refer to the swapped orientation). Two firing positions,
    both deterministic shape checks (never a search): a frame DESCENDS into
    such an if (the swap must precede the descent), or the node sits ON the
    if — its recorded `lhs` IS the swapped orientation (exact match
    required). Emits the normalization lifted to the chain root and returns
    the swapped running term; `none` when neither case applies (the caller's
    fail-closed navigation stands). -/
def bridgeIfNegTestSwap (cfg : ReplayConfig) (rel : List PathFrame)
    (start lhs : SExpr) : MetaM (Option (Expr × SExpr)) := do
  let mut cur := start
  let mut steps : List PathStep := []
  let emitSwap (steps : List PathStep) (cur c a b swapped : SExpr) :
      MetaM (Option (Expr × SExpr)) := do
    let (inner, root') ← liftNegTestSwap cfg steps start cur c a b swapped
    return some (inner, root')
  for fr in rel do
    match fr with
    | .boundary .. => return none      -- residual boundary: not this bridge's case
    | .argLam .. => return none        -- lambda descent: not this bridge's case
    | .arg idx _ =>
      if let .cons (.atom (.symbol ifS))
          (.cons (.cons (.atom (.symbol ifS2))
              (.cons c (.cons qn (.cons qt2 .nil))))
            (.cons a (.cons b .nil))) := cur then
        if ifS.name == "IF" && ifS2.name == "IF" && qn == quoteNil && qt2 == quoteT then
          let swapped : SExpr :=
            .cons (.atom (.symbol ifS)) (.cons c (.cons b (.cons a .nil)))
          return ← emitSwap steps cur c a b swapped
      match asApp cur with
      | none => return none
      | some (fn, args) =>
        if args.length > 3 || idx < 1 || idx > args.length then return none
        let siblings := (args.zipIdx).filterMap
          (fun (a, i) => if i + 1 == idx then none else some a)
        steps := steps ++ [{ fn, arity := args.length, argIdx := idx - 1, siblings }]
        cur := args[idx - 1]!
  -- TARGET case: the node is ON the swapped if — recorded lhs must BE the
  -- swapped orientation exactly
  if let .cons (.atom (.symbol ifS))
      (.cons (.cons (.atom (.symbol ifS2))
          (.cons c (.cons qn (.cons qt2 .nil))))
        (.cons a (.cons b .nil))) := cur then
    if ifS.name == "IF" && ifS2.name == "IF" && qn == quoteNil && qt2 == quoteT then
      let swapped : SExpr :=
        .cons (.atom (.symbol ifS)) (.cons c (.cons b (.cons a .nil)))
      if swapped == lhs then
        return ← emitSwap steps cur c a b swapped
  return none

/-- Find the first position where `cur` has a SWAPPED-P redex
    `(IF (IF c 'NIL 'T) a b)` while `target` has the stripped test `c` at the
    same position — descending only through structurally-parallel
    applications into the FIRST differing argument (a deterministic zip,
    never a search). Returns the path steps and the redex parts. -/
partial def findSwapPos (cur target : SExpr) (steps : List PathStep) :
    Option (List PathStep × SExpr × Bool × SExpr × SExpr × SExpr) :=
  if cur == target then none
  else
    -- the Bool tags the variant: false = the NOT-shape `(IF (IF c 'NIL 'T)
    -- a b)`; true = the EQUAL-NIL shape `(IF (EQUAL 'NIL c) a b)`
    -- (sorting-completion-2 Class A) — both swap to `(IF c b a)`
    let fire? : Option (Bool × SExpr × SExpr × SExpr) :=
      match cur, target with
      | .cons (.atom (.symbol ifS)) (.cons (.cons (.atom (.symbol ifS2))
            (.cons c (.cons qn (.cons qt2 .nil)))) (.cons a (.cons b .nil))),
        .cons (.atom (.symbol ifT')) (.cons c' _) =>
        if ifS.name == "IF" && ifS2.name == "IF" && qn == quoteNil &&
           qt2 == quoteT && ifT'.name == "IF" && c' == c then
          some (false, c, a, b)
        else none
      | _, _ => none
    let fire? := fire?.orElse fun _ =>
      match cur, target with
      | .cons (.atom (.symbol ifS)) (.cons (.cons (.atom (.symbol eqS))
            (.cons qn (.cons c .nil))) (.cons a (.cons b .nil))),
        .cons (.atom (.symbol ifT')) (.cons c' _) =>
        if ifS.name == "IF" && eqS.name == "EQUAL" && qn == quoteNil &&
           ifT'.name == "IF" && c' == c then
          some (true, c, a, b)
        else none
      | _, _ => none
    match fire? with
    | some (v, c, a, b) => some (steps, cur, v, c, a, b)
    | none =>
      match asApp cur, asApp target with
      | some (fn, args), some (fn', args') =>
        if fn == fn' && args.length == args'.length && args.length ≤ 3 then
          ((args.zip args').zipIdx).findSome? fun ((x, y), i) =>
            if x == y then none
            else
              let siblings := (args.zipIdx).filterMap
                (fun (s, j) => if j == i then none else some s)
              findSwapPos x y (steps ++
                [{ fn, arity := args.length, argIdx := i, siblings }])
        else none
      | _, _ => none

/-- Normalize `cur` toward `target` by iterated SWAPPED-P steps at mismatch
    positions (the if-finish JOINT case: a NOT unfold inside a test position
    makes ACL2 swap the enclosing if between the recorded children and the
    recorded rhs). Recompute-and-check: each step's position is dictated by
    the target, and the caller's final `== rhs` gate still stands. -/
def normalizeSwapsToward (cfg : ReplayConfig) (cur0 target : SExpr) :
    MetaM (Option Expr × SExpr) := do
  let mut cur := cur0
  let mut chain : Option Expr := none
  for _ in List.range 32 do
    if cur == target then break
    match findSwapPos cur target [] with
    | none => break
    | some (steps, sub, variant, c, a, b) =>
      let swapped : SExpr :=
        .cons (.atom (.symbol { name := "IF" }))
          (.cons c (.cons b (.cons a .nil)))
      let (inner, cur') ←
        if variant then liftEqualNilTestSwap cfg steps cur sub c a b swapped
        else liftNegTestSwap cfg steps cur sub c a b swapped
      chain ← some <$> chainAfter chain inner
      cur := cur'
  return (chain, cur)

/-- The DEFINITION-node recipe, UNIFORM: unfold `(fn args) ⇒ substTerm formals args
    body`, then chain the node's children (recognizer / if-simplification / deeper
    rewrites) over the substituted body via the ordinary path-directed congruence
    machinery (`replayRewrites` — their `:PATH`s carry the boundary
    frame), checking the chain reaches the node's recorded rhs.

    Two unfold routes by where the definition lives: a WORLD defun unfolds via
    the world lemmas (body convergence from two ordered evidence sources: the
    application's PINNED value — totality, required for recursive fns — else
    the ∀-env convergence analyzer); a builtin ABSENT from the world takes the
    D4 definition-fact route (`replayBuiltinDefUnfold`). -/
partial def replayDefinition (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    : MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  let .cons (.atom (.symbol fn)) argSpine := lhs
    | throwError "definition: lhs is not an application: {repr lhs}"
  let args := (argSpine.toList?).getD []
  let (formals, body, unfold) ←
    if (cfg.worldVal.defs.get? fn).isNone then
      -- D4 route: builtin definition fact against the emitted snapshot
      replayBuiltinDefUnfold cfg ctx fn args
    else do
      let di ← deriveDefInfoN cfg fn
      unless di.formals.length == args.length do
        throwError "definition: {fn.name} arity {di.formals.length} ≠ {args.length} args"
      let hns ← proveNotSpecial fn
      -- the unfold: eval lhs = eval (substTerm formals args body), with the body
      -- convergence from the ordered evidence sources
      let unfold ←
        match ctx.val? lhs with
        | some (rv, papp) =>
          -- evidence 1: pinned application value (totality)
          let argVals ← args.mapM (ctxValExpr cfg ctx)
          let argConvs ← args.mapM (ctxValProof cfg ctx)
          match di.formals, args, argVals, argConvs with
          | [f1], [a1], [v1], [p1] =>
            let hbody ← mkAppM ``re_body_conv1
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSExpr di.body, reflectSExpr a1, v1, rv, hns, di.defFact, p1, papp]
            mkAppM ``evalOpt_unfold1_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSExpr di.body, reflectSExpr a1, v1, rv, hns,
                di.defFact, di.closedFact, di.wellScopedFact, p1, hbody]
          | [f1, f2], [a1, a2], [v1, v2], [p1, p2] =>
            let hbody ← mkAppM ``re_body_conv2
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
                reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, v1, v2, rv, hns,
                di.defFact, p1, p2, papp]
            mkAppM ``evalOpt_unfold2_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
                reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, v1, v2, rv, hns,
                di.defFact, di.closedFact, di.wellScopedFact, p1, p2, hbody]
          | [f1, f2, f3], [a1, a2, a3], [v1, v2, v3], [p1, p2, p3] =>
            let hbody ← mkAppM ``re_body_conv3
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr di.body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3,
                v1, v2, v3, rv, hns, di.defFact, p1, p2, p3, papp]
            mkAppM ``evalOpt_unfold3_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr di.body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3, v1, v2, v3, rv,
                hns, di.defFact, di.closedFact, di.wellScopedFact, p1, p2, p3, hbody]
          | _, _, _, _ => throwError "definition: only 1/2/3-arg unfolds supported (frontier)"
        | none =>
          -- evidence 2: the ∀-env convergence analyzer
          let hbodyAll ← proveConvAllEnv cfg ctx di.body
          match di.formals, args with
          | [f1], [a1] =>
            let harg ← proveConv cfg cfg.envExpr ctx a1
            mkAppM ``re_unfold1_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSExpr di.body, reflectSExpr a1, hns,
                di.defFact, di.closedFact, di.wellScopedFact, harg, hbodyAll]
          | [f1, f2], [a1, a2] =>
            let h1 ← proveConv cfg cfg.envExpr ctx a1
            let h2 ← proveConv cfg cfg.envExpr ctx a2
            mkAppM ``re_unfold2_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
                reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, hns,
                di.defFact, di.closedFact, di.wellScopedFact, h1, h2, hbodyAll]
          | [f1, f2, f3], [a1, a2, a3] =>
            let h1 ← proveConv cfg cfg.envExpr ctx a1
            let h2 ← proveConv cfg cfg.envExpr ctx a2
            let h3 ← proveConv cfg cfg.envExpr ctx a3
            mkAppM ``re_unfold3_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr di.body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3, hns,
                di.defFact, di.closedFact, di.wellScopedFact, h1, h2, h3, hbodyAll]
          | _, _ => throwError "definition: only 1/2/3-arg unfolds supported (frontier)"
      pure (di.formals, di.body, unfold)
  -- children chain over the substituted body (their paths carry one more
  -- boundary frame), reaching the node's recorded rhs
  let substBody := ACL2.Replay.substTerm formals args body
  let (chainOpt, finalTerm) ← rec.rewrites cfg ctx substBody children
  let chainOpt ← chainReqEq chainOpt
  -- rewrite-if's SILENT swap at the chain end (BUG-026 — a swapped if
  -- whose branch windows are empty leaves no tree trace): recompute-and-
  -- check toward the recorded rhs (the `== rhs` gate below stays); the
  -- EQUAL-NIL variant covers rewrite-equal's nil-normalization landing in
  -- a test position
  let (chainOpt, finalTerm) ← do
    if finalTerm != rhs then
      let (swapOpt, finalTerm') ← normalizeSwapsToward cfg finalTerm rhs
      match swapOpt with
      | none => pure (chainOpt, finalTerm)
      | some sw => match chainOpt with
        | none => pure ((some sw : Option Expr), finalTerm')
        | some ch => pure (some (← mkAppM ``fuel_chain_eq #[ch, sw]), finalTerm')
    else pure (chainOpt, finalTerm)
  let chainOpt ← do
    if finalTerm == rhs then pure chainOpt else
    -- rewrite-equal's unrecorded NIL normalization at the chain end
    match ← bridgeEqualNilNorm cfg ctx finalTerm rhs with
    | some br => match chainOpt with
      | none => pure (some br)
      | some ch => pure (some (← mkAppM ``fuel_chain_eq #[ch, br]))
    | none =>
      throwError "definition: children chain reached {repr finalTerm}, node rhs is {repr rhs}"
  match chainOpt with
  | none => return unfold
  | some ch => mkAppM ``fuel_chain_eq #[unfold, ch]

/-- Replay a `lambda-body` node — the BETA step of a translated `let`/`mv-let`
    (emitted at `rewrite-fncall`'s lambda case, S2 2026-07-24). Structurally
    the definition-unfold recipe with the binder in place of a defun: the node
    replaces the lambda application (actuals already rewritten by earlier chain
    steps) by its body under `formals ↦ actuals`, and the adopted LAMBDA-BODY
    block rewrites that substituted body on to the node's recorded rhs. The
    scoping side conditions are ACL2's own translate invariant, re-checked here
    by kernel decision (`WellScoped` / freeVars ⊆ formals). -/
partial def replayLambdaBody (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) : MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  let some (head, lam, actuals) := asLamApp lhs
    | throwError "lambda-body: lhs is not a lambda application: {repr lhs}"
  let some (_, formalsE, lamBody) := asLamHead head
    | throwError "lambda-body: malformed LAMBDA head: {repr head}"
  let some lformals := ACL2.lamFormals? formalsE
    | throwError "lambda-body: malformed LAMBDA formals: {repr formalsE}"
  let lamE := reflectSymbol lam
  let formalsSE := reflectSExpr formalsE
  let bodyE := reflectSExpr lamBody
  let lformalsE ← mkListLit (mkConst ``Symbol) (lformals.map reflectSymbol)
  let hlam ← proveIsNamedTrue lam "LAMBDA"
  let hform ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.lamFormals? #[formalsSE]) (← mkAppM ``Option.some #[lformalsE]))
    "lambda-body formals"
  let hnl ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[bodyE]) (mkConst ``Bool.true)) "well-scoped lambda body"
  let hbodyAll ← proveConvAllEnv cfg ctx lamBody
  let unfold ← match lformals, actuals with
    | [lf], [a1] =>
      let h1 ← proveConv cfg cfg.envExpr ctx a1
      mkAppM ``re_lam_beta1_conv
        #[cfg.worldExpr, cfg.envExpr, lamE, formalsSE, bodyE, reflectSExpr a1,
          reflectSymbol lf, hlam, hform, hnl, h1, hbodyAll]
    | [f1, f2], [a1, a2] =>
      let h1 ← proveConv cfg cfg.envExpr ctx a1
      let h2 ← proveConv cfg cfg.envExpr ctx a2
      mkAppM ``re_lam_beta2_conv
        #[cfg.worldExpr, cfg.envExpr, lamE, formalsSE, bodyE, reflectSExpr a1,
          reflectSExpr a2, reflectSymbol f1, reflectSymbol f2,
          hlam, hform, hnl, h1, h2, hbodyAll]
    | _, _ =>
      throwError "lambda-body: binder of {lformals.length} formals / {actuals.length} \
                  actuals is a frontier — only 1- and 2-actual translated lets are emitted"
  -- the adopted LAMBDA-BODY block rewrites the substituted body (its
  -- paths carry the LAMBDA-BODY boundary frame)
  let substBody := ACL2.Replay.substTerm lformals actuals lamBody
  let (chainOpt, finalTerm) ← rec.rewrites cfg ctx substBody children
  let chainOpt ← chainReqEq chainOpt
  unless finalTerm == rhs do
    throwError "lambda-body: children chain reached {repr finalTerm}, node rhs is {repr rhs}"
  match chainOpt with
  | none => return unfold
  | some ch => mkAppM ``fuel_chain_eq #[unfold, ch]

/-- The LEXORDER-TOTAL FC relief (extracted from the marker-relief arm,
    weight ratchet): prove the marker-relieved hyp `hσ` (a LEXORDER
    application) from the registered FC rule's kernel-proved core +
    the in-scope falsity of the commuted application, anchored on
    either emitted channel (marker `:TA-RUNES` or a clause-level
    `(:FC-DERIVATIONS …)` record). `notH`/`vH` feed the frontier
    message only. -/
def fcReliefLexorderTotal (cfg : ReplayConfig) (ctx : ReplayCtx)
    (rname : String) (hσ notH : SExpr) (vH tNeNil : Expr)
    (reliefMarkers : List ProofNode) : MetaM Expr := do
  let some marker := reliefMarkers.find? fun c => (nodeLhsRhs c).1 == hσ
    | throwError "rule {rname}: internal — marker vanished"
  let .node _ _ _ _ mprov := marker
  -- ANCHOR (BUG-023 discipline), two emitted channels: the
  -- marker's own :TA-RUNES, or — when those are empty (the
  -- cumulative set adds nothing at some sites; final-closeout
  -- item C, HOW-MANY-SMALLER-BNEXT) — a clause-level
  -- (:FC-DERIVATIONS …) record whose :CONCL is EXACTLY this
  -- hyp instance and whose rune is the registered FC rule.
  let taAnchored := mprov.taRunes.any
    (fun r => r.ty == "forward-chaining" && r.name == "LEXORDER-TOTAL")
  let fcDeriv? := ctx.fcDerivs.find? fun d =>
    (fcDerivField? d "CONCL" == some hσ) &&
    (match fcDerivField? d "RUNE" with
     | some (.cons (.atom (.keyword cls))
         (.cons (.atom (.symbol nm)) .nil)) =>
       cls == "FORWARD-CHAINING" && nm.name == "LEXORDER-TOTAL"
     | _ => false)
  unless taAnchored || fcDeriv?.isSome do
    throwError "rule {rname}: marker-relieved hyp {repr hσ} has no \
                (not …)-falsity fact in scope, and its :TA-RUNES \
                {repr (mprov.taRunes.map (·.name))} name no \
                registered FC relief (frontier; \
                lit-facts {repr (ctx.litFacts.map (·.2.1))}; \
                seg-facts {repr (ctx.segFacts.map (·.1))}; \
                candidate types: {← (ctx.segFacts.filterMap
                  (fun (st, p) => if st == notH then some p else none)).mapM
                  (fun p => do pure (← Lean.Meta.inferType p))}; \
                expected: {← mkEq (mkApp (mkConst ``Logic.not) vH)
                  (mkConst ``SExpr.nil)})"
  let some spec := cfg.fcRules.find? (·.name == "LEXORDER-TOTAL")
    | throwError "rule {rname}: :TA-RUNES cite LEXORDER-TOTAL but \
                  the (:GROUND-ZERO-FC-RULES) snapshot lacks it \
                  (stale log? recapture-all)"
  let varX : SExpr := .atom (.symbol { name := "X" })
  let varY : SExpr := .atom (.symbol { name := "Y" })
  let lexT (p q : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "LEXORDER" })) (.cons p (.cons q .nil))
  let notT (t : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
  unless spec.trigger == lexT varX varY &&
         spec.hyps == [notT (lexT varX varY)] &&
         spec.concls == [lexT varY varX] do
    throwError "rule {rname}: LEXORDER-TOTAL snapshot shape drifted \
                from the pinned form: {repr spec.trigger} / \
                {repr spec.hyps} / {repr spec.concls}"
  -- unify the concl (LEXORDER Y X) with hσ: Y ↦ u, X ↦ v
  let .cons (.atom (.symbol ls)) (.cons u (.cons v .nil)) := hσ
    | throwError "rule {rname}: FC relief target {repr hσ} is not \
                  a LEXORDER application (frontier)"
  unless ls.name == "LEXORDER" do
    throwError "rule {rname}: FC relief target {repr hσ} is not \
                a LEXORDER application (frontier)"
  -- instantiated FC hyp (NOT (LEXORDER v u)): its truth is the
  -- in-scope FALSITY of the clause literal (LEXORDER v u)
  let source := lexT v u
  -- fc-derivations anchoring: the record's :TRIGGER must BE the
  -- source instance (the emitted record corroborates exactly the
  -- flip we are about to justify — never a shape guess)
  if let some d := fcDeriv? then
    unless fcDerivField? d "TRIGGER" == some source do
      throwError "rule {rname}: the anchoring FC-derivation's \
                  :TRIGGER {repr (fcDerivField? d "TRIGGER")} ≠ \
                  the relief source {repr source} (emission/replay \
                  instance drift — a defect, not a frontier)"
  let some hNilSrc := ctx.litFactByTerm? source
    | throwError "rule {rname}: FC relief via LEXORDER-TOTAL needs \
                  the falsity of {repr source} in scope (frontier)"
  let vu ← ctxValExpr cfg ctx u
  let vv ← ctxValExpr cfg ctx v
  let hTotal ← mkAppM ``ACL2.lexorder_total #[vv, vu]
  -- left disjunct (lexorder vv vu = t) refuted by hNilSrc
  let vSrc ← ctxValExpr cfg ctx source
  let notLeft ← withLocalDeclD `h (← mkEq vSrc (mkConst ``SExpr.t))
    fun h => do
      let tEqNil ← mkAppM ``Eq.trans
        #[← mkAppM ``Eq.symm #[h], hNilSrc]
      mkLambdaFVars #[h] (mkApp tNeNil tEqNil)
  let hT ← mkAppM ``Or.resolve_left #[hTotal, notLeft]
  let hne ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
  mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hσ, hne]



/-- The PCE-class chain-end IF-COLLAPSE bridge (final-closeout arc):
    when a literal's composed chain reaches an IF-nest whose recorded
    result has the ifs COLLAPSED (rewrite-atm's boundary
    normalization), prove the two terms' VALUES equal and bridge by
    `fuel_eq_of_conv`. Every collapse is justified, never inferred:
    a test resolves `'t` ONLY via an emitted `:IF-TEST-TRUE` marker
    for that exact test (the type-set basis then PROVED by
    `replayRecognizer`'s closure machinery) or by the recursive
    structure; the `(IF x 'T 'NIL) ⇒ x` collapse ONLY by the branch
    values' two-valued RANGE (the emitted case-split shapes'
    primitives). `none` on any other shape — the caller's loud
    frontier stays. -/
partial def bridgeIfCollapseNorm (cfg : ReplayConfig) (ctx : ReplayCtx)
    (ifMarkers : List (SExpr × Bool × SExpr))
    (reached recorded : SExpr) : MetaM (Option Expr) := do
  -- (no top-level marker gate: each collapse case carries its own
  -- anchor — markers for test-true, the emitted TP corollary for the
  -- boolean-TP fold, the two-valued primitives for the range collapse)
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx reached
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx recorded
  let quoteT' : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons SExpr.t .nil)
  let quoteNil' : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons SExpr.nil .nil)
  -- v(t) = 't, justified: quoted 'T; a marker-anchored test (the
  -- type-set basis proved by the recognizer closure); or a
  -- (IF x 'T 'NIL) whose x is itself so justified
  let rec valIsT (t : SExpr) : MetaM (Option Expr) := do
    if t == quoteT' then
      return some (← mkEqRefl (mkConst ``SExpr.t))
    if ifMarkers.any (fun (mt, sense, _) => sense && mt == t) then
      let pT ← try some <$> replayRecognizer cfg ctx t SExpr.t
        catch _ => pure none
      match pT with
      | some pT =>
        let pV ← ctxValProof cfg ctx t
        return some (← mkAppM ``conv_val_eq #[pV, pT])
      | none => return none
    match t with
    | .cons (.atom (.symbol ifS)) (.cons c (.cons th (.cons el .nil))) =>
      if ifS.name == "IF" && th == quoteT' && el == quoteNil' then
        match ← valIsT c with
        | some hc => return some (← Lean.Meta.mkAppOptM ``cond_of_val_t
            #[none, some (mkConst ``SExpr.t), some (mkConst ``SExpr.nil),
              some hc])
        | none => return none
      else return none
    | _ => return none
  -- v(t) ∈ {'t, 'nil}: the two-valued RANGE by structure
  let rec bRange (t : SExpr) : MetaM (Option Expr) := do
    if t == quoteT' then
      return some (← Lean.Meta.mkAppOptM ``Or.inl
        #[none, some (← mkEq (mkConst ``SExpr.t) (mkConst ``SExpr.nil)),
          some (← mkEqRefl (mkConst ``SExpr.t))])
    if t == quoteNil' then
      return some (← Lean.Meta.mkAppOptM ``Or.inr
        #[some (← mkEq (mkConst ``SExpr.nil) (mkConst ``SExpr.t)), none,
          some (← mkEqRefl (mkConst ``SExpr.nil))])
    match t with
    | .cons (.atom (.symbol hs)) (.cons a (.cons b .nil)) =>
      if hs.name == "EQUAL" then
        return some (← mkAppM ``logic_equal_range
          #[← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx b])
      else return none
    | .cons (.atom (.symbol hs)) (.cons a .nil) =>
      if hs.name == "NOT" then
        return some (← mkAppM ``logic_not_range #[← ctxValExpr cfg ctx a])
      else return none
    | .cons (.atom (.symbol ifS)) (.cons c (.cons th (.cons el .nil))) =>
      if ifS.name == "IF" then
        match ← bRange th, ← bRange el with
        | some hx, some hy =>
          return some (← mkAppM ``cond_range
            #[mkApp (mkConst ``Logic.toBool) (← ctxValExpr cfg ctx c),
              hx, hy])
        | _, _ => return none
      else return none
    | _ => return none
  -- v(a) = v(b), by justified collapses only
  let rec go (a b : SExpr) : MetaM (Option Expr) := do
    if a == b then
      return some (← mkEqRefl (← ctxValExpr cfg ctx a))
    match a, b with
    | .cons (.atom (.symbol na)) (.cons xa .nil),
      .cons (.atom (.symbol nb)) (.cons xb .nil) =>
      if na.name == "NOT" && nb.name == "NOT" then
        match ← go xa xb with
        | some h =>
          return some (← Lean.Meta.mkCongrArg (mkConst ``Logic.not) h)
        | none => return none
      else return none
    | .cons (.atom (.symbol ifS)) (.cons c (.cons th (.cons el .nil))), _ =>
      if ifS.name != "IF" then return none
      -- (i) marker-justified test-true: take the then-branch
      match ← valIsT c with
      | some hc =>
        let hstep ← Lean.Meta.mkAppOptM ``cond_of_val_t
          #[none, some (← ctxValExpr cfg ctx th),
            some (← ctxValExpr cfg ctx el), some hc]
        match ← go th b with
        | some hrest => return some (← mkAppM ``Eq.trans #[hstep, hrest])
        | none => return none
      | none =>
        -- (ii) the boolean collapse (IF b 'T 'NIL) ⇒ b
        if th == quoteT' && el == quoteNil' && c == b then
          match ← bRange b with
          | some hr => return some (← mkAppM ``cond_tnil_of_range #[hr])
          | none => return none
        else return none
    | .cons (.atom (.symbol eqS)) (.cons p (.cons qt' .nil)), _ =>
      -- (iii) the BOOLEAN-TP fold under composition: (EQUAL p 'T) vs p,
      -- where p's fn carries the emitted boolean TP corollary
      -- (IF (EQUAL p 'T) 'T (EQUAL p 'NIL)) — the value identity
      -- logic_equal_t_self_of_boolean_tp (consumed, not inferred)
      if eqS.name == "EQUAL" && qt' == quoteT' && p == b then
        match p with
        | .cons (.atom (.symbol fs)) argsSpine =>
          match ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) with
          | none => return none
          | some (_, cor, tpHyp) =>
            let some (formals, _) := cfg.worldVal.defs.get? fs
              | return none
            let args := (argsSpine.toList?).getD []
            if formals.length != args.length then return none
            let eqT' (x y : SExpr) : SExpr :=
              .cons (.atom (.symbol { name := "EQUAL" }))
                (.cons x (.cons y .nil))
            let inst := ACL2.Replay.substTerm formals args cor
            let expected : SExpr :=
              .cons (.atom (.symbol { name := "IF" }))
                (.cons (eqT' p quoteT')
                  (.cons quoteT' (.cons (eqT' p quoteNil') .nil)))
            if inst != expected then return none
            let some (vp, convp) := ctx.val? p | return none
            let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
              ++ (args.map reflectSExpr).toArray ++ #[vp, convp])
            return some (← mkAppM ``logic_equal_t_self_of_boolean_tp
              #[fact])
        | _ => return none
      else return none
    | _, _ => return none
  match ← go reached recorded with
  | none => return none
  | some hval =>
    let pA ← ctxValProof cfg ctx reached
    let pB ← ctxValProof cfg ctx recorded
    return some (← mkAppM ``fuel_eq_of_conv #[pA, pB, hval])

end ACL2.Replay.Driver
