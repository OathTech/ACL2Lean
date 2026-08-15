/-
  Driver/NodeCore/TypeSetWalk — positional slice of the former NodeCore
  monolith (perf arc 3a, 2026-08-07): MOVE-ONLY; the boundaries are the
  file's own def-before-use order, so the import chain IS the
  dependency order.
-/
import ACL2Lean.Replay.Driver.NodeCore.Compose
import ACL2Lean.Replay.Driver.TsFacts

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- The bounded VALUE-LEVEL TYPE-SET WALKER (the epicycle consolidation —
    design: docs/notes/2026-07-31_type-set-walker-design.md): every
    clause-context type-fact derivation goes through this ONE request
    surface over ONE view of the fact channels. The rungs are exactly the
    former kits' (`deriveNilFact` / `deriveConspT` / `conspEvidence?`),
    moved — no new derivation power; the entry compositions mirror what
    ACL2's assume-true-false performs on the same assumptions (such
    entries emit `:PARENTS NIL :RUNES NIL/fake` — assumption-composed, no
    rune provenance to consume). Depth-bounded, deterministic,
    type-checked at every fact use, fail-closed (`none`). -/
partial def typeSetWalk (cfg : ReplayConfig) (ctx : ReplayCtx)
    (req : TsReq) (depth : Nat := 3) : MetaM (Option Expr) := do
  match req with
  | .isTruthy t =>
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx t
    let vT ← ctxValExpr cfg ctx t
    -- a truthy branch fact on the term itself (ACL2's assume-true-false
    -- context IS the type-alist entry's source — HOW-MANY-QSORT).
    -- The proof's TYPE is checked like every other rung (audit
    -- 2026-07-31 inside finding 6 — this site relied on the
    -- branchFacts tuple invariant alone).
    for (bt, vB, sign, h) in ctx.branchFacts do
      if sign && bt == t then
        if ← Lean.Meta.isDefEq vB vT then
          if ← Lean.Meta.isDefEq (← Lean.Meta.inferType h)
              (← Lean.Meta.mkAppM ``Ne #[vT, mkConst ``SExpr.nil]) then
            return some h
    -- a false `(NOT t)` fact in any falsity channel
    let notT : SExpr := .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
    if let some hf ← findFactChecked (falsitySources ctx) notT
        (← mkEq (mkApp (mkConst ``Logic.not) vT) (mkConst ``SExpr.nil)) then
      return some (← Lean.Meta.mkAppM ``logic_not_nil_ne #[vT, hf])
    -- a false EXPANDED `(IF t 'NIL 'T)` fact (ORDERED-PERMS Subgoal 3)
    let ifNilT : SExpr := .cons (.atom (.symbol { name := "IF" }))
      (.cons t (.cons quoteNil (.cons quoteT .nil)))
    if let some hf ← findFactChecked (falsitySources ctx) ifNilT
        (← mkEq (← Lean.Meta.mkAppM ``cond
            #[mkApp (mkConst ``Logic.toBool) vT, mkConst ``SExpr.nil,
              mkConst ``SExpr.t])
          (mkConst ``SExpr.nil)) then
      return some (← Lean.Meta.mkAppM ``logic_ne_nil_of_if_nil_t_nil #[hf])
    return none
  | .isNil t =>
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx t
    let vT ← ctxValExpr cfg ctx t
    let expected ← mkEq vT (mkConst ``SExpr.nil)
    -- direct, type-checked
    if let some h ← ctx.litFactByTermChecked? t expected then
      return some h
    if let some h := (ctx.branchFacts.find? (fun (bt, _, sign, _) =>
        bt == t && !sign)).map (·.2.2.2) then
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType h) expected then
        return some h
    if depth == 0 then return none
    -- car/cdr of a NON-cons (the completion defaults)
    match t with
    | .cons (.atom (.symbol cs)) (.cons u .nil) =>
      if cs.name == "CAR" || cs.name == "CDR" then
        let conspU : SExpr :=
          .cons (.atom (.symbol { name := "CONSP" })) (.cons u .nil)
        if let some hc ← typeSetWalk cfg ctx (.isNil conspU) (depth - 1) then
          let ctxU ← pinTermOpaques cfg cfg.envExpr ctx conspU
          let vC ← ctxValExpr cfg ctxU conspU
          if vC.isAppOfArity ``Logic.consp 1 then
            let vu := vC.appArg!
            let lem := if cs.name == "CAR" then ``logic_car_of_consp_nil
                       else ``logic_cdr_of_consp_nil
            let hDef ← Lean.Meta.mkAppM lem #[hc]
            let target := mkApp
              (mkConst (if cs.name == "CAR" then ``Logic.car else ``Logic.cdr)) vu
            if ← Lean.Meta.isDefEq vT target then
              return some hDef
    | _ => pure ()
    -- EQUAL symmetry (the component protocol's CAR/CDR-SYMMETRIC silent
    -- refutation): a refutation of the FLIPPED equality commutes over
    if let .cons (.atom (.symbol eqS)) (.cons a (.cons b .nil)) := t then
      if eqS.name == "EQUAL" then
        let flip : SExpr := .cons (.atom (.symbol eqS)) (.cons b (.cons a .nil))
        if let some h ← typeSetWalk cfg ctx (.isNil flip) 0 then
          return some (← Lean.Meta.mkAppM ``logic_equal_nil_comm #[h])
        -- EQUATION-CLOSURE DISEQUALITY. Two rungs, tried in order:
        --
        -- RUNG A (directed, RETIRES the search where it applies —
        -- 2026-08-07): read the RECORDED verdict basis
        -- (:CANON1/:CANON2/:TA-ENTRY on the equal/type-alist-nil step,
        -- assoc-equiv+'s own inputs). Each side chains through the
        -- in-scope equations to its RECORDED canon; the RECORDED entry
        -- is the disequality. Fully deterministic toward recorded
        -- targets.
        --
        -- RUNG B — DRIFT MARKER, still held under EXPIRY (sharpened
        -- 2026-08-07): the recorded basis is SHALLOW when the entry is a
        -- DERIVED type-alist entry (subst-type-alist built it during
        -- assume-true-false — MEMB-RM's (EQUAL B A) = nil from
        -- A ≠ (CAR X) ∧ B = (CAR X)); its own derivation is not yet
        -- emitted, so the bounded deterministic search survives for
        -- exactly that class. EXPIRES when the derived-entry provenance
        -- emission (subst-type-alist instrumentation — the same item
        -- HOW-MANY-RM-GENERAL's frontier names) lands in the next
        -- batch; do NOT extend this search.
        -- RUNG A restructure (audit 2026-08-07 S2: the try/catch that
        -- swallowed every rung-A frontier is GONE). Applicability is
        -- decided by DATA: a recorded basis whose :TA-ENTRY has an
        -- in-scope falsity fact is a DIRECT entry — rung A is then
        -- COMMITTED (its failures are real frontiers and THROW); a
        -- basis whose entry has no in-scope fact is a DERIVED entry —
        -- rung B′ consumes its ta-subst provenance below.
        let mkEqT : SExpr → SExpr → SExpr := fun p q =>
          .cons (.atom (.symbol { name := "EQUAL" }))
            (.cons p (.cons q .nil))
        let basis? := ctx.taBases.find? (fun (t', _, _, _) => t' == t || t' == flip)
        let directFact? ← match basis? with
          | none => pure none
          | some (_, _, _, none) => pure none
          | some (tRec, c1, c2, some dt) => do
            let (ca, cb) := if tRec == t then (c1, c2) else (c2, c1)
            let .cons (.atom (.symbol _)) (.cons x (.cons y .nil)) := dt
              | throwError "equal/type-alist-nil basis: :TA-ENTRY \
                  {repr dt} is not binary (frontier)"
            let (xa, ya) ←
              if x == ca && y == cb then pure (x, y)
              else if x == cb && y == ca then pure (y, x)
              else throwError "equal/type-alist-nil basis: entry \
                  {repr dt} sides off the recorded canons {repr ca} / \
                  {repr cb} (frontier)"
            let ctxD ← pinTermOpaques cfg cfg.envExpr ctx (mkEqT xa ya)
            let vX ← ctxValExpr cfg ctxD xa
            let vY ← ctxValExpr cfg ctxD ya
            let hDirect? ← findFactChecked (falsitySources ctxD)
              (mkEqT xa ya)
              (← mkEq (← Lean.Meta.mkAppM ``Logic.equal #[vX, vY])
                (mkConst ``SExpr.nil))
            match hDirect? with
            | some h => pure (some (xa, ya, ctxD, h))
            | none =>
              let hFlip? ← findFactChecked (falsitySources ctxD)
                (mkEqT ya xa)
                (← mkEq (← Lean.Meta.mkAppM ``Logic.equal #[vY, vX])
                  (mkConst ``SExpr.nil))
              match hFlip? with
              | some h => pure (some (xa, ya, ctxD,
                  ← Lean.Meta.mkAppM ``logic_equal_nil_comm #[h]))
              | none =>
                -- LEXORDER-ORDER rung RETIRED (endgame arc, 2026-08-10 —
                -- the C1 expiry fired): scout F refuted the order-derived
                -- theory — both serving witnesses' :TA-ENTRY is a verbatim
                -- TAIL clause literal (rewrite-clause-type-alist item (a)),
                -- and the spine now HOISTS the recorded entry as a demand
                -- (collectContextDemands' type-alist arm), so the direct
                -- lookup above finds ACL2's own justification. The retired
                -- rung supplied a kernel order-axiom justification the
                -- artifact never named.
                pure none  -- DERIVED entry → rung B′
        if let some (xa, ya, ctxD, hXY) := directFact? then
          -- COMMITTED rung A: every failure from here is a thrown frontier
          let eqs := inScopeEquations ctx
          match eqChain? eqs a xa, eqChain? eqs b ya with
          | some chA, some chB =>
            let pa ← match ← composeEqChain cfg ctxD chA with
              | some e => pure e
              | none => Lean.Meta.mkEqRefl (← ctxValExpr cfg ctxD a)
            let pb ← match ← composeEqChain cfg ctxD chB with
              | some e => pure e
              | none => Lean.Meta.mkEqRefl (← ctxValExpr cfg ctxD b)
            let hCong ← Lean.Meta.mkAppM ``congr
              #[← Lean.Meta.mkAppM ``congrArg
                  #[mkConst ``Logic.equal, pa], pb]
            let hNil ← Lean.Meta.mkAppM ``Eq.trans #[hCong, hXY]
            if ← Lean.Meta.isDefEq (← Lean.Meta.inferType hNil) expected then
              return some hNil
            throwError "equal/type-alist-nil rung A: directed composition \
                for {repr t} did not produce the expected refutation type \
                (frontier)"
          | _, _ =>
            throwError "equal/type-alist-nil rung A: no in-scope equation \
                chain to the recorded canons for {repr t} (frontier)"
        -- RUNG B′ — DERIVED entries, DIRECTED (2026-08-07, user-approved
        -- ta-subst emission; the candidate×orientation SEARCH is fully
        -- RETIRED): the recorded (:TA-SUBST) provenance names the parent
        -- entry (FROM, an in-scope fact) and the substituted pair
        -- (SUBST-NEW for SUBST-OLD — the assumed equality). The proof
        -- composes exactly those recorded pieces; a class instance with
        -- no recorded provenance hard-falls-through to the generic
        -- frontier error (never a search).
        -- S1 (audit 2026-08-07): the recorded :TS binds the SELECTION —
        -- this falsity rung consumes only *ts-nil* (128) records; a
        -- truthy derived entry (ts 256) on the same term must never be
        -- picked (both polarities coexist in real artifacts — qsort).
        match ctx.taSubsts.find? (fun (n, _, ts, _, _) =>
            (n == t || n == flip) && ts == 128) with
        | none => pure ()
        | some (newT, fromT, _, substNew, substOld) =>
          -- S6 (audit 2026-08-07): JOIN the two recorded provenances —
          -- when the verdict's own basis is in scope for this term, its
          -- :TA-ENTRY must BE the derived entry we are about to replay.
          match ctx.taBases.find? (fun (t', _, _, _) => t' == t || t' == flip) with
          | some (_, _, _, some e) =>
            let flipOf : SExpr → SExpr := fun x => match x with
              | .cons h (.cons p (.cons q .nil)) =>
                .cons h (.cons q (.cons p .nil))
              | other => other
            unless e == newT || e == flipOf newT do
              throwError "ta-subst: the verdict basis's :TA-ENTRY \
                  {repr e} is not the derived entry {repr newT} \
                  (provenance mismatch — frontier)"
          | _ => pure ()
          let .cons _ (.cons n1 (.cons n2 .nil)) := newT
            | throwError "ta-subst: derived entry {repr newT} not binary \
                (frontier)"
          let .cons _ (.cons f1 (.cons f2 .nil)) := fromT
            | throwError "ta-subst: parent entry {repr fromT} not binary \
                (frontier)"
          -- the substituted position: new differs from from exactly where
          -- substOld became substNew
          let pos1 := n1 == substNew && f1 == substOld && n2 == f2
          let pos2 := n2 == substNew && f2 == substOld && n1 == f1
          unless pos1 || pos2 do
            throwError "ta-subst: recorded substitution does not relate \
                {repr fromT} to {repr newT} via {repr substOld} ↦ \
                {repr substNew} (frontier)"
          let ctxD ← pinTermOpaques cfg cfg.envExpr ctx fromT
          let ctxD ← pinTermOpaques cfg cfg.envExpr ctxD newT
          let vF1 ← ctxValExpr cfg ctxD f1
          let vF2 ← ctxValExpr cfg ctxD f2
          -- (i) the parent entry's in-scope falsity — the clause literal
          -- may carry either orientation of the recorded parent
          let mkEqT : SExpr → SExpr → SExpr := fun p q =>
            .cons (.atom (.symbol { name := "EQUAL" }))
              (.cons p (.cons q .nil))
          let hFrom? ← findFactChecked (falsitySources ctxD) fromT
            (← mkEq (← Lean.Meta.mkAppM ``Logic.equal #[vF1, vF2])
              (mkConst ``SExpr.nil))
          let hFrom ← match hFrom? with
            | some h => pure h
            | none =>
              let hFlip? ← findFactChecked (falsitySources ctxD)
                (mkEqT f2 f1)
                (← mkEq (← Lean.Meta.mkAppM ``Logic.equal #[vF2, vF1])
                  (mkConst ``SExpr.nil))
              match hFlip? with
              | some h => Lean.Meta.mkAppM ``logic_equal_nil_comm #[h]
              | none =>
                throwError "ta-subst: parent entry {repr fromT} has no \
                    in-scope falsity fact in either orientation (frontier)"
          -- (ii) the assumed equality v(substNew) = v(substOld)
          let eqs := inScopeEquations ctx
          let hSub ← match eqChain? eqs substNew substOld with
            | some ch => match ← composeEqChain cfg ctxD ch with
              | some e => pure e
              | none => Lean.Meta.mkEqRefl (← ctxValExpr cfg ctxD substNew)
            | none =>
              throwError "ta-subst: no in-scope equation chain \
                  {repr substNew} → {repr substOld} (frontier)"
          -- (iii) v(n_i) = v(f_i): the substituted side via hSub, the
          -- other by refl
          let pa ← if pos1 then pure hSub
            else Lean.Meta.mkEqRefl (← ctxValExpr cfg ctxD n1)
          let pb ← if pos2 then pure hSub
            else Lean.Meta.mkEqRefl (← ctxValExpr cfg ctxD n2)
          let hCong ← Lean.Meta.mkAppM ``congr
            #[← Lean.Meta.mkAppM ``congrArg
                #[mkConst ``Logic.equal, pa], pb]
          let hNilNew ← Lean.Meta.mkAppM ``Eq.trans #[hCong, hFrom]
          -- orient to t
          let hT ← if newT == t then pure hNilNew
            else Lean.Meta.mkAppM ``logic_equal_nil_comm #[hNilNew]
          if ← Lean.Meta.isDefEq (← Lean.Meta.inferType hT) expected then
            return some hT
          throwError "ta-subst: directed composition for {repr t} did not \
              produce the expected refutation type (frontier)"
    -- TRUE-LISTP ∧ ¬CONSP → 'NIL (TRUE-LISTP-MSORT's `MT ⇒ 'NIL`): a
    -- TRUTHY true-listp fact (a false `(not (true-listp t))`) composed with
    -- consp-false evidence pins the value to exactly nil
    let notTlp : SExpr := .cons (.atom (.symbol { name := "NOT" }))
      (.cons (.cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons t .nil))
        .nil)
    let tlpT : SExpr := .cons (.atom (.symbol { name := "TRUE-LISTP" }))
      (.cons t .nil)
    for (st, hf) in falsitySources ctx do
      unless st == notTlp do continue
      let ctxT2 ← pinTermOpaques cfg cfg.envExpr ctx tlpT
      let vTlp ← ctxValExpr cfg ctxT2 tlpT
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType hf)
          (← mkEq (mkApp (mkConst ``Logic.not) vTlp) (mkConst ``SExpr.nil)) do
        continue
      unless vTlp.isAppOfArity ``Logic.trueListp 1 do continue
      let conspT' : SExpr :=
        .cons (.atom (.symbol { name := "CONSP" })) (.cons t .nil)
      if let some hc ← typeSetWalk cfg ctxT2 (.isNil conspT') (depth - 1) then
        let vC ← ctxValExpr cfg (← pinTermOpaques cfg cfg.envExpr ctxT2 conspT')
          conspT'
        if vC.isAppOfArity ``Logic.consp 1 &&
            (← Lean.Meta.isDefEq vC.appArg! vTlp.appArg!) &&
            (← Lean.Meta.isDefEq vT vTlp.appArg!) then
          let hne ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlp, hf]
          return some (← Lean.Meta.mkAppM ``logic_nil_of_trueListp_consp_nil
            #[hne, hc])
    -- equation transport: a false (not (equal p q)) with t on one side
    for (st, hSeg) in falsitySources ctx do
      let .cons (.atom (.symbol ns))
          (.cons pq@(.cons (.atom (.symbol eqS))
            (.cons pv (.cons q .nil))) .nil) := st
        | continue
      unless ns.name == "NOT" && eqS.name == "EQUAL" do continue
      unless t == pv || t == q do continue
      let other := if t == pv then q else pv
      let ctxE ← pinTermOpaques cfg cfg.envExpr ctx pq
      let vPQ ← ctxValExpr cfg ctxE pq
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType hSeg)
          (← mkEq (mkApp (mkConst ``Logic.not) vPQ) (mkConst ``SExpr.nil)) do
        continue
      if let some hOther ← typeSetWalk cfg ctxE (.isNil other) (depth - 1) then
        let hne ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vPQ, hSeg]
        let heq ← Lean.Meta.mkAppM ``Logic.eq_of_equal_ne_nil #[hne]  -- vp = vq
        let heqO ← if t == pv then pure heq else Lean.Meta.mkAppM ``Eq.symm #[heq]
        -- vt = vother; vother = nil
        return some (← Lean.Meta.mkAppM ``Eq.trans #[heqO, hOther])
    return none
  | .isConspT w =>
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx w
    let vW ← ctxValExpr cfg ctx w
    -- a syntactic-cons VALUE
    if vW.isAppOfArity ``SExpr.cons 2 then
      return some (← Lean.Meta.mkAppM ``logic_consp_cons_t
        #[vW.appFn!.appArg!, vW.appArg!])
    -- direct clause evidence — a `(not (consp w))`-falsity fact, a truthy
    -- (consp w) branch fact, or the truthy-(CDR w) route (the former
    -- `conspEvidence?`, folded)
    let conspT : SExpr := .cons (.atom (.symbol { name := "CONSP" })) (.cons w .nil)
    let vC := mkApp (mkConst ``Logic.consp) vW
    let notC : SExpr := .cons (.atom (.symbol { name := "NOT" })) (.cons conspT .nil)
    match ← ctx.litFactByTermChecked? notC
        (← mkEq (mkApp (mkConst ``Logic.not) vC) (mkConst ``SExpr.nil)) with
    | some hNotNil =>
      let hne ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vC, hNotNil]
      return some (← Lean.Meta.mkAppM ``logic_consp_ne_nil_t #[vW, hne])
    | none =>
    match ctx.branchFacts.find? (fun (bt, _, sign, _) => bt == conspT && sign) with
    | some (_, vB, _, hNe) =>
      if ← Lean.Meta.isDefEq vB vC then
        return some (← Lean.Meta.mkAppM ``logic_consp_ne_nil_t #[vW, hNe])
      else return none
    | none =>
    let cdrW : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons w .nil)
    let notCdr : SExpr := .cons (.atom (.symbol { name := "NOT" })) (.cons cdrW .nil)
    let vCdr := mkApp (mkConst ``Logic.cdr) vW
    match ← ctx.litFactByTermChecked? notCdr
        (← mkEq (mkApp (mkConst ``Logic.not) vCdr) (mkConst ``SExpr.nil)) with
    | some hNotNil =>
      let hne ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vCdr, hNotNil]
      return some (← Lean.Meta.mkAppM ``logic_consp_of_cdr_ne_nil #[hne])
    | none =>
    -- an IF with BOTH branches conses
    if let .cons (.atom (.symbol ifS)) (.cons c (.cons a (.cons b .nil))) := w then
      if ifS.name == "IF" && depth > 0 then
        if let some ha ← typeSetWalk cfg ctx (.isConspT a) (depth - 1) then
          if let some hb ← typeSetWalk cfg ctx (.isConspT b) (depth - 1) then
            let vc ← ctxValExpr cfg ctx c
            return some (← Lean.Meta.mkAppM ``logic_consp_if_branches
              #[mkApp (mkConst ``Logic.toBool) vc, ha, hb])
    -- GENERAL truthy + proper-list route: (NOT (TRUE-LISTP w)) false in
    -- scope plus w-truthy evidence (the walker's own .isTruthy rung —
    -- ORDERED-PERMS Subgoal 3's (CONSP B))
    do
      let notOf (t : SExpr) : SExpr :=
        .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
      let tlpW : SExpr := .cons (.atom (.symbol { name := "TRUE-LISTP" }))
        (.cons w .nil)
      let vTlpW := mkApp (mkConst ``Logic.trueListp) vW
      let hTlp? ← findFactChecked (falsitySources ctx) (notOf tlpW)
        (← mkEq (mkApp (mkConst ``Logic.not) vTlpW) (mkConst ``SExpr.nil))
      if let some hTlpF := hTlp? then do
        let hTlpNe ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlpW, hTlpF]
        if let some hWne ← typeSetWalk cfg ctx (.isTruthy w) 0 then
          return some (← Lean.Meta.mkAppM ``logic_consp_of_trueListp_ne_nil
            #[hTlpNe, hWne])
    -- `(CDR u)` of an in-scope proper list
    if let .cons (.atom (.symbol fs)) (.cons u .nil) := w then
      if fs.name == "CDR" then do
        let ctx ← pinTermOpaques cfg cfg.envExpr ctx u
        let vU ← ctxValExpr cfg ctx u
        let vCdrU := mkApp (mkConst ``Logic.cdr) vU
        let vTlpU := mkApp (mkConst ``Logic.trueListp) vU
        let vTlpCdrU := mkApp (mkConst ``Logic.trueListp) vCdrU
        let notOf (t : SExpr) : SExpr :=
          .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
        let tlpOf (t : SExpr) : SExpr :=
          .cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons t .nil)
        let some hCdrF ← findFactChecked (falsitySources ctx) (notOf w)
            (← mkEq (mkApp (mkConst ``Logic.not) vCdrU) (mkConst ``SExpr.nil))
          | return none
        let hCdrNe ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vCdrU, hCdrF]
        let hTlpCdrNe? ← do
          match ← findFactChecked (falsitySources ctx) (notOf (tlpOf w))
              (← mkEq (mkApp (mkConst ``Logic.not) vTlpCdrU)
                (mkConst ``SExpr.nil)) with
          | some hf =>
            pure (some (← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlpCdrU, hf]))
          | none =>
            match ← findFactChecked (falsitySources ctx) (notOf (tlpOf u))
                (← mkEq (mkApp (mkConst ``Logic.not) vTlpU)
                  (mkConst ``SExpr.nil)) with
            | some hf => do
              let hTlpNe ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlpU, hf]
              let hTlpCdrT ← Lean.Meta.mkAppM ``logic_trueListp_cdr_t #[hTlpNe]
              let tNeNil ← proveByDecide
                (← Lean.Meta.mkAppM ``Ne
                  #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
              pure (some (← Lean.Meta.mkAppM ``ne_of_eq_of_ne #[hTlpCdrT, tNeNil]))
            | none => pure none
        let some hTlpCdrNe := hTlpCdrNe? | return none
        return some (← Lean.Meta.mkAppM ``logic_consp_of_trueListp_ne_nil
          #[hTlpCdrNe, hCdrNe])
    return none


/-- ONE-WAY term match: extend `σ` so that `pat`σ `== t` (`pat`'s variables
    drawn from `vars`; quoted subterms match only literally). Deterministic —
    the pool-subsumption witness recompute (validated by the caller,
    recompute-and-check; never a proof search). -/
partial def termMatch (vars : List Symbol) (pat t : SExpr)
    (σ : List (Symbol × SExpr)) : Option (List (Symbol × SExpr)) :=
  match pat with
  | .atom (.symbol sy) =>
    if vars.contains sy then
      match σ.lookup sy with
      | some b => if b == t then some σ else none
      | none => some (σ ++ [(sy, t)])
    else if pat == t then some σ else none
  | .cons (.atom (.symbol q)) rest =>
    if q.name == "QUOTE" then (if pat == t then some σ else none)
    else match t with
      | .cons t1 t2 =>
        (termMatch vars (.atom (.symbol q)) t1 σ).bind (termMatch vars rest t2 ·)
      | _ => none
  | .cons p1 p2 =>
    match t with
    | .cons t1 t2 => (termMatch vars p1 t1 σ).bind (termMatch vars p2 t2 ·)
    | _ => none
  | _ => if pat == t then some σ else none

/-- CLAUSE-subsumption witness: a σ under which every literal of `G` (the
    general clause) σ-instantiates to SOME literal of `C` — first witness in
    canonical order (G-literal order × C-literal order, backtracking). The
    caller VALIDATES the result against `C` (fail-closed). -/
partial def subsumeWitness (vars : List Symbol) (G C : List SExpr)
    (σ : List (Symbol × SExpr)) : Option (List (Symbol × SExpr)) :=
  match G with
  | [] => some σ
  | g :: rest =>
    C.findSome? fun c =>
      (termMatch vars g c σ).bind (subsumeWitness vars rest C ·)

/-- Fold per-entry proofs into a reflected list + its `∀ x ∈ list, P x`
    proof (`forall_mem_nil`/`forall_mem_cons` chain). -/
def mkForallMemProof (entryTy P : Expr) (entries : List (Expr × Expr)) :
    MetaM (Expr × Expr) := do
  match entries with
  | [] =>
    let listE ← mkAppOptM ``List.nil #[some entryTy]
    let prf ← mkAppOptM ``List.forall_mem_nil #[some entryTy, some P]
    return (listE, prf)
  | (e, h) :: rest =>
    let (restE, restP) ← mkForallMemProof entryTy P rest
    let listE ← mkAppM ``List.cons #[e, restE]
    let andP ← mkAppM ``And.intro #[h, restP]
    let consIff ← mkAppOptM ``List.forall_mem_cons
      #[some entryTy, some P, some e, some restE]
    return (listE, ← mkAppM ``Iff.mpr #[consIff, andP])

/-- The shared substN BRIDGE slice (dp-premises fold-back extraction): pin
    the σ terms, build `env' = bindArgsOver env formals vals`, and return the
    transport `bridge t : eval env (substTerm σ t) ≐ eval env' t`
    (`evalOpt_substTerm_substN` with kernel-decided WellScoped + length
    certificates). The SINGLE derivation site for the with-lemma recipe's
    scaffold — `instantiateEvTrueHypAt` and the linear/rule premise passes
    all consume it (three inline copies retired). σ-term pinning is part of
    the contract (audit F3: the linear copy relied on every σ term occurring
    inside the assembled premise — a latent hard-fail for a max-term-only
    variable). -/
structure SubstNBridge where
  env' : Expr
  bridge : SExpr → MetaM Expr
  ctx : ReplayCtx

def mkSubstNBridge (cfg : ReplayConfig) (ctx : ReplayCtx)
    (σvars : List Symbol) (σterms : List SExpr) (label : String) :
    MetaM SubstNBridge := do
  let w := cfg.worldExpr
  let env := cfg.envExpr
  let mut ctx := ctx
  for tt in σterms do
    ctx ← pinTermOpaques cfg env ctx tt
  let vals ← σterms.mapM (ctxValExpr cfg ctx)
  let convs ← σterms.mapM (ctxValProof cfg ctx)
  let formalsE ← mkListLit (mkConst ``Symbol) (σvars.map reflectSymbol)
  let argsE ← mkListLit (mkConst ``SExpr) (σterms.map reflectSExpr)
  let valsE ← mkListLit (mkConst ``SExpr) vals
  let env' ← mkAppM ``bindArgsOver #[env, formalsE, valsE]
  let hlenPf ← proveByDecide
    (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
    s!"substN lengths ({label})"
  let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
  let pFn ← withLocalDeclD `pr prodTy fun prV => do
    let fst ← mkAppM ``Prod.fst #[prV]
    let snd ← mkAppM ``Prod.snd #[prV]
    mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
  let entries ← (σterms.zip vals).mapM fun (tt, v) =>
    mkAppM ``Prod.mk #[reflectSExpr tt, v]
  let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
  let zipE ← mkAppM ``List.zip #[argsE, valsE]
  let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
    let mem ← mkAppM ``Membership.mem #[zipE, prV]
    mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
  let hargs ← mkExpectedTypeHint hargsRaw hargsTy
  let bridge : SExpr → MetaM Expr := fun t => do
    let hWellScoped ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr t])
         (mkConst ``Bool.true))
      s!"WellScoped ({label}): {repr t}"
    mkAppM ``evalOpt_substTerm_substN
      #[w, env, formalsE, argsE, valsE, reflectSExpr t,
        hWellScoped, hlenPf, hargs]
  return { env', bridge, ctx }

/-- Instantiate a PREMISE-FREE `∀ env', EvTrue w env' t`-shaped hypothesis
    at the current env under σ: returns `EvTrue w env (substTerm σ t)` via
    the substN bridge (the with-lemma scaffold's premise-free slice — G2
    rung 2; used for user-equivalence rule conclusions and `cong:` formula
    instances). Also returns the pinned ctx (σ-term opaques). -/
def instantiateEvTrueHypAt (cfg : ReplayConfig) (ctx : ReplayCtx) (hypV : Expr)
    (σvars : List Symbol) (σterms : List SExpr) (t : SExpr) :
    MetaM (Expr × ReplayCtx) := do
  let tσ := ACL2.Replay.substTerm σvars σterms t
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx tσ
  let sb ← mkSubstNBridge cfg ctx σvars σterms "instantiateEvTrueHypAt"
  let happ := mkApp hypV sb.env'
  return (← mkAppM ``evtrue_of_fuel_eq #[← sb.bridge t, happ], sb.ctx)

/-- The D4 BUILTIN-DEFINITION unfold (design §D4, WP2): `(fn a) ⇒ body[a]` for a
    `callBuiltin` builtin ABSENT from the world, where `body` is the fn's EMITTED
    ground-zero snapshot body (the only record of it — builtin-named snapshots
    are excluded from the world by `builtinNames`, no-shadow). The unfold is
    `fuel_eq_of_conv` of (a) the application's convergence to the builtin value
    (`conv_builtin1` — the world does not define fn, so `evalOpt` dispatches to
    `callBuiltin`) and (b) the body instance's value convergence (the ordinary
    value walker over the emitted body), bridged by the registered
    `gz_def_<fn>` lemma: `Logic.<fn> v = <body value composition>`. The bridge
    applies ONLY if the emitted body's composition unifies with the lemma's
    rhs — the fail-closed recompute-check against the emission; a drifted
    snapshot hard-fails here. Returns (formals, emitted body, unfold) for
    `replayDefinition`'s shared children-chaining tail. -/
def replayBuiltinDefUnfold (cfg : ReplayConfig) (ctx : ReplayCtx)
    (fn : Symbol) (args : List SExpr) : MetaM (List Symbol × SExpr × Expr) := do
  let some bodyLemma := d4DefFacts.lookup fn.name
    | throwError "definition: {fn.name} is not defined in the world and has no \
                  registered D4 definition fact (frontier)"
  let some (logicFn, cbLemma) := dpUnary.lookup fn.name
    | throwError "definition: D4 entry {fn.name} missing from dpUnary (internal)"
  let some (_, formals, body) := cfg.gzDefs.find? (fun e => e.1 == fn)
    | throwError "definition: builtin {fn.name} has no emitted ground-zero \
                  snapshot (emission gap, frontier)"
  let [f1] := formals
    | throwError "definition: D4 builtin {fn.name} snapshot arity \
                  {formals.length} ≠ 1 (frontier)"
  let [a] := args
    | throwError "definition: {fn.name} arity 1 ≠ {args.length} args"
  let substBody := ACL2.Replay.substTerm [f1] [a] body
  let va ← ctxValExpr cfg ctx a
  let pa ← ctxValProof cfg ctx a
  let pBody ← ctxValProof cfg ctx substBody
  let hNs ← proveNotSpecial fn
  let hNo ← proveNoShadow cfg fn
  let rv := mkApp (mkConst logicFn) va
  let hr ← mkAppM cbLemma #[va]
  let pL ← mkAppM ``conv_builtin1
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSExpr a, va, rv,
      hNs, hNo, pa, hr]
  let valueEq ← mkAppM bodyLemma #[va]
  let unfold ← mkAppM ``fuel_eq_of_conv #[pL, pBody, valueEq]
  return ([f1], body, unfold)

/-! ### The CLAUSE-CONTEXT `InTs` derivation (T1+2 sprint P3b)

ACL2 closes an `EQUAL` (`:LHS-TS`/`:RHS-TS`) and a RECOGNIZER
(`:TYPESET` vs `:TRUETS`/`:FALSETS`) by comparing TYPE-SETS it derived
from the context. Replaying such a step needs the same entry, so the
walk below reconstructs `InTs <ACL2's own emitted mask> <the term's
value>` — and ONLY that: the target mask is never chosen here, it is
read off the emission and the composition must land inside it.

Fact sources, in order: (1) LOCAL hypotheses the caller introduced (the
`IF` case-split of an `:ARG-LEAVES` walk), (2) the CLAUSE CONTEXT via
`typeSetWalk`, over the shapes `tsCtxProbes` generates, (3) COMPOUND
RECOGNIZERS the step's own ttree CITES. Everything is interpreted back
through the `Driver/TsFacts` registry, so the masks and proved lemmas
are the admission walk's. -/

/-- `tsSubsumedM m m' = true`, by ground kernel decision. -/
def tsSubsumedProofM (m m' : Int) : MetaM Expr := do
  mkDecideProof (← mkEq (← mkAppM ``ACL2.Replay.tsSubsumedM
    #[Lean.toExpr m, Lean.toExpr m']) (mkConst ``Bool.true))

mutual

/-- The `InTs` candidates for `t` the walk can see: `(mask, proof)`
    pairs. `local` carries the caller's own `Logic.toBool <test value> =
    <sign>` hypotheses (the `IF` split); `citedCr` the compound-recognizer
    RUNE NAMES the step cites. -/
partial def inTsCandidates (cfg : ReplayConfig) (ctx : ReplayCtx)
    (localFacts : List (SExpr × Bool × Expr)) (citedCr : List String)
    (t : SExpr) (tv : Expr) : MetaM (List (Int × Expr)) := do
  let inTsTy (m : Int) : MetaM Expr :=
    mkAppM ``ACL2.Replay.InTs #[Lean.toExpr m, tv]
  let mut out : List (Int × Expr) := []
  -- (1) the caller's LOCAL branch hypotheses
  for (f, pos, hb) in localFacts do
    if let some (a, m, nm) := tsFactOf f pos then
      if a == t then
        out := out ++ [(m, ← mkExpectedTypeHint (← mkAppM nm #[hb])
          (← inTsTy m))]
  -- (2) the CLAUSE CONTEXT, over the registry's own test shapes
  for p in tsCtxProbes t do
    for pos in [true, false] do
      if let some (a, m, nm) := tsFactOf p pos then
        if a == t then
          let ctxP ← pinTermOpaques cfg cfg.envExpr ctx p
          let vP ← ctxValExpr cfg ctxP p
          let hb? ←
            if pos then
              match ← typeSetWalk cfg ctxP (.isTruthy p) with
              | some hNe => pure (some (← mkAppM ``toBool_true_of_ne_nil #[hNe]))
              | none => pure none
            else
              match ← typeSetWalk cfg ctxP (.isNil p) with
              | some hNil =>
                pure (some (← mkAppM ``Iff.mpr
                  #[← mkAppM ``Logic.toBool_eq_false #[vP], hNil]))
              | none => pure none
          if let some hb := hb? then
            -- the proved fact's own statement pins the lifted test value's
            -- shape; a drifted lift fails the hint rather than passing
            out := out ++ [(m, ← mkExpectedTypeHint (← mkAppM nm #[hb])
              (← inTsTy m))]
  -- (3) COMPOUND RECOGNIZERS, gated on the step's OWN cited runes
  for (rune, fn, m, nm) in tsCompoundRecogProbes do
    if citedCr.contains rune then
      let p : SExpr := .cons (.atom (.symbol { name := fn })) (.cons t .nil)
      let ctxP ← pinTermOpaques cfg cfg.envExpr ctx p
      if let some hNil ← typeSetWalk cfg ctxP (.isNil p) then
        let vP ← ctxValExpr cfg ctxP p
        let hb ← mkAppM ``Iff.mpr
          #[← mkAppM ``Logic.toBool_eq_false #[vP], hNil]
        out := out ++ [(m, ← mkExpectedTypeHint (← mkAppM nm #[hb])
          (← inTsTy m))]
  -- (4) ARITHMETIC PRIMITIVES: ACL2's `type-set-binary-+` cell — both
  -- arguments typed (recursively, from the SAME sources) and the
  -- registered closure fact applied
  if let .cons (.atom (.symbol op)) (.cons a (.cons b .nil)) := t then
    if let some (inMask, outMask, nm) := tsBinaryOf op.name then
      let ctxA ← pinTermOpaques cfg cfg.envExpr ctx a
      let va ← ctxValExpr cfg ctxA a
      let ctxB ← pinTermOpaques cfg cfg.envExpr ctxA b
      let vb ← ctxValExpr cfg ctxB b
      match ← inTsFromCtx cfg ctxB localFacts citedCr a va inMask,
            ← inTsFromCtx cfg ctxB localFacts citedCr b vb inMask with
      | some ha, some hb =>
        out := out ++ [(outMask, ← mkExpectedTypeHint
          (← mkAppM nm #[ha, hb]) (← inTsTy outMask))]
      | _, _ => pure ()
  return out

/-- Prove `InTs target tv` for `t` — ACL2's OWN emitted mask — from the
    visible typing facts: one (weakened) or two (intersected), exactly as
    `tsFromFacts` does on the admission side. Anything else is a frontier
    rather than a guess. -/
partial def inTsFromCtx (cfg : ReplayConfig) (ctx : ReplayCtx)
    (localFacts : List (SExpr × Bool × Expr)) (citedCr : List String)
    (t : SExpr) (tv : Expr) (target : Int) : MetaM (Option Expr) := do
  -- a QUOTED CONSTANT needs no fact at all: its value is closed, so
  -- ACL2's verdict for it is a kernel decision
  if let .cons (.atom (.symbol q)) (.cons _ .nil) := t then
    if q.name == "QUOTE" then
      let ty ← mkAppM ``ACL2.Replay.InTs #[Lean.toExpr target, tv]
      try
        return some (← mkExpectedTypeHint (← mkDecideProof (← mkEq
          (← mkAppM ``ACL2.Replay.tsMember
            #[Lean.toExpr target, ← mkAppM ``ACL2.Replay.tsIndex #[tv]])
          (mkConst ``Bool.true))) ty)
      catch _ => return none
  let cands ← inTsCandidates cfg ctx localFacts citedCr t tv
  for (m, h) in cands do
    if ACL2.Replay.tsSubsumedM m target then
      return some (← mkAppM ``ACL2.Replay.inTs_weaken
        #[← tsSubsumedProofM m target, h])
  for (m1, h1) in cands do
    for (m2, h2) in cands do
      if ACL2.Replay.tsInter2Subsumed m1 m2 target then
        let hsub ← mkDecideProof (← mkEq
          (← mkAppM ``ACL2.Replay.tsInter2Subsumed
            #[Lean.toExpr m1, Lean.toExpr m2, Lean.toExpr target])
          (mkConst ``Bool.true))
        return some (← mkAppM ``ACL2.Replay.inTs_inter2 #[hsub, h1, h2])
  return none

end

/-- THE `:ARG-LEAVES` WALK (T1+2 sprint P3b — the recognizer-under-`IF`
    trio: `COUNT-DOWN` / `MY-EVENP` / `CD2`'s termination clauses, whose
    `(CONSP (IF (INTEGERP N) (IF (< N '0) '0 N) '0))` argument ACL2
    types by walking the `IF` and UNIONING the branch verdicts).

    The union alone is not replayable, so this walk mirrors ACL2's own
    `type-set-rec` `'if` case: case-split the `IF` at the VALUE level
    (`inTs_cond`) and, at each LEAF, consume THAT branch's OWN emitted
    verdict — the entry whose governing tests the branch establishes —
    proving it from the split's hypotheses. Every leaf verdict must land
    inside the step's emitted `:TYPESET` (the union ACL2 published), and
    a leaf with no addressed entry is a frontier, never a guess. -/
partial def inTsFromArgLeaves (cfg : ReplayConfig) (ctx : ReplayCtx)
    (leaves : List TpLeaf) (localFacts : List (SExpr × Bool × Expr))
    (t : SExpr) (target : Int) : MetaM (Option Expr) := do
  let ctxT ← pinTermOpaques cfg cfg.envExpr ctx t
  let vT ← ctxValExpr cfg ctxT t
  let want ← mkAppM ``ACL2.Replay.InTs #[Lean.toExpr target, vT]
  match t with
  | .cons (.atom (.symbol ifS)) (.cons c (.cons th (.cons el .nil))) =>
    if ifS.name == "IF" then
      let ctxC ← pinTermOpaques cfg cfg.envExpr ctxT c
      let vC ← ctxValExpr cfg ctxC c
      let bE ← mkAppM ``Logic.toBool #[vC]
      let branch (sign : Bool) (br : SExpr) : MetaM (Option Expr) := do
        let hbTy ← mkEq bE (mkConst (if sign then ``Bool.true else ``Bool.false))
        withLocalDeclD `hb hbTy fun hb => do
          match ← inTsFromArgLeaves cfg ctx leaves
              ((c, sign, hb) :: localFacts) br target with
          | some p => pure (some (← mkLambdaFVars #[hb] p))
          | none => pure none
      let some hx ← branch true th | return none
      let some hy ← branch false el | return none
      try
        return some (← mkExpectedTypeHint (← mkAppM ``ACL2.Replay.inTs_cond
          #[hx, hy]) want)
      catch _ => return none
    else pure ()
  | _ => pure ()
  -- a LEAF: ACL2's ADDRESSED entry for it — the emitted branch whose
  -- governing tests THIS branch establishes
  let fs := localFacts.map (fun (f, p, _) => (f, p))
  let addressed := leaves.filter fun l =>
    l.term == t && l.tests.all (fun cnd => branchEstablishes fs cnd true)
  let some leaf := addressed.head?
    | return none
  unless ACL2.Replay.tsSubsumedM leaf.ts target do
    return none
  match ← inTsFromCtx cfg ctxT localFacts [] t vT leaf.ts with
  | none => return none
  | some hLeaf =>
    return some (← mkExpectedTypeHint (← mkAppM ``ACL2.Replay.inTs_weaken
      #[← tsSubsumedProofM leaf.ts target, hLeaf]) want)

/-- ACL2'S RECOGNIZER VERDICT FROM ITS OWN TYPE-SETS (T1+2 sprint P3b):
    a `recognizer/true` or `recognizer/false` step publishes the
    argument's `:TYPESET` and the recognizer's `:TRUETS`, and closes the
    verdict by comparing them. The replay does the same — derive `InTs m
    <the argument's value>` from the facts it can see (the `:ARG-LEAVES`
    walk for an `IF`-valued argument, otherwise the clause context and
    the step's CITED compound recognizers), then apply the registered
    model fact for the verdict side.

    Two cross-checks, both against ACL2's OWN emitted numbers: the
    step's `:TRUETS` must equal the registry's, and ACL2's emitted
    `:TYPESET` must be INSIDE the mask we derived (we may prove something
    weaker than ACL2 knew — never something it contradicts). -/
def recogVerdictFromTs (cfg : ReplayConfig) (ctx : ReplayCtx)
    (recog : String) (arg : SExpr) (verdict : SExpr)
    (stepTs trueTs : Option Int) (argLeaves : List TpLeaf)
    (citedCr : List String) : MetaM (Option Expr) := do
  let entry? : Option (Int × Lean.Name) :=
    if verdict == SExpr.t then
      (tsRecogTrue.find? (fun (n, _, _) => n == recog)).map (fun (_, m, l) => (m, l))
    else if verdict == SExpr.nil then
      (tsRecogNil.find? (fun (n, _, _) => n == recog)).map (fun (_, m, l) => (m, l))
    else none
  let some (regTrueTs, lem) := entry? | return none
  -- the step's OWN emitted true-ts must be the registry's number
  match trueTs with
  | some ts => unless ts == regTrueTs do return none
  | none => return none
  let ctxA ← pinTermOpaques cfg cfg.envExpr ctx arg
  let va ← ctxValExpr cfg ctxA arg
  -- the candidate masks: the `:ARG-LEAVES` walk (IF-valued argument) or
  -- the ordinary context probes
  let cands : List (Int × Expr) ←
    if !argLeaves.isEmpty then
      match stepTs with
      | none => pure []
      | some ts =>
        match ← inTsFromArgLeaves cfg ctxA argLeaves [] arg ts with
        | some h => pure [(ts, h)]
        | none => pure []
    else inTsCandidates cfg ctxA [] citedCr arg va
  for (m, hv) in cands do
    -- ACL2's own verdict for the argument must be INSIDE what we derived
    let acl2Ok := match stepTs with
      | some ts => ACL2.Replay.tsSubsumedM ts m
      | none => false
    unless acl2Ok do continue
    if verdict == SExpr.t then
      if ACL2.Replay.tsSubsumedM m regTrueTs then
        return some (← mkAppM lem #[← tsSubsumedProofM m regTrueTs, hv])
    else if ACL2.Replay.tsDisjointM m regTrueTs then
      let hd ← mkDecideProof (← mkEq
        (← mkAppM ``ACL2.Replay.tsDisjointM
          #[Lean.toExpr m, Lean.toExpr regTrueTs])
        (mkConst ``Bool.true))
      return some (← mkAppM lem #[hd, hv])
  return none

/-- The `(TRUE-LISTP …)` term and its CONS-peels, outermost first:
    `(TRUE-LISTP (CONS a d))` also lists `(TRUE-LISTP d)` (recursively). Each
    peel is a DEFINITIONAL reduction on the value side (`trueListp (cons a d) =
    trueListp d` is a match-arm equation), so a spine fact about any peel
    discharges the original term — the type-set reasoning ACL2 records as
    `fake-rune-for-type-set` on recognizer/true nodes. -/
partial def trueListpConsPeels (term : SExpr) : List SExpr :=
  term :: match term with
  | .cons r@(.atom (.symbol rs))
      (.cons (.cons (.atom (.symbol cs)) (.cons _ (.cons d .nil))) .nil) =>
    if rs.name == "TRUE-LISTP" && cs.name == "CONS" then
      trueListpConsPeels (.cons r (.cons d .nil))
    else []
  | _ => []

/-- THE COMPOUND-RECOGNIZER TS CELL (T1+2 sprint P3b): a
    `(:COMPOUND-RECOGNIZER …)` node is ACL2 closing a recognizer from
    the argument's TYPE-SET — the record publishes both (`:TYPESET`,
    `:TRUETS`), and where the argument is an `IF` it also publishes the
    per-branch `:ARG-LEAVES`. Replay it by the same comparison
    (`recogVerdictFromTs`, whose cross-checks are against ACL2's own
    numbers); `none` leaves the recipe's existing routes and its honest
    frontier untouched. -/
def compoundRecogTsCell (cfg : ReplayConfig) (ctx : ReplayCtx)
    (prov : StepProvenance) (lhs rhs : SExpr) : MetaM (Option Expr) := do
  let .cons (.atom (.symbol rs)) (.cons arg .nil) := lhs | return none
  let verdict := match rhs with
    | .cons (.atom (.symbol q)) (.cons v .nil) =>
      if q.name == "QUOTE" then v else rhs
    | v => v
  let citedCr := prov.runes.filterMap fun r =>
    if r.ty == "compound-recognizer" then some r.name else none
  match ← recogVerdictFromTs cfg ctx rs.name arg verdict prov.typeSet
      prov.trueTs prov.argLeaves citedCr with
  | none => return none
  | some hV =>
    let ctxL ← pinTermOpaques cfg cfg.envExpr ctx lhs
    let p ← ctxValProof cfg ctxL lhs
    let pQ ← mkAppM ``re_val_quote
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr verdict]
    return some (← mkAppM ``fuel_eq_of_conv #[p, pQ, hV])

/-- THE `EQUAL`-VERDICT TS-DISJOINTNESS CELL (T1+2 sprint P3b): the R2
    fold-in `:LHS-TS`/`:RHS-TS` are the two operand type-sets ACL2's
    `type-set-equal` intersected to reach a `'NIL` verdict. DISJOINT
    masks make the equality nil, and the replay proves exactly that —
    each operand's membership in ACL2's OWN emitted mask (from the
    clause context, never chosen here) plus the masks' disjointness by
    kernel decision. Driving instance: `CLASSIFY-POS`'s `(EQUAL N '0)`,
    `:LHS-TS 6` (positive integer, from the `(INTEGERP N)` / `(< '0 N)`
    hypotheses) against `:RHS-TS 1` (zero). Stated in the ORIGINAL
    operand order, so it needs no re-orientation. `none` (no emitted
    pair, non-disjoint masks, an operand the context does not type) and
    the recipe's other cells take over. -/
def tseTsDisjointCell (cfg : ReplayConfig) (ctx : ReplayCtx)
    (prov : StepProvenance) (lhs x0 qc0 : SExpr) : MetaM (Option Expr) := do
  let some mL := prov.lhsTs | return none
  let some mR := prov.rhsTs | return none
  unless ACL2.Replay.tsDisjointM mL mR do return none
  let ctxL ← pinTermOpaques cfg cfg.envExpr ctx x0
  let vL ← ctxValExpr cfg ctxL x0
  let ctxR ← pinTermOpaques cfg cfg.envExpr ctxL qc0
  let vR ← ctxValExpr cfg ctxR qc0
  let some hL ← inTsFromCtx cfg ctxR [] [] x0 vL mL | return none
  let some hR ← inTsFromCtx cfg ctxR [] [] qc0 vR mR | return none
  let hd ← mkDecideProof (← mkEq
    (← mkAppM ``ACL2.Replay.tsDisjointM #[Lean.toExpr mL, Lean.toExpr mR])
    (mkConst ``Bool.true))
  let hTs ← mkAppM ``ACL2.Replay.logic_equal_nil_of_ts_disjoint #[hd, hL, hR]
  let pL ← ctxValProof cfg ctx lhs
  let pR ← mkAppM ``re_val_quote
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.nil]
  return some (← mkAppM ``fuel_eq_of_conv #[pL, pR, hTs])

/-- The registered `ZP-COMPOUND-RECOGNIZER` recipe (moved out of
    Driver/NodeCore/Node at the module-size ratchet, T1+2 sprint P3b —
    MOVE-ONLY, body unchanged; `prov`/`lhs`/`rhs` are the node's). -/
def replayZpCompoundRecog (cfg : ReplayConfig) (ctx : ReplayCtx)
    (prov : StepProvenance) (lhs rhs : SExpr) : MetaM Expr := do
  -- registered COMPOUND-RECOGNIZER recipe, pinned to the one ground-zero
  -- rule the corpus cites: `(ZP u) ⇒ 'T` believed by type-set from the
  -- in-scope FALSITY of `(INTEGERP u)` (zp is t on non-integers — kernel
  -- `logic_zp_of_integerp_nil`). Any other shape is a named frontier.
  unless prov.origin == "recognizer/true" do
    throwError "compound-recognizer: origin {prov.origin} ≠ recognizer/true \
                (frontier)"
  let .cons (.atom (.symbol zs)) (.cons u .nil) := lhs
    | throwError "compound-recognizer: lhs {repr lhs} is not (zp u)"
  unless zs.name == "ZP" && rhs == quoteT do
    throwError "compound-recognizer: expected (zp u) ⇒ 't, got \
                {repr lhs} ⇒ {repr rhs}"
  let intU : SExpr :=
    .cons (.atom (.symbol { name := "INTEGERP" })) (.cons u .nil)
  let some hNil := ctx.litFactByTerm? intU
    | throwError "compound-recognizer: no in-scope falsity fact for \
                  {repr intU} (frontier)"
  let vInt ← ctxValExpr cfg ctx intU
  unless vInt.isAppOfArity ``Logic.integerp 1 do
    throwError "compound-recognizer: value of {repr intU} is not \
                (Logic.integerp _)"
  let hT ← mkAppM ``logic_zp_of_integerp_nil #[vInt.appArg!, hNil]
  let v ← ctxValExpr cfg ctx lhs
  unless ← isDefEq v (mkApp (mkConst ``Logic.zp) vInt.appArg!) do
    throwError "compound-recognizer: value of {repr lhs} does not match \
                the (Logic.zp _) instance"
  let p ← ctxValProof cfg ctx lhs
  let pQ ← mkAppM ``re_val_quote
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
  mkAppM ``fuel_eq_of_conv #[p, pQ, hT]

end ACL2.Replay.Driver
