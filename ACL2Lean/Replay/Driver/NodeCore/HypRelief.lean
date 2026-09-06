import ACL2Lean.Replay.Driver.NodeCore.SubstitutionFolds
import ACL2Lean.Replay.Driver.NodeCore.KnownTrue

/-! Replay the recorded hypothesis relief of an ordinary stored rule.

The caller validates the rule/substitution and supplies its substitution
bridge. This module consumes the HYP block and returns the rule premises;
RHS continuation and application stay in Node.
-/

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay the RHS chain that ACL2 used to bind an EQUAL hypothesis's free
    variable. The recorded final substitution supplies the binding; the
    chain must end at that exact term. The final equality is reflexivity
    after right congruence, not a second search for hypothesis relief. -/
private def replayBindingRhs (rec : NodeRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (rname : String) (idx : Nat) (hyp hypσ : SExpr)
    (kids : List ProofNode) : MetaM Expr := do
  let .cons (.atom (.symbol eqS))
      (.cons (.atom (.symbol _)) (.cons _ .nil)) := hyp
    | throwError "rule {rname}: binding-RHS hypothesis {idx} is not (EQUAL variable rhs)"
  unless eqS.name == "EQUAL" do
    throwFrontier m!"rule {rname}: binding-RHS hypothesis {idx} uses {eqS.name}; \
      non-EQUAL binding relief is not implemented"
  let .cons _ (.cons bound (.cons rhs .nil)) := hypσ
    | throwError "rule {rname}: malformed instantiated binding hypothesis {idx}"
  let (chainOpt, finalTerm) ← rec.rewrites cfg ctx rhs kids
  let some chain ← chainReqEq chainOpt
    | throwError "rule {rname}: binding-RHS hypothesis {idx} has no recorded steps"
  unless finalTerm == bound do
    throwError "rule {rname}: binding-RHS hypothesis {idx} ends at {repr finalTerm}, \
      but :SUBST binds its variable to {repr bound}"
  let lifted ← mkAppM ``evalOpt_congr_binary_right
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol eqS, reflectSExpr bound,
      reflectSExpr rhs, reflectSExpr bound, ← proveNotSpecial eqS, chain]
  let self ← mkAppM ``re_equal_self
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr bound,
      ← proveConv cfg cfg.envExpr ctx bound, ← proveNoShadow cfg eqS]
  mkAppM ``evtrue_of_fuel_eq #[lifted, ← mkAppM ``evtrue_of_eq_t #[self]]

partial def replayRuleHypotheses (rec : NodeRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (rname : String) (hyps : List SExpr)
    (σvars : List Symbol) (σterms : List SExpr) (hypKids : List ProofNode)
    (runes : List Rune) (bridge : SExpr → MetaM Expr) : MetaM (Array Expr) := do
  let (reliefMarkers, chainKids) := hypKids.partition
    fun c => (runeOf c).ty == "hyp-relief"
  let bindingIndex : ProofNode → Option Nat := fun
    | .node _ _ _ _ p => match p.path.head? with
      | some (.bindingRhs i _) => some i
      | _ => none
  let bindingKids := chainKids.filterMap fun n => (bindingIndex n).map (·, n)
  let plainKids := chainKids.filter fun n => (bindingIndex n).isNone
  let bindingIndices := (bindingKids.map Prod.fst).eraseDups
  for i in bindingIndices do
    unless i > 0 && i ≤ hyps.length do
      throwError "rule {rname}: binding-RHS index {i} outside its {hyps.length} hypotheses"
  -- premises: EvTrue w env' hᵢ from the recorded relief. Sources, per hyp:
  -- a silent-relief MARKER whose hyp matches hσ (recompute-and-check) —
  -- clause-context lookup; else an indexed binding-RHS chain; otherwise
  -- the one ordinary relief chain. Multiple unindexed chains still need
  -- per-hyp bracketing and fail closed.
  -- SYNP hyps are relieved by neither a marker nor a chain (they discharge
  -- definitionally below) — exclude them from the partition count
  -- (audit 2026-07-19 R1)
  let synpHyps := hyps.countP fun h =>
    match h with
    | .cons (.atom (.symbol s)) _ => s.name == "SYNP"
    | _ => false
  if !plainKids.isEmpty &&
      hyps.length != reliefMarkers.length + synpHyps + bindingIndices.length + 1 then
    throwError "rule {rname}: {hyps.length} hyps with one recorded \
                relief chain, {reliefMarkers.length} markers, and \
                {synpHyps} synp hyps, {bindingIndices.length} indexed binding chains \
                — per-hyp partition (frontier)"
  let tNeNil ← proveByDecide
    (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
  let mut prems : Array Expr := #[]
  for (h, idx) in hyps.zipIdx do
    let originalHσ := ACL2.Replay.substTerm σvars σterms h
    let marker? := reliefMarkers.find? (fun c => hypothesisMarkerInput c == originalHσ)
    let hasMarker := marker?.isSome
    let (hσ, foldProof?) ← match marker? with
      | some (.node _ lhs rhs _ prov) => do
        unless lhs == rhs do throwError "rule {rname}: hypothesis marker endpoints differ"
        match prov.substBasis with
        | none => pure (originalHσ, none)
        | some basis =>
          unless prov.origin == "relieve-hyp/known-true" do
            throwError "rule {rname}: substitution basis on unsupported relief origin"
          pure (lhs, ← replayHypSubstitution cfg basis lhs)
      | none => pure (originalHσ, none)
    let reliefMarkers := marker?.toList
    let ownBinding := (bindingKids.filter (fun p => p.1 == idx + 1)).map Prod.snd
    let chainKids := if ownBinding.isEmpty then plainKids else ownBinding
    -- a SYNP hyp (syntaxp/bind-free): ACL2 relieves it by the meta-level
    -- syntactic check and records `(:DEFINITION SYNP)` in the ttree — in
    -- the LOGIC, `synp` ignores its (always-quoted) args and returns `t`,
    -- so the recorded relief IS the definitional ground evaluation
    let isSynp := match hσ with
      | .cons (.atom (.symbol s)) _ => s.name == "SYNP"
      | _ => false
    if !ownBinding.isEmpty && (hasMarker || isSynp) then
      throwError "rule {rname}: hypothesis {idx + 1} has both indexed binding \
        steps and another relief record — unconsumed binding chain"
    -- EVERY hyp must have an emitted relief RECORD — a silent-relief marker
    -- or a rewrite chain. No record at all is an emission gap (audit
    -- 2026-07-06 finding A): the clause context may well justify the hyp,
    -- but nothing in the tree says ACL2 relieved it that way — hard-fail
    -- and emit more, never paper over.
    if !hasMarker && chainKids.isEmpty && !isSynp then
      throwError "rule {rname}: hyp {repr hσ} has NO emitted relief record \
                  (no relieve-hyp marker, no relief chain) — emission gap \
                  (frontier)"
    let evTrueEnv ←
      if isSynp then do
        -- consistency check on the CUMULATIVE ttree rune set (it can only
        -- REJECT — ACL2 pushes (:DEFINITION SYNP) on every successful synp
        -- relief, but the set may also carry it from earlier steps; the
        -- honest relief record is the definitional evaluation below)
        unless runes.any (fun r => r.ty == "definition" && r.name == "SYNP") do
          throwError "rule {rname}: SYNP hyp {repr hσ} but no \
                      (:DEFINITION SYNP) in the node's ttree runes \
                      (frontier)"
        -- re-run the same closed computation (`synp`'s world body is 'T):
        -- the exec-counterpart carve-out, exactly how ACL2 regards it
        let conv ← replayExecGround cfg hσ SExpr.t
        mkAppM ``evtrue_of_conv_ne_nil #[conv, tNeNil]
      else if hasMarker then do
        let quoted? := match hσ with
          | .cons (.atom (.symbol q)) (.cons value .nil) =>
            if q.name == "QUOTE" then some value else none
          | _ => none
        if let some value := quoted? then do
          -- Check the recorded final truth value after substitution folding.
          let ne ← proveByDecide
            (← mkAppM ``Ne #[reflectSExpr value, mkConst ``SExpr.nil]) "quoted hypothesis is nonnil"
          let conv ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr value]
          mkAppM ``evtrue_of_conv_ne_nil #[conv, ne]
        else do
          -- relieved SILENTLY from the clause context (the emitted marker
          -- names the instantiated hyp): the spine's (not hσ)-falsity fact
          -- (the type-alist source the type-alist recipe also consumes)
          let notH : SExpr := .cons (.atom (.symbol { name := "NOT" }))
            (.cons hσ .nil)
          let vH ← ctxValExpr cfg ctx hσ
          -- TYPE-CHECKED lookup (G1 arc 2026-07-29): a term-keyed fact from
          -- another env context (pool-root/elim crossings) must not be
          -- consumed — mismatches fall through to the alternate sources.
          let checkedHit ← ctx.litFactByTermChecked? notH
            (← mkEq (mkApp (mkConst ``Logic.not) vH) (mkConst ``SExpr.nil))
          match checkedHit with
          | some hNotNil => do
            let hne ← mkAppM ``logic_not_nil_ne #[vH, hNotNil]
            mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hσ, hne]
          | none =>
            -- a NOT-wrapped hyp whose ATOM's falsity is in scope: the hyp's
            -- truth is definitional (Logic.not nil = t) — the complement
            -- orientation of the direct case above (multi-elim guard-child
            -- walks surface this: DEFAULT-CAR's hyp (NOT (CONSP v2)) with
            -- the literal (CONSP v2) assumed false). The lookup —
            -- lit-facts, false-branch assumptions, and upstream
            -- `assoc-equiv`'s two-orientation EQUAL match — is
            -- `notAtomFalsity?` (Compose.lean).
            if let some hAtmNil ← notAtomFalsity? cfg ctx hσ then do
              let hT ← mkAppM ``logic_not_t_of_nil #[hAtmNil]
              let hne ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
              mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hσ, hne]
            else if (ACL2.Replay.freeVars hσ).isEmpty then do
              -- GROUND hyp KNOWN-TRUE (Phase-3 class, 2026-08-04:
              -- convert-perm's TRUE-LISTP-RM / RM-TLFIX — marker
              -- RELIEVE-HYP/KNOWN-TRUE on (TRUE-LISTP 'NIL)). Audit
              -- 2026-08-04 F1 corrected the mechanism attribution: ACL2's
              -- verdict here comes from the BUILT-IN RECOGNIZER TUPLE in
              -- type-set-rec (probed live: knownp=T with ZERO runes added
              -- — type-set-rec has no ground-evaluation clause), NOT from
              -- the executable counterpart. It is a VERDICT-ONLY type-set
              -- step — the ratified DP carve-out shape — and the replay
              -- SUBSTITUTES closed-form evaluation for it on the closed
              -- hyp instance: same value, kernel-checked, leaf-granular.
              -- F2 caution: the marker's :TA-RUNES are the cumulative
              -- incoming set (the verdict adds none), so there is nothing
              -- verdict-specific to anchor on; the arm keys on the closed
              -- term alone. A ground hyp whose value is not exactly t
              -- hard-fails inside replayExecGround (honest frontier).
              -- R4 EXPIRY DISCHARGED (2026-08-07): the arm is GATED on
              -- the EMITTED recognizer tuple for the ground hyp's head
              -- fn — the verdict basis ACL2's type-set-rec consulted,
              -- now read from the cited snapshot (fork-batch item 2)
              -- per the user's option-2 ruling. The value recompute
              -- stays (kernel-checked evaluation toward the recorded
              -- verdict); a ground hyp whose head has NO cited tuple
              -- hard-fails — no tuple, no verdict basis, no discharge.
              let headFn ← match hσ with
                | .cons (.atom (.symbol hs)) _ => pure hs.name
                | _ => throwError "ground-hyp: {repr hσ} has no \
                    application head (frontier)"
              unless (cfg.recogTuples.find? (fun t => t.fn == headFn)).isSome do
                throwError "ground-hyp: head fn {headFn} has no cited \
                    recognizer tuple in the emitted snapshot — the \
                    KNOWN-TRUE verdict's basis is absent (frontier)"
              let conv ← replayExecGround cfg hσ SExpr.t
              mkAppM ``evtrue_of_conv_ne_nil #[conv, tNeNil]
            else if let some p ← replayHypLookupFromBasis? cfg ctx hσ reliefMarkers then
              pure p
            else if let some p ← replayKnownTrueIf? cfg ctx hσ reliefMarkers then
              pure p
            else if let some p ← replayKnownTruePrimitive? cfg ctx hσ reliefMarkers then
              pure p
            else do
            -- FC-DERIVED type-alist entry (emission arc 2026-07-21): the
            -- marker's :TA-RUNES name the forward-chaining rule that put the
            -- fact on the type-alist. Registered reliefs (rule-of-three:
            -- a third entry triggers registry-ization): LEXORDER-TOTAL —
            -- pinned against the EMITTED snapshot (audit-F2 style), the
            -- instantiated FC hyp discharged from the in-scope falsity
            -- fact, the conclusion via the kernel-proved
            -- `ACL2.lexorder_total`.
            fcReliefLexorderTotal cfg ctx rname hσ notH vH tNeNil
              reliefMarkers
      else if !ownBinding.isEmpty then
        replayBindingRhs rec cfg ctx rname (idx + 1) h hσ ownBinding
      else if let some (notS, atm) := (match hσ with
          | .cons (.atom (.symbol s)) (.cons a .nil) =>
            if s.name == "NOT" then some (s, a) else none
          | _ => none) then do
        -- NEGATED hyp: ACL2's relieve-hyp strips the `not` and rewrites the
        -- ATM (obj flipped, NO gstack frame) — the recorded chain is
        -- atm-rooted and must land on 'nil. Lift the composed atm chain
        -- through the `not` wrapper by unary congruence and fold
        -- `(not 'nil) ⇒ 't` by re-running the same closed computation
        -- (the exec-counterpart carve-out), as `replayLiteralChain` does
        -- for :NOT-FLG literals.
        let (chainOpt, finalAtom) ← rec.rewrites cfg ctx atm chainKids
        let chainOpt ← chainReqEq chainOpt
        unless finalAtom == quoteNil do
          throwError "rule {rname}: negated-hyp relief chain for {repr hσ} \
                      ends at {repr finalAtom}, not (quote nil)"
        let some ch := chainOpt
          | throwError "rule {rname}: negated-hyp relief chain for {repr hσ} \
                        composed to no steps"
        let ns ← proveNotSpecial notS
        let lifted := mkAppN (mkConst ``evalOpt_congr_unary)
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol notS, reflectSExpr atm,
            reflectSExpr quoteNil, ns, ch]
        let notNil : SExpr := .cons (.atom (.symbol notS)) (.cons quoteNil .nil)
        let pNot ← replayExecGround cfg notNil SExpr.t
        let pQ ← mkAppM ``re_val_quote
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
        let step ← mkAppM ``fuel_eq_of_conv
          #[pNot, pQ, ← mkEqRefl (reflectSExpr SExpr.t)]
        let chain ← mkAppM ``fuel_chain_eq #[lifted, step]
        let hconv ← mkAppM ``fuel_conv_of_eq #[chain, ← quoteTFact cfg]
        mkAppM ``evtrue_of_conv_ne_nil #[hconv, tNeNil]
      else do
        -- the recorded HYP chain rewrites hσ ⇒ … ⇒ 't (paths carry one
        -- more boundary frame, as definition-body children do)
        let (chainOpt, finalT) ← rec.rewrites cfg ctx hσ chainKids
        let chainOpt ← chainReqEq chainOpt
        unless finalT == quoteT do
          throwError "rule {rname}: relief chain for {repr hσ} ends at \
                      {repr finalT}, not (quote t)"
        let some chain := chainOpt
          | throwError "rule {rname}: relief chain for {repr hσ} \
                        composed to no steps"
        let hconv ← mkAppM ``fuel_conv_of_eq #[chain, ← quoteTFact cfg]
        mkAppM ``evtrue_of_conv_ne_nil #[hconv, tNeNil]
    let evTrueEnv ← match foldProof? with
      | none => pure evTrueEnv
      | some p => mkAppM ``evtrue_of_fuel_eq #[p, evTrueEnv]
    -- transport to env': eval env' h ≡ eval env hσ (the bridge, reversed)
    let pB ← bridge h
    prems := prems.push
      (← mkAppM ``evtrue_of_fuel_eq #[← mkAppM ``fuel_eq_symm #[pB], evTrueEnv])
  return prems

end ACL2.Replay.Driver
