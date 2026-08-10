/-
  Driver/NodeCore/Literal — positional slice of the former NodeCore
  monolith (perf arc 3a, 2026-08-07): MOVE-ONLY; the boundaries are the
  file's own def-before-use order, so the import chain IS the
  dependency order.
-/
import ACL2Lean.Replay.Driver.NodeCore.Rewrites

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- CONSUME the literal's recorded boundary verdicts (`emit/atm/
    try-type-set`; audit 2026-08-07 M2 — previously extracted but read
    by NOTHING, and the node-path arm was unreachable dead code, now
    deleted): each record asserts rewrite-atm ABANDONED the chain and
    re-decided the ORIGINAL atom by type-set in isolation, to the
    recorded constant. The replay VALIDATES each verdict at value level
    (the value must BE the recorded constant — recompute toward the
    recorded target) and hard-fails on mismatch; the chain composition
    (also fully recorded) remains the proof route, with the verdict
    record now a consumed cross-check rather than dropped data. -/
def validateBoundaryVerdicts (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lp : LiteralProof) : MetaM Unit := do
  for st in lp.boundaryVerdicts do
    let .cons (.atom (.symbol qS)) (.cons cv .nil) := st.rhs
      | throwError "boundary verdict: rhs {repr st.rhs} is not a quoted \
          constant (frontier)"
    unless qS.name == "QUOTE" do
      throwError "boundary verdict: rhs {repr st.rhs} is not a quoted \
          constant (frontier)"
    let ctxV ← pinTermOpaques cfg cfg.envExpr ctx st.lhs
    let vL ← ctxValExpr cfg ctxV st.lhs
    unless ← Lean.Meta.isDefEq vL (reflectSExpr cv) do
      throwError "boundary verdict: value of {repr st.lhs} does not \
          reduce to the recorded {repr st.rhs} (truthy-but-not-'T class \
          — frontier)"

/-- Replay a literal's rewrite chain at the LITERAL level. ACL2's rewriter works on
    the literal's ATOM (`rewrite-atm`): for a `:NOT-FLG T` literal `(not atm)` the
    node `:PATH`s are atom-relative, so chain on the atom and lift the composed
    eval-equality back through the `not` wrapper by unary congruence. Returns the
    literal-level chain (if any) and the final literal. -/
def replayLiteralChain (cfg : ReplayConfig) (ctx : ReplayCtx) (lp : LiteralProof)
    : MetaM (Option (Expr × Bool) × SExpr) := do
  let ctx := { ctx with taBases := taBasesOfNodes lp.nodes ++ ctx.taBases,
                        taSubsts := lp.taSubsts ++ ctx.taSubsts }
  validateBoundaryVerdicts cfg ctx lp
  if lp.notFlg then
    let .cons (.atom (.symbol notS)) (.cons atm .nil) := lp.literal
      | throwError "replayLiteralChain: notFlg literal is not (not atm): {repr lp.literal}"
    unless notS.name == "NOT" do
      throwError "replayLiteralChain: notFlg literal head {notS.name} ≠ not"
    let (chainOpt, finalAtom) ← replayRewrites cfg ctx atm lp.nodes
    let chainOpt ← chainReqEq chainOpt
    -- HIDDEN definitional `implies` unfold: rewrite-atm expands an implies
    -- atom with NO emitted node (only the literal's :RESULT shows it) —
    -- mirror it via the same ground-zero recipe as the preprocess step,
    -- record-directed (only when the plain chain does not already match).
    let (chainOpt, finalAtom) ←
      match finalAtom with
      | .cons (.atom (.symbol impS)) (.cons A (.cons B .nil)) =>
        if impS.name == "IMPLIES" &&
           SExpr.cons (.atom (.symbol notS)) (.cons finalAtom .nil) != lp.result then do
          let expanded : SExpr :=
            .cons (.atom (.symbol { name := "IF" }))
              (.cons A (.cons (.cons (.atom (.symbol { name := "IF" }))
                (.cons B (.cons quoteT (.cons quoteNil .nil))))
                (.cons quoteT .nil)))
          let step ← replayImpliesDef cfg ctx
            (.node ⟨"definition", "IMPLIES", none⟩ finalAtom expanded [] {})
          let combined ← match chainOpt with
            | none => pure step
            | some c => mkAppM ``fuel_chain_eq #[c, step]
          pure (some combined, expanded)
        else pure (chainOpt, finalAtom)
      | _ => pure (chainOpt, finalAtom)
    let finalLit := SExpr.cons (.atom (.symbol notS)) (.cons finalAtom .nil)
    let lifted ← match chainOpt with
      | none => pure none
      | some ch =>
        let ns ← proveNotSpecial notS
        pure (some (mkAppN (mkConst ``evalOpt_congr_unary)
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol notS, reflectSExpr atm,
            reflectSExpr finalAtom, ns, ch]))
    -- when the atom chain ends at a quoted constant, ACL2 folds `(not 'c)` by
    -- execution — implicit in the record (only the literal's :RESULT shows it).
    -- Mirror it: re-run the SAME closed computation (the exec-counterpart
    -- carve-out) and chain `eval (not 'c) ≡ eval 'folded`. The spine's
    -- result check then validates the fold against ACL2's recorded :RESULT.
    match finalAtom with
    | .cons (.atom (.symbol q)) (.cons c .nil) =>
      if q.name == "QUOTE" then
        let foldedV : SExpr := if c == SExpr.nil then SExpr.t else SExpr.nil
        let foldedT : SExpr :=
          .cons (.atom (.symbol { name := "QUOTE" })) (.cons foldedV .nil)
        let pNot ← replayExecGround cfg finalLit foldedV
        let pQ ← mkAppM ``re_val_quote
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr foldedV]
        let step ← mkAppM ``fuel_eq_of_conv
          #[pNot, pQ, ← mkEqRefl (reflectSExpr foldedV)]
        let chain ← match lifted with
          | none => pure step
          | some l => mkAppM ``fuel_chain_eq #[l, step]
        return (some (chain, false), foldedT)
      else
        return (lifted.map ((·, false)), finalLit)
    | _ => return (lifted.map ((·, false)), finalLit)
  else
    replayRewrites cfg ctx lp.literal lp.nodes

/-- Replay a literal that closes to `t`: chain its rewrite nodes, then close with the
    terminal node. The closer is either `equal-self` (reflexivity of `equal`) or an
    `executable-counterpart` ground computation that reduces the rewritten literal
    (a closed term, e.g. `(equal 'nil 'nil)`) to `t` — the same way ACL2 closed it.
    Returns `∃N∀f≥N, eval lp.literal = some t`. -/
def replayLiteral (cfg : ReplayConfig) (ctx : ReplayCtx) (lp : LiteralProof) : MetaM Expr := do
  if lp.notFlg then
    -- A `:NOT-FLG T` closer `(not atm)` reaches `t` because ACL2 rewrote the
    -- atom to a nil constant and then ran `(not <nil-const>)` implicitly (no
    -- separate closer node — the negation-of-false is recorded only as the
    -- literal's `:RESULT 'T`). Replay it the same way: chain the atom and lift
    -- through `not` exactly as the non-closing notFlg path does
    -- (`replayLiteralChain`), then close the resulting ground `(not finalAtom)`
    -- by re-running the SAME computation (`replayExecGround`, the
    -- exec-counterpart carve-out). Hard-fails cleanly if the lifted literal is
    -- not ground or does not reduce to `t` — i.e. if ACL2 closed it some other
    -- way (a new, named frontier, not a guess).
    let (chainOpt, finalLit) ← replayLiteralChain cfg ctx lp
    let chainOpt ← chainReqEq chainOpt
    let closeProof ← replayExecGround cfg finalLit SExpr.t
    match chainOpt with
    | none => return closeProof
    | some ch => return (← mkAppM ``fuel_chain_eq #[ch, closeProof])
  -- non-notFlg closer: the FULL chain — equal-self, executable-counterpart,
  -- with-lemma-to-'t, clause-context-resolution reports are all ordinary
  -- node recipes now — must reduce the literal to `(quote t)`; close by the
  -- chain + the quote's evaluation.
  let ctx := { ctx with taBases := taBasesOfNodes lp.nodes ++ ctx.taBases,
                        taSubsts := lp.taSubsts ++ ctx.taSubsts }
  validateBoundaryVerdicts cfg ctx lp
  if lp.nodes.isEmpty then
    throwError "replayLiteral: literal {repr lp.literal} has no proof nodes"
  let (chainOpt, finalT) ← replayRewrites cfg ctx lp.literal lp.nodes
  let chainOpt ← chainReqEq chainOpt
  unless finalT == quoteT do
    throwError "replayLiteral: closing literal's chain reached {repr finalT}, \
                not (quote t) (frontier)"
  let some ch := chainOpt
    | throwError "replayLiteral: closing literal {repr lp.literal} chained to \
                  't with no effective steps"
  mkAppM ``fuel_conv_of_eq #[ch, ← quoteTFact cfg]

/-- The clause's literal items in order, with their 1-based indices, descending
    into case branches (a branch's items continue the same clause's literals). -/
partial def flattenLiterals : List ClauseItem → List (Nat × LiteralProof)
  | [] => []
  | .literal lp :: rest => (lp.index, lp) :: flattenLiterals rest
  | .step _ :: rest => flattenLiterals rest
  | .clausify _ :: rest => flattenLiterals rest
  | .useHint _ _ _ _ :: rest => flattenLiterals rest
  | .fcDerivations _ :: rest => flattenLiterals rest
  | .complementClose _ :: rest => flattenLiterals rest
  | .taSubst .. :: rest => flattenLiterals rest
  | .branch _ items :: rest => flattenLiterals items ++ flattenLiterals rest

/-- A clause-context falsity demand: either an exact clause-literal TERM, or
    a clause-literal INDEX (solidify nodes name their source literal by index,
    not by term). -/
inductive ContextDemand where
  | term (t : SExpr)
  | litIdx (k : Nat)
  /-- The clause's equality literals CONNECTED to `{a, b}` (the solidify
      node's `:EQUIV-TERM` sides) are all demanded — the transitive
      type-alist equivalence needs the whole component in scope. -/
  | equivClass (a b : SExpr)
  /-- A later literal of shape `(NOT (TRUE-LISTP (CONS a w)))` for the
      recognizer's inner term `w` (any car `a`): ACL2's type-set closure
      justifies `(TRUE-LISTP w) ⇒ 'T` from that literal's falsity —
      `trueListp (cons a w)` reduces to `trueListp w` (sorting-completion-2
      Class A, ORDERED-PERMS Subgoal *1/7'5' literal 1 after the
      branch-substitutions). Pattern demand — the car is not knowable at
      demand-collection time. -/
  | tlpCons (w : SExpr)
  deriving BEq

/-- Every IF-test subterm of `t`, recursively (never descending QUOTE):
    candidates for clause-context demands — an if-test the rewriter resolved
    against the type-alist with NO emitted node (the reconciled constant-test
    class in `replayRewritesWith`) consumes a clause literal's falsity, and
    the test appears as an if-test inside the chain's own lhs/rhs terms
    (G2 rung 2: qsort's PERM-IMPLIES-EQUAL-ALL-REL-2 opens REL's FN-dispatch
    body whose tests are the clause's own `(EQUAL FN 'LT/'LTE)` literals). -/
partial def ifTestsOf : SExpr → List SExpr
  | .cons (.atom (.symbol f)) args =>
    if f.name == "QUOTE" then []
    else
      let rec argsOf : SExpr → List SExpr
        | .cons a rest => ifTestsOf a ++ argsOf rest
        | _ => []
      (if f.name == "IF" then
         match args with
         | .cons t _ =>
           match t with
           | .cons (.atom (.symbol q)) _ =>
             if q.name == "QUOTE" then [] else [t]
           | .atom _ => [t]
           | _ => [t]
         | _ => []
       else []) ++ argsOf args
  | _ => []

/-- A `.term` falsity demand plus its EQUAL-flip (the hoist site matches
    clause-literal terms exactly; type-alist lookups go through `equal`'s
    commutativity, so both orientations are demanded). -/
def ifTestDemandsOf (t : SExpr) : List ContextDemand :=
  [ContextDemand.term t] ++
  (match t with
   | .cons (.atom (.symbol es)) (.cons u (.cons v .nil)) =>
     if es.name == "EQUAL" then
       [ContextDemand.term
         (.cons (.atom (.symbol es)) (.cons v (.cons u .nil)))]
     else []
   | _ => [])

/-- Every `(CDR u)` subterm of `t` (never descending QUOTE) — the CONSP
    closure's ingredient scan. -/
partial def cdrSubterms : SExpr → List SExpr
  | t@(.cons (.atom (.symbol f)) args) =>
    if f.name == "QUOTE" then []
    else
      let rec argsOf : SExpr → List SExpr
        | .cons a rest => cdrSubterms a ++ argsOf rest
        | _ => []
      (if f.name == "CDR" then [t] else []) ++ argsOf args
  | _ => []

/-- IF-marker test ingredient demands (the PCE-class reconciliation):
    a TRUE-sense marker's `(TRUE-LISTP (CDR u))` test resolves by the
    trueListp-CDR closure, whose ingredient `(NOT (TRUE-LISTP u))` may
    sit LATER in the clause — demand it (skipped harmlessly when it is
    no clause literal). -/
def ifMarkerDemands : SExpr × Bool × SExpr → List ContextDemand
  | (t, sense, _) =>
    if sense then
      match t with
      | .cons (.atom (.symbol rs)) (.cons w .nil) =>
        if rs.name == "TRUE-LISTP" then
          (match w with
           | .cons (.atom (.symbol fs)) (.cons u .nil) =>
             if fs.name == "CDR" then
               [ContextDemand.term (.cons
                 (.atom (.symbol { name := "NOT" }))
                 (.cons (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                   (.cons u .nil)) .nil))]
             else []
           | _ => [])
        else []
      | _ => []
    else []

/-- The CLAUSE-CONTEXT falsity demands of a literal's chain, as the exact
    clause-literal terms/indices whose falsity the chain's nodes consume
    (ACL2 rewrites literal i under the falsity of ALL other clause literals):
    - a silent hyp-relief marker for hyp `h` demands `(not h)`;
    - a `type-alist` nil-verdict node `l ⇒ 'nil` demands `l` itself;
    - a `type-alist` truthy node `l ⇒ 't` demands `(not l)`;
    - a solidify node with a `.literal k` equiv source demands literal `k`
      (S1 2026-07-23 — the IH equation consumed from a LATER literal);
    - every IF-test subterm of a node's lhs/rhs (and its EQUAL-flip) — the
      reconciled constant-test class resolves such a test from the clause
      context with no emitted node (G2 rung 2). A demand that is no later
      clause literal is skipped harmlessly at the hoist site. -/
partial def collectContextDemands (fcDerivs : List SExpr := []) :
    ProofNode → List ContextDemand
  | .node ⟨rty, _, _⟩ l rh children prov =>
    let notOf : SExpr → SExpr := fun t =>
      .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
    let ifTestDemands : List ContextDemand :=
      (ifTestsOf l ++ ifTestsOf rh).flatMap ifTestDemandsOf
    (if rty == "hyp-relief" then
       [ContextDemand.term (notOf l)] ++
       -- a (NOT atom) hyp's clause-context source is the ATOM literal — its
       -- falsity IS the hyp's truth (the complement orientation the marker
       -- consumer's route already reads; DEFAULT-CDR's (NOT (CONSP (CDR X)))
       -- hyp at HOW-MANY-EVENS-AND-ODDS, S1 2026-07-23). Demand the atom too
       -- so the walk hoists it when it sits later in the clause; a demand
       -- that is no clause literal is skipped harmlessly at the hoist site.
       (match l with
        | .cons (.atom (.symbol ns)) (.cons atm .nil) =>
          if ns.name == "NOT" then
            [ContextDemand.term atm] ++
            -- upstream `assoc-equiv` (type-set-b.lisp) consults the
            -- type-alist under BOTH argument orders of an equivalence
            -- relation — demand the COMMUTED EQUAL literal too (final
            -- close-out: Subgoal *1/2.1's later literal (EQUAL B (CAR X))
            -- relieves (NOT (EQUAL (CAR X) B)))
            (match atm with
             | .cons (.atom (.symbol es)) (.cons u (.cons v .nil)) =>
               if es.name == "EQUAL" then
                 [ContextDemand.term (.cons (.atom (.symbol es))
                   (.cons v (.cons u .nil)))]
               else []
             | _ => [])
          else []
        | _ => []) ++
       -- an FC-DERIVED relief consumes the COMMUTED lexorder
       -- application's falsity — demand that literal too so the walk
       -- hoists it when it sits later in the clause (HOW-MANY-FILTER-1).
       -- Anchors, both emitted channels (final-closeout item C): the
       -- marker's :TA-RUNES, or a clause-level (:FC-DERIVATIONS …)
       -- record whose :CONCL is this hyp (HOW-MANY-SMALLER-BNEXT's
       -- markers carry empty :TA-RUNES)
       (match l with
        | .cons (.atom (.symbol ls)) (.cons u (.cons v .nil)) =>
          if ls.name == "LEXORDER" &&
              (prov.taRunes.any
                (fun r => r.ty == "forward-chaining" && r.name == "LEXORDER-TOTAL")
               || fcDerivs.any (fun d =>
                    fcDerivField? d "CONCL" == some l &&
                    (match fcDerivField? d "RUNE" with
                     | some (.cons (.atom (.keyword cls))
                         (.cons (.atom (.symbol nm)) .nil)) =>
                       cls == "FORWARD-CHAINING" && nm.name == "LEXORDER-TOTAL"
                     | _ => false)))
          then [ContextDemand.term (.cons (.atom (.symbol ls)) (.cons v (.cons u .nil)))]
          else []
        | _ => [])
     else if rty == "type-alist" then
       if rh == quoteNil then
         [ContextDemand.term l] ++
         -- the nil-verdict closure's TRUE-LISTP∧¬CONSP ingredient: the
         -- truthy true-listp fact may sit in a LATER literal
         -- (ORDERED-PERMS *1/7'5' literal 5: `B ⇒ 'NIL` from segment
         -- (CONSP B)-false + later literal 9 (NOT (TRUE-LISTP B)))
         [ContextDemand.term (notOf
           (.cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons l .nil)))]
       else if rh == quoteT then [ContextDemand.term (notOf l)]
       else []
     else if rty == "rewriting-equivalence" then
       -- a solidify node consumes its source literal's falsity BY INDEX; a
       -- transitive equivalence (S1 2026-07-23) additionally needs the whole
       -- connected component of its :EQUIV-TERM sides in scope
       (match prov.equivSource with
        | some (.literal k) => [ContextDemand.litIdx k]
        | _ => []) ++
       (match prov.equivTerm with
        | some (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) =>
          if es.name == "EQUAL" then [ContextDemand.equivClass a b] else []
        | _ => [])
     else if prov.origin == "recognizer/true" then
       -- a recognizer resolved TRUE from the clause context (a later
       -- literal is its negation — EQUAL-CONS Subgoal 4); hoisting is a
       -- no-op when the fact is derivable another way
       [ContextDemand.term (notOf l)] ++
       -- the TRUE-LISTP type-set-closure justifications: a later
       -- `(NOT (TRUE-LISTP (CONS a w)))` literal (see `tlpCons`), and — for
       -- the (TRUE-LISTP (CDR u)) shape — the closure arm's DIRECT
       -- ingredient `(NOT (TRUE-LISTP u))` (ORDERED-PERMS: literal 9's
       -- (NOT (TRUE-LISTP B)) justifies (TRUE-LISTP (CDR B)) ⇒ 'T)
       (match l with
        | .cons (.atom (.symbol rs)) (.cons w .nil) =>
          if rs.name == "TRUE-LISTP" then
            [ContextDemand.tlpCons w] ++
            (match w with
             | .cons (.atom (.symbol fs)) (.cons u .nil) =>
               if fs.name == "CDR" then
                 [ContextDemand.term (notOf
                   (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                     (.cons u .nil)))]
               else []
             | _ => []) ++
            -- tpthm ingredients (the :CLASSES consumer, resurrected at
            -- the final close-out): a THEOREM-classed TP rule's hyp
            -- instance is typically the recognizer at an ARGUMENT of the
            -- inner application ((TRUE-LISTP (RM E X))'s hyp is
            -- (TRUE-LISTP X)) — demand each. GATED on the node citing a
            -- :TYPE-PRESCRIPTION rune (tpthm audit F9 — cuts the
            -- recognizer/true blast radius to the citing nodes) and
            -- QUOTE-guarded (F10). A demand is hoisted only if its value
            -- constructs in scope; over-approximation is bounded by both.
            (if prov.runes.any (·.ty == "type-prescription") then
              match w with
              | .cons (.atom (.symbol wf)) argsS =>
                if wf.name == "QUOTE" then []
                else (argsS.toList?.getD []).map fun a =>
                  ContextDemand.term (notOf
                    (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                      (.cons a .nil)))
              | _ => []
             else [])
          else if rs.name == "CONSP" then
            -- the CONSP-closure ingredients (ORDERED-PERMS *1/2.2 and the
            -- IF-split shapes): for EVERY (CDR u) subterm of w, the truthy
            -- (CDR u) / (TRUE-LISTP u) / (TRUE-LISTP (CDR u)) literals
            ((cdrSubterms w).flatMap fun cu =>
              match cu with
              | .cons _ (.cons u .nil) =>
                [ContextDemand.term (notOf cu),
                 ContextDemand.term (notOf
                   (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                     (.cons u .nil))),
                 ContextDemand.term (notOf
                   (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                     (.cons cu .nil)))]
              | _ => []) ++
            -- the conspEvidence? truthy-(CDR w) route on the inner term
            -- itself ((CONSP B) with a later (NOT (CDR B)) literal), and the
            -- general truthy+proper-list route's TRUE-LISTP ingredient
            [ContextDemand.term (notOf
              (.cons (.atom (.symbol { name := "CDR" })) (.cons w .nil))),
             ContextDemand.term (notOf
              (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                (.cons w .nil)))]
          else []
        | _ => [])
     else if prov.origin == "recognizer/false" then [ContextDemand.term l]
     else []) ++ ifTestDemands ++ children.flatMap (collectContextDemands fcDerivs)

/-- WORLD-AWARE demand augmentation: a DEFINITION node's unfolded body (read
    from the world's defun, formals substituted by the recorded call args)
    contributes its if-tests as falsity demands. The recorded rhs shows
    ACL2's POST-resolution view (a context-resolved test appears there as
    the quoted verdict), so a test the reconciled constant-test class must
    resolve appears ONLY in the world-side body — invisible to
    `collectContextDemands` (G2 rung 2: REL's FN-dispatch body whose tests
    are the clause's own `(EQUAL FN 'LT/'LTE)` literals). -/
partial def collectDefBodyDemands (cfg : ReplayConfig) : ProofNode → List ContextDemand
  | .node ⟨rty, _, _⟩ l _ children _ =>
    (if rty == "definition" then
       match l with
       | .cons (.atom (.symbol fn)) args =>
         match cfg.worldVal.defs.get? fn, args.toList? with
         | some (formals, body), some argL =>
           if formals.length == argL.length then
             (ifTestsOf (ACL2.Replay.substTerm formals argL body)).flatMap
               ifTestDemandsOf
           else []
         | _, _ => []
       | _ => []
     else []) ++ children.flatMap (collectDefBodyDemands cfg)

/-- `EvTrue (disjoin lits)` from the TRUTH of the k-th literal (0-based):
    descend the lazy if-spine by value splits — an earlier literal's truth
    closes the clause anyway; at `k` the nil case is refuted by `hTrue`
    (`v(litK) ≠ nil`). -/
partial def evtrueOfLitTrue (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lits : List SExpr) (k : Nat) (litK : SExpr) (hTrue : Expr) : MetaM Expr := do
  match lits with
  | [] => throwError "evtrueOfLitTrue: index beyond the clause"
  | [l] =>
    unless k == 0 && l == litK do
      throwError "evtrueOfLitTrue: index/literal mismatch at the last literal"
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx l
    let pL ← ctxValProof cfg ctx l
    mkAppM ``evtrue_of_conv_ne_nil #[pL, hTrue]
  | l :: rest =>
    -- pin the literal's user-fn opaques on demand (callers hold facts about
    -- other literals; this walk may be the first to touch this one)
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx l
    let vL ← ctxValExpr cfg ctx l
    let pL ← ctxValProof cfg ctx l
    let restTerm := disjoinTerm rest
    let nilC := mkConst ``SExpr.nil
    let hthen ← withLocalDeclD `h (← mkAppM ``Ne #[vL, nilC]) fun h => do
      let p ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
      let _ := h
      mkLambdaFVars #[h] p
    let helse ← withLocalDeclD `h (← mkEq vL nilC) fun h => do
      let p ←
        if k == 0 then do
          unless l == litK do
            throwError "evtrueOfLitTrue: literal at k ≠ the true literal"
          let goalTy ← mkAppM ``EvTrue
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr restTerm]
          mkAppOptM ``absurd #[none, some goalTy, some h, some hTrue]
        else
          evtrueOfLitTrue cfg ctx rest (k - 1) litK hTrue
      mkLambdaFVars #[h] p
    mkAppM ``evtrue_dp_if_split
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr l, reflectSExpr quoteT,
        reflectSExpr restTerm, vL, pL, hthen, helse]

/-- Extend a proved disjunction PREFIX by dropped tail literals: from
    `EvTrue ⟦disjoin pre⟧` to `EvTrue ⟦disjoin (pre ++ dropped)⟧`, by
    byCases down the prefix spine — a truthy literal closes the full
    disjunction at its own position (`evtrueOfLitTrue`); all-nil descends
    and rebuilds each frame (`re_if_false`). Needs NO assumption about
    the dropped literals (monotone weakening). Consumer: the whole-clause
    discharge PREFIX arm — ACL2's verdict node covers the clause minus
    literals its add-literal dropped as trivially nil
    (ORDEREDP-WHEN-BNEXT-CONSTANT *1/4.1.3''s `(NOT (EQUAL X1 X1))`). -/
partial def evtrueExtendTail (cfg : ReplayConfig) (ctx : ReplayCtx)
    (pre dropped : List SExpr) (p : Expr) : MetaM Expr := do
  match pre with
  | [] => throwError "evtrueExtendTail: empty prefix"
  | [l] => do
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx l
    let pL ← ctxValProof cfg ctx l
    let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[p, pL]
    evtrueOfLitTrue cfg ctx (l :: dropped) 0 l hNe
  | l :: rest => do
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx l
    let vL ← ctxValExpr cfg ctx l
    let pL ← ctxValProof cfg ctx l
    let nilC := mkConst ``SExpr.nil
    let fullLits := pre ++ dropped
    let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
      mkLambdaFVars #[hNe] (← evtrueOfLitTrue cfg ctx fullLits 0 l hNe)
    let negL ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
      let hcNil ← mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr l, vL, nilC, pL, hNil]
      -- collapse l's frame in p (p : EvTrue ⟦IF l 'T (disjoin rest)⟧)
      let pRest ← mkAppM ``evtrue_tail_of_if_head_nil #[hcNil, p]
      let pFull ← evtrueExtendTail cfg ctx rest dropped pRest
      -- rebuild the frame over the EXTENDED tail
      let restFull := disjoinTerm (rest ++ dropped)
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx restFull
      let vRest ← ctxValExpr cfg ctx restFull
      let hRest ← ctxValProof cfg ctx restFull
      let hIf ← mkAppM ``re_if_false
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr l, reflectSExpr quoteT,
          reflectSExpr restFull, vRest, hcNil, hRest]
      mkLambdaFVars #[hNil] (← mkAppM ``evtrue_of_fuel_eq #[hIf, pFull])
    (try mkAppM ``Classical.byCases #[negL, posL]
      catch e => throwError "byCases compose failed (extend-tail):\n\
          {e.toMessageData}")

/-- The spine's SKIPPED-literal falsity collapse: given `hNil` (`v(clit) =
    nil`), fold the head literal's if-frame out of the disjunction
    (`re_if_false`) and re-enter the walk via `recur` on the renumbered
    tail. Shared by the fact-backed skip and the add-literal dedup arm
    (CoreSpine's walk-mismatch site). -/
def litSkipCollapse (cfg : ReplayConfig) (ctx : ReplayCtx)
    (restLits : List (Nat × SExpr)) (clit : SExpr) (hNil : Expr)
    (recur : ReplayCtx → List (Nat × SExpr) → MetaM Expr) : MetaM Expr := do
  let restTerm := disjoinTerm (restLits.map (·.2))
  let vC ← ctxValExpr cfg ctx clit
  let pC ← ctxValProof cfg ctx clit
  let hcNil ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr clit, vC,
      mkConst ``SExpr.nil, pC, hNil]
  let hRest ← ctxValProof cfg ctx restTerm
  let vRest ← ctxValExpr cfg ctx restTerm
  let hIf ← mkAppM ``re_if_false
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr clit, reflectSExpr quoteT,
      reflectSExpr restTerm, vRest, hcNil, hRest]
  let p ← recur ctx (restLits.map fun (i, l) => (i - 1, l))
  mkAppM ``evtrue_of_fuel_eq #[hIf, p]

/-- add-literal DEDUP skip (the final close-out's known class,
    HOW-MANY-SMALLER-BNEXT *1/4.5): upstream
    `subst-equiv-and-maybe-delete-lit` (simplify.lisp) rebuilds the
    substituted clause through `add-literal`, whose `member-term` check
    drops a literal already present in the rebuilt TAIL — of a duplicated
    literal only the LAST occurrence survives, and the recorded item walk
    skips the earlier one. The recorded items disambiguate the drop (it
    fires only when the walk item disagrees at the head AND the literal
    recurs later); a spurious fire misaligns the walk and hard-fails
    downstream — never a wrong proof. byCases on the literal's value:
    truthy closes the whole disjunction at its head position; falsity is
    the shared `litSkipCollapse`.

    HELD UNDER EXPIRY (audit 2026-08-09, inside D1): this infers the drop
    from the clause shape, and its upstream twin — add-literal's
    member-COMPLEMENT-term branch, 35 lines above the member-term drop in
    the same `cond` — was user-ruled (2026-08-06) to require an EMISSION
    (`emit/complement-close`) precisely because inference-from-absence was
    judged insufficient there. The matching `emit/dedup-drop` record at
    simplify.lisp's member-term branch is QUEUED for the next fork batch's
    item-by-item review; when it lands this arm becomes a read-off. Do not
    extend the inference. -/
def dedupSkipClose (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (clauseLits restLits : List (Nat × SExpr)) (clit : SExpr)
    (recur : ReplayCtx → List (Nat × SExpr) → MetaM Expr) : MetaM Expr := do
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx clit
  let vC ← ctxValExpr cfg ctx clit
  let nilC := mkConst ``SExpr.nil
  let negL ← withLocalDeclD `hnil (← mkEq vC nilC) fun hNil => do
    mkLambdaFVars #[hNil] (← litSkipCollapse cfg ctx restLits clit hNil recur)
  let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vC, nilC]) fun hNe => do
    mkLambdaFVars #[hNe]
      (← evtrueOfLitTrue cfg ctx (clauseLits.map (·.2)) 0 clit hNe)
  (try mkAppM ``Classical.byCases #[negL, posL]
    catch e => throwError "byCases compose failed (add-literal dedup) \
        at {idStr}:\n{e.toMessageData}")

/-- Close `EvTrue (disjoin lits)` for a TAUTOLOGOUS clause — one containing a
    complementary pair `L` / `(NOT L)`, or the COMMUTED-EQUAL pair
    `(EQUAL a b)` / `(NOT (EQUAL b a))` (ACL2's type-set treats the commuted
    equality as the same type-alist entry — p7's SAME-LN sym conjunct) — by
    cases on the negated literal's atom value. ACL2 recognizes such a clause
    as *t* with no recorded steps (add-literal and
    remove-trivial-equivalences drop it as proved silently), so the mirror is
    the pair's excluded middle. Fails loudly when no pair exists. `who` names
    the calling site in the error. -/
def tautClauseClose (cfg : ReplayConfig) (ctx : ReplayCtx) (lits : List SExpr)
    (who : String) : MetaM Expr := do
  let notOf (t : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
  let commuteEq? : SExpr → Option SExpr := fun t =>
    match t with
    | .cons (.atom (.symbol eqS)) (.cons a (.cons b .nil)) =>
      if eqS.name == "EQUAL" then
        some (.cons (.atom (.symbol eqS)) (.cons b (.cons a .nil)))
      else none
    | _ => none
  -- (positive index, negated index, positive atom, negated atom): the
  -- negated literal is (NOT negAtom) with negAtom == atom (direct) or the
  -- commuted equality
  let pair? : Option (Nat × Nat × SExpr × SExpr) :=
    lits.zipIdx.findSome? fun (l, i) =>
      lits.zipIdx.findSome? fun (l2, j) =>
        if l2 == notOf l then some (i, j, l, l)
        else match commuteEq? l with
          | some lC => if l2 == notOf lC then some (i, j, l, lC) else none
          | none => none
  let some (iPos, iNeg, atom, negAtom) := pair?
    | throwError "{who}: tautology close — no complementary literal pair in \
        {repr lits} (frontier)"
  let ctxT ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm lits)
  let vN ← ctxValExpr cfg ctxT negAtom
  let nilC := mkConst ``SExpr.nil
  let tNeNil ← proveByDecide
    (← mkAppM ``Ne #[mkConst ``SExpr.t, nilC]) "t ≠ nil"
  let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vN, nilC]) fun hNe => do
    let p ←
      if negAtom == atom then
        evtrueOfLitTrue cfg ctxT lits iPos atom hNe
      else do
        -- commuted pair: v(EQUAL b a) ≠ nil gives vb = va, so
        -- v(EQUAL a b) = Logic.equal va vb = Logic.equal va va = t
        unless vN.isAppOfArity ``Logic.equal 2 do
          throwError "{who}: commuted-equal value of {repr negAtom} is not \
              (Logic.equal _ _) (internal)"
        let vb := vN.appFn!.appArg!
        let va := vN.appArg!
        let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hNe]  -- vb = va
        let vA ← ctxValExpr cfg ctxT atom  -- Logic.equal va vb
        unless vA.isAppOfArity ``Logic.equal 2 do
          throwError "{who}: value of {repr atom} is not (Logic.equal _ _) \
              (internal)"
        let fL ← withLocalDeclD `z (mkConst ``SExpr) fun zV => do
          mkLambdaFVars #[zV] (← mkAppM ``Logic.equal #[va, zV])
        -- vA = Logic.equal va vb = Logic.equal va va (by vb = va) = t
        let hStep ← mkAppM ``congrArg #[fL, hEq]  -- equal va vb = equal va va
        let hSelf ← mkAppM ``Logic.equal_self #[va]
        let hT ← mkAppM ``Eq.trans #[hStep, hSelf]  -- vA = t
        let hATrue ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
        let _ := vb
        evtrueOfLitTrue cfg ctxT lits iPos atom hATrue
    mkLambdaFVars #[hNe] p
  let negL ← withLocalDeclD `hnil (← mkEq vN nilC) fun hNil => do
    let hT ← mkAppM ``logic_not_t_of_nil #[hNil]
    let hTrue ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
    mkLambdaFVars #[hNil]
      (← evtrueOfLitTrue cfg ctxT lits iNeg (notOf negAtom) hTrue)
  mkAppM ``Classical.byCases #[negL, posL]

end ACL2.Replay.Driver
