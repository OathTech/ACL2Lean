/-
  Driver/NodeCore/Node — positional slice of the former NodeCore
  monolith (perf arc 3a, 2026-08-07): MOVE-ONLY; the boundaries are the
  file's own def-before-use order, so the import chain IS the
  dependency order.
-/
import ACL2Lean.Replay.Driver.NodeCore.Recognizer

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay one rewrite node to its eval-equality `∃N∀f≥N, eval lhs = eval rhs`, by
    applying that rune's recipe. (equal-self is the literal closer, handled in
    `replayLiteral`, not here.) Unhandled runes hard-fail. -/
partial def replayNodeWith (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    : MetaM Expr := do
  let rune := runeOf n
  let (rty, rname) := (rune.ty, rune.name)
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children prov := n
  -- a non-EQUAL rule application is IFF/user-equivalence rewriting — it must
  -- route through the R-parameterized judgment, not the eval-equality recipes.
  -- EXEMPT the COMPOSITE node classes (definition unfolds and lambda betas,
  -- S2b 2026-07-25): their :EQUIV is the geneqv-derived strength of ACL2's
  -- CLAIM for the whole lhs⇒rhs composite (honest emission, option B), but
  -- the replay never uses that label — it composes the recorded child chain
  -- and hard-checks it reaches the recorded rhs, so what it proves is the
  -- kernel-checked EQUALITY of its own composition (stronger than an iff
  -- claim is sound; a genuinely-iff CHILD still gates at its own node, and a
  -- composite whose rhs needs an unrecorded iff-only normalization fails the
  -- rhs check — fail-closed either way).
  unless prov.equiv == "equal" || rty == "definition" || rty == "lambda-body" do
    throwError "replayNode: rune ({rty}, {rname}) applied under equivalence \
                {prov.equiv} — R-parameterized recipe pending (G1 frontier)"
  match rty, rname with
  | "rewriting-equivalence", _ =>
    -- SOLIDIFY: the rewrite `lhs ⇒ rhs` is justified by a clause hypothesis — the
    -- (post-rewrite) literal named by `equivSource`, whose falsity in the spine
    -- branch IS the equation. Value-level: the literal `(not (equal A B))` being
    -- nil gives `vA = vB`; the node's sides converge to those values.
    let some src := prov.equivSource
      | throwError "solidify: node has no equivSource (unlinked rewriting-equivalence)"
    let idx ← match src with
      | .literal idx => pure idx
      | .typeSetDerived =>
        -- J6 → S1 (MDD-ratified 2026-07-23): the type-set believed the
        -- equivalence under the clause context (verdict-class, no recorded
        -- derivation — ACL2 has nothing more to emit). When the equation
        -- lies in the context's equivalence CLOSURE, the closure chain IS
        -- the derivation — the same deterministic route as the transitive
        -- literal case. Verdicts beyond the equation closure (genuine
        -- type-set reasoning, e.g. both sides nil under ¬consp) remain the
        -- named J6 frontier.
        let eqs := inScopeEquations ctx
        let some chain := eqChain? eqs lhs rhs
          | throwFrontier m!"solidify: type-set-derived equivalence \
              {repr (prov.equivTerm.getD .nil)} — not in the clause context's \
              equation closure ({eqs.length} in-scope equation(s)); \
              value-level type-set discharge not implemented (J6 replay \
              frontier)"
        let some valueEq ← composeEqChain cfg ctx chain
          | throwError "solidify: internal — empty equation chain for \
                        type-set-derived {repr lhs} ⇒ {repr rhs}"
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx rhs
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
      | .branchTest =>
        -- the equivalence IS an enclosing unresolved-if's test, assumed TRUE
        -- in the then-branch the node's path descends through (ACL2's
        -- assume-true-false) — the if-finish recipe put the test's truth in
        -- scope as a branch fact.
        let some eqTerm := prov.equivTerm
          | throwError "solidify: branchTest node has no :EQUIV-TERM"
        let some (_, _, sign, hFact) :=
            ctx.branchFacts.find? (fun (t, _, _, _) => t == eqTerm)
          | throwError "solidify: no in-scope branch fact for test \
                        {repr eqTerm} (frontier)"
        unless sign do
          throwError "solidify: branch fact for {repr eqTerm} is the FALSE \
                      branch — equation unavailable (frontier)"
        let .cons (.atom (.symbol eqS)) (.cons ta (.cons tb .nil)) := eqTerm
          | throwError "solidify: branch test {repr eqTerm} is not (equal A B)"
        unless eqS.name == "EQUAL" do
          throwError "solidify: branch test head {eqS.name} ≠ equal (frontier)"
        -- hFact : (Logic.equal va vb) ≠ nil — decode to va = vb
        let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hFact]
        let (flip : Bool) ←
          if lhs == tb && rhs == ta then pure true
          else if lhs == ta && rhs == tb then pure false
          else throwError "solidify: node sides {repr lhs} ⇒ {repr rhs} do not \
                           match the branch test ({repr ta} = {repr tb})"
        let valueEq ← if flip then mkAppM ``Eq.symm #[hEq] else pure hEq
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx rhs
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
      | .segment =>
        -- the equivalence IS an enclosing clausify-branch SEGMENT hypothesis
        -- (ACL2's :CONTEXT-SUBST): the segment literal `(not (equal A B))`,
        -- assumed false in the branch, gives the equation. The branch-split
        -- composer put its falsity in scope as a segFact; match the node's
        -- equiv term against it modulo `equal`'s argument order.
        let some eqTerm := prov.equivTerm
          | throwError "solidify: segment node has no :EQUIV-TERM"
        let .cons (.atom (.symbol eqS)) (.cons ta (.cons tb .nil)) := eqTerm
          | throwError "solidify: segment equiv {repr eqTerm} is not (equal A B)"
        unless eqS.name == "EQUAL" do
          throwError "solidify: segment equiv head {eqS.name} ≠ equal (frontier)"
        let mkNotEq (x y : SExpr) : SExpr :=
          .cons (.atom (.symbol { name := "NOT" }))
            (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
              (.cons x (.cons y .nil))) .nil)
        -- the segment literal, in either argument order
        let (segLit, (flipArgs : Bool)) ←
          match ctx.segFacts.find? (fun (st, _) => st == mkNotEq ta tb) with
          | some f => pure (f, false)
          | none =>
            match ctx.segFacts.find? (fun (st, _) => st == mkNotEq tb ta) with
            | some f => pure (f, true)
            | none =>
              throwError "solidify: no in-scope segment fact for \
                          (not {repr eqTerm}) (frontier)"
        let (a', b') := if flipArgs then (tb, ta) else (ta, tb)
        let va ← ctxValExpr cfg ctx a'
        let vb ← ctxValExpr cfg ctx b'
        -- segLit.2 : Logic.not (Logic.equal va vb) = nil → va = vb
        let hEq0 ← mkAppM ``logic_not_equal_nil_eq #[va, vb, segLit.2]
        -- orient to (ta = tb), then to the node's lhs ⇒ rhs
        let hEq ← if flipArgs then mkAppM ``Eq.symm #[hEq0] else pure hEq0
        let (flip : Bool) ←
          if lhs == tb && rhs == ta then pure true
          else if lhs == ta && rhs == tb then pure false
          else throwError "solidify: node sides {repr lhs} ⇒ {repr rhs} do not \
                           match the segment equation ({repr ta} = {repr tb})"
        let valueEq ← if flip then mkAppM ``Eq.symm #[hEq] else pure hEq
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx rhs
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
    let some (litTerm0, hNil0) := ctx.litFact? idx
      | throwError "solidify: no spine fact for literal {idx} (clause context missing)"
    -- when the source literal's recorded form is NOT a bare (not (equal A B))
    -- — e.g. an implies-expanded IH whose equation was clausified out — the
    -- equation reaches the chain as a BRANCH SEGMENT fact: fall back to the
    -- segFacts by the node's equiv term (either argument order)
    let (litTerm, hNil) ←
      match litTerm0 with
      | .cons (.atom (.symbol ns))
          (.cons (.cons (.atom (.symbol es)) (.cons _ (.cons _ .nil))) .nil) =>
        if ns.name == "NOT" && es.name == "EQUAL" then pure (litTerm0, hNil0)
        else pure (litTerm0, hNil0)
      | _ =>
        match prov.equivTerm with
        | some (.cons (.atom (.symbol eqS')) (.cons a' (.cons b' .nil))) => do
          unless eqS'.name == "EQUAL" do
            throwError "solidify: source literal is not (not (equal A B)) and \
                        equiv {repr prov.equivTerm} is not an equal equation: \
                        {repr litTerm0}"
          let mk (x y : SExpr) : SExpr :=
            .cons (.atom (.symbol { name := "NOT" }))
              (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
                (.cons x (.cons y .nil))) .nil)
          match ctx.segFacts.find? (fun (st, _) => st == mk a' b') with
          | some (st, h) => pure (st, h)
          | none =>
            match ctx.segFacts.find? (fun (st, _) => st == mk b' a') with
            | some (st, h) => pure (st, h)
            | none =>
              throwError "solidify: source literal is not (not (equal A B)) \
                          and no segment fact matches {repr prov.equivTerm}: \
                          {repr litTerm0}"
        | _ =>
          throwError "solidify: source literal is not (not (equal A B)): \
                      {repr litTerm0}"
    let .cons (.atom (.symbol notS))
        (.cons (.cons (.atom (.symbol eqS)) (.cons ta (.cons tb .nil))) .nil) := litTerm
      | throwError "solidify: source literal is not (not (equal A B)): {repr litTerm}"
    unless notS.name == "NOT" && eqS.name == "EQUAL" do
      throwError "solidify: source literal heads {notS.name}/{eqS.name}"
    -- orientation: the node rewrites one side of the equation to the other
    if lhs == ta && rhs == tb || lhs == tb && rhs == ta then
      let flip := lhs == tb && rhs == ta
      let va ← ctxValExpr cfg ctx ta
      let vb ← ctxValExpr cfg ctx tb
      -- hNil : Logic.not (Logic.equal va vb) = nil  (the spine built the literal's
      -- value with the same builder, so this is its exact type)
      let hEq ← mkAppM ``logic_not_equal_nil_eq #[va, vb, hNil]   -- va = vb
      let valueEq ← if flip then mkAppM ``Eq.symm #[hEq] else pure hEq
      let pl ← ctxValProof cfg ctx lhs
      let pr ← ctxValProof cfg ctx rhs
      mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
    else
      -- TRANSITIVE type-alist equivalence (MDD-ratified 2026-07-23): the
      -- node's equation is a composition across the clause's equations —
      -- ACL2's type-alist unions equivalence classes and records no chain
      -- (there is nothing more to emit), so derive the chain as the
      -- deterministic closure of the in-scope equations. The three
      -- E-equations of HOW-MANY-EVENS-AND-ODDS *1/2.8 are the anchor case.
      let eqs := inScopeEquations ctx
      let some chain := eqChain? eqs lhs rhs
        | throwError "solidify: node sides {repr lhs} ⇒ {repr rhs} match \
                      neither the source equation ({repr ta} = {repr tb}) nor \
                      any equation chain of the clause context \
                      ({eqs.length} in-scope equation(s)) (frontier)"
      let some valueEq ← composeEqChain cfg ctx chain
        | throwError "solidify: internal — empty equation chain for distinct \
                      sides {repr lhs} ⇒ {repr rhs}"
      let pl ← ctxValProof cfg ctx lhs
      let pr ← ctxValProof cfg ctx rhs
      mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
  | "rewrite", "CDR-CONS" =>
    -- `(cdr (cons a b)) ⇒ b`.
    match lhs with
    | .cons (.atom (.symbol cdrS))
        (.cons (.cons (.atom (.symbol consS)) (.cons a (.cons b .nil))) .nil) =>
      unless cdrS.name == "CDR" && consS.name == "CONS" do
        throwError "cdr-cons: lhs head not (cdr (cons …)): {repr lhs}"
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCdr ← proveNoShadow cfg { name := "CDR" }
      let hNoCons ← proveNoShadow cfg { name := "CONS" }
      let ruleEq ← mkAppM ``re_cdr_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCdr, hNoCons, ha, hb]
      -- children may rewrite the rule's result further (see car-cons)
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx b children
      let chainOpt ← chainReqEq chainOpt
      unless finalTerm == rhs do
        throwError "cdr-cons: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "cdr-cons: lhs not (cdr (cons a b)): {repr lhs}"
  | "rewrite", "CAR-CONS" =>
    -- `(car (cons a b)) ⇒ a`.
    match lhs with
    | .cons (.atom (.symbol carS))
        (.cons (.cons (.atom (.symbol consS)) (.cons a (.cons b .nil))) .nil) =>
      unless carS.name == "CAR" && consS.name == "CONS" do
        throwError "car-cons: lhs head not (car (cons …)): {repr lhs}"
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCar ← proveNoShadow cfg { name := "CAR" }
      let hNoCons ← proveNoShadow cfg { name := "CONS" }
      let ruleEq ← mkAppM ``re_car_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCar, hNoCons, ha, hb]
      -- the rule's result may be FURTHER rewritten by children (e.g. a
      -- solidify inside the rule's RHS — their paths carry the (RHS . _)
      -- boundary, consumed by the sub-walk); the node's rhs is the NET result.
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx a children
      let chainOpt ← chainReqEq chainOpt
      unless finalTerm == rhs do
        throwError "car-cons: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "car-cons: lhs not (car (cons a b)): {repr lhs}"
  | "rewrite", "UNICITY-OF-0" =>
    -- `(binary-+ '0 z) ⇒ z` via the REAL intermediate `(fix z)` (the def:fix child
    -- subtree is REPLAYED, not collapsed): (A) `(+ '0 z) ⇒ (fix z)` by both
    -- converging to z's pinned int value; (B) the child `(fix z) ⇒ z`.
    match lhs with
    | .cons (.atom (.symbol plusS)) (.cons q0 (.cons z .nil)) =>
      unless plusS.name == "BINARY-+" && rhs == z do
        throwError "unicity-of-0: unexpected shape {repr lhs} ⇒ {repr rhs}"
      let pin? ← match ctx.val? z with
        | some p => pure (some p)
        | none => builtinIntVal? cfg ctx z   -- gz-builtin TP route (e.g. LEN)
      let some (vz, pz) := pin?
        | throwError "unicity-of-0: {repr z} has no pinned value (need the TP int fact)"
      let k ← intValExpr? vz
      let some fixChild := children.find? (fun c => (runeOf c).ty == "definition")
        | throwError "unicity-of-0: missing the definition:fix child"
      let (_fixLhs, fixRhs) := nodeLhsRhs fixChild
      unless fixRhs == z do
        throwError "unicity-of-0: fix child rhs {repr fixRhs} ≠ {repr z}"
      let fixEq ← replayNodeWith rec cfg ctx fixChild
      let fixConv ← mkAppM ``fuel_conv_of_eq #[fixEq, pz]
      let hq0 ← ctxValProof cfg ctx q0
      let vq0 ← ctxValExpr cfg ctx q0
      let hNoPlus ← proveNoShadow cfg { name := "BINARY-+" }
      let hNsPlus ← proveNotSpecial { name := "BINARY-+" }
      let hr ← mkAppM ``callBuiltin_plus #[vq0, vz]
      let plusConvRaw ← mkAppM ``conv_builtin2
        #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "BINARY-+" },
          reflectSExpr q0, reflectSExpr z, vq0, vz,
          mkApp2 (mkConst ``Logic.plus) vq0 vz, hNsPlus, hNoPlus, hq0, pz, hr]
      let hzero ← mkAppM ``logic_plus_zero_int #[k]
      let plusConv ← mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr lhs,
          mkApp2 (mkConst ``Logic.plus) vq0 vz, vz, plusConvRaw, hzero]
      let stepA ← mkAppM ``fuel_eq_of_conv #[plusConv, fixConv, ← mkEqRefl vz]
      mkAppM ``fuel_chain_eq #[stepA, fixEq]
    | _ => throwError "unicity-of-0: lhs not (binary-+ '0 z): {repr lhs}"
  | "rewrite", "COMMUTATIVITY-OF-+" =>
    -- `(+ a b) ⇒ (+ b a)`, then the node's children chain on the rule's rhs
    -- (their paths carry an `(RHS . …)` boundary frame) to the recorded rhs.
    match lhs with
    | .cons (.atom (.symbol plusS)) (.cons a (.cons b .nil)) =>
      unless plusS.name == "BINARY-+" do
        throwError "commutativity-of-+: head {plusS.name}"
      let ha ← ctxValProof cfg ctx a
      let hb ← ctxValProof cfg ctx b
      let va ← ctxValExpr cfg ctx a
      let vb ← ctxValExpr cfg ctx b
      let hNoPlus ← proveNoShadow cfg { name := "BINARY-+" }
      let ruleEq ← mkAppM ``re_plus_comm
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, va, vb, hNoPlus, ha, hb]
      let swapped : SExpr :=
        .cons (.atom (.symbol plusS)) (.cons b (.cons a .nil))
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx swapped children
      let chainOpt ← chainReqEq chainOpt
      unless finalTerm == rhs do
        throwError "commutativity-of-+: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "commutativity-of-+: lhs not (binary-+ a b): {repr lhs}"
  | "rewrite", "COMMUTATIVITY-2-OF-+" =>
    -- `(+ a (+ b c)) ⇒ (+ b (+ a c))`, then the children chain on the rule's rhs
    -- by the sub-walk to the recorded rhs.
    match lhs with
    | .cons (.atom (.symbol plusS))
        (.cons a (.cons (.cons (.atom (.symbol plusS2)) (.cons b (.cons c .nil))) .nil)) =>
      unless plusS.name == "BINARY-+" && plusS2.name == "BINARY-+" do
        throwError "commutativity-2-of-+: heads"
      let ha ← ctxValProof cfg ctx a
      let hb ← ctxValProof cfg ctx b
      let hc ← ctxValProof cfg ctx c
      let va ← ctxValExpr cfg ctx a
      let vb ← ctxValExpr cfg ctx b
      let vc ← ctxValExpr cfg ctx c
      let hNoPlus ← proveNoShadow cfg { name := "BINARY-+" }
      let ruleEq ← mkAppM ``re_plus_comm2
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, reflectSExpr c,
          va, vb, vc, hNoPlus, ha, hb, hc]
      let swapped : SExpr :=
        .cons (.atom (.symbol plusS))
          (.cons b (.cons (.cons (.atom (.symbol plusS2)) (.cons a (.cons c .nil))) .nil))
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx swapped children
      let chainOpt ← chainReqEq chainOpt
      unless finalTerm == rhs do
        throwError "commutativity-2-of-+: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "commutativity-2-of-+: lhs not (+ a (+ b c)): {repr lhs}"
  | "definition", dname =>
    -- `implies` is an evalOpt BUILTIN modeled by `callBuiltin`, not a world
    -- definition — its :DEFINITION rune gets the ground-zero recipe.
    if dname == "IMPLIES" && (cfg.worldVal.defs.get? { name := "IMPLIES" }).isNone then
      replayImpliesDef cfg ctx n
    else if dname == "IFF" && (cfg.worldVal.defs.get? { name := "IFF" }).isNone then
      -- `iff` is likewise an evalOpt BUILTIN (the preprocess boot-strap
      -- non-rec arm's body adoption, G1 iff rung)
      replayIffDef cfg ctx n
    else replayDefinition rec cfg ctx n
  | "lambda-body", _ => replayLambdaBody rec cfg ctx n
  | "fake-rune-for-anonymous-enabled-rule", _ =>
    -- recognizer node: term-eq form (eval lhs = eval rhs, rhs the quoted verdict).
    let verdictV := match rhs with
      | .cons (.atom (.symbol q)) (.cons v .nil) => if q.name == "QUOTE" then v else rhs
      | v => v
    -- the node's cited (:TYPE-PRESCRIPTION <name>) runes — the tpthm
    -- route's BUG-023 anchor (theorem-classed TP rules; defun-TP names
    -- simply have no tpthm offer and fall through to the tp: routes)
    let citedTpThms := prov.runes.filterMap fun r =>
      if r.ty == "type-prescription" then some r.name else none
    -- the node's cited (:COMPOUND-RECOGNIZER <name>) runes — the
    -- BUG-023 anchor for a compound-recognizer typing probe (T1+2
    -- sprint P3b); `:ARG-LEAVES` and `:TRUETS` come off the same record
    let citedCr := prov.runes.filterMap fun r =>
      if r.ty == "compound-recognizer" then some r.name else none
    let fact ← replayRecognizer cfg ctx lhs verdictV prov.typeSet
      (citedTpThms := citedTpThms) (argLeaves := prov.argLeaves)
      (citedCr := citedCr) (stepTrueTs := prov.trueTs)
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr verdictV]
    mkAppM ``fuel_eq_of_conv #[fact, hq, ← mkEqRefl (reflectSExpr verdictV)]
  | "if-simplification", _ =>
    -- `(if 'c thn els) ⇒ branch` — the test is already a quoted constant (a
    -- preceding recognizer rewrote it via if-test congruence). The
    -- `if1/boolean` origin instead collapses `(if tst 't 'nil) ⇒ tst` for a
    -- BOOLEAN-valued symbolic test (ACL2 justifies it by type-set; the replay
    -- discharges the same claim by the test value's two-valuedness).
    match lhs with
    | .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) =>
      unless ifS.name == "IF" do
        throwError "if-simplification: head {ifS.name}"
      if prov.origin == "if1/boolean" then
        unless thn == quoteT && els == quoteNil && rhs == c do
          throwError "if1/boolean: node is not (if tst 't 'nil) ⇒ tst: \
                      {repr lhs} ⇒ {repr rhs}"
        let vC ← ctxValExpr cfg ctx c
        let hBool ←
          if vC.isAppOfArity ``Logic.equal 2 then
            mkAppM ``cond_toBool_equal #[vC.appFn!.appArg!, vC.appArg!]
          else if vC.isAppOfArity ``ACL2.lexorder 2 then
            -- LEXORDER test: two-valuedness DIRECTLY from `lexorder_boolean`
            -- (a builtin boolean predicate — no TP hypothesis needed).
            mkAppM ``cond_toBool_lexorder #[vC.appFn!.appArg!, vC.appArg!]
          else if vC.isAppOfArity ``Logic.lt 2 then
            -- `<` test (G1 rung 1, p6): two-valued builtin — same closer
            -- via the disjunction form.
            mkAppM ``cond_toBool_of_t_or_nil
              #[← mkAppM ``logic_lt_t_or_nil #[vC.appFn!.appArg!, vC.appArg!]]
          else if (match c with
                   | .cons (.atom (.symbol s)) (.cons _ (.cons _ (.cons _ .nil))) =>
                     s.name == "IF"
                   | _ => false) then do
            -- IF-headed test (G1 rung 1, inc-2 — p3-conj-mid-literal):
            -- two-valuedness derived STRUCTURALLY from the branches
            -- (quoted constants / equal / lexorder / boolean-TP fns,
            -- recursively through nested ifs) — the same sources ACL2's
            -- type-set unions over the if's leaves.
            let some hd ← boolDisj? cfg ctx c
              | throwError "if1/boolean: IF-headed test {repr c} has a \
                  branch with no two-valuedness source (frontier)"
            mkAppM ``cond_toBool_of_t_or_nil #[hd]
          else do
            -- USER-FN test: two-valuedness from the fn's EMITTED
            -- :TYPE-PRESCRIPTION hypothesis (the boolean corollary shape),
            -- instantiated at the test's pinned value — consumed, not
            -- inferred (same source as the type-alist truthy verdict)
            let .cons (.atom (.symbol fs)) argsSpine := c
              | throwError "if1/boolean: test {repr c} is neither a \
                            Logic.equal value nor a fn application \
                            (two-valuedness source, frontier)"
            let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
              | throwError "if1/boolean: no :TYPE-PRESCRIPTION hypothesis for \
                            {fs.name} (emit more, frontier)"
            let some (formals, _) := cfg.worldVal.defs.get? fs
              | throwError "if1/boolean: {fs.name} not defined in the world"
            let args := (argsSpine.toList?).getD []
            unless formals.length == args.length do
              throwError "if1/boolean: arity mismatch instantiating the TP \
                          of {fs.name}"
            let some (v, conv) := ctx.val? c
              | throwError "if1/boolean: {repr c} has no pinned value (frontier)"
            let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
              ++ (args.map reflectSExpr).toArray ++ #[v, conv])
            mkAppM ``cond_toBool_of_tp_boolean #[v, fact]
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx c
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, hBool]
      let .cons (.atom (.symbol q)) (.cons cv .nil) := c
        | throwError "if-simplification: test is not a quoted constant: {repr c}"
      unless q.name == "QUOTE" do
        throwError "if-simplification: test is not a quoted constant: {repr c}"
      let hc ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      if cv == SExpr.nil then
        unless rhs == els do
          throwError "if-simplification: nil test but rhs ≠ else branch"
        let pEls ← ctxValProof cfg ctx els
        let vEls ← ctxValExpr cfg ctx els
        mkAppM ``re_if_false
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
            vEls, hc, pEls]
      else
        unless rhs == thn do
          throwError "if-simplification: non-nil test but rhs ≠ then branch"
        let pThn ← ctxValProof cfg ctx thn
        let vThn ← ctxValExpr cfg ctx thn
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (reflectSExpr cv)) (mkConst ``Bool.true))
          "toBool verdict = true"
        mkAppM ``re_if_true
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
            reflectSExpr cv, vThn, hc, hcv, pThn]
    | _ => throwError "if-simplification: lhs not an if: {repr lhs}"
  | "if-same-branches", _ =>
    -- `(if c a a) ⇒ a` (if1/same-branches): the branch value is the if value
    -- whichever way the test goes; the test's convergence is the only premise.
    match lhs with
    | .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) =>
      unless ifS.name == "IF" do
        throwError "if-same-branches: head {ifS.name}"
      unless thn == els && rhs == thn do
        throwError "if-same-branches: node is not (if c a a) ⇒ a: \
                    {repr lhs} ⇒ {repr rhs}"
      let pc ← ctxValProof cfg ctx c
      let pa ← ctxValProof cfg ctx thn
      mkAppM ``re_if_same
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
          ← ctxValExpr cfg ctx c, ← ctxValExpr cfg ctx thn, pc, pa]
    | _ => throwError "if-same-branches: lhs not an if: {repr lhs}"
  | "equal-self", _ =>
    -- `(equal X X) ⇒ 't` as a MID-CHAIN node (reflexivity of `equal`; the
    -- closing-literal form lives in `replayLiteral`).
    match asEqualSelf lhs with
    | none => throwError "equal-self: lhs is not (equal X X): {repr lhs}"
    | some X =>
      unless rhs == quoteT do
        throwError "equal-self: rhs {repr rhs} ≠ (quote t)"
      let hX ← proveConv cfg cfg.envExpr ctx X
      let hNoEqual ← proveNoShadow cfg { name := "EQUAL" }
      let pEq ← mkAppM ``re_equal_self
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr X, hX, hNoEqual]
      let pQ ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
      mkAppM ``fuel_eq_of_conv #[pEq, pQ, ← mkEqRefl (mkConst ``SExpr.t)]
  | "compound-recognizer", "ZP-COMPOUND-RECOGNIZER" =>
    if let some p ← compoundRecogTsCell cfg ctx prov lhs rhs then return p
    replayZpCompoundRecog cfg ctx prov lhs rhs
  | "compound-recognizer", rname =>
    if let some p ← compoundRecogTsCell cfg ctx prov lhs rhs then return p
    -- ACL2's built-in COMPOUND-RECOGNIZER rules (BNEXT-SIZE route layer
    -- 3: (NATP (LEN X)) ⇒ 'T in non-ACL2-COUNT measure admissions).
    -- Registered rune → recognizer head (a read-off check, never
    -- shape-inferred); the inner fn's fact from the trusted-core builtin
    -- registry, GATED on the EMITTED nonneg-int TP corollary. A WORLD-fn
    -- inner (BNEXT-SIZE itself) is the named next frontier.
    unless nodeOrigin n == "recognizer/true" do
      throwError "compound-recognizer: origin {nodeOrigin n} (frontier)"
    let some recogHead :=
        ([("NATP-COMPOUND-RECOGNIZER", "NATP")].lookup rname)
      | throwError "compound-recognizer: rune {rname} not registered \
                    (frontier)"
    let .cons (.atom (.symbol rs)) (.cons inner .nil) := lhs
      | throwError "compound-recognizer: lhs {repr lhs} is not a unary \
                    recognizer application (frontier)"
    unless rs.name == recogHead do
      throwError "compound-recognizer: lhs head {rs.name} ≠ the rune's \
                  recognizer {recogHead} (emission divergence)"
    unless rhs == quoteT do
      throwError "compound-recognizer: rhs {repr rhs} ≠ 'T (frontier)"
    let .cons (.atom (.symbol fs)) (.cons innerArg .nil) := inner
      | throwError "compound-recognizer: inner {repr inner} is not a unary \
                    application (frontier)"
    -- R2 gate (2026-08-07): the NATP-true verdict is admitted by the
    -- EMITTED numbers (basicTs ⊆ NATP true-ts) before any lemma applies.
    recogVerdictGate cfg fs.name "NATP" true
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
    let hT ← match builtinRecogFacts.find? (fun e => e.1 == fs.name) with
      | some (_, _, natpLem) =>
        -- BUILTIN route: the trusted-core value lemma, still anchored to
        -- the emitted corollary shape.
        let some cor := cfg.gzTps.lookup fs.name
          | throwError "compound-recognizer: {fs.name}'s TP corollary not \
                        emitted (type facts from ACL2 — emission gap)"
        let .cons _ (.cons (.cons _ (.cons app _)) _) := cor
          | throwError "compound-recognizer: corollary destructure failed: \
                        {repr cor}"
        unless cor == intTpCorollary app do
          throwError "compound-recognizer: {fs.name}'s corollary drifted \
                      from the nonneg-int shape: {repr cor}"
        let vArg ← ctxValExpr cfg ctx innerArg
        mkAppM natpLem #[vArg]
      | none =>
        -- WORLD-fn route (item 9 UNPARKED 2026-08-07 — BNEXT-SIZE): the
        -- natp fact is the fn's BOUND tp: hypothesis (type facts from
        -- ACL2) instantiated at the application, closed by the
        -- resurrected logic_natp_t_of_int_tp_fact.
        let some (_, cor, tpHyp) :=
            ctx.tpHyps.find? (fun (n, _, _) => n == fs.name)
          | throwError "compound-recognizer: inner fn {fs.name} passed \
                        the emitted-data gate but has neither a \
                        trusted-core value lemma nor a bound tp: \
                        hypothesis (frontier)"
        let some (formals, _) := cfg.worldVal.defs.get? fs
          | throwError "compound-recognizer: {fs.name} has a tp: \
                        hypothesis but is not in the world (internal)"
        let args := [innerArg]
        unless formals.length == args.length do
          throwError "compound-recognizer: {fs.name} arity mismatch \
                      (frontier)"
        let inst := ACL2.Replay.substTerm formals args cor
        unless inst == intTpCorollary inner do
          throwError "compound-recognizer: {fs.name}'s instantiated \
                      corollary {repr inst} is not the nonneg-int shape \
                      at {repr inner} (frontier)"
        let some (vz, convz) := ctx.val? inner
          | throwError "compound-recognizer: {repr inner} has no pinned \
                        value (totality hypothesis missing?)"
        let hFact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
          ++ (args.map reflectSExpr).toArray ++ #[vz, convz])
        mkAppM ``logic_natp_t_of_int_tp_fact #[hFact]
    let pl ← ctxValProof cfg ctx lhs
    let pr ← mkAppM ``re_val_quote
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    mkAppM ``fuel_eq_of_conv #[pl, pr, hT]
  | "equal-case-split", _ =>
    -- rewrite-equal's boolean CASE-RESTRUCTURING (fork-batch item 1's
    -- consumer): `(EQUAL p q)` with the split side an EQUALITY — hence
    -- two-valued — restructures to `(IF split (EQUAL other 'T) (IF other
    -- 'NIL 'T))`. The emitted rhs is RECOMPUTE-AND-CHECKED against the
    -- origin's exact construction; the close is the value identity
    -- `logic_equal_case_split` (the split side's two-valuedness from
    -- `Logic.equal`'s range), with `logic_equal_comm` orienting the
    -- lhs-variant.
    let .cons (.atom (.symbol eqS)) (.cons p (.cons q .nil)) := lhs
      | throwError "equal-case-split: lhs {repr lhs} is not (EQUAL p q)"
    unless eqS.name == "EQUAL" do
      throwError "equal-case-split: lhs head {eqS.name} ≠ EQUAL"
    let origin := nodeOrigin n
    let (splitT, otherT) ←
      if origin == "equal/case-split-rhs" then pure (q, p)
      else if origin == "equal/case-split-lhs" then pure (p, q)
      else throwError "equal-case-split: origin {origin} (frontier)"
    let isEqApp : SExpr → Bool := fun s => match s with
      | .cons (.atom (.symbol e2)) (.cons _ (.cons _ .nil)) =>
        e2.name == "EQUAL"
      | _ => false
    unless isEqApp splitT do
      throwError "equal-case-split: split side {repr splitT} is not an \
                  EQUAL application (emission divergence)"
    let expectedRhs : SExpr := .cons (.atom (.symbol { name := "IF" }))
      (.cons splitT (.cons
        (.cons (.atom (.symbol { name := "EQUAL" }))
          (.cons otherT (.cons quoteT .nil)))
        (.cons (.cons (.atom (.symbol { name := "IF" }))
          (.cons otherT (.cons quoteNil (.cons quoteT .nil)))) .nil)))
    unless rhs == expectedRhs do
      throwError "equal-case-split: rhs {repr rhs} ≠ the recomputed \
                  restructure of {repr lhs} (emission divergence)"
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
    let vSplit ← ctxValExpr cfg ctx splitT
    let vOther ← ctxValExpr cfg ctx otherT
    unless vSplit.isAppOfArity ``Logic.equal 2 do
      throwError "equal-case-split: split value is not (Logic.equal _ _) \
                  (internal — the value walker's EQUAL composition)"
    let hq ← mkAppM ``logic_equal_t_or_nil
      #[vSplit.appFn!.appArg!, vSplit.appArg!]
    let idRhs ← mkAppM ``logic_equal_case_split #[vOther, vSplit, hq]
    -- lhs value: equal p q — for the rhs-variant that IS equal other split;
    -- the lhs-variant needs the comm bridge (equal split other)
    let valueEq ←
      if origin == "equal/case-split-rhs" then pure idRhs
      else do
        let comm ← mkAppM ``logic_equal_comm #[vSplit, vOther]
        mkAppM ``Eq.trans #[comm, idRhs]
    let pl ← ctxValProof cfg ctx lhs
    let pr ← ctxValProof cfg ctx rhs
    mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
  | "type-alist", _ =>
    -- SOLIDIFY from the type-alist: the clause context — a spine literal's
    -- falsity — pins the term's value; the node rewrites the term to that
    -- constant. Only the direct-falsity/nil form is supported (a truthy or
    -- derived type-alist entry is a named frontier).
    let .cons (.atom (.symbol q)) (.cons cv .nil) := rhs
      | throwError "type-alist: rhs {repr rhs} is not a quoted constant"
    unless q.name == "QUOTE" do
      throwError "type-alist: rhs {repr rhs} is not a quoted constant"
    if cv == SExpr.nil then
      -- sources (sorting-completion-2 Class A): the bounded value-level
      -- type-set closure — direct falsity facts, equation transport, the
      -- car/cdr completion defaults (ORDEREDP-MEMB's `E ⇒ 'NIL` composes
      -- a segment equation E = (CAR (CDR A)) with (CONSP (CDR A)) false;
      -- such entries emit :PARENTS NIL :RUNES NIL/fake — assumption-
      -- composed, no rune provenance to consume)
      let some hNil ← typeSetWalk cfg ctx (.isNil lhs)
        | throwError "type-alist: no spine falsity fact for {repr lhs}             (frontier; lit-facts {repr (ctx.litFacts.map (·.2.1))};             seg-facts {repr (ctx.segFacts.map (·.1))};             branch-facts {repr (ctx.branchFacts.map (fun (t,_,sg,_) => (t, sg)))})"
      let pl ← ctxValProof cfg ctx lhs
      let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    else if cv == SExpr.t then
      -- TRUTHY verdict: the spine's `(not lhs)`-false fact gives ≠ nil; the
      -- fn's EMITTED :TYPE-PRESCRIPTION (the rune is on the node) pins the
      -- non-nil value to exactly `t` (two-valuedness — consumed, not inferred)
      let notLhs : SExpr := .cons (.atom (.symbol { name := "NOT" }))
        (.cons lhs .nil)
      -- EQUIVALENCE-REFLEXIVITY route (sorting-completion-2 Class A,
      -- ORDERED-PERMS): a syntactically REFLEXIVE application (R u u) of an
      -- in-scope equivalence relation is truthy by the rule's reflexivity
      -- component (`equivrefl:<thm>` — instantiated premise-free at u);
      -- the fn's emitted TP pins the non-nil value to exactly t below.
      -- NOTE: the emitted record's ttree does not name the equivalence
      -- rune (the entry's own derivation is untracked) — this discharge
      -- is the replayed-fact route for a derivation ACL2 did not record.
      let reflHyp? : Option Expr ← do
        match lhs with
        | .cons (.atom (.symbol rS)) (.cons u (.cons u2 .nil)) =>
          if u == u2 then
            match ctx.equivReflHyps.find? (fun (sp, _) => sp.rel == rS) with
            | some (sp, hypV) => do
              let (h, _) ← instantiateEvTrueHypAt cfg ctx hypV [sp.vx] [u]
                (.cons (.atom (.symbol sp.rel))
                  (.cons (.atom (.symbol sp.vx))
                    (.cons (.atom (.symbol sp.vx)) .nil)))
              pure (some h)
            | none => pure none
          else pure none
        | _ => pure none
      if let some hRefl := reflHyp? then
        -- hRefl : EvTrue w env (R u u) → value ≠ nil; TP pins to t
        let vL ← ctxValExpr cfg ctx lhs
        let hne ← mkAppM ``ne_nil_of_evtrue_conv
          #[hRefl, ← ctxValProof cfg ctx lhs]
        let .cons (.atom (.symbol fs)) argSpine := lhs
          | throwError "type-alist: internal — refl lhs not an application"
        let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
          | throwError "type-alist: refl route needs {fs.name}'s emitted \
              :TYPE-PRESCRIPTION to pin the exact value (frontier)"
        let args := (argSpine.toList?).getD []
        let some (vLL, convL) := ctx.val? lhs
          | throwError "type-alist: refl lhs {repr lhs} has no pinned value \
              (frontier)"
        let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
          ++ (args.map reflectSExpr).toArray ++ #[vLL, convL])
        let hT ← mkAppM ``tp_cond_boolean_t #[vLL, fact, hne]
        let _ := vL
        let pl ← ctxValProof cfg ctx lhs
        let pr ← mkAppM ``re_val_quote
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, hT]
      let _ := notLhs
      let vL ← ctxValExpr cfg ctx lhs
      -- the walker's truthy request covers the spine (not …)-falsity fact,
      -- a truthy branch fact on lhs itself (HOW-MANY-QSORT), and the
      -- expanded (IF lhs 'NIL 'T) falsity — consumed, not inferred
      let some hne ← typeSetWalk cfg ctx (.isTruthy lhs)
        | throwError "type-alist: no truthy evidence for \
                      {repr lhs} (frontier; \
                      lit-facts {repr (ctx.litFacts.map (·.2.1))}; \
                      seg-facts {repr (ctx.segFacts.map (·.1))}; \
                      branch-facts {repr (ctx.branchFacts.map
                        (fun (t,_,sg,_) => (t, sg)))})"
      -- TWO-VALUED BUILTIN lhs (G1 rung 1, p6; EQUAL added with the
      -- HOW-MANY-QSORT route): a `<`/`equal`-valued term's truthy pin
      -- needs no TP — the builtin's provable two-valuedness resolves
      -- ≠ nil to = t directly.
      if vL.isAppOfArity ``Logic.lt 2 || vL.isAppOfArity ``Logic.equal 2 then
        let hd ←
          if vL.isAppOfArity ``Logic.lt 2 then
            mkAppM ``logic_lt_t_or_nil #[vL.appFn!.appArg!, vL.appArg!]
          else
            mkAppM ``logic_equal_t_or_nil #[vL.appFn!.appArg!, vL.appArg!]
        let hT ← mkAppM ``Or.resolve_right #[hd, hne]
        let pl ← ctxValProof cfg ctx lhs
        let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, hT]
      let .cons (.atom (.symbol fs)) argsSpine := lhs
        | throwError "type-alist: truthy verdict on a non-application \
                      {repr lhs} (frontier)"
      let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
        | throwError "type-alist: no :TYPE-PRESCRIPTION hypothesis for \
                      {fs.name} (emit more, frontier)"
      let some (formals, _) := cfg.worldVal.defs.get? fs
        | throwError "type-alist: {fs.name} not defined in the world"
      let args := (argsSpine.toList?).getD []
      unless formals.length == args.length do
        throwError "type-alist: arity mismatch instantiating the TP of {fs.name}"
      let some (v, conv) := ctx.val? lhs
        | throwError "type-alist: {repr lhs} has no pinned value (frontier)"
      let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
        ++ (args.map reflectSExpr).toArray ++ #[v, conv])
      let hT ← mkAppM ``tp_cond_boolean_t #[v, fact, hne]
      let pl ← ctxValProof cfg ctx lhs
      let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      mkAppM ``fuel_eq_of_conv #[pl, pr, hT]
    else
      throwError "type-alist: verdict {repr rhs} is neither nil nor t (frontier)"
  | "executable-counterpart", _ =>
    -- a GROUND computation step within a rewrite chain (e.g. `(consp 'nil) ⇒ 'nil`):
    -- ACL2 ran the executable counterpart; re-run the SAME closed computation and
    -- lift to the node-equality `eval lhs = eval rhs` (rhs the recorded constant).
    let .cons (.atom (.symbol q)) (.cons v .nil) := rhs
      | throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    unless q.name == "QUOTE" do
      throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    let convLhs ← replayExecGround cfg lhs v
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr v]
    mkAppM ``fuel_eq_of_conv #[convLhs, hq, ← mkEqRefl (reflectSExpr v)]
  | "rewrite", _ =>
    -- USER rewrite rule (with-lemma): the THEOREM-DEPENDENCY recipe
    -- (docs/plans/2026-07-05_theorem-dependency-hypotheses.md). The node
    -- consumes the bound `rule:<thm>` hypothesis — the STORED rule's replayed statement —
    -- instantiated strictly by the emitted :SUBST; hypothesis relief comes
    -- from the recorded :KIND HYP chain or the clause context, never
    -- re-searched. (The built-in-axiom runes above keep their hand recipes —
    -- their formulas are in no log.)
    -- `abbreviation-expansion` is the SAME rule application recorded at
    -- preprocess's expand-abbreviations: ACL2's `abbreviation` subclass is
    -- hypothesis-free by construction (find-abbreviation-lemma), enforced
    -- below at the spec — the recipe is otherwise identical
    unless prov.origin == "with-lemma" ||
           prov.origin == "abbreviation-expansion" do
      throwError "rewrite rune ({rname}): origin {prov.origin} is not \
                  with-lemma (frontier)"
    let σvars ← prov.subst.mapM fun (v, _) => do
      let .atom (.symbol s) := v
        | throwError "rule {rname}: :SUBST binds a non-variable {repr v}"
      pure s
    let σterms := prov.subst.map (·.2)
    -- the matching stored rule: recompute-and-check joint —
    -- substTerm(:SUBST, rule lhs) must BE the node's lhs
    -- identity includes the multi-rule index (J7): a step citing
    -- (:REWRITE FOO . 2) matches only the idx-2 stored rule.
    -- equiv is part of the match (audit F5): ruleHyps is heterogeneous
    -- since G2 (equal rules carry eval-equality hypotheses, user-R rules
    -- the interpreted-relation shape) — this eq-composing consumer must
    -- never select a non-equal hypothesis it cannot compose
    let candidates := ctx.ruleHyps.filter fun (r, _) =>
      r.name == rname && r.idx == rune.idx && r.equiv == prov.equiv
    if candidates.isEmpty then
      throwError "rule {rname}: no stored-rule hypothesis in scope (no \
                  (:RULES …) entry — emission gap or missing telescope)"
    let matched := candidates.filter fun (r, _) =>
      ACL2.Replay.substTerm σvars σterms r.lhs == lhs
    -- an EQUAL-headed rule lhs may match the target equality COMMUTED —
    -- ACL2's `one-way-unify1` tries both argument orders for EQUAL patterns
    -- (the CAR-APPEND class). Recompute-and-check against the commuted node
    -- lhs; the proof prepends the `re_equal_comm` bridge below.
    let commutedLhs? : Option SExpr := match lhs with
      | .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) =>
        if eqS.name == "EQUAL" then
          some (.cons (.atom (.symbol eqS)) (.cons y (.cons x .nil)))
        else none
      | _ => none
    let (matched, commuted) :=
      if matched.isEmpty then
        match commutedLhs? with
        | some lhsC =>
          (candidates.filter fun (r, _) =>
            ACL2.Replay.substTerm σvars σterms r.lhs == lhsC, true)
        | none => (matched, false)
      else (matched, false)
    let (spec, hypV) ← match matched with
      | [m] => pure m
      | m :: restM =>
        -- multi-include RE-STORAGE (sorting arc 2026-07-28): one rule stored
        -- once per include path — arithmetic-3's FOLD-CONSTS-IN-+ appears
        -- 13× in the qsort development's (:RULES …) stream, all IDENTICAL.
        -- Identical specs ARE one rule: take the first. Any DISTINCT
        -- matching specs remain a hard ambiguity.
        if restM.all (fun (r, _) => r == m.1) then pure m
        else throwError "rule {rname}: {matched.length} DISTINCT stored \
                    rules match substTerm(:SUBST, lhs) == {repr lhs} \
                    (direct or EQUAL-commuted; need exactly 1)"
      | [] => throwError "rule {rname}: 0 stored rules match \
                    substTerm(:SUBST, lhs) == {repr lhs} (direct or EQUAL-\
                    commuted; need exactly 1)"
    if prov.origin == "abbreviation-expansion" && !spec.hyps.isEmpty then
      throwError "rule {rname}: abbreviation-expansion step cites a rule \
                  with {spec.hyps.length} hypotheses — abbreviations are \
                  hyp-free (record/world mismatch)"
    -- block membership: a window-tagged sibling inside a classic block
    -- carries the block in `blockKind` (path-emission Phase 1)
    let blockOf : ProofNode → String := fun
      | .node _ _ _ _ p => if p.blockKind.isEmpty then p.innerKind else p.blockKind
    let hypKids := children.filter fun c => blockOf c == "hyp"
    let rhsKids := children.filter fun c => blockOf c == "rhs"
    let otherKids := children.filter fun c =>
      blockOf c != "hyp" && blockOf c != "rhs"
    unless otherKids.isEmpty do
      throwError "rule {rname}: {otherKids.length} child(ren) outside the \
                  HYP/RHS blocks — unconsumed record (frontier)"
    -- rhs joint: the node's rhs is the instantiated rule rhs, possibly
    -- rewritten FURTHER by the recorded RHS-block chain (with-lemma rewrites
    -- the instantiated rhs before returning), or normalized by
    -- rewrite-equal's UNRECORDED nil-normalization (bridged at the
    -- composition point below). A residual mismatch is a hard-fail there.
    let rhsσ := ACL2.Replay.substTerm σvars σterms spec.rhs
    -- partition the HYP block: silent-relief MARKERS (emit/relieve-hyp/*)
    -- vs an actual relief rewrite chain
    let (reliefMarkers, chainKids) := hypKids.partition
      fun c => (runeOf c).ty == "hyp-relief"
    -- coverage: every rule variable must be bound by σ (free-var hyps extend
    -- σ at emission; a gap means the emission is incomplete)
    let ruleFrees := ACL2.Replay.freeVars spec.lhs ++
      spec.hyps.flatMap ACL2.Replay.freeVars ++ ACL2.Replay.freeVars spec.rhs
    for s in ruleFrees do
      unless σvars.contains s do
        throwError "rule {rname}: rule variable {s.name} not bound by the \
                    emitted :SUBST (emission gap)"
    -- σ-term values and the substN bridge scaffold (shared by hyps/lhs/rhs)
    let w := cfg.worldExpr
    let env := cfg.envExpr
    let vals ← σterms.mapM (ctxValExpr cfg ctx)
    let convs ← σterms.mapM (ctxValProof cfg ctx)
    let formalsE ← mkListLit (mkConst ``Symbol) (σvars.map reflectSymbol)
    let argsE ← mkListLit (mkConst ``SExpr) (σterms.map reflectSExpr)
    let valsE ← mkListLit (mkConst ``SExpr) vals
    let env' ← mkAppM ``bindArgsOver #[env, formalsE, valsE]
    let hlenPf ← proveByDecide
      (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
      s!"substN lengths ({rname})"
    let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
    let pFn ← withLocalDeclD `pr prodTy fun prV => do
      let fst ← mkAppM ``Prod.fst #[prV]
      let snd ← mkAppM ``Prod.snd #[prV]
      mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
    let entries ← (σterms.zip vals).mapM fun (t, v) =>
      mkAppM ``Prod.mk #[reflectSExpr t, v]
    let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
    let zipE ← mkAppM ``List.zip #[argsE, valsE]
    let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
      let mem ← mkAppM ``Membership.mem #[zipE, prV]
      mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
    let hargs ← mkExpectedTypeHint hargsRaw hargsTy
    -- bridge t : eval env (substTerm σ t) ≡ eval env' t, for any rule-side term
    let bridge : SExpr → MetaM Expr := fun t => do
      let hWellScoped ← proveByDecide
        (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr t]) (mkConst ``Bool.true))
        s!"WellScoped rule term ({rname})"
      mkAppM ``evalOpt_substTerm_substN
        #[w, env, formalsE, argsE, valsE, reflectSExpr t, hWellScoped, hlenPf, hargs]
    -- premises: EvTrue w env' hᵢ from the recorded relief. Sources, per hyp:
    -- a silent-relief MARKER whose hyp matches hσ (recompute-and-check) —
    -- clause-context lookup; else the recorded relief chain (v1: one hyp
    -- with a chain; multi-hyp chains need per-hyp bracketing — hard-fail
    -- until a real tree shows the shape).
    -- SYNP hyps are relieved by neither a marker nor a chain (they discharge
    -- definitionally below) — exclude them from the partition count
    -- (audit 2026-07-19 R1)
    let synpHyps := spec.hyps.countP fun h =>
      match h with
      | .cons (.atom (.symbol s)) _ => s.name == "SYNP"
      | _ => false
    if !chainKids.isEmpty &&
        spec.hyps.length != reliefMarkers.length + synpHyps + 1 then
      throwError "rule {rname}: {spec.hyps.length} hyps with one recorded \
                  relief chain, {reliefMarkers.length} markers, and \
                  {synpHyps} synp hyps — per-hyp partition (frontier)"
    let tNeNil ← proveByDecide
      (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
    let mut prems : Array Expr := #[]
    for h in spec.hyps do
      let hσ := ACL2.Replay.substTerm σvars σterms h
      let hasMarker := reliefMarkers.any fun c => (nodeLhsRhs c).1 == hσ
      -- a SYNP hyp (syntaxp/bind-free): ACL2 relieves it by the meta-level
      -- syntactic check and records `(:DEFINITION SYNP)` in the ttree — in
      -- the LOGIC, `synp` ignores its (always-quoted) args and returns `t`,
      -- so the recorded relief IS the definitional ground evaluation
      let isSynp := match hσ with
        | .cons (.atom (.symbol s)) _ => s.name == "SYNP"
        | _ => false
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
          unless prov.runes.any (fun r => r.ty == "definition" && r.name == "SYNP") do
            throwError "rule {rname}: SYNP hyp {repr hσ} but no \
                        (:DEFINITION SYNP) in the node's ttree runes \
                        (frontier)"
          -- re-run the same closed computation (`synp`'s world body is 'T):
          -- the exec-counterpart carve-out, exactly how ACL2 regards it
          let conv ← replayExecGround cfg hσ SExpr.t
          mkAppM ``evtrue_of_conv_ne_nil #[conv, tNeNil]
        else if hasMarker then do
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
      -- transport to env': eval env' h ≡ eval env hσ (the bridge, reversed)
      let pB ← bridge h
      prems := prems.push
        (← mkAppM ``evtrue_of_fuel_eq #[← mkAppM ``fuel_eq_symm #[pB], evTrueEnv])
    -- the rule's replayed statement at env', premises applied, bridged back to the node:
    -- eval env lhs ≡ eval env' rule.lhs ≡ eval env' rule.rhs ≡ eval env rhsσ
    -- [≡ eval env rhs, by the recorded RHS-block chain when one exists]
    let hRule := mkAppN (mkApp hypV env') prems
    let pL ← bridge spec.lhs
    let pR ← bridge spec.rhs
    let pCore ← mkAppM ``fuel_chain_eq
      #[pL, ← mkAppM ``fuel_chain_eq #[hRule, ← mkAppM ``fuel_eq_symm #[pR]]]
    -- COMMUTED match: pCore proves the commuted equality's rewrite — prepend
    -- eval (EQUAL x y) ≡ eval (EQUAL y x) to root it at the node's lhs
    let pCore ← if commuted then do
        let .cons _ (.cons x (.cons y .nil)) := lhs
          | throwError "rule {rname}: internal — commuted non-equality lhs"
        let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
        let comm ← mkAppM ``re_equal_comm
          #[w, env, reflectSExpr x, reflectSExpr y, hNoEq]
        mkAppM ``fuel_chain_eq #[comm, pCore]
      else pure pCore
    if rhsKids.isEmpty then
      if rhsσ == rhs then return pCore
      -- rewrite-equal's built-in NIL NORMALIZATION inside the instantiated
      -- rhs (rewrite.lisp:18089-92 — unconditional/syntactic, never
      -- recorded): recompute-and-check via the deep single-position bridge
      -- (fold-back fix round 2026-07-31 — the old spurious no-op combined
      -- records, BUG-025, used to absorb this via the running-term joint).
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx rhsσ
      match ← bridgeEqualNilNormDeep cfg ctx rhsσ rhs with
      | some br => return ← mkAppM ``fuel_chain_eq #[pCore, br]
      | none =>
        throwError "rule {rname}: node rhs {repr rhs} ≠ substTerm(:SUBST, \
                    rule rhs {repr spec.rhs}) and no RHS chain recorded \
                    (emission gap)"
    -- the RHS continuation: replay the recorded chain from rhsσ; it must land
    -- exactly on the node's recorded rhs (fail-closed)
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx rhsσ
    let (chainOpt, finalT) ← rec.rewrites cfg ctx rhsσ rhsKids
    let chainOpt ← chainReqEq chainOpt
    unless finalT == rhs do
      throwError "rule {rname}: RHS chain reached {repr finalT}, node rhs is \
                  {repr rhs}"
    match chainOpt with
    | none => return pCore
    | some ch => mkAppM ``fuel_chain_eq #[pCore, ch]
  | "type-set-equality", _ =>
    -- `(equal x 'c) ⇒ 'nil` decided by ACL2's type-set on DISJOINT types
    -- (origin equal/type-set-nil). Registered cell: the clause context
    -- proves `(consp x)` and the quoted constant is a NON-CONS (a cons can
    -- never equal an atom — logic_equal_nil_of_consp_t_nil). Consumed, not
    -- inferred; anything else is a frontier.
    unless nodeOrigin n == "equal/type-set-nil" do
      throwError "type-set-equality: origin {nodeOrigin n} (frontier)"
    let .cons (.atom (.symbol eqS)) (.cons x0 (.cons qc0 .nil)) := lhs
      | throwError "type-set-equality: lhs {repr lhs} is not (equal x 'c) (frontier)"
    unless eqS.name == "EQUAL" do
      throwError "type-set-equality: lhs head {eqS.name} (frontier)"
    unless rhs == quoteNil do
      throwError "type-set-equality: rhs {repr rhs} ≠ 'nil (frontier)"
    -- orientation-normalize (PCE *1/1.x; RESURRECTED at the final
    -- close-out — killed at 910785a, its consumer now reachable): the
    -- quoted constant may sit LEFT — (EQUAL '0 (BINARY-+ …)); the cells
    -- below assume (term, constant) order, and a flip re-orients the
    -- final value fact through logic_equal_comm.
    let isQuoteS : SExpr → Bool := fun s => match s with
      | .cons (.atom (.symbol q)) (.cons _ .nil) => q.name == "QUOTE"
      | _ => false
    let (x, qc, flippedEq) :=
      if isQuoteS x0 && !isQuoteS qc0 then (qc0, x0, true)
      else (x0, qc0, false)
    -- TERM-vs-SUM disjointness (PCE *1/1.x; same resurrection):
    -- `(EQUAL u (BINARY-+ '1 u))` (either orientation) ⇒ 'NIL off u's
    -- emitted nonneg-int TP — `m ≠ 1 + m`.
    let q1' : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
      (.cons (.atom (.number (.int 1))) .nil)
    let plus1Of : SExpr → Option SExpr := fun s => match s with
      | .cons (.atom (.symbol pS)) (.cons oneT (.cons u .nil)) =>
        if pS.name == "BINARY-+" && oneT == q1' then some u else none
      | _ => none
    let sumSelf? : Option (SExpr × Bool) :=
      match plus1Of qc with
      | some u => if u == x then some (x, false) else none
      | none => match plus1Of x with
        | some u => if u == qc then some (qc, true) else none
        | none => none
    if let some (u, flipped) := sumSelf? then do
      return ← tseSumSelfCell cfg ctx lhs u flipped
    -- THIRD registered cell (T1+2 sprint P3b): ACL2'S OWN EMITTED
    -- OPERAND TYPE-SETS (`:LHS-TS`/`:RHS-TS`) — see `tseTsDisjointCell`.
    if let some p ← tseTsDisjointCell cfg ctx prov lhs x0 qc0 then return p
    let .cons (.atom (.symbol q)) (.cons cv .nil) := qc
      | throwError "type-set-equality: {repr qc} is not a quoted constant \
          (lhs-x {repr x}) (frontier)"
    unless q.name == "QUOTE" do
      throwError "type-set-equality: {repr qc} is not a quoted constant (frontier)"
    if cv matches .cons _ _ then
      throwError "type-set-equality: constant {repr cv} is a cons — only the \
          cons-vs-atom cell is registered (frontier)"
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx x
    let vx ← ctxValExpr cfg ctx x
    -- SECOND registered cell (sorting-absolute 2b): POSITIVE-SUM vs '0 —
    -- x = (BINARY-+ '1 (BINARY-+ p q)) with p q fn applications whose
    -- EMITTED TP corollaries are the nonneg-int shape, and the constant
    -- '0: 1 + p + q ≥ 1 ≠ 0 (`logic_equal_nil_of_plus1_nonneg`).
    -- Consumed, not inferred — the facts are the fns' emitted
    -- corollaries at the pinned values (ACL2-COUNT-EVENS-STRONG's
    -- *1/2.1 CAR-CONS window is the driving instance). Non-matching
    -- shapes fall through to the cons-vs-atom cell.
    let q1 : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
      (.cons (.atom (.number (.int 1))) .nil)
    let q0 : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
      (.cons (.atom (.number (.int 0))) .nil)
    let tpNonnegFactOf : SExpr → MetaM (Option Expr) := fun z => do
      let .cons (.atom (.symbol fs)) argsSpine := z | return none
      match ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) with
      | none => return none
      | some (_, cor, tpHyp) =>
        let some (formals, _) := cfg.worldVal.defs.get? fs | return none
        let args := (argsSpine.toList?).getD []
        unless formals.length == args.length do return none
        let inst := ACL2.Replay.substTerm formals args cor
        let ok := match inst with
          | .cons (.atom (.symbol ifS))
              (.cons (.cons (.atom (.symbol intS)) (.cons z1 .nil))
                (.cons (.cons (.atom (.symbol notS))
                  (.cons (.cons (.atom (.symbol ltS))
                    (.cons z2 (.cons zeroT .nil))) .nil))
                  (.cons elseB .nil))) =>
            ifS.name == "IF" && intS.name == "INTEGERP" &&
            notS.name == "NOT" && ltS.name == "<" &&
            z1 == z && z2 == z && elseB == quoteNil && zeroT == q0
          | _ => false
        unless ok do return none
        let some (vz, convz) := ctx.val? z | return none
        return some (mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
          ++ (args.map reflectSExpr).toArray ++ #[vz, convz]))
    let numericCell? ← do
      match x, cv with
      | .cons (.atom (.symbol pS)) (.cons oneT (.cons uT .nil)),
        .atom (.number (.int 0)) =>
        -- the general binary-application pattern with an INNER dispatch —
        -- the match-capture fix (a specific nested pattern here dead-ended
        -- the arm for non-BINARY-+ summands); only the NESTED-SUM cell is
        -- registered.
        if pS.name == "BINARY-+" && oneT == q1 then
          -- nested-sum sub-case (BINARY-+ '1 (BINARY-+ p q)) first; any
          -- other summand (the PCE tower's HOW-MANY) takes the
          -- SINGLE-SUMMAND sibling off its own emitted nonneg-int TP
          -- (RESURRECTED at the final close-out — killed at 910785a with
          -- the tpthm stack; its consumer is now reachable)
          let nested? ← match uT with
            | .cons (.atom (.symbol pS2)) (.cons pT (.cons qT .nil)) =>
              if pS2.name == "BINARY-+" then
                match ← tpNonnegFactOf pT, ← tpNonnegFactOf qT with
                | some fp, some fq =>
                  pure (some (← mkAppM ``logic_equal_nil_of_plus1_nonneg
                    #[fp, fq]))
                | _, _ => pure none
              else pure none
            | _ => pure none
          match nested? with
          | some h => pure (some h)
          | none =>
            match ← tpNonnegFactOf uT with
            | some fu =>
              pure (some (← mkAppM ``logic_equal_nil_of_plus1_nonneg1 #[fu]))
            | none => pure none
        else pure none
      | _, _ => pure none
    let hVal ←
      match numericCell? with
      | some h => pure h
      | none => do
        let some hConsp ← typeSetWalk cfg ctx (.isConspT x)
          | throwError "type-set-equality: no consp evidence for {repr x} \
              in the clause context, and the positive-sum cell does not \
              apply (frontier)"
        let hC ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.consp) (reflectSExpr cv))
            (mkConst ``SExpr.nil))
          "consp of the quoted constant is nil"
        mkAppM ``logic_equal_nil_of_consp_t_nil #[hConsp, hC]
    let hVal ← do
      if flippedEq then
        -- re-orient: the cells prove (equal v_term v_const) = nil; the
        -- lhs value composes in the ORIGINAL (const, term) order
        let vx ← ctxValExpr cfg (← pinTermOpaques cfg cfg.envExpr ctx x) x
        mkAppM ``Eq.trans
          #[← mkAppM ``logic_equal_comm #[reflectSExpr cv, vx], hVal]
      else pure hVal
    let pL ← ctxValProof cfg ctx lhs
    let pR ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.nil]
    mkAppM ``fuel_eq_of_conv #[pL, pR, hVal]
  | _, _ =>
    throwError "replayNode: no rule for rune ({rty}, {rname}) — unimplemented frontier"

/-- The literal-clausify DECISION TREE, reconstructed from the flat
    `SplitDecision` trace (docs/notes/2026-07-03_branch-split-spine.md).
    `if-interp` pushes events else-branch-FIRST at splits; every event is
    self-located by its `path`, which the parser validates against its
    position (fail-closed). -/
inductive TraceTree where
  /-- `segment` (segment-* outcomes): the EMITTED clause segment for this
      leaf — the exact leaf→branch link the composer selects by. -/
  | leaf (value : SExpr) (outcome : String) (segment : Option (List SExpr))
  | resolved (test : SExpr) (verdict : String) (how : String) (sub : TraceTree)
  /-- A genuine split: `fSide` (test assumed false — the ELSE branch,
      logged first) and `tSide`. -/
  | split (test : SExpr) (fSide tSide : TraceTree)
  deriving Repr, Inhabited

partial def parseTraceTree (path : List (Bool × SExpr)) :
    List SplitDecision → Except String (TraceTree × List SplitDecision)
  | [] => throw "parseTraceTree: trace ended without a leaf"
  | .test t v h p :: rest => do
    unless p == path do
      throw s!"parseTraceTree: test {repr t} at path {repr p}, expected \
               {repr path}"
    if v == "split" then
      let (fSide, rest) ← parseTraceTree (path ++ [(false, t)]) rest
      let (tSide, rest) ← parseTraceTree (path ++ [(true, t)]) rest
      return (.split t fSide tSide, rest)
    else
      let (sub, rest) ← parseTraceTree path rest
      return (.resolved t v h sub, rest)
  | .leaf v o p seg :: rest => do
    unless p == path do
      throw s!"parseTraceTree: leaf {repr v} at path {repr p}, expected \
               {repr path}"
    -- ∧-DECOMPOSITION (observed: ALL-REL-FILTER-1 literal 2): on a term
    -- `(if v X 'nil)`, if-interp emits the SEGMENT-OPEN leaf `v` (the
    -- `[v]`-segment child clause of `lit ≡ v ∧ X`) and CONTINUES
    -- enumerating X's segments at the SAME path — the leaf is not
    -- terminal. For the composer this is the decision split on `v`:
    -- under ¬v the literal is 'nil (and the `[v]` branch's segment —
    -- carried over from the open leaf's emitted :SEGMENT — is selected
    -- right there); under v the continuation's decisions apply.
    -- Synthesize exactly that split — every downstream check
    -- (collapse-vs-leaf-value, branch selection) stays fail-closed.
    let nextSamePath := match rest with
      | .test _ _ _ p' :: _ => p' == path
      | .leaf _ _ p' _ :: _ => p' == path
      | [] => false
    if o == "segment-open" && nextSamePath then
      let (k, rest') ← parseTraceTree path rest
      return (.split v (.leaf quoteNil "segment-false" seg) k, rest')
    return (.leaf v o seg, rest)

/-- Collapse `t`'s ifs whose tests are DECIDED by the in-scope facts (the
    branch-split composer's byCases hypotheses + re-derived resolved
    verdicts), plus the two `call-stack` folds if-interp applied — `(not 'c)`
    by ground re-execution, `(equal X X)` by reflexivity — bottom-up,
    mirroring if-interp's interpretation of the rewritten literal. Returns
    the fuel-eq chain `eval t ≡ eval t'` and the collapsed `t'`. Anything the
    enumerated rule set cannot decide is left in place; the composer's
    leaf-value check fail-closes on divergence from the emitted trace. -/
partial def collapseEval (cfg : ReplayConfig) (ctx : ReplayCtx)
    (facts : List (SExpr × Expr × Bool × Expr)) (t : SExpr) :
    MetaM (Option Expr × SExpr) := do
  let w := cfg.worldExpr
  let e := cfg.envExpr
  let some (fs, args) := asApp t | return (none, t)
  if fs.name == "QUOTE" then return (none, t)
  -- an in-scope SPINE falsity fact resolves the term outright: if-interp
  -- consults the clause-segment ASSUMPTIONS for the terms it encounters (the
  -- other literals are assumed false) — e.g. a collapsed residual that IS
  -- another clause literal. Divergence still fail-closes at the composer's
  -- leaf-value check.
  if let some hNil := ctx.litFactByTerm? t then
    let pl ← ctxValProof cfg ctx t
    let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
    let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    return (some step, quoteNil)
  -- EQUAL falsity via the spine facts (if-interp-assumed-value2's rule
  -- set): the commuted form, and ONE transport step through an in-scope
  -- segment EQUALITY (a `(not (equal a b))` literal's falsity, i.e. a = b —
  -- ACL2's type-alist canonicalizes the test through it; observed:
  -- (EQUAL D E) resolved from D = (CAR X) and (EQUAL (CAR X) E) = nil,
  -- ALL-REL-RM-2). All derivations are proof-carrying; anything beyond
  -- this bounded rule set stays unresolved and fail-closes downstream.
  if let .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) := t then
    if eqS.name == "EQUAL" then
      let mkEqT (u v : SExpr) : SExpr :=
        .cons (.atom (.symbol eqS)) (.cons u (.cons v .nil))
      -- falsity of `(equal u v)` from a direct or commuted spine fact,
      -- stated over the given value exprs
      let eqFalsity (u v : SExpr) (vu vv : Expr) : MetaM (Option Expr) := do
        if let some h := ctx.litFactByTerm? (mkEqT u v) then
          return some h
        if let some h := ctx.litFactByTerm? (mkEqT v u) then
          return some (← mkAppM ``Eq.trans #[← mkAppM ``logic_equal_comm #[vu, vv], h])
        return none
      let vx ← ctxValExpr cfg ctx x
      let vy ← ctxValExpr cfg ctx y
      let mut hNil? ← eqFalsity x y vx vy
      if hNil?.isNone then
        -- one transport step through each in-scope segment equality a = b
        for (st, h) in ctx.segFacts do
          if hNil?.isSome then break
          let .cons (.atom (.symbol ns)) (.cons
              (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) .nil) := st
            | continue
          unless ns.name == "NOT" && es.name == "EQUAL" do continue
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          let hab ← mkAppM ``logic_not_equal_nil_eq #[va, vb, h]  -- va = vb
          -- try rewriting x (a→b / b→a), then y likewise
          let tryPos (isX : Bool) (frm tgt : SExpr) (hft : Expr) :
              MetaM (Option Expr) := do
            unless (if isX then x else y) == frm do return none
            let vto ← ctxValExpr cfg ctx tgt
            let some hf ← (if isX then eqFalsity tgt y vto vy
                           else eqFalsity x tgt vx vto) | return none
            -- v(equal x y) = v(equal [to/frm]) = nil
            let f ← withLocalDeclD `v (mkConst ``SExpr) fun vV =>
              mkLambdaFVars #[vV]
                (if isX then mkApp2 (mkConst ``Logic.equal) vV vy
                 else mkApp2 (mkConst ``Logic.equal) vx vV)
            let step ← mkAppM ``congrArg #[f, hft]
            return some (← mkAppM ``Eq.trans #[step, hf])
          let hba ← mkAppM ``Eq.symm #[hab]
          for (isX, frm, tgt, hft) in
              [(true, a, b, hab), (true, b, a, hba),
               (false, a, b, hab), (false, b, a, hba)] do
            if hNil?.isNone then
              hNil? ← tryPos isX frm tgt hft
      if let some hNil := hNil? then
        let pl ← ctxValProof cfg ctx t
        let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
        let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
        return (some step, quoteNil)
  if fs.name == "IF" then
    match args with
    | [c, a, b] =>
      -- collapse the test first; decide; then only the LIVE branch
      let (chC, c') ← collapseEval cfg ctx facts c
      let mut acc : Option Expr := none
      let mut cur := t
      if let some ch := chC then
        let st : PathStep := { fn := fs, arity := 3, argIdx := 0, siblings := [a, b] }
        acc := some (← applyStep w e st c c' ch)
        cur := .cons (.atom (.symbol fs)) ([c', a, b].foldr .cons .nil)
      -- the test collapsed to a QUOTED CONSTANT (an in-scope litFact or fold
      -- resolved it): take the branch, exactly as if-interp does
      if let .cons (.atom (.symbol q)) (.cons cv .nil) := c' then
        if q.name == "QUOTE" then
          let (step, sel) ← mkConstTestCollapse cfg ctx c' cv a b
          let acc' ← chainAfter acc step
          let (chSel, final) ← collapseEval cfg ctx facts sel
          match chSel with
          | none => return (some acc', final)
          | some m => return (some (← mkAppM ``fuel_chain_eq #[acc', m]), final)
      match facts.find? (fun (T, _, _, _) => T == c') with
      | some (_, vT, sign, h) =>
        let hc ← ctxValProof cfg ctx c'
        let step ←
          if sign then
            let hcv ← mkAppM ``toBool_true_of_ne_nil #[h]
            let va ← ctxValExpr cfg ctx a
            let ha ← ctxValProof cfg ctx a
            let _ := va
            mkAppM ``re_if_true
              #[w, e, reflectSExpr c', reflectSExpr a, reflectSExpr b, vT, va, hc, hcv, ha]
          else
            let hcNil ← mkAppM ``re_val_cast
              #[w, e, reflectSExpr c', vT, mkConst ``SExpr.nil, hc, h]
            let vb ← ctxValExpr cfg ctx b
            let hb ← ctxValProof cfg ctx b
            let _ := vb
            mkAppM ``re_if_false
              #[w, e, reflectSExpr c', reflectSExpr a, reflectSExpr b, vb, hcNil, hb]
        let sel := if sign then a else b
        let acc' ← chainAfter acc step
        let (chSel, final) ← collapseEval cfg ctx facts sel
        match chSel with
        | none => return (some acc', final)
        | some m => return (some (← mkAppM ``fuel_chain_eq #[acc', m]), final)
      | none =>
        -- unresolved test: collapse both branches in place
        let (chA, a') ← collapseEval cfg ctx facts a
        if let some ch := chA then
          let st : PathStep := { fn := fs, arity := 3, argIdx := 1, siblings := [c', b] }
          let lifted ← applyStep w e st a a' ch
          acc := some (← chainAfter acc lifted)
          cur := .cons (.atom (.symbol fs)) ([c', a', b].foldr .cons .nil)
        let (chB, b') ← collapseEval cfg ctx facts b
        if let some ch := chB then
          let st : PathStep := { fn := fs, arity := 3, argIdx := 2, siblings := [c', a'] }
          let lifted ← applyStep w e st b b' ch
          acc := some (← chainAfter acc lifted)
          cur := .cons (.atom (.symbol fs)) ([c', a', b'].foldr .cons .nil)
        let _ := cur
        return (acc, .cons (.atom (.symbol fs)) ([c', a', b'].foldr .cons .nil))
    | _ => throwError "collapseEval: malformed if {repr t}"
  -- generic application: collapse arguments left-to-right, then head folds
  let mut curArgs := args.toArray
  let mut acc : Option Expr := none
  for i in [0:args.length] do
    let a := curArgs[i]!
    let (chA, a') ← collapseEval cfg ctx facts a
    if let some ch := chA then
      let siblings := (curArgs.toList.zipIdx.filterMap fun (x, j) =>
        if j == i then none else some x)
      let st : PathStep := { fn := fs, arity := args.length, argIdx := i, siblings }
      let lifted ← applyStep w e st a a' ch
      acc := some (← chainAfter acc lifted)
      curArgs := curArgs.set! i a'
  let cur : SExpr := .cons (.atom (.symbol fs)) (curArgs.toList.foldr .cons .nil)
  -- the POST-COLLAPSE term may be the form an in-scope assumption is about
  -- (argument collapse rebuilt it into another clause literal)
  if let some hNil := ctx.litFactByTerm? cur then
    let pl ← ctxValProof cfg ctx cur
    let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
    let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    let acc' ← chainAfter acc step
    return (some acc', quoteNil)
  -- call-stack folds (the enumerated rule set; extend ONLY with rules
  -- if-interp itself applies — rewrite.lisp:3671-3778)
  let fold? ← do
    -- cons-term's GROUND-PRIMITIVE fold: an argument-ground application of
    -- an UNDEFINED (builtin) head folds to its value — e.g. (CAR 'NIL) ⇒
    -- 'NIL (CAR-RM). Re-run the same closed computation (the
    -- exec-counterpart carve-out); user-fn heads stay in place (cons-term
    -- folds primitives only).
    if curArgs.all (fun a => match a with
        | .cons (.atom (.symbol q)) (.cons _ .nil) => q.name == "QUOTE"
        | _ => false) &&
       cfg.worldVal.defs.get? fs == none && fs.name != "NOT" then
      let mut F := 8
      let mut v? : Option SExpr := none
      while v?.isNone && F ≤ 65536 do
        v? := ACL2.evalOpt F cfg.worldVal {} cur
        if v?.isNone then F := F * 2
      match v? with
      | none => pure none  -- leave in place; downstream checks fail-closed
      | some v =>
        let foldedT : SExpr :=
          .cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)
        let p ← replayExecGround cfg cur v
        let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr v]
        pure (some (← mkAppM ``fuel_eq_of_conv
          #[p, pQ, ← mkEqRefl (reflectSExpr v)], foldedT))
    else if fs.name == "NOT" then
      match curArgs.toList with
      | [.cons (.atom (.symbol q)) (.cons cc .nil)] =>
        if q.name == "QUOTE" then
          let foldedV : SExpr := if cc == SExpr.nil then SExpr.t else SExpr.nil
          let foldedT : SExpr :=
            .cons (.atom (.symbol { name := "QUOTE" })) (.cons foldedV .nil)
          let pNot ← replayExecGround cfg cur foldedV
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr foldedV]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pNot, pQ, ← mkEqRefl (reflectSExpr foldedV)], foldedT))
        else pure none
      | _ => pure none
    else if fs.name == "EQUAL" then
      let isEqualApp : SExpr → Bool := fun t =>
        match t with
        | .cons (.atom (.symbol es)) (.cons _ (.cons _ .nil)) => es.name == "EQUAL"
        | _ => false
      match curArgs.toList with
      | [x, y] =>
        if x == y then
          let hX ← proveConv cfg e ctx x
          let hNoEqual ← proveNoShadow cfg { name := "EQUAL" }
          let pEq ← mkAppM ``re_equal_self #[w, e, reflectSExpr x, hX, hNoEqual]
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.t]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pEq, pQ, ← mkEqRefl (mkConst ``SExpr.t)], quoteT))
        else if y == quoteT && isEqualApp x then
          -- (equal (equal a b) 't) = (equal a b) — rewrite.lisp:3791
          let pl ← ctxValProof cfg ctx cur
          let pr ← ctxValProof cfg ctx x
          let .cons _ (.cons a (.cons b .nil)) := x
            | throwError "collapseEval: internal — isEqualApp shape"
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pl, pr, ← mkAppM ``logic_equal_equal_t_r #[va, vb]], x))
        else if x == quoteT && isEqualApp y then
          -- (equal 't (equal a b)) = (equal a b) — rewrite.lisp:3785
          let pl ← ctxValProof cfg ctx cur
          let pr ← ctxValProof cfg ctx y
          let .cons _ (.cons a (.cons b .nil)) := y
            | throwError "collapseEval: internal — isEqualApp shape"
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pl, pr, ← mkAppM ``logic_equal_equal_t_l #[va, vb]], y))
        else pure none
      | _ => pure none
    else pure none
  match fold? with
  | none => return (acc, cur)
  | some (stepPf, next) =>
    let acc' ← chainAfter acc stepPf
    return (some acc', next)



/-- Lift an `EvRel SIff` node proof through ONE position step, per the
    congruence table (G1): if-THEN and if-ELSE positions preserve SIff (the
    untaken branch relates by reflexivity — needs the test's and the other
    branch's convergence); the if-TEST position COLLAPSES SIff to an
    eval-equality (the lazy `if` consults only `toBool`), and so do the
    IMPLIES argument positions (boolean-consumer rows, G1 rung 1 inc-2).
    Returns the lifted proof and whether it is still SIff (`true`) or
    collapsed to Eq (`false`). Any other position under an iff payload is a
    frontier. -/
def applyStepSIff (cfg : ReplayConfig) (ctx : ReplayCtx) (st : PathStep)
    (inner : Expr) : MetaM (Expr × Bool) := do
  -- a composition that does not typecheck (e.g. a branch-congruence result fed
  -- into a test-collapse — a NESTED conditional structure) is the conditional-
  -- congruence frontier (R1 wall d, deferred — perm-is-an-equivalence); surface
  -- it as a CLEAN named frontier rather than leaking `mkAppM` metavariables.
  -- The original error is PRESERVED in the message: this is still a hard-fail
  -- (never a false pass), but if a FIXABLE bug (wrong sibling/order) — rather
  -- than the genuine wall-d nesting — caused the failure, its text stays visible
  -- so it is not silently misattributed to the deferred frontier.
  let wallD : Exception → MetaM Expr := fun e => do
    throwError "applyStepSIff: SIff branch-congruence composition unsupported for \
      this nesting at {st.fn.name}-position {st.argIdx} (conditional-congruence — \
      R1 wall d, deferred); underlying elaboration error: {e.toMessageData}"
  if st.fn.name == "IMPLIES" && st.arity == 2 then
    -- boolean-consumer COLLAPSE rows: `implies` consults only its
    -- arguments' truthiness — SIff in either argument makes the
    -- applications eval-EQUAL (needs the OTHER argument's convergence +
    -- the builtin's no-shadow fact).
    let hNo ← proveNoShadow cfg { name := "IMPLIES" }
    match st.argIdx, st.siblings with
    | 0, [c] =>
      let pc ← ctxValProof cfg ctx c
      let p ← (try mkAppM ``evrel_implies_arg1_siff_collapse #[hNo, pc, inner]
               catch e => wallD e)
      return (p, false)
    | 1, [h] =>
      let ph ← ctxValProof cfg ctx h
      let p ← (try mkAppM ``evrel_implies_arg2_siff_collapse #[hNo, ph, inner]
               catch e => wallD e)
      return (p, false)
    | _, _ => throwError "iff congruence: bad implies position {st.argIdx}"
  unless st.fn.name == "IF" && st.arity == 3 do
    throwError "iff congruence: position {st.fn.name}/{st.argIdx} does not \
                propagate IFF (frontier — only if-test/branch and implies \
                positions do)"
  match st.argIdx, st.siblings with
  | 0, [thn, els] =>
    -- TEST position: SIff collapses to eval-equality. `thn`/`els` occur only
    -- in the collapse lemma's RESULT type, so they cannot be inferred from
    -- `inner` — supply them explicitly from the path step's siblings (the
    -- former mkAppM metavariable failure here was misattributed to the
    -- wall-d nesting; the lemma is fully general in the tests).
    let p ← (try
      mkAppOptM ``evrel_if_test_siff_collapse
        #[none, none, none, none, some (reflectSExpr thn),
          some (reflectSExpr els), some inner]
      catch e => wallD e)
    return (p, false)
  | 1, [c, els] =>
    -- THEN position
    let pc ← ctxValProof cfg ctx c
    let pels ← ctxValProof cfg ctx els
    let p ← (try mkAppM ``evrel_if_then_congr #[mkConst ``siff_refl, pc, pels, inner]
             catch e => wallD e)
    return (p, true)
  | 2, [c, thn] =>
    -- ELSE position
    let pc ← ctxValProof cfg ctx c
    let pthn ← ctxValProof cfg ctx thn
    let p ← (try mkAppM ``evrel_if_else_congr #[mkConst ``siff_refl, pc, pthn, inner]
             catch e => wallD e)
    return (p, true)
  | _, _ => throwError "iff congruence: bad if position {st.argIdx}"

/-- The applied step's recorded equivalence relation. -/
def nodeEquiv : ProofNode → String | .node _ _ _ _ p => p.equiv

end ACL2.Replay.Driver
