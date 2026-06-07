/-
  Clause-level proof tree — the retrofitted "proof object".

  ACL2 has no proof object; the closest thing it emits is its waterfall, a tree
  of CLAUSES each processed by a sequence of processors (preprocess, simplify,
  settled-down, push, fertilize, generalize, eliminate-destructors, …). The
  proof log records one `:STEP` per (clause, processor) with the clause's
  `:CLAUSEID`, `:INPUTCLAUSE`, `:RESULT`, `:NEWCLAUSES`, and (for SIMPLIFY) the
  rewriter trace events. This module reconstructs that tree DETERMINISTICALLY
  from the clause-id lineage — never by guessing.

  The clause-id child rule (ACL2 `prove.lisp`, `waterfall1-lst`) is:
  - a processor leaving ONE clause  → child id = parent with primes+1
  - a processor splitting into N     → children = parent with case-lst ++ [k]
                                       (k from N down to 1), primes 0
  - `settled-down-clause` / initial   → id unchanged
  So the PARENT of a node is the inverse: drop a prime, or drop the last
  case-lst element (landing on the most-simplified clause that split).

  Induction is the one place ACL2's log is implicit: a `PUSH-CLAUSE` defers a
  clause to the pool, then an `:INDUCTION` event splits it. ACL2 does not log
  the pool root (`*1`) as a step, so we SYNTHESIZE it from the push→induct
  adjacency and make it the parent of the `*1/k` case subgoals.

  Anything we cannot link (an orphan node, an induction with no pushed clause)
  is a hard error, surfaced — not papered over.
-/
import ACL2Lean.ClauseId
import ACL2Lean.ProofTree

namespace ACL2

/-- One processor applied to a clause: a single `:STEP` record. -/
structure WaterfallStep where
  processor : String
  result : ProofResult
  runes : List (String × String)
  newClauses : List SExpr
  /-- Rewriter detail, present only for SIMPLIFY-CLAUSE steps (the per-literal
      rewrite sub-trees). Empty for every other processor. -/
  literalProofs : List LiteralProof
  deriving Repr, Inhabited

/-- A node of the reconstructed clause tree: one clause (addressed by its
    clause-id), the processors applied to it in order, an optional induction
    applied here (whose subgoals are this node's children), and the child
    clauses. -/
structure ClauseNode where
  id : ClauseId
  idStr : String
  inputClause : List SExpr
  steps : List WaterfallStep
  induction : Option InductionStep
  children : List ClauseNode
  deriving Repr, Inhabited

/-- A theorem's reconstructed proof: its name, formula, and the root clause
    node (`Goal`). `root` is `none` for an imported theorem with no logged
    proof. -/
structure ClauseProof where
  name : String
  formula : SExpr
  root : Option ClauseNode
  deriving Repr, Inhabited

namespace ClauseTree

/-- A flat node before tree assembly: its parsed id, the printed id, the input
    clause, the steps applied, and any induction synthesized at this id. -/
private structure FlatNode where
  id : ClauseId
  idStr : String
  inputClause : List SExpr
  steps : Array WaterfallStep
  induction : Option InductionStep := none
  synthetic : Bool := false   -- true for synthesized induction pool roots
  deriving Inhabited

/-- The structural parent id of a node, per the inverse of `waterfall1-lst`.
    `allIds` is the set of node ids actually present (needed to pick the
    splitter — the most-simplified clause that produced a case split). Returns
    `none` for the root `Goal` and for pool roots (linked separately via the
    induction). -/
private def parentId (allIds : List ClauseId) (id : ClauseId) : Option ClauseId :=
  if id.primes > 0 then
    some { id with primes := id.primes - 1 }
  else if !id.caseLst.isEmpty then
    -- The splitter has the same forcing-round/pool and the case-lst with its
    -- last element dropped; among those, ACL2 split from the most-simplified
    -- one (max primes).
    let parentCase := id.caseLst.dropLast
    let cands := allIds.filter fun k =>
      k.forcingRound == id.forcingRound && k.poolLst == id.poolLst
        && k.caseLst == parentCase
    cands.foldl (fun acc k =>
      match acc with
      | none => some k
      | some a => if k.primes > a.primes then some k else acc) none
  else
    -- primes 0, no case-lst: either the root Goal (no pool) or a pool root
    -- (linked via the induction, not here).
    none

/-! ### Linking solidify (rewriting-equivalence) nodes to the hypothesis used

A `rewriting-equivalence` node rewrites a term using an equivalence assumed in
the clause context — in an induction step case, the induction hypothesis. ACL2
logs `:PARENTS NIL` for assumptions that are whole clause hypotheses (only
forward-chained/linear facts get `'pt` parents; see the notes). We recover the
link deterministically: the node's `equivTerm` equals, up to the equivalence
relation's symmetry, the (post-rewrite) result of a sibling clause literal. -/

/-- Peel a leading `(not X)`. -/
private def peelNot (e : SExpr) : Option SExpr :=
  match e.toList? with
  | some [h, x] => match h with
    | .atom (.symbol s) => if s.name.toLower == "not" then some x else none
    | _ => none
  | _ => none

/-- View `(equiv a b)` as `(equiv, a, b)`. -/
private def asBinApp (e : SExpr) : Option (SExpr × SExpr × SExpr) :=
  match e.toList? with
  | some [h, a, b] => some (h, a, b)
  | _ => none

/-- Two equivalence terms match iff same relation and same operands up to swap
    (valid by the symmetry of any equivalence relation). -/
private def equivMatch (e1 e2 : SExpr) : Bool :=
  match asBinApp e1, asBinApp e2 with
  | some (h1, a1, b1), some (h2, a2, b2) =>
    h1 == h2 && ((a1 == a2 && b1 == b2) || (a1 == b2 && b1 == a2))
  | _, _ => false

/-- The equivalence a clause literal contributes as an available hypothesis:
    if its (rewritten) result is `(not (equiv a b))`, the assumption `(equiv a b)`
    holds. -/
private def hypEquiv (lp : LiteralProof) : Option SExpr :=
  match peelNot lp.result with
  | some e => match asBinApp e with | some _ => some e | none => none
  | none => none

/-- Set `equivSource` on every `rewriting-equivalence` node in this proof-node
    tree by matching its `equivTerm` against the candidate hypotheses
    `(literalIndex, equiv)`. Hard-fails on a solidify with no matching
    hypothesis (and no `'pt` parents) — the detectable frontier. -/
private partial def linkNode (cands : List (Nat × SExpr)) (n : ProofNode)
    : Except String ProofNode := do
  match n with
  | .node rune lhs rhs children prov =>
    let children ← children.mapM (linkNode cands)
    if rune.1 == "rewriting-equivalence" && prov.parents.isEmpty then
      match prov.equivTerm with
      | some e =>
        match cands.find? (fun (_, c) => equivMatch e c) with
        | some (idx, _) =>
          return .node rune lhs rhs children { prov with equivSource := some idx }
        | none =>
          throw s!"ClauseTree: rewriting-equivalence node {repr e} matches no clause \
                   hypothesis (assume-true-false-decomposed source? needs the producer \
                   source-tag at simplify.lisp:5012)"
      | none => return .node rune lhs rhs children prov
    else
      return .node rune lhs rhs children prov

/-- Within one SIMPLIFY step, link each literal's solidify nodes to the OTHER
    literals' hypotheses (a literal cannot justify rewriting itself — matching
    ACL2's parent-tree loop-avoidance). -/
private def linkEquivSources (lps : List LiteralProof) : Except String (List LiteralProof) := do
  let mut out : Array LiteralProof := #[]
  for lp in lps do
    let cands : List (Nat × SExpr) :=
      lps.filterMap fun other =>
        if other.index == lp.index then none
        else (hypEquiv other).map (fun e => (other.index, e))
    let nodes ← lp.nodes.mapM (linkNode cands)
    out := out.push { lp with nodes := nodes }
  return out.toList

/-- Find the index of the flat node with the given printed id. -/
private def findIdx (flats : Array FlatNode) (idStr : String) : Option Nat :=
  flats.findIdx? (·.idStr == idStr)

/-- Collect the steps and inductions of a single theorem from the event list,
    in order. Returns the flat nodes (one per distinct clause-id, steps merged)
    plus the (pushed-clause-id, induction) pairs in occurrence order. Fails if a
    clause-id does not parse (no silent skip). -/
private def collectFlat (events : List ProofEvent)
    : Except String (Array FlatNode × Array (String × InductionStep)) := do
  let mut flats : Array FlatNode := #[]
  let mut inductions : Array (String × InductionStep) := #[]
  let mut lastPush : Option String := none
  for ev in events do
    match ev with
    | .step s =>
      let wstep : WaterfallStep := {
        processor := s.processor, result := s.result, runes := s.runes,
        newClauses := s.newClauses,
        literalProofs := ← linkEquivSources (buildLiteralProofs s.traceEvents) }
      match findIdx flats s.clauseId with
      | some i =>
        flats := flats.modify i (fun fn => { fn with steps := fn.steps.push wstep })
      | none =>
        let cid ← ClauseId.parse s.clauseId
        flats := flats.push {
          id := cid, idStr := s.clauseId, inputClause := s.inputClause,
          steps := #[wstep] }
      if s.processor.toLower == "push-clause" then
        lastPush := some s.clauseId
    | .induction i =>
      inductions := inductions.push (lastPush.getD "", i)
    | _ => pure ()
  return (flats, inductions)

/-- Synthesize the induction pool-root nodes (`*1`, `*1.1`, …) that ACL2 does
    not log as steps. The m-th induction whose pushed clause sits at pool-lst P
    creates a pool root at P ++ [m]; it becomes a child of the pushed clause and
    parent of the `*P++[m]/k` case subgoals. Returns the synthetic nodes paired
    with their pushed-parent id. Fails if an induction has no pushed clause. -/
private def synthesizePoolRoots (logged : Array FlatNode)
    (inductions : Array (String × InductionStep))
    : Except String (Array (FlatNode × String)) := do
  let mut out : Array (FlatNode × String) := #[]
  -- Count, per parent pool-lst, how many inductions have fired so far.
  let mut counts : Array (List Nat × Nat) := #[]
  for (pid, ind) in inductions do
    if pid.isEmpty then
      throw "ClauseTree: :INDUCTION with no preceding PUSH-CLAUSE"
    let pcid ← ClauseId.parse pid
    let key := pcid.poolLst
    let m := (counts.find? (·.1 == key)).map (·.2) |>.getD 0
    counts := (counts.filter (·.1 != key)).push (key, m + 1)
    let poolLst := key ++ [m + 1]
    let idStr := "*" ++ String.intercalate "." (poolLst.map toString)
    -- The pool goal IS the clause that was pushed; recover its clause from the
    -- pushed (parent) node so the synthesized node shows the goal being proved
    -- by induction rather than a placeholder.
    let pushClause ← match logged.find? (·.idStr == pid) with
      | some pushNode => pure pushNode.inputClause
      | none => throw s!"ClauseTree: pushed clause {repr pid} for :INDUCTION not found in log"
    let node : FlatNode := {
      id := { forcingRound := pcid.forcingRound, poolLst := poolLst },
      idStr := idStr, inputClause := pushClause, steps := #[],
      induction := some ind, synthetic := true }
    out := out.push (node, pid)
  return out

/-- Assemble the subtree rooted at the node with id `key`. Children are kept in
    the order the clauses appear in the log — ACL2's own emit/processing order
    (`*1/N … *1/1`) — so the tree mirrors ACL2 rather than imposing a re-sort.
    A missing key is a hard error (the linking is supposed to be total). -/
private partial def assemble (flats : Array FlatNode)
    (childKeys : Array (String × String)) (key : String) : Except String ClauseNode := do
  match (findIdx flats key).bind (flats[·]?) with
  | none => throw s!"ClauseTree: assemble found no node for key {repr key}"
  | some fn =>
    let kids := childKeys.filterMap (fun (c, p) => if p == key then some c else none)
    let children ← kids.toList.mapM (assemble flats childKeys)
    return {
      id := fn.id, idStr := fn.idStr, inputClause := fn.inputClause,
      steps := fn.steps.toList, induction := fn.induction, children := children }

/-- Build the clause tree for one theorem's events. -/
private def buildOne (name : String) (formula : SExpr) (events : List ProofEvent)
    : Except String ClauseProof := do
  let (logged, inductions) ← collectFlat events
  if logged.isEmpty then
    return { name, formula, root := none }
  let synth ← synthesizePoolRoots logged inductions
  let allFlats := logged ++ synth.map (·.1)
  let allIds := (allFlats.map (·.id)).toList
  -- Parent key for each node: synthetic → its pushed clause; logged → inverse
  -- of the waterfall child rule. Root Goal has none.
  let mut childKeys : Array (String × String) := #[]   -- (childIdStr, parentIdStr)
  let mut roots : Array String := #[]
  for (sn, pid) in synth do
    childKeys := childKeys.push (sn.idStr, pid)
  for fn in logged do
    if fn.id.isRoot then
      roots := roots.push fn.idStr
    else match parentId allIds fn.id with
      | some pcid =>
        match allFlats.find? (·.id == pcid) with
        | some pfn => childKeys := childKeys.push (fn.idStr, pfn.idStr)
        | none => throw s!"ClauseTree: no parent node for {repr fn.idStr} (wanted {repr pcid})"
      | none =>
        throw s!"ClauseTree: orphan clause {repr fn.idStr} (no structural parent)"
  if roots.size != 1 then
    throw s!"ClauseTree: expected exactly one root Goal, found {roots.size} ({repr roots.toList})"
  return { name, formula, root := some (← assemble allFlats childKeys roots[0]!) }

/-- Close the current event block into a `ClauseProof`. A block with a `:DEFTHM`
    name is that theorem's proof. A block with proof steps but NO name is an
    admission/termination proof (these precede their `:DEFUN`, so the name is not
    yet known) — surface it as an anonymous proof rather than silently dropping
    it (the no-skip rule; this is also where measure/termination proofs live).
    Returns the proof (if any) and the updated anonymous-proof counter. -/
private def closeBlock (name : Option String) (formula : SExpr)
    (events : Array ProofEvent) (anon : Nat)
    : Except String (Option ClauseProof × Nat) := do
  match name with
  | some n => return (some (← buildOne n formula events.toList), anon)
  | none =>
    if events.any (fun | .step _ => true | _ => false) then
      return (some (← buildOne s!"<admission/termination proof {anon + 1}>" .nil events.toList),
              anon + 1)
    else
      return (none, anon)

/-- Build the reconstructed clause proof for every theorem (and admission proof)
    in a proof log. Walks the event stream, slicing it at each `:DEFTHM`/`:QED`. -/
def buildClauseProofs (log : ProofLog) : Except String (List ClauseProof) := do
  let mut out : Array ClauseProof := #[]
  let mut curName : Option String := none
  let mut curFormula : SExpr := .nil
  let mut curEvents : Array ProofEvent := #[]
  let mut anon : Nat := 0
  for ev in log.events do
    match ev with
    | .defthm name formula _ =>
      let (p?, a) ← closeBlock curName curFormula curEvents anon
      anon := a
      if let some p := p? then out := out.push p
      curName := some name; curFormula := formula; curEvents := #[]
    | .qed =>
      let (p?, a) ← closeBlock curName curFormula curEvents anon
      anon := a
      if let some p := p? then out := out.push p
      curName := none; curFormula := .nil; curEvents := #[]
    | other => curEvents := curEvents.push other
  let (p?, _) ← closeBlock curName curFormula curEvents anon
  if let some p := p? then out := out.push p
  return out.toList

end ClauseTree

/-! ## Tests — the reconstructed clause tree of `my-len-my-app`. -/
section Tests

private def simpleLog : String := include_str "../acl2_samples/simple.proof-log"

private def simpleProof : Option ClauseProof := do
  let log ← (ProofLog.parse simpleLog).toOption
  (ClauseTree.buildClauseProofs log).toOption.bind (·.head?)

/-- All clause nodes in a subtree (pre-order). -/
private partial def clauseNodes (n : ClauseNode) : List ClauseNode :=
  n :: n.children.flatMap clauseNodes

/-- Every rewriter proof-node reachable from a clause proof (across all steps,
    all literals, recursively). -/
private partial def proofNodesOf : ProofNode → List ProofNode
  | n@(.node _ _ _ cs _) => n :: cs.flatMap proofNodesOf

private def allProofNodes (cp : ClauseProof) : List ProofNode :=
  match cp.root with
  | none => []
  | some r => (clauseNodes r).flatMap fun n =>
      n.steps.flatMap fun s => s.literalProofs.flatMap fun lp => lp.nodes.flatMap proofNodesOf

private def runeOf : ProofNode → String × String | .node r _ _ _ _ => r
private def equivSrcOf : ProofNode → Option Nat | .node _ _ _ _ p => p.equivSource

-- The theorem and its root clause.
#guard (simpleProof.map (·.name)) == some "my-len-my-app"
#guard (simpleProof.bind (·.root) |>.map (·.idStr)) == some "Goal"

-- A synthesized induction node (`*1`) with two case subgoals.
#guard (simpleProof.bind (·.root) |>.map fun r =>
  (clauseNodes r).any fun n => n.induction.isSome && n.children.length == 2) == some true

-- Both induction subgoals are present (base *1/2 and step *1/1).
#guard (simpleProof.bind (·.root) |>.map fun r =>
  let ids := (clauseNodes r).map (·.idStr)
  ids.contains "Subgoal *1/1" && ids.contains "Subgoal *1/2") == some true

-- The rewriter detail is attached: my-app / my-len definition unfoldings appear.
#guard (simpleProof.map fun p =>
  (allProofNodes p).any (runeOf · == ("definition", "my-app"))) == some true
#guard (simpleProof.map fun p =>
  (allProofNodes p).any (runeOf · == ("definition", "my-len"))) == some true

-- The induction hypothesis link (R-A): a solidify node is justified by
-- hypothesis literal 2 in the step case.
#guard (simpleProof.map fun p =>
  (allProofNodes p).any (equivSrcOf · == some 2)) == some true

end Tests

end ACL2
