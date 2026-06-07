/-
  Proof tree types and parser.

  Converts ACL2's flat proof trace (a list of TraceEvents) into a
  structured proof tree. The tree represents ACL2's proof at three
  levels: theorem → induction cases → literal simplifications.

  Each rewrite step is enriched with its IF branch decisions, turning
  the flat interleaving of IF-TEST and REWRITE-STEP events into
  per-step justifications.
-/
import ACL2Lean.Syntax
import ACL2Lean.ProofLog

namespace ACL2

/-! ## Proof tree types -/

/-- Provenance for a proof node: what justified this reasoning step. -/
structure StepProvenance where
  origin : String := ""
  runes : List (String × String) := []
  parents : List SExpr := []
  subst : List (SExpr × SExpr) := []
  equivTerm : Option SExpr := none
  /-- For a `rewriting-equivalence` (solidify) node: the index of the clause
      hypothesis literal whose (post-rewrite) equality justifies this step — the
      induction hypothesis, in an induction step case. Set by the clause-tree
      builder by matching `equivTerm` to a sibling literal's result (up to the
      equivalence relation's symmetry). `none` when not a solidify node, or when
      the source is a forward-chained/linear fact already named in `parents`. -/
  equivSource : Option Nat := none
  /-- Type-set of the argument (for recognizer steps, from ACL2's type-set engine). -/
  typeSet : Option Int := none
  /-- True type-set of the recognizer (bits where it returns T). -/
  trueTs : Option Int := none
  deriving Repr, Inhabited

inductive ProofNode where
  | node (rune : String × String) (lhs rhs : SExpr)
         (children : List ProofNode)
         (provenance : StepProvenance := {})
  deriving Repr, Inhabited

/-- Proof that a single literal simplifies to a result under clause
    assumptions. The nodes form a proof tree: top-level nodes are the
    main reasoning chain, and each node may contain sub-proofs. -/
structure LiteralProof where
  index : Nat
  literal : SExpr
  notFlg : Bool
  nodes : List ProofNode
  result : SExpr
  deriving Repr, Inhabited

/-- One item in a clause-level proof step's branch tree (ACL2's `:REWRITES`), in
    log order. A `literal` is one disjunct reduced via its rewrite chain; a `step`
    is a clause-level rewrite or branch substitution between literals; a `branch`
    is a case split (its `segment` is the clause segment) whose items are proved
    under that case. This is the structure a Lean replay folds over: recurse the
    branches (case analysis), apply substitutions, replay each literal's chain. -/
inductive ClauseItem where
  | literal (lp : LiteralProof)
  | step (node : ProofNode)
  | branch (segment : SExpr) (items : List ClauseItem)
  deriving Repr, Inhabited

/-! ## Parser: flat trace → rewriter-detail tree

    `ProofNode` / `LiteralProof` / `ClauseItem` and the builders below are the
    rewriter-detail layer that `ClauseTree` hangs off each SIMPLIFY clause node.
    The clause-level proof tree (theorem → induction → case subgoals) lives in
    `ClauseTree.lean`. Every known trace event is handled explicitly; the parser
    hard-fails on anything else (no silent drop). -/

/-- Build a `ProofNode` from a rewrite step and its (already-parsed) children. -/
private def rewriteStepNode (step : RewriteStep) (children : List ProofNode) : ProofNode :=
  .node step.rune step.lhs step.rhs children
    { origin := step.origin, runes := step.runes, parents := step.parents,
      subst := step.subst, equivTerm := step.equivTerm,
      typeSet := step.typeSet, trueTs := step.trueTs }

/-- Parse the events of ONE literal's rewrite chain into proof nodes, returning
    the nodes and the events after this block. `BEGIN/END-INNER-REWRITE` and
    `BEGIN/END-IF-REWRITE` delimit a child block (its nodes become children of
    the next rewrite step). Every known in-literal event is handled; anything
    else hard-fails. -/
partial def parseProofNodesAux (events : List TraceEvent)
    (pendingChildren : List ProofNode) (nodes : List ProofNode)
    : Except String (List ProofNode × List TraceEvent) := do
  -- `pendingChildren` are inner-rewrite-block nodes awaiting the rewrite step
  -- that adopts them as children. At every return we FLUSH them onto the result
  -- (`nodes.reverse ++ pendingChildren`): if no rewrite step adopted them — a
  -- bare clause-level chain that ends inside an inner block — they are real
  -- steps and become standalone nodes, never dropped. (Normally `pendingChildren`
  -- is already empty at a return, so the flush is a no-op.)
  match events with
  | [] => return (nodes.reverse ++ pendingChildren, [])
  | .beginInnerRewrite _ :: rest | .beginIfRewrite _ _ :: rest =>
      let (innerNodes, rest') ← parseProofNodesAux rest [] []
      parseProofNodesAux rest' (pendingChildren ++ innerNodes) nodes
  | .endInnerRewrite _ :: rest | .endIfRewrite _ _ :: rest =>
      return (nodes.reverse ++ pendingChildren, rest)
  | .rewriteStep step :: rest =>
      parseProofNodesAux rest [] (rewriteStepNode step pendingChildren :: nodes)
  | .typeSetReasoning term result _ _ :: rest =>
      -- a term closed by type-set reasoning (e.g. a literal forced true/false)
      parseProofNodesAux rest [] (.node ("type-set", "") term result pendingChildren {} :: nodes)
  | .branchSubstitution equiv lhs rhs :: rest =>
      parseProofNodesAux rest []
        (.node ("branch-substitution", "") lhs rhs pendingChildren { equivTerm := equiv } :: nodes)
  | .contextSubst var value _ :: rest =>
      parseProofNodesAux rest [] (.node ("context-subst", "") var value pendingChildren {} :: nodes)
  | .ifTestTrue _ _ _ :: rest | .ifTestFalse _ _ _ :: rest | .ifTestUnknown _ _ _ :: rest =>
      -- IF-test markers delimit the if-rewrite block; not standalone nodes.
      parseProofNodesAux rest pendingChildren nodes
  | .rewrittenLiteral _ _ :: rest =>
      -- the literal's net result, captured separately by findLiteralResult.
      parseProofNodesAux rest pendingChildren nodes
  | .beginLiteral _ _ _ :: _ | .endLiteral _ _ _ :: _ | .beginBranch _ :: _
  | .endBranch :: _ | .caseSplit _ _ :: _ =>
      -- A clause-structure boundary: stop and hand the remaining events back to
      -- the clause-level parser. (This match is exhaustive over TraceEvent, so a
      -- new event kind becomes a compile error here — never a silent drop.)
      return (nodes.reverse ++ pendingChildren, events)

/-- Parse a literal's rewrite chain into proof nodes. Hard-fails if any
    clause-structure event is left unconsumed (a literal should not contain a
    branch/literal boundary). -/
def buildProofNodes (events : List TraceEvent) : Except String (List ProofNode) := do
  let (nodes, rest) ← parseProofNodesAux events [] []
  if !rest.isEmpty then
    throw s!"buildProofNodes: unexpected clause-structure event inside a literal: {repr rest.head?}"
  return nodes

/-- Collect events for a single literal from the trace. Returns events
    between BEGIN-LITERAL and END-LITERAL, and the remaining events.
    Uses a fuel bound to ensure termination. -/
private def collectLiteralEvents (index : Nat) (events : List TraceEvent)
    (fuel : Nat) : List TraceEvent × List TraceEvent :=
  match fuel, events with
  | 0, rest => ([], rest)
  | _, [] => ([], [])
  | fuel + 1, .endLiteral idx _ _ :: rest =>
      if idx == index then ([], rest)
      else
        let (inner, remaining) := collectLiteralEvents index rest fuel
        (.endLiteral idx .nil 0 :: inner, remaining)
  | fuel + 1, ev :: rest =>
      let (inner, remaining) := collectLiteralEvents index rest fuel
      (ev :: inner, remaining)

/-- Find the rewritten result for a literal from its trace events.
    Looks for a REWRITTEN-LITERAL event; falls back to the original. -/
private def findLiteralResult (events : List TraceEvent) (original : SExpr) : SExpr :=
  events.foldl (fun acc ev =>
    match ev with
    | .rewrittenLiteral _ result => result
    | .typeSetReasoning _ result _ _ => result
    | _ => acc) original

/-- Parse a clause-level event list (ACL2's `:REWRITES`) into its branch tree, in
    log order, returning the items and the events after this branch. A
    `BEGIN-BRANCH`/`END-BRANCH` pair is a case split; `BEGIN-LITERAL`/
    `END-LITERAL` is one literal reduced via its chain; rewrite-steps and branch
    substitutions between literals are clause-level `step` items. Hard-fails on
    any other clause-level event (no silent drop). -/
partial def parseClauseItems (events : List TraceEvent)
    : Except String (List ClauseItem × List TraceEvent) := do
  match events with
  | [] => return ([], [])
  | .endBranch :: rest => return ([], rest)
  | .beginBranch segment :: rest =>
      let (inner, rest') ← parseClauseItems rest
      let (more, rest'') ← parseClauseItems rest'
      return (.branch segment inner :: more, rest'')
  | .beginLiteral index literal notFlg :: rest =>
      let (litEvents, rest') := collectLiteralEvents index rest (rest.length + 1)
      let nodes ← buildProofNodes litEvents
      let litResult := findLiteralResult litEvents literal
      let (more, rest'') ← parseClauseItems rest'
      return (.literal ⟨index, literal, notFlg, nodes, litResult⟩ :: more, rest'')
  | _ =>
      -- A clause-level rewrite chain not wrapped in a literal — e.g. a
      -- termination conjecture being simplified, or the inter-literal ground
      -- rewrites / branch substitutions inside a branch. Parse the maximal
      -- rewrite-chain prefix (stops at the next literal/branch boundary) and
      -- emit each node as a clause-level `step`.
      let (nodes, rest) ← parseProofNodesAux events [] []
      if rest.length == events.length then
        throw s!"parseClauseItems: no progress on clause-level event {repr events.head?}"
      let (more, rest') ← parseClauseItems rest
      return (nodes.map ClauseItem.step ++ more, rest')

/-- Build the branch tree (`ClauseItem`s) for one clause-level proof step. -/
def buildClauseItems (events : List TraceEvent) : Except String (List ClauseItem) := do
  let (items, _) ← parseClauseItems events
  return items

end ACL2
