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

/-- Why an IF branch decision was made. -/
inductive BranchJustification where
  | clauseAssumption   -- test's truth follows from a negated clause literal
  | typeSet            -- test's truth follows from type reasoning
  | rewrittenConstant  -- test rewrote to a constant ('T or 'NIL)
  | unknown            -- justification not captured
  deriving Repr, BEq, Inhabited

/-- A branch decision made during IF processing inside a rewrite step. -/
inductive BranchDecision where
  | true (test : SExpr) (justification : BranchJustification)
  | false (test : SExpr) (justification : BranchJustification)
  deriving Repr, BEq, Inhabited

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

/-! ## Parser: flat trace → proof tree

    This module provides the rewriter-detail layer — `ProofNode` / `LiteralProof`
    and the builders below — which `ClauseTree` consumes as the per-literal
    rewrite sub-trees hanging off SIMPLIFY clause nodes. The clause-level proof
    tree (theorem → induction → case subgoals) lives in `ClauseTree.lean`. -/

/-- Map an IF-TEST justification SExpr to a BranchJustification. -/
private def parseBranchJustification (j : SExpr) : BranchJustification :=
  match j with
  | .atom (.keyword "rewritten-to-constant") => .rewrittenConstant
  | .atom (.keyword "type-set") => .typeSet
  | .atom (.keyword "clause") => .clauseAssumption
  | _ => .unknown

/-- Recursively parse a flat event list into a proof tree.
    Returns the parsed nodes and any remaining (unconsumed) events.

    The tree structure comes from BEGIN/END-INNER-REWRITE markers:
    events inside a BEGIN/END block become children of the next
    REWRITE-STEP at the enclosing level.

    Uses a fuel parameter for termination. -/
private def parseProofNodesAux (fuel : Nat) (events : List TraceEvent)
    (pendingChildren : List ProofNode) (nodes : List ProofNode)
    : List ProofNode × List TraceEvent :=
  match fuel with
  | 0 => (nodes.reverse, events)
  | fuel + 1 =>
    match events with
    | [] => (nodes.reverse, [])
    | .beginInnerRewrite _ :: rest =>
        let (innerNodes, rest') := parseProofNodesAux fuel rest [] []
        parseProofNodesAux fuel rest' (pendingChildren ++ innerNodes) nodes
    | .endInnerRewrite _ :: rest =>
        (nodes.reverse, rest)
    | .beginIfRewrite _ _ :: rest =>
        let (innerNodes, rest') := parseProofNodesAux fuel rest [] []
        parseProofNodesAux fuel rest' (pendingChildren ++ innerNodes) nodes
    | .endIfRewrite _ _ :: rest =>
        (nodes.reverse, rest)
    | .rewriteStep step :: rest =>
        let prov : StepProvenance := {
          origin := step.origin
          runes := step.runes
          parents := step.parents
          subst := step.subst
          equivTerm := step.equivTerm
          typeSet := step.typeSet
          trueTs := step.trueTs
        }
        let node := .node step.rune step.lhs step.rhs pendingChildren prov
        parseProofNodesAux fuel rest [] (node :: nodes)
    | .ifTestTrue _ _ _ :: rest | .ifTestFalse _ _ _ :: rest
    | .ifTestUnknown _ _ _ :: rest =>
        parseProofNodesAux fuel rest pendingChildren nodes
    | _ :: rest =>
        parseProofNodesAux fuel rest pendingChildren nodes

/-- Parse a flat event list into a proof tree using BEGIN/END-INNER-REWRITE
    markers for tree structure. Events inside a BEGIN/END block become
    children of the next REWRITE-STEP at the enclosing level. -/
def buildProofNodes (events : List TraceEvent) : List ProofNode × List TraceEvent :=
  parseProofNodesAux (events.length + 1) events [] []

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
    | _ => acc) original

/-- Build LiteralProofs from a flat event list. Extracts events between
    BEGIN-LITERAL/END-LITERAL boundaries and converts each to a
    LiteralProof with JustifiedSteps. -/
def buildLiteralProofs (events : List TraceEvent) : List LiteralProof := Id.run do
  let mut result : Array LiteralProof := #[]
  let mut remaining := events
  let mut fuel := events.length + 1  -- termination bound
  while remaining.length > 0 && fuel > 0 do
    fuel := fuel - 1
    match remaining with
    | .beginLiteral index literal notFlg :: rest =>
      let (litEvents, rest') := collectLiteralEvents index rest (rest.length + 1)
      let (nodes, _) := buildProofNodes litEvents
      let litResult := findLiteralResult litEvents literal
      result := result.push ⟨index, literal, notFlg, nodes, litResult⟩
      remaining := rest'
    | _ :: rest => remaining := rest
    | [] => break
  return result.toList

end ACL2
