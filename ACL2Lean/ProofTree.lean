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

/-- Where a `rewriting-equivalence` (solidify) node's equivalence hypothesis
    lives. Both kinds reach ACL2's rewriter through the same type-alist, so
    the LOG does not discriminate them — the clause-tree builder does, by
    deterministic matching (literal results first, then the node's `:PATH`
    if-branch frames). -/
inductive EquivSource where
  /-- A clause hypothesis: literal `idx`'s (post-rewrite) result is
      `(not (equiv a b))`, so the spine branch assumes `(equiv a b)` —
      the induction hypothesis, in an induction step case. -/
  | literal (idx : Nat)
  /-- An ENCLOSING UNRESOLVED-IF's test, assumed true/false in the branch the
      node's `:PATH` descends through (ACL2's assume-true-false). Replay needs
      conditional congruence through if-branch positions — R1 of the
      sorting-corpus roadmap. -/
  | branchTest
  /-- An enclosing CLAUSIFY-BRANCH's segment literal `(not (equiv a b))` —
      the hypothesis ACL2's `:CONTEXT-SUBST` substitutes with inside that
      branch (clause-lst branch context). Replay needs branch-segment facts
      in scope — R1 of the sorting-corpus roadmap. -/
  | segment
  /-- TYPE-SET-DERIVED under the enclosing branch/segment facts (J6,
      induction-generality arc): ACL2's rewriter believed the equivalence by
      type-set reasoning — verdict-class, `:PARENTS NIL`, no recorded
      derivation (e.g. both sides reduce to NIL under a `(NOT (CONSP …))`
      segment fact, msort/bsort). The replay must discharge the equiv-term's
      truth from the in-scope branch facts at the VALUE level (the ratified
      carve-out's class) — a named replay frontier until that recipe lands. -/
  | typeSetDerived
  deriving Repr, Inhabited, BEq

/-- Provenance for a proof node: what justified this reasoning step. -/
structure StepProvenance where
  origin : String := ""
  /-- The applied rule's equivalence relation ("equal" unless emitted
      otherwise) — non-"equal" steps route through the R-parameterized
      judgment (G1) or fail closed. -/
  equiv : String := "equal"
  /-- For a rewrite-step node (B2): the CUMULATIVE ttree rune set on entry, NOT
      this step's rule — the rule is the node's own `rune`. For a `type-set`
      node: the per-step justification runes. A replay must not read this as the
      single rule applied here (use the node's rune for that). -/
  runes : List Rune := []
  parents : List SExpr := []
  subst : List (SExpr × SExpr) := []
  equivTerm : Option SExpr := none
  /-- For a `hyp-relief` marker (free-type-alist origin): the matched
      type-alist ENTRY's ttree runes — the provenance of a DERIVED entry
      (e.g. forward-chaining; emission arc 2026-07-21). -/
  taRunes : List Rune := []
  /-- For a `rewriting-equivalence` (solidify) node: the source of the
      equivalence hypothesis (see `EquivSource`). Set by the clause-tree
      builder by matching `equivTerm` to a sibling literal's result (up to the
      equivalence relation's symmetry), falling back to the `:PATH`'s
      if-branch frames. `none` when not a solidify node, or when the source is
      a forward-chained/linear fact already named in `parents`. -/
  equivSource : Option EquivSource := none
  /-- Type-set of the argument (for recognizer steps, from ACL2's type-set engine). -/
  typeSet : Option Int := none
  /-- True type-set of the recognizer (bits where it returns T). -/
  trueTs : Option Int := none
  /-- The redex's congruence path within the literal (from `:PATH`),
      literal-root-first — see `PathFrame`. The replay lifts this node by composing
      congruences along the path rather than locating the redex by subterm match. -/
  path : List PathFrame := []
  /-- The `:KIND` of the inner-rewrite block this node arrived in ("HYP" =
      hypothesis-relief chain of the adopting rewrite step, "RHS" = its
      instantiated-rhs continuation, "BODY"/"EXPANSION" = a definition body;
      "" = not from an inner block). Set on the block's TOP-LEVEL nodes only —
      the rule-application recipe partitions children by it. -/
  innerKind : String := ""
  deriving Repr, Inhabited

inductive ProofNode where
  | node (rune : Rune) (lhs rhs : SExpr)
         (children : List ProofNode)
         (provenance : StepProvenance := {})
  deriving Repr, Inhabited

/-- One literal-clausify DECISION-TRACE item (partial logging,
    `emit/if-interp/*` — docs/notes/2026-07-03_branch-split-spine.md): the
    decision skeleton of the assume-true-false split `rewrite-clause` performs
    on a rewritten literal. `path` is the tests split so far, outermost-first,
    as (assumed-true?, test). Justifications are deliberately not recorded —
    the replay re-derives them fail-closed. -/
inductive SplitDecision where
  /-- An if-test decision: `verdict` ∈ split/true/false, `how` ∈
      constant/assumed/split. -/
  | test (test : SExpr) (verdict : String) (how : String)
      (path : List (Bool × SExpr))
  /-- A path's leaf: `outcome` ∈ dropped/segment-false/segment-open.
      `segment` (segment-* outcomes only) is the EMITTED clause segment ACL2
      constructed for this leaf — the exact leaf→child-clause link. -/
  | leaf (value : SExpr) (outcome : String) (path : List (Bool × SExpr))
      (segment : Option (List SExpr))
  deriving Repr, Inhabited, BEq

/-- Proof that a single literal simplifies to a result under clause
    assumptions. The nodes form a proof tree: top-level nodes are the
    main reasoning chain, and each node may contain sub-proofs. -/
structure LiteralProof where
  index : Nat
  literal : SExpr
  notFlg : Bool
  nodes : List ProofNode
  result : SExpr
  /-- The literal's clausify decision trace (see `SplitDecision`), log order. -/
  splitTrace : List SplitDecision := []
  /-- Fired-markers: a clausify post-pass (Satriani / subsumption loop)
      RESHAPED the segment set — a replay consuming the decision trace must
      hard-fail when this is non-empty. -/
  splitReshaped : List String := []
  deriving Repr, Inhabited

/-- One `expand-and-or` firing inside clausification (emit/clausify/expand,
    S1-enriched): a complete instruction FROM ⇒ TO under polarity `pos`,
    justified by `runes` (the ttree delta — may be EMPTY when the fired
    rune was already in the incoming ttree; the def-body bridge keys on
    the FROM head's unique unfold with TO as the checked target). -/
structure ClausifyExpansion where
  fromTerm : SExpr
  toTerm : SExpr
  pos : Bool
  runes : List Rune
  deriving Repr, Inhabited

/-- The recorded CLAUSIFY checkpoints (preprocess formula → clause set;
    `emit/clausify/*`): the input term (the preprocess chain's final term), the
    neg-clause (its disjunction ≡ the NEGATION of the input), the per-negated-
    literal split clauses, the conjoined output clause set, and the ORDERED
    `expand-and-or` firings (S2 attachment; `expanded` retained as the
    derived flag for existing consumers). -/
structure ClausifyInfo where
  input : SExpr
  negClause : List SExpr
  splits : List (SExpr × List SExpr)
  out : List (List SExpr)
  expanded : Bool := false
  /-- Expansions fired during the WHOLE-FORMULA (bool=nil) pass, in
      clausify-input1's depth-first order. -/
  negExpands : List ClausifyExpansion := []
  /-- Expansions fired during the per-negated-literal (bool=t) passes:
      `(k, e)` = expansion `e` fired while clausifying the literal of the
      k-th split (0-based, log order — the expansions PRECEDE their split
      checkpoint). -/
  splitExpands : List (Nat × ClausifyExpansion) := []
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
  /-- The clausification record of a preprocess step that SPLIT the clause. -/
  | clausify (info : ClausifyInfo)
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
    { origin := step.origin, equiv := step.equiv, runes := step.runes,
      parents := step.parents, subst := step.subst, equivTerm := step.equivTerm,
      typeSet := step.typeSet, trueTs := step.trueTs, path := step.path }

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
  | .beginInnerRewrite kind :: rest =>
      -- tag the block's top-level nodes with its :KIND so the adopting step can
      -- partition its children (HYP-relief chains vs RHS continuation vs body).
      let (innerNodes, rest') ← parseProofNodesAux rest [] []
      let tagged := innerNodes.map fun
        | n@(.node rune lhs rhs children prov) =>
          -- an already-tagged node is a DEEPER block's unadopted flush-out
          -- (see the pendingChildren note above) — keep its own kind.
          if prov.innerKind.isEmpty then
            .node rune lhs rhs children { prov with innerKind := kind }
          else n
      parseProofNodesAux rest' (pendingChildren ++ tagged) nodes
  | .beginIfRewrite _ _ :: rest =>
      let (innerNodes, rest') ← parseProofNodesAux rest [] []
      parseProofNodesAux rest' (pendingChildren ++ innerNodes) nodes
  | .endInnerRewrite _ :: rest | .endIfRewrite _ _ :: rest =>
      return (nodes.reverse ++ pendingChildren, rest)
  | .rewriteStep step :: rest =>
      parseProofNodesAux rest [] (rewriteStepNode step pendingChildren :: nodes)
  | .typeSetReasoning term result _ justification :: rest =>
      -- a term closed by type-set reasoning (e.g. a literal forced true/false);
      -- the :JUSTIFICATION is the rune list of supporting rules — carry it so the
      -- type fact's provenance (which ACL2 supplied) isn't dropped.
      let runes ← ProofLog.parseRunes justification
      parseProofNodesAux rest []
        (.node ⟨"type-set", "", none⟩ term result pendingChildren { runes } :: nodes)
  | .branchSubstitution equiv lhs rhs :: rest =>
      parseProofNodesAux rest []
        (.node ⟨"branch-substitution", "", none⟩ lhs rhs pendingChildren { equivTerm := equiv } :: nodes)
  | .contextSubst var value _ :: rest =>
      parseProofNodesAux rest [] (.node ⟨"context-subst", "", none⟩ var value pendingChildren {} :: nodes)
  | .hypRelief hyp origin taRunes parents :: rest =>
      -- a silent hyp-relief marker (no rewrite events): recorded as a leaf
      -- node; the adopting rule step's recipe consumes it in place of a
      -- relief chain. It never adopts children.
      unless pendingChildren.isEmpty do
        throw s!"parseProofNodesAux: hyp-relief marker with pending inner \
                 nodes: {repr hyp}"
      parseProofNodesAux rest []
        (.node ⟨"hyp-relief", "", none⟩ hyp hyp []
          { origin, taRunes, parents } :: nodes)
  | .ifTestTrue _ _ _ :: rest | .ifTestFalse _ _ _ :: rest | .ifTestUnknown _ _ _ :: rest =>
      -- IF-test markers delimit the if-rewrite block; not standalone nodes.
      parseProofNodesAux rest pendingChildren nodes
  | .rewrittenLiteral _ _ :: rest =>
      -- the literal's net result, captured separately by findLiteralResult.
      parseProofNodesAux rest pendingChildren nodes
  | .beginLiteral _ _ _ :: _ | .endLiteral _ _ _ :: _ | .beginBranch _ :: _
  | .endBranch :: _ | .caseSplit _ _ :: _
  | .clausifyInput _ :: _ | .clausifyNeg _ :: _ | .clausifySplit _ _ :: _
  | .clausifyOut _ :: _ | .clausifyExpand _ _ _ _ :: _ =>
      -- A clause-structure boundary: stop and hand the remaining events back to
      -- the clause-level parser. (This match is exhaustive over TraceEvent, so a
      -- new event kind becomes a compile error here — never a silent drop.)
      return (nodes.reverse ++ pendingChildren, events)
  | .clausifyTest .. :: _ | .clausifyLeaf .. :: _ | .clausifySetReshaped _ :: _
  | .clausifyConjunction .. :: _ =>
      -- literal-clausify decision-trace events are partitioned out by
      -- `parseClauseItems` before the chain is parsed; reaching one here means
      -- it appeared OUTSIDE a literal block — the scoping in the ACL2 fork
      -- (infra/clausify-trace-scope) guarantees it cannot.
      throw s!"parseProofNodesAux: clausify decision-trace event outside a \
               literal block: {repr events.head?}"

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

/-- Collect a CLAUSIFY checkpoint block following a `:CLAUSIFY-INPUT` event:
    optional `:CLAUSIFY-EXPAND` markers (flagged), then `:CLAUSIFY-NEG`, the
    `:CLAUSIFY-SPLIT`s (markers may interleave), then `:CLAUSIFY-OUT`.
    Out-of-order structure hard-fails. -/
private def collectClausify (input : SExpr) (evs : List TraceEvent)
    : Except String (ClausifyInfo × List TraceEvent) := do
  -- phase 1: whole-formula (bool=nil) expansions before the neg event
  let rec takeExpands (acc : List ClausifyExpansion)
      : List TraceEvent → (List ClausifyExpansion × List TraceEvent)
    | .clausifyExpand fr to pos runes :: rest =>
        takeExpands (acc ++ [⟨fr, to, pos, runes⟩]) rest
    | rest => (acc, rest)
  let (negExpands, evs) := takeExpands [] evs
  let (negClause, evs) ← match evs with
    | .clausifyNeg cl :: rest => pure (cl, rest)
    | ev :: _ => throw s!"collectClausify: expected :CLAUSIFY-NEG, got {repr ev}"
    | [] => throw "collectClausify: events ended before :CLAUSIFY-NEG"
  -- phase 2: splits, with each split's (bool=t) expansions PRECEDING its
  -- checkpoint; then out
  let rec go (acc : List (SExpr × List SExpr))
      (sx : List (Nat × ClausifyExpansion))
      : List TraceEvent → Except String (ClausifyInfo × List TraceEvent)
    | .clausifyExpand fr to pos runes :: rest =>
        go acc (sx ++ [(acc.length, ⟨fr, to, pos, runes⟩)]) rest
    | .clausifySplit lit cl :: rest => go (acc ++ [(lit, cl)]) sx rest
    | .clausifyOut clauses :: rest =>
        return ({ input, negClause, splits := acc, out := clauses,
                  expanded := !negExpands.isEmpty || !sx.isEmpty,
                  negExpands, splitExpands := sx }, rest)
    | ev :: _ => throw s!"collectClausify: expected split/out, got {repr ev}"
    | [] => throw "collectClausify: events ended before :CLAUSIFY-OUT"
  go [] [] evs

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
      -- partition out the literal's clausify DECISION TRACE (all emitted by
      -- the single clausify call after the chain — their position among the
      -- chain events carries no information)
      let splitTrace := litEvents.filterMap fun
        | .clausifyTest t v h p => some (SplitDecision.test t v h p)
        | .clausifyLeaf v o p seg => some (SplitDecision.leaf v o p seg)
        -- conjunction markers (S1.2): ADDITIONAL provenance for the
        -- and-shape union — flattened out of the decision stream here, which
        -- reproduces the pre-marker trace exactly (the composer links leaves
        -- by their emitted :SEGMENT); the ORDEREDP-ISORT spine consumer that
        -- READS the marker is the tracked follow-up (map P8)
        | .clausifyConjunction .. => none
        | _ => none
      let splitReshaped := litEvents.filterMap fun
        | .clausifySetReshaped w => some w
        | _ => none
      let chainEvents := litEvents.filter fun
        | .clausifyTest .. | .clausifyLeaf .. | .clausifySetReshaped _
        | .clausifyConjunction .. => false
        | _ => true
      let nodes ← buildProofNodes chainEvents
      let litResult := findLiteralResult chainEvents literal
      let (more, rest'') ← parseClauseItems rest'
      return (.literal { index, literal, notFlg, nodes, result := litResult,
                         splitTrace, splitReshaped } :: more, rest'')
  | .clausifyInput input :: rest =>
      -- collect the contiguous clausify block: [expand*] neg ([expand*] split)* out
      let (info, rest') ← collectClausify input rest
      let (more, rest'') ← parseClauseItems rest'
      return (.clausify info :: more, rest'')
  | .caseSplit _ _ :: rest =>
      -- Informational header (`clause/case-split`): the preceding literal split the
      -- clause into N branches. The branches themselves follow as BEGIN-BRANCH/
      -- END-BRANCH (parsed by the `.beginBranch` case), which carry the case structure
      -- — so the marker consumes to nothing here, losing no tree structure. (A function
      -- with a multi-way `if` body, e.g. cd2's zp/=1/else, triggers this.)
      parseClauseItems rest
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
