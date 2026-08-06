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
import ACL2Lean.EvalOpt

namespace ACL2

/-- One processor applied to a clause: a single `:STEP` record. -/
structure WaterfallStep where
  processor : String
  result : ProofResult
  runes : List Rune
  newClauses : List SExpr
  /-- Rewriter detail (the clause's `:REWRITES` branch tree), present for steps
      that carry one — chiefly SIMPLIFY-CLAUSE. Empty for processors that don't. -/
  items : List ClauseItem
  /-- Processor-specific justification fields (verbatim), e.g. fertilize's
      target/bullet, eliminate-destructors' elim sequence, generalize's term→var
      map — carried so the derivation of a non-rewriter step isn't dropped. -/
  extraFields : List (String × SExpr) := []
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
  /-- The RAW declared rule-classes (`:CLASSES`, cluster item 5):
      `none` = pre-cluster log; `some .nil` = declared `:rule-classes nil`
      (distinct by design — audit 2026-08-03 F6). Consumed by the
      equivalence/congruence gates once their consumption lands. -/
  classes : Option SExpr := none
  deriving Repr, Inhabited

/-- One world-extending event of an ACL2 development, in file order. In the
    logical world each event scopes over everything after it — definitions are
    let-bindings over the later definitions and theorems that may use them. -/
inductive WorldEvent where
  /-- A function definition. `body` is the (translated) form ACL2 reasons about.
      `just` is the admission justification (measure/well-founded relation/
      measured subset), present exactly when the defun is recursive.
      `termination` is the admission (measure-conjecture) proof, present when
      the admission was non-trivial. -/
  | defun (name : String) (formals : List Symbol) (body : SExpr)
          (just : Option Justification) (termination : Option ClauseProof)
  /-- A scoped `local` WITNESS defun (R6/Phase 4): recorded with its
      admission tree, EXCLUDED from `toWorld` by construction (BUG-019 —
      the certified world never contains witness bodies; the witness model
      is the scope's conservativity artifact, consumed by the ScopeHolds
      machinery when it lands). `buildDevelopment` hard-fails a witness
      outside any bracket. -/
  | witnessDefun (name : String) (formals : List Symbol) (body : SExpr)
      (just : Option Justification := none)
      (termination : Option ClauseProof := none)
  /-- A type-prescription corollary ACL2 derived for a function. -/
  | typePrescription (name : String) (corollary : SExpr)
          (basicTs : Option Int) (leaves : List (SExpr × Int))
  /-- Stored rewrite rules created by preceding defthms (emitted before any
      use — the source for `rule:<thm>` dependency hypotheses). -/
  | rules (specs : List RuleSpec)
  /-- Encapsulate scope OPEN (cluster item 2 / R6 justified-extensions):
      recorded in event order; SCOPE SEMANTICS (witness admission into the
      canonical model, per-scope dedup, ScopeHolds) land with the close-out
      arc's Phase 4 — until then `toWorld` treats the brackets as inert
      (an EXPLICIT decision, not a default-case skip). -/
  | encapsulateBegin (sigs : List Symbol)
  | encapsulateEnd
  /-- The scope's constraint axioms (verbatim from ACL2's constraint-lst). -/
  | constraints (fns : List Symbol) (formulas : List SExpr)
  /-- A ground-zero defun SNAPSHOT (design D3): a boot-strap definition read
      off ACL2's world at capture end because the captured events cite it
      (recursive ones carry RECOMPUTED termination clauses in `just`).
      Emitted at the log's TAIL; logically it precedes the whole development.
      INERT until WP1 wires snapshots into `toWorld`/the totality prover. -/
  | groundZeroDefun (name : String) (formals : List Symbol) (body : SExpr)
      (just : Option Justification)
  /-- The cited ground-zero REWRITE rules read off ACL2's world at capture
      end (design D5), match-free flags included. INERT until WP3/WP5 wire
      them into the rule-discharge registry (deliberately NOT part of
      `storedRules` — these were not created during capture). -/
  | groundZeroRules (specs : List RuleSpec)
  /-- The cited ground-zero FORWARD-CHAINING rules (emission arc
      2026-07-21) — trigger/hyps/concls verbatim; consumed by the
      FC-derived type-alist relief recipe. -/
  | groundZeroFcRules (specs : List FcRuleSpec)
  /-- The cited ground-zero LINEAR rules (sorting-absolute 2b) —
      hyps/concl/max-term verbatim; consumed as the DP obligation's
      premise where simplify's linear arithmetic cites the rune. -/
  | groundZeroLinearRules (specs : List LinearRuleSpec)
  /-- The cited recognizer-alist tuples (fork-batch item 2, 2026-08-06)
      — the recognizer/ground-hyp verdict basis. INERT until the R2/R4
      retirement consumers wire them (this phase). -/
  | groundZeroRecognizerTuples (specs : List RecognizerTupleSpec)
  /-- An include GRAPH edge (fork-batch item 6): the provenance DAG the
      cross-book offer gate consumes. -/
  | includeBookEdge (book : String) (parent : Option String)
  /-- The post-`ld` capture manifest (fork-batch item 8): parse already
      requires `:STATUS :COMPLETE`; the books alist is kept opaque. -/
  | captureEnd (books : SExpr)
  /-- A proved theorem and its clause-tree proof. -/
  | theorem (proof : ClauseProof)
  /-- An INCLUDE-BOOK'd theorem (R2): certified in its OWN book — no
      waterfall runs on include, so this log carries its statement (and,
      separately, its stored rules via a `.rules` event) but NO proof tree.
      A `rule:<name>` citation of it replays fine (the rule is offered);
      only the step-5 DISCHARGE stays hypothesis-backed from this log (D6) —
      cross-book proof import is the tracked follow-up. `classes` carries the
      emitted raw `:CLASSES` (fresh-verify N3, 2026-08-03: the equivalence/
      congruence consumers' data arrives on THIS arm — e.g.
      PERM-IS-AN-EQUIVALENCE is `:SOURCE :INCLUDE-BOOK` in qsort/equisort);
      `none` = key absent, `some .nil` = declared `:rule-classes nil`. -/
  | includedTheorem (name : String) (formula : SExpr)
      (classes : Option SExpr := none)
  deriving Repr, Inhabited

/-- An ACL2 development reconstructed as a SINGLE proof tree: a right-nested
    sequence of world events, each binding (scoping) over the rest — definitions
    as let-bindings over the later definitions/theorems that use them. This is
    the structure a replay folds over: extend the world with each definition,
    then discharge each theorem in that world. The proof *branching* lives inside
    each event (a theorem's clause tree, a defun's termination clause tree); the
    backbone here is the linear file order. -/
inductive Development where
  | bind (event : WorldEvent) (rest : Development)
  | done
  deriving Repr, Inhabited

/-- A reconstructed ENCAPSULATE scope (R6/Phase 4): the signature fns, the
    emitted constraint axioms (verbatim from ACL2's constraint-lst), the
    scoped witnesses, and the in-scope theorem names (BOTH passes' events
    ride inside the bracket — the per-scope dedup obligation). This is the
    single structured read-off for the parametric-statement machinery
    (ConstraintsHold, the R7b instantiation). -/
structure Scope where
  sigs : List Symbol
  /-- The constrained fns as EMITTED on the (:CONSTRAINTS …) event —
      `none` when the scope emitted no constraints event (a trivial
      grouping encapsulate). -/
  constraintFns : Option (List Symbol) := none
  constraintFormulas : List SExpr := []
  witnesses : List (String × List Symbol × SExpr) := []
  theoremNames : List String := []
  deriving Repr, Inhabited

/-- The TOP-LEVEL scopes of a development, in file order (nested scopes
    fold into their outermost bracket — pairing beyond depth counting is
    the recorded Phase-4 frontier; equisort's scopes are flat). Hard-fails
    on imbalance are buildDevelopment's job — here a stray shape means the
    Development itself is malformed, so mismatches throw. -/
def Development.scopes (dev : Development) : Except String (List Scope) := do
  let rec go (d : Development) (depth : Nat) (cur : Option Scope)
      (acc : List Scope) : Except String (List Scope) :=
    match d with
    | .done =>
      match cur with
      | none => pure acc.reverse
      | some _ => throw "Development.scopes: unclosed scope at end (internal — buildDevelopment enforces balance)"
    | .bind ev rest =>
      match ev with
      | .encapsulateBegin sigs =>
        if depth == 0 then
          go rest 1 (some { sigs }) acc
        else go rest (depth + 1) cur acc
      | .encapsulateEnd =>
        if depth == 0 then
          throw "Development.scopes: stray scope end (internal)"
        else if depth == 1 then
          match cur with
          | some s => go rest 0 none (s :: acc)
          | none => throw "Development.scopes: internal — no open scope at depth 1"
        else go rest (depth - 1) cur acc
      | .constraints fns formulas =>
        match cur with
        | some s =>
          if s.constraintFns.isSome then
            throw "Development.scopes: second (:CONSTRAINTS) in one scope (frontier)"
          else go rest depth
            (some { s with constraintFns := some fns,
                           constraintFormulas := formulas }) acc
        | none => throw "Development.scopes: (:CONSTRAINTS) outside any scope (malformed)"
      | .witnessDefun n formals body _ _ =>
        match cur with
        | some s => go rest depth
            (some { s with witnesses := s.witnesses ++ [(n, formals, body)] }) acc
        | none => throw s!"Development.scopes: witness '{n}' outside any scope (internal — buildDevelopment enforces)"
      | .theorem cp =>
        match cur with
        | some s => go rest depth
            (some { s with theoremNames := s.theoremNames ++ [cp.name] }) acc
        | none => go rest depth cur acc
      | _ => go rest depth cur acc
  go dev 0 none []

/-- All INCLUDE-BOOK'd theorems in development order. (The explicit `_` for
    `classes` matters: a 2-arg pattern would DEFAULT-FILL `classes := none`
    and silently skip classed entries — the TamperTests F1 lesson.) -/
def Development.includedTheorems : Development → List (String × SExpr)
  | .bind (.includedTheorem n f _) rest => (n, f) :: rest.includedTheorems
  | .bind _ rest => rest.includedTheorems
  | .done => []
/-- Project the `evalOpt` `World` from a reconstructed `Development`: fold each `defun`
    event's `(name, formals, body)` into `World.defs`. The world the replay reasons over is
    thus DERIVED from the parsed proof-log, not hand-written — so the only input to a replay
    is the log. (`typePrescription`/`theorem` events don't extend `defs`.) The `defun` name
    is a `String`; the key uses the default `Symbol` package, matching the symbols the parser produces in bodies/calls.

    Ground-zero SNAPSHOT defuns (design D3, WP1) enter the world the same way —
    EXCEPT names `callBuiltin` dispatches (`builtinNames`): world-first dispatch
    would shadow the builtin, changing fuel profiles and falsifying the `hnew`
    side condition of `evalOpt_world_mono` (D2). Those take the D4
    definition-fact route instead (WP2: `d4DefFacts`/`replayBuiltinDefUnfold`,
    reading the emitted body off `Development.groundZeroSnapshotDefs`).
    This retires the old hand-pinned `groundZeroDefs`. `defs.entries` keeps
    user defuns in development order with the snapshot defs at the tail
    (the log emits snapshots after the last theorem). -/
def Development.toWorld : Development → World
  | .done => { defs := DefMap.mk [] }
  | .bind ev rest =>
    let w := rest.toWorld
    match ev with
    | .defun name formals body _ _ => { w with defs := w.defs.insert { name := name } (formals, body) }
    | .groundZeroDefun name formals body _ =>
      if builtinNames.contains name then w
      else { w with defs := w.defs.insert { name := name } (formals, body) }
    -- Pre-merge audit fix N5 (2026-08-06): the witness-defun exclusion
    -- from the certified world (BUG-019 resolution — :SOURCE
    -- :LOCAL-WITNESS bodies are untrusted witness artifacts) is
    -- LOAD-BEARING; write it explicitly rather than defaulting it.
    | .witnessDefun .. => w
    | _ => w

/-- A development's ground-zero SNAPSHOT defuns — (name, formals, emitted body)
    for ALL of them, world-entering or builtin-excluded — the
    `ReplayConfig.gzDefs` input. Two consumers: the totality prover's lazy
    bound treats these names as always-in-scope (they logically precede the
    whole development), and the D4 definition-fact route reads a builtin's
    recorded body from here (its only record — builtin-named snapshots do not
    enter the world). -/
def Development.groundZeroSnapshotDefs :
    Development → List (Symbol × List Symbol × SExpr)
  | .done => []
  | .bind ev rest =>
    match ev with
    | .groundZeroDefun n formals body _ =>
      ({ name := n }, formals, body) :: rest.groundZeroSnapshotDefs
    | _ => rest.groundZeroSnapshotDefs

/-- The emitted type-prescription corollaries of a development (fn name ↦
    corollary term) — the type facts the replay consumes as hypotheses. -/
def Development.typePrescriptions : Development → List (String × SExpr)
  | .done => []
  | .bind ev rest =>
    match ev with
    | .typePrescription n cor _ _ => (n, cor) :: rest.typePrescriptions
    | _ => rest.typePrescriptions

/-- The STORED rewrite rules of a development, in creation order (rune name ↦
    spec) — the statements the `rule:<thm>` dependency hypotheses assert
    (docs/plans/2026-07-05_theorem-dependency-hypotheses.md). -/
def Development.storedRules : Development → List RuleSpec
  | .done => []
  | .bind ev rest =>
    match ev with
    | .rules specs => specs ++ rest.storedRules
    | _ => rest.storedRules

/-- A development's ground-zero RULE snapshot entries (the
    `(:GROUND-ZERO-RULES …)` event, design D5) — boot-stored rules, in
    emitted (world) order. They logically PRECEDE the whole development:
    the rule-offer telescope seeds with them ahead of every user rule. -/
def Development.groundZeroRuleSpecs : Development → List RuleSpec
  | .done => []
  | .bind ev rest =>
    match ev with
    | .groundZeroRules specs => specs ++ rest.groundZeroRuleSpecs
    | _ => rest.groundZeroRuleSpecs

/-- All FC-rule snapshot specs in the development. -/
def Development.groundZeroFcRuleSpecs : Development → List FcRuleSpec
  | .done => []
  | .bind ev rest =>
    match ev with
    | .groundZeroFcRules specs => specs ++ rest.groundZeroFcRuleSpecs
    | _ => rest.groundZeroFcRuleSpecs

/-- All LINEAR-rule snapshot specs in the development (2b). -/
def Development.groundZeroLinearRuleSpecs :
    Development → List LinearRuleSpec
  | .done => []
  | .bind ev rest =>
    match ev with
    | .groundZeroLinearRules specs =>
      specs ++ rest.groundZeroLinearRuleSpecs
    | _ => rest.groundZeroLinearRuleSpecs

/-- All recognizer-tuple snapshot specs in the development (item 2). -/
def Development.groundZeroRecognizerTupleSpecs :
    Development → List RecognizerTupleSpec
  | .done => []
  | .bind ev rest =>
    match ev with
    | .groundZeroRecognizerTuples specs =>
      specs ++ rest.groundZeroRecognizerTupleSpecs
    | _ => rest.groundZeroRecognizerTupleSpecs

/-- The include GRAPH edges in the development (item 6):
    (book, parent) per include-book encounter. -/
def Development.includeEdges : Development → List (String × Option String)
  | .done => []
  | .bind ev rest =>
    match ev with
    | .includeBookEdge b p => (b, p) :: rest.includeEdges
    | _ => rest.includeEdges

/-- The admission justifications of a development's RECURSIVE defuns
    (fn name ↦ measure/wfrel/measured-subset + the raw termination clauses),
    in development order — the data the totality prover consumes (#37).
    Ground-zero snapshot defuns contribute their RECOMPUTED admission
    clauses the same way (design D6: the totality prover treats them
    exactly like local defuns; a frontier failure keeps the `total:`
    hypothesis — completeness, never soundness). -/
def Development.justifications : Development → List (String × Justification)
  | .done => []
  | .bind ev rest =>
    match ev with
    | .defun n _ _ (some j) _ => (n, j) :: rest.justifications
    | .groundZeroDefun n _ _ (some j) => (n, j) :: rest.justifications
    | _ => rest.justifications

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
    | .atom (.symbol s) => if s.name == "NOT" then some x else none
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
    `(source, equiv)` — clause literals first, then enclosing clausify-branch
    segments (list order is match priority). A solidify with no matching
    hypothesis, no if-branch `:PATH` frame, and no `'pt` parents is tagged
    `.typeSetDerived` (J6) — a classification BY ELIMINATION, since ACL2
    emits no positive marker for type-set-derived equivalences (`:PARENTS
    NIL`); the replay side refuses the tag (named frontier), so a mis-link
    landing here fails closed at replay, not silently. Emitting a positive
    type-set-verdict marker and consuming it here is the tracked follow-up
    (audit 2026-07-18). -/
private partial def linkNode (cands : List (EquivSource × SExpr)) (n : ProofNode)
    : Except String ProofNode := do
  match n with
  | .node rune lhs rhs children prov =>
    let children ← children.mapM (linkNode cands)
    if rune.1 == "rewriting-equivalence" then
      match prov.equivTerm with
      | some e =>
        match cands.find? (fun (_, c) => equivMatch e c) with
        | some (src, _) =>
          -- a matching hypothesis links regardless of `:PARENTS` — a
          -- 'pt-bearing solidify (the type-alist entry's parent tree names
          -- the source literal) matches its literal here just the same
          -- (HOW-MANY-FILTER-1's IH-fed solidify)
          return .node rune lhs rhs children { prov with equivSource := some src }
        | none =>
          -- the BY-ELIMINATION fallback tags apply only to `:PARENTS NIL`
          -- nodes; a 'pt-bearing node with no matching hypothesis stays
          -- UNLINKED (the replay fails closed with its named error), never
          -- misclassified as branch-test/type-set-derived
          if !prov.parents.isEmpty then
            return .node rune lhs rhs children prov
          -- No clause-literal/segment hypothesis matches. If the node's :PATH
          -- descends through an UNRESOLVED if's then/else ARGUMENT (frame
          -- `(2 . IF)` / `(3 . IF)`), the equivalence is that if's test,
          -- assumed by assume-true-false in the branch — tag it; the replay
          -- validates the test term during its path walk (conditional
          -- congruence, R1) or fails closed there.
          if prov.path.any (fun f => match f with
              | .arg i s => (i == 2 || i == 3) && s.name == "IF"
              | .boundary _ _ => false
              | .argLam _ _ => false) then
            return .node rune lhs rhs children
              { prov with equivSource := some .branchTest }
          else
            -- J6: no hypothesis and no if-branch frame — ACL2 believed the
            -- equivalence by TYPE-SET reasoning under the enclosing branch
            -- facts (verdict-class, :PARENTS NIL — msort/bsort's
            -- car/cdr-of-non-cons collapses). Tag it; the REPLAY discharges
            -- the equiv-term from branch facts or fails closed there.
            return .node rune lhs rhs children
              { prov with equivSource := some .typeSetDerived }
      | none => return .node rune lhs rhs children prov
    else
      return .node rune lhs rhs children prov

/-- Collect the hypotheses (source, available equivalence) from every
    `literal` item in a clause's branch tree — the IH is a clause-level
    hypothesis, available in all branches. -/
private partial def collectHypEquivs : List ClauseItem → List (EquivSource × SExpr)
  | [] => []
  | .literal lp :: rest =>
      (match hypEquiv lp with | some e => [(.literal lp.index, e)] | none => [])
        ++ collectHypEquivs rest
  | .step _ :: rest => collectHypEquivs rest
  | .clausify _ :: rest => collectHypEquivs rest
  | .useHint _ _ _ _ :: rest => collectHypEquivs rest
  | .fcDerivations _ :: rest => collectHypEquivs rest
  | .complementClose _ :: rest => collectHypEquivs rest
  | .branch _ items :: rest => collectHypEquivs items ++ collectHypEquivs rest

/-- The hypotheses a clausify-branch SEGMENT contributes inside its branch:
    each segment literal `(not (equiv a b))` makes `(equiv a b)` assumable
    (this is what ACL2's `:CONTEXT-SUBST` substitutes with — perm/PERM-CONS). -/
private def segmentHypEquivs (seg : SExpr) : List (EquivSource × SExpr) :=
  match seg.toList? with
  | some lits => lits.filterMap fun l =>
      match peelNot l with
      | some e => match asBinApp e with
        | some _ => some (.segment, e)
        | none => none
      | none => none
  | none => []

/-- Link each `literal`'s solidify nodes to a sibling literal's hypothesis (a
    literal cannot justify rewriting itself — matching ACL2's parent-tree
    loop-avoidance), recursing through branches; inside a branch, the branch
    SEGMENT's hypotheses are additionally in scope (appended AFTER the clause
    literals — literal matches keep priority). -/
private partial def linkItems (cands : List (EquivSource × SExpr))
    : List ClauseItem → Except String (List ClauseItem)
  | [] => return []
  | .literal lp :: rest => do
      let nodes ← lp.nodes.mapM (linkNode (cands.filter (·.1 != .literal lp.index)))
      return .literal { lp with nodes } :: (← linkItems cands rest)
  | .step n :: rest => do return .step n :: (← linkItems cands rest)
  | .clausify info :: rest => do return .clausify info :: (← linkItems cands rest)
  | .useHint h c a l :: rest => do return .useHint h c a l :: (← linkItems cands rest)
  | .complementClose lit :: rest => do
      return .complementClose lit :: (← linkItems cands rest)
  | .fcDerivations d :: rest => do return .fcDerivations d :: (← linkItems cands rest)
  | .branch seg items :: rest => do
      return .branch seg (← linkItems (cands ++ segmentHypEquivs seg) items)
        :: (← linkItems cands rest)

/-- Link the solidify nodes in a clause's branch tree to their hypotheses. -/
private def linkEquivSources (items : List ClauseItem) : Except String (List ClauseItem) := do
  linkItems (collectHypEquivs items) items

/-- Find the index of the flat node with the given printed id. -/
private def findIdx (flats : Array FlatNode) (idStr : String) : Option Nat :=
  flats.findIdx? (·.idStr == idStr)

/-- The pool bookkeeping `collectFlat` extracts alongside the flat nodes:
    pushes registered by their emitted `:POOLNAME`, inductions paired with the
    pool root the pop-clause walk was CONSIDERING (from `(:POOL-CONSIDER …)`),
    and the pool-subsumption discharges. `sawPool` distinguishes a log with
    pool events (registry linking, fail-closed) from a legacy log (adjacency
    linking). -/
private structure PoolData where
  pushes : Array (List Nat × String × List SExpr) := #[]
  inductions : Array (Option (List Nat) × String × List SExpr × InductionStep) := #[]
  subsumptions : Array (List Nat × List Nat) := #[]
  /-- REVERT-aborted pushes (J5, design I6 as ratified: ACL2 abandons the
      prior work on the conjecture and REASSIGNS the pool name to the
      ORIGINAL conjecture): (reassigned pool name, aborting clause id). -/
  reverts : Array (List Nat × String) := #[]
  sawPool : Bool := false

private def collectFlat (events : List ProofEvent)
    : Except String (Array FlatNode × PoolData) := do
  let mut flats : Array FlatNode := #[]
  let mut pd : PoolData := {}
  let mut lastPush : Option String := none
  -- The clause the most recent PUSH-CLAUSE pushed to the pool. This is the
  -- actual induction subject — NOT a clause node's first-step inputClause, which
  -- may be a pre-NNF form (e.g. `(implies h c)` before preprocess splits it).
  let mut lastPushClause : List SExpr := []
  let mut currentPool : Option (List Nat) := none
  for ev in events do
    match ev with
    | .step s =>
      let wstep : WaterfallStep := {
        processor := s.processor, result := s.result, runes := s.runes,
        newClauses := s.newClauses, extraFields := s.extraFields,
        items := ← linkEquivSources (← buildClauseItems s.traceEvents) }
      match findIdx flats s.clauseId with
      | some i =>
        flats := flats.modify i (fun fn => { fn with steps := fn.steps.push wstep })
      | none =>
        let cid ← ClauseId.parse s.clauseId
        flats := flats.push {
          id := cid, idStr := s.clauseId, inputClause := s.inputClause,
          steps := #[wstep] }
      if s.processor.toLower == "push-clause" then
        let parsePoolName (pn : SExpr) : Except String (List Nat) := do
          match pn.toList? with
          | some items =>
            items.mapM fun i => match i with
              | .atom (.number (.int n)) =>
                if n ≥ 0 then pure n.toNat
                else throw s!"collectFlat: negative :POOLNAME entry {repr i}"
              | _ => throw s!"collectFlat: non-natural :POOLNAME entry {repr i}"
          | none => throw s!"collectFlat: :POOLNAME {repr pn} is not a list"
        match s.extraFields.lookup "abort-cause" with
        | some (.atom (.symbol c)) =>
          -- an ABORTED push (J5): REVERT reassigns the emitted pool name to
          -- the ORIGINAL conjecture; any other cause means a FAILED proof
          -- inside the log — fail-closed
          if c.name == "REVERT" || c.name == "MAYBE-REVERT" then
            let some pn := s.extraFields.lookup "poolname"
              | throw s!"collectFlat: REVERT push at {s.clauseId} without \
                        :POOLNAME (emission gap)"
            let name ← parsePoolName pn
            pd := { pd with reverts := pd.reverts.push (name, s.clauseId) }
          else
            throw s!"collectFlat: push-clause ABORT at {s.clauseId} with \
                    cause {c.name} — a failed/aborted proof in the log \
                    (fail-closed)"
        | some other =>
          throw s!"collectFlat: malformed :ABORT-CAUSE {repr other}"
        | none =>
          lastPush := some s.clauseId
          lastPushClause := s.inputClause
          -- register the push under its emitted pool name; the emitter always
          -- attaches :POOLNAME to a non-abort push, so its absence is an
          -- emission gap — hard-fail, symmetric with the abort path (a silent
          -- drop here would only surface later IF an induction consumed the
          -- pool, and never for an unconsumed one — audit 2026-07-18)
          let some pn := s.extraFields.lookup "poolname"
            | throw s!"collectFlat: push-clause at {s.clauseId} without \
                      :POOLNAME (emission gap)"
          let name ← parsePoolName pn
          pd := { pd with pushes := pd.pushes.push (name, s.clauseId, s.inputClause) }
    | .induction i =>
      pd := { pd with inductions :=
        pd.inductions.push (currentPool, lastPush.getD "", lastPushClause, i) }
    | .poolConsider name =>
      currentPool := some name
      pd := { pd with sawPool := true }
    | .poolSubsumed name byName =>
      pd := { pd with subsumptions := pd.subsumptions.push (name, byName),
                      sawPool := true }
    | other =>
      -- buildDevelopment routes defun/type-prescription/defthm/qed elsewhere, so
      -- a theorem block should contain only steps and inductions; anything else
      -- is a mis-sliced block — surface it rather than swallow it.
      throw s!"collectFlat: unexpected event in a theorem block: {repr other}"
  return (flats, pd)

private def poolIdStr (poolLst : List Nat) : String :=
  "*" ++ String.intercalate "." (poolLst.map toString)

/-- Synthesize the induction pool-root nodes (`*1`, `*1.1`, …) that ACL2 does
    not log as steps, plus SUBSUMED pool roots (a synthetic `pool-subsumed`
    step naming the subsumer). With pool events (`sawPool`) linking is exact:
    a push's emitted `:POOLNAME` names the root it creates, and each
    `(:POOL-CONSIDER …)` names the root the following induction proves —
    subsumption REORDERS pool processing, so adjacency linking is wrong there.
    Legacy logs (no pool events) keep the adjacency+counting scheme. Returns
    the synthetic nodes paired with their pushed-parent id, plus EXTRA
    child links (subsumer-subtree → subsumed-root, for the replay). -/
private def synthesizePoolRoots (pd : PoolData)
    (goalClause? : Option (List SExpr) := none)
    (rootIdStr? : Option String := none)
    : Except String (Array (FlatNode × String) × Array (String × String)) := do
  let mut out : Array (FlatNode × String) := #[]
  let mut extraLinks : Array (String × String) := #[]
  if pd.sawPool then
    -- FAIL-CLOSED guards (audit 2026-07-06, emission findings 1-2): pool
    -- names must be UNIQUE within the block — the name-keyed find? would
    -- silently pick the first of a collision (pool names reset per forcing
    -- round, and the events do not carry the round; extend the emission
    -- when forcing rounds appear). And every registered push must be
    -- CONSUMED by a consider or subsumed event — an unconsumed push (e.g.
    -- ACL2's subsumed-by-parent arm, currently unemitted) must not drop a
    -- pool root silently.
    unless (pd.pushes.map (·.1)).toList.eraseDups.length == pd.pushes.size do
      throw "ClauseTree: duplicate :POOLNAME within one theorem block              (forcing-round collision? — extend the pool-event emission)"
    for (name, _, _) in pd.pushes do
      unless (pd.inductions.any fun (n?, _, _, _) => n? == some name) ||
             (pd.subsumptions.any fun (n, _) => n == name) do
        throw s!"ClauseTree: pushed pool root {name} never considered or                  subsumed (unemitted pool outcome — emission gap)"
    for (name?, pid, _, ind) in pd.inductions do
      let some name := name?
        | throw "ClauseTree: :INDUCTION with no preceding (:POOL-CONSIDER …)                  in a pool-event log"
      let _ := pid
      -- REVERT first (J5): a reassigned pool name's content IS the ORIGINAL
      -- conjecture, parented to the root (the abandoned pushes are gone)
      match pd.reverts.find? (·.1 == name) with
      | some (_, rPushId) =>
        let some goalClause := goalClause?
          | throw "ClauseTree: reverted induction with no root Goal clause"
        let some rootIdStr := rootIdStr?
          | throw "ClauseTree: reverted induction with no root id"
        let pcid ← ClauseId.parse rPushId
        out := out.push ({
          id := { forcingRound := pcid.forcingRound, poolLst := name },
          idStr := poolIdStr name, inputClause := goalClause, steps := #[],
          induction := some ind, synthetic := true }, rootIdStr)
      | none =>
      let some (_, pushId, pushClause) := pd.pushes.find? (·.1 == name)
        | throw s!"ClauseTree: no PUSH-CLAUSE with :POOLNAME {name} for the                    induction the pool considered there"
      let pcid ← ClauseId.parse pushId
      out := out.push ({
        id := { forcingRound := pcid.forcingRound, poolLst := name },
        idStr := poolIdStr name, inputClause := pushClause, steps := #[],
        induction := some ind, synthetic := true }, pushId)
    for (name, byName) in pd.subsumptions do
      let some (_, pushId, pushClause) := pd.pushes.find? (·.1 == name)
        | throw s!"ClauseTree: no PUSH-CLAUSE with :POOLNAME {name} for the                    pool-subsumed root"
      let pcid ← ClauseId.parse pushId
      let subStep : WaterfallStep := {
        processor := "pool-subsumed", result := .proved, runes := [],
        newClauses := [], items := [],
        extraFields := [("subsumed-by",
          .atom (.symbol { name := poolIdStr byName }))] }
      out := out.push ({
        id := { forcingRound := pcid.forcingRound, poolLst := name },
        idStr := poolIdStr name, inputClause := pushClause,
        steps := #[subStep], synthetic := true }, pushId)
      -- the subsumer's subtree becomes the subsumed root's child so the
      -- replay can instantiate it
      extraLinks := extraLinks.push (poolIdStr byName, poolIdStr name)
    return (out, extraLinks)
  -- LEGACY (no pool events): the m-th induction whose pushed clause sits at
  -- pool-lst P creates a pool root at P ++ [m].
  let mut counts : Array (List Nat × Nat) := #[]
  for (_, pid, pushClause, ind) in pd.inductions do
    if pid.isEmpty then
      throw "ClauseTree: :INDUCTION with no preceding PUSH-CLAUSE"
    let pcid ← ClauseId.parse pid
    let key := pcid.poolLst
    let m := (counts.find? (·.1 == key)).map (·.2) |>.getD 0
    counts := (counts.filter (·.1 != key)).push (key, m + 1)
    let poolLst := key ++ [m + 1]
    -- The pool goal IS the clause the PUSH-CLAUSE pushed (the real induction
    -- subject), captured from that step — not the node's first-step inputClause.
    let node : FlatNode := {
      id := { forcingRound := pcid.forcingRound, poolLst := poolLst },
      idStr := poolIdStr poolLst, inputClause := pushClause, steps := #[],
      induction := some ind, synthetic := true }
    out := out.push (node, pid)
  return (out, #[])

/-- Assemble the subtree rooted at the node with id `key`. Children are kept in
    the order the clauses appear in the log — ACL2's own emit/processing order
    (`*1/N … *1/1`) — so the tree mirrors ACL2 rather than imposing a re-sort.
    A missing key is a hard error (the linking is supposed to be total). -/
private partial def assemble (flats : Array FlatNode)
    (childKeys : Array (String × String)) (key : String)
    (ancestors : List String := []) : Except String ClauseNode := do
  -- cycle guard (audit 2026-07-06): the subsumer→subsumed extra links could
  -- in principle form a cycle (mutual subsumption); recursion must fail
  -- loudly, not hang
  if ancestors.contains key then
    throw s!"ClauseTree: assemble cycle through {repr key} (mutual pool              subsumption?)"
  match (findIdx flats key).bind (flats[·]?) with
  | none => throw s!"ClauseTree: assemble found no node for key {repr key}"
  | some fn =>
    let kids := childKeys.filterMap (fun (c, p) => if p == key then some c else none)
    let children ← kids.toList.mapM (assemble flats childKeys · (key :: ancestors))
    return {
      id := fn.id, idStr := fn.idStr, inputClause := fn.inputClause,
      steps := fn.steps.toList, induction := fn.induction, children := children }

/-- Build the clause tree for one theorem's events. -/
private def buildOne (name : String) (formula : SExpr) (events : List ProofEvent)
    : Except String ClauseProof := do
  let (logged, pd) ← collectFlat events
  if logged.isEmpty then
    return { name, formula, root := none }
  -- J5 REVERT (design I6, ratified reading 2026-07-16): ACL2 "abandons our
  -- previous work on this conjecture and reassigns the name *1 to the
  -- ORIGINAL conjecture" — we replay the proof that SUCCEEDED; the
  -- abandoned pre-revert waterfall is search that never discharged, not
  -- part of the certifying proof. The tree becomes: root Goal closed by a
  -- synthetic push of the reverted pool name; kept nodes = the root + the
  -- reverted pool's subtree; everything else is DETACHED (fail-closed: a
  -- detached node carrying an induction is a structure we do not expect —
  -- hard-fail rather than drop silently).
  let (logged, pd) ←
    if pd.reverts.isEmpty then pure (logged, pd)
    else do
      let #[(rname, _)] := pd.reverts
        | throw s!"ClauseTree: {pd.reverts.size} reverts in one theorem \
                  block (frontier)"
      let some rootFn := logged.find? (·.id.isRoot)
        | throw "ClauseTree: revert with no root Goal node"
      let keep := fun (fn : FlatNode) =>
        fn.id.isRoot || rname.isPrefixOf fn.id.poolLst
      for fn in logged do
        unless keep fn do
          if fn.induction.isSome then
            throw s!"ClauseTree: revert would detach induction node \
                    {fn.idStr} (unexpected structure — frontier)"
      let synthPush : WaterfallStep := {
        processor := "push-clause", result := .proved, runes := [],
        newClauses := [], items := [],
        extraFields := [("poolname",
          SExpr.ofList (rname.map fun n => .atom (.number (.int (Int.ofNat n))))),
          ("revert", .atom (.symbol { name := "T" }))] }
      let logged' := (logged.filter keep).map fun fn =>
        if fn.id.isRoot then { fn with steps := #[synthPush] } else fn
      -- the abandoned pushes of the reassigned name (and any other
      -- abandoned pool names) drop with their nodes
      let keptIds := (logged'.map (·.idStr)).toList
      let pd' := { pd with
        pushes := pd.pushes.filter (fun (n, pid, _) =>
          keptIds.contains pid && !pd.reverts.any (·.1 == n)),
        subsumptions := pd.subsumptions }
      pure (logged', pd')
  let (synth, extraLinks) ← synthesizePoolRoots pd
    (goalClause? := (logged.find? (·.id.isRoot)).map (·.inputClause))
    (rootIdStr? := (logged.find? (·.id.isRoot)).map (·.idStr))
  let allFlats := logged ++ synth.map (·.1)
  let allIds := (allFlats.map (·.id)).toList
  -- Parent key for each node: synthetic → its pushed clause; logged → inverse
  -- of the waterfall child rule. Root Goal has none.
  let mut childKeys : Array (String × String) := #[]   -- (childIdStr, parentIdStr)
  let mut roots : Array String := #[]
  for (sn, pid) in synth do
    childKeys := childKeys.push (sn.idStr, pid)
  for (c, p) in extraLinks do
    childKeys := childKeys.push (c, p)
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

/-- Build the whole development as a single proof tree (`Development`): a
    right-nested sequence of world events in file order. `:DEFUN` /
    `:TYPE-PRESCRIPTION` become world-extending bindings; a `:DEFTHM` block
    becomes a `theorem` node; an anonymous proof block (steps with no `:DEFTHM`
    name) is an admission/termination proof, held and attached to the next
    `:DEFUN` it admits. -/
def buildDevelopment (log : ProofLog) : Except String Development := do
  let mut events : Array WorldEvent := #[]
  let mut curName : Option String := none
  let mut curFormula : SExpr := .nil
  let mut curEvents : Array ProofEvent := #[]
  let mut anon : Nat := 0
  let mut pendingTermination : Option ClauseProof := none
  -- encapsulate bracket DEPTH (audit 2026-08-03 F3): balance is enforced —
  -- a stray END (depth 0) or an unclosed BEGIN at EOF hard-fails. Nesting
  -- is supported by the counter (cov-defun-sk nests 3 deep); PAIRING
  -- semantics (scope membership, per-scope dedup) are Phase 4.
  let mut encDepth : Nat := 0
  let mut curClasses : Option SExpr := none
  for ev in log.events do
    match ev with
    | .defthm name formula .includeBook cls =>
      -- an INCLUDE-BOOK'd theorem: no waterfall runs, no proof block, no
      -- QED. An OPEN named block here still means THAT theorem's proof
      -- never closed — hard-fail exactly as below.
      if let some openName := curName then
        throw s!"buildDevelopment: theorem '{openName}' has no closing (:QED) before included theorem '{name}' — ACL2 proof incomplete or FAILED (log truncated mid-proof)."
      -- flush a pending anonymous (termination) block
      let (p?, a) ← closeBlock curName curFormula curEvents anon
      anon := a
      if let some p := p? then pendingTermination := some p
      events := events.push (.includedTheorem name formula cls)
      curEvents := #[]
    | .defthm _ _ _ _ | .qed =>
      -- A named (:DEFTHM) block is a completed proof ONLY if it ends with its
      -- (:QED). If a NEW :DEFTHM closes it instead, ACL2 never emitted QED for the
      -- open theorem — its proof FAILED/aborted (the log is truncated mid-proof).
      -- Hard-fail: a failed proof must never flow through as a reconstructed
      -- theorem (the no-silent-skip rule; a failed ACL2 run is not a theorem).
      if let some openName := curName then
        if (match ev with | .defthm _ _ _ _ => true | _ => false) then
          throw s!"buildDevelopment: theorem '{openName}' has no closing (:QED) before the next (:DEFTHM) — ACL2 proof incomplete or FAILED (log truncated mid-proof)."
      -- Close the current block: named → a theorem event; anonymous with steps
      -- → the pending termination proof for the next defun.
      let (p?, a) ← closeBlock curName curFormula curEvents anon
      anon := a
      if let some p := p? then
        if curName.isSome then
          events := events.push (.theorem { p with classes := curClasses })
        else pendingTermination := some p
      -- A :DEFTHM opens the next block; a :QED closes to the between-blocks state.
      match ev with
      | .defthm name formula _ cls =>
        curName := some name; curFormula := formula; curClasses := cls
        curEvents := #[]
      | _ => curName := none; curFormula := .nil; curEvents := #[]
    | .defun n formals body just =>
      let termination := pendingTermination.map fun t => { t with name := s!"termination of {n}" }
      events := events.push (.defun n formals body just termination)
      pendingTermination := none
    | .witnessDefun n formals body just =>
      -- BUG-019 by tag+scope (R6/Phase 4): a witness OUTSIDE any bracket
      -- has no scope to be conservative for — malformed emission.
      if encDepth == 0 then
        throw s!"buildDevelopment: witness defun '{n}' outside any \
                (:ENCAPSULATE-BEGIN) scope (malformed emission)"
      let termination := pendingTermination.map fun t =>
        { t with name := s!"termination of {n}" }
      events := events.push (.witnessDefun n formals body just termination)
      pendingTermination := none
    | .groundZeroDefun n formals body just =>
      -- A world snapshot, not an admission: it must NOT consume a pending
      -- anonymous proof block as its termination proof (its clauses are
      -- recomputed, and no waterfall ran for it in this capture).
      events := events.push (.groundZeroDefun n formals body just)
    | .groundZeroRules specs =>
      events := events.push (.groundZeroRules specs)
    | .groundZeroFcRules specs =>
      events := events.push (.groundZeroFcRules specs)
    | .groundZeroLinearRules specs =>
      events := events.push (.groundZeroLinearRules specs)
    | .groundZeroRecognizerTuples specs =>
      events := events.push (.groundZeroRecognizerTuples specs)
    | .includeBookEdge book parent =>
      events := events.push (.includeBookEdge book parent)
    | .captureEnd books =>
      -- parse already validated :STATUS :COMPLETE; recorded so consumers
      -- can gate on its presence (the strict at-EOF requirement flips
      -- after the corpus-wide recapture — tracked in TODO).
      events := events.push (.captureEnd books)
    | .typePrescription n cor bts leaves =>
      events := events.push (.typePrescription n cor bts leaves)
    | .rules specs =>
      events := events.push (.rules specs)
    | .encapsulateBegin sigs =>
      -- a bracket while a THEOREM block is open means that theorem never
      -- closed — the true malformation is the missing :QED (audit
      -- 2026-08-03 F4: name the real cause, not the bracket)
      if let some openName := curName then
        throw s!"buildDevelopment: theorem '{openName}' has no closing \
          (:QED) before (:ENCAPSULATE-BEGIN) — ACL2 proof incomplete or \
          FAILED (log truncated mid-proof)."
      encDepth := encDepth + 1
      events := events.push (.encapsulateBegin sigs)
    | .encapsulateEnd =>
      if let some openName := curName then
        throw s!"buildDevelopment: theorem '{openName}' has no closing \
          (:QED) before (:ENCAPSULATE-END) — ACL2 proof incomplete or \
          FAILED (log truncated mid-proof)."
      -- balance (audit F3): a stray END is a malformed log — the capture
      -- came from a fork predating the include-path BEGIN, or the
      -- emission regressed
      if encDepth == 0 then
        throw "buildDevelopment: stray (:ENCAPSULATE-END) with no open \
          bracket (malformed log — recapture with the current fork)"
      encDepth := encDepth - 1
      -- flush a pending anonymous (admission) block at the boundary
      let (p?, a) ← closeBlock curName curFormula curEvents anon
      anon := a
      if let some p := p? then pendingTermination := some p
      curEvents := #[]
      events := events.push .encapsulateEnd
    | .constraints fns formulas =>
      events := events.push (.constraints fns formulas)
    | .step _ | .induction _ | .poolConsider _ | .poolSubsumed _ _ =>
      curEvents := curEvents.push ev
  -- balance at EOF (audit 2026-08-03 F3): an unclosed BEGIN means the
  -- encapsulate errored mid-event — an invalid capture
  unless encDepth == 0 do
    throw s!"buildDevelopment: {encDepth} unclosed (:ENCAPSULATE-BEGIN) \
      bracket(s) at end of log (the encapsulate failed mid-capture — \
      invalid log)"
  -- Close any trailing block. A still-open NAMED block at end-of-log means the
  -- final theorem never emitted its (:QED) — ACL2's proof FAILED or the log was
  -- truncated mid-proof. Hard-fail rather than accept it as a proven theorem.
  if let some openName := curName then
    throw s!"buildDevelopment: theorem '{openName}' has no closing (:QED) at end of log — ACL2 proof incomplete or FAILED (log truncated mid-proof)."
  -- Close any trailing block.
  let (p?, _) ← closeBlock curName curFormula curEvents anon
  if let some p := p? then
    if curName.isSome then events := events.push (.theorem p)
    else pendingTermination := some p
  -- A termination proof with no following :DEFUN (unexpected; e.g. a guard proof
  -- after its defun) — surface it standalone rather than drop it.
  if let some t := pendingTermination then events := events.push (.theorem t)
  return events.foldr Development.bind Development.done

end ClauseTree

/-! ## Tests — the reconstructed clause tree of `my-len-my-app`. -/
section Tests

private def simpleLog : String := include_str "../acl2_samples/simple.proof-log"

private def simpleDev : Option Development := do
  (ClauseTree.buildDevelopment (← (ProofLog.parse simpleLog).toOption)).toOption

/-- The world events of a development, in order. -/
private partial def devEvents : Development → List WorldEvent
  | .bind e rest => e :: devEvents rest
  | .done => []

private def devTheorems (d : Development) : List ClauseProof :=
  (devEvents d).filterMap fun | .theorem p => some p | _ => none

private def devDefunNames (d : Development) : List String :=
  (devEvents d).filterMap fun | .defun n _ _ _ _ => some n | _ => none

private def simpleProof : Option ClauseProof := do
  (devTheorems (← simpleDev)).head?

/-- All clause nodes in a subtree (pre-order). -/
private partial def clauseNodes (n : ClauseNode) : List ClauseNode :=
  n :: n.children.flatMap clauseNodes

/-- Every rewriter proof-node reachable from a clause proof (across all steps,
    all literals, recursively). -/
private partial def proofNodesOf : ProofNode → List ProofNode
  | n@(.node _ _ _ cs _) => n :: cs.flatMap proofNodesOf

/-- Every rewriter proof-node reachable from a clause's branch-tree items. -/
private partial def itemNodes : List ClauseItem → List ProofNode
  | [] => []
  | .literal lp :: rest => lp.nodes.flatMap proofNodesOf ++ itemNodes rest
  | .step n :: rest => proofNodesOf n ++ itemNodes rest
  | .clausify _ :: rest => itemNodes rest
  | .useHint _ _ _ _ :: rest => itemNodes rest
  | .fcDerivations _ :: rest => itemNodes rest
  | .complementClose _ :: rest => itemNodes rest
  | .branch _ items :: rest => itemNodes items ++ itemNodes rest

private def allProofNodes (cp : ClauseProof) : List ProofNode :=
  match cp.root with
  | none => []
  | some r => (clauseNodes r).flatMap fun n => n.steps.flatMap fun s => itemNodes s.items

private def runeOf : ProofNode → Rune | .node r _ _ _ _ => r
private def equivSrcOf : ProofNode → Option EquivSource
  | .node _ _ _ _ p => p.equivSource
private def pathOf : ProofNode → List PathFrame | .node _ _ _ _ p => p.path

-- The theorem and its root clause.
#guard (simpleProof.map (·.name)) == some "MY-LEN-MY-APP"
#guard (simpleProof.bind (·.root) |>.map (·.idStr)) == some "Goal"

-- Regression: a FAILED/incomplete ACL2 proof must be REJECTED, never accepted as
-- a theorem. ACL2 emits (:DEFTHM …) at proof START and (:QED) only on SUCCESS, so a
-- :DEFTHM block with no closing :QED is a failed/truncated proof. buildDevelopment
-- must hard-fail on it (previously it silently rendered a full tree, exit 0).
-- A lone :DEFTHM, no :QED → rejected at end-of-log (trailing-block check).
#guard (ClauseTree.buildDevelopment { events := [.defthm "bogus"] }).toOption.isNone
-- Same theorem WITH its :QED → accepted (control: the gate is the missing :QED, not the block).
#guard (ClauseTree.buildDevelopment { events := [.defthm "ok", .qed] }).toOption.isSome
-- A :DEFTHM whose :QED never comes before the NEXT :DEFTHM → rejected (mid-stream check).
#guard (ClauseTree.buildDevelopment { events := [.defthm "bad", .defthm "next", .qed] }).toOption.isNone
-- Two fully-completed theorems in sequence → accepted (no false positive).
#guard (ClauseTree.buildDevelopment { events := [.defthm "a", .qed, .defthm "b", .qed] }).toOption.isSome

-- A synthesized induction node (`*1`) with two case subgoals.
#guard (simpleProof.bind (·.root) |>.map fun r =>
  (clauseNodes r).any fun n => n.induction.isSome && n.children.length == 2) == some true

-- Both induction subgoals are present (base *1/2 and step *1/1).
#guard (simpleProof.bind (·.root) |>.map fun r =>
  let ids := (clauseNodes r).map (·.idStr)
  ids.contains "Subgoal *1/1" && ids.contains "Subgoal *1/2") == some true

-- The rewriter detail is attached: my-app / my-len definition unfoldings appear.
#guard (simpleProof.map fun p =>
  (allProofNodes p).any (runeOf · == ⟨"definition", "MY-APP", none⟩)) == some true
#guard (simpleProof.map fun p =>
  (allProofNodes p).any (runeOf · == ⟨"definition", "MY-LEN", none⟩)) == some true

-- The induction hypothesis link (R-A): a solidify node is justified by
-- hypothesis literal 2 in the step case.
#guard (simpleProof.map fun p =>
  (allProofNodes p).any (equivSrcOf · == some (.literal 2))) == some true

-- The congruence path (:PATH) is threaded onto rewrite nodes (e.g. def:my-app at
-- equal arg1 → my-len arg1). Confirms the ACL2 → ProofLog → ProofTree path plumbing.
#guard (simpleProof.map fun p =>
  (allProofNodes p).any fun n => !(pathOf n).isEmpty) == some true

-- Development structure: my-len and my-app are world-event bindings (they scope
-- over the theorem that uses them); exactly one theorem.
#guard (simpleDev.map fun d => devDefunNames d) == some ["MY-LEN", "MY-APP"]
#guard (simpleDev.map fun d => (devTheorems d).length) == some 1

end Tests


/-! ## Tree printers (shared by the `acl2lean` CLI and the focused replay binary) -/

partial def printProofNodes (nodes : List ACL2.ProofNode) (indent : Nat) : IO Unit := do
  for node in nodes do
    match node with
    | .node rune lhs rhs children prov =>
      let pad := String.ofList (List.replicate (indent * 2) ' ')
      let originStr := if prov.origin.isEmpty then "" else s!" [{prov.origin}]"
      let windowStr := if prov.innerKind.isEmpty then "" else
        s!" ⟨{prov.innerKind}{if prov.blockKind.isEmpty then "" else s!" in {prov.blockKind}"}⟩"
      IO.println s!"{pad}{rune.tag}{originStr}{windowStr}"
      IO.println s!"{pad}  {lhs} => {rhs}"
      if let some wt := prov.innerTerm then
        IO.println s!"{pad}  window: {wt} @ {repr prov.innerPath}"
      if !prov.runes.isEmpty then
        let runeStrs := prov.runes.map (·.tag)
        IO.println s!"{pad}  runes: {String.intercalate ", " runeStrs}"
      if !prov.subst.isEmpty then
        let substStrs := prov.subst.map fun (k, v) => s!"{k} → {v}"
        IO.println s!"{pad}  subst: {String.intercalate ", " substStrs}"
      if let some eq := prov.equivTerm then
        IO.println s!"{pad}  equiv: {eq}"
      if let some src := prov.equivSource then
        match src with
        | .literal idx =>
          IO.println s!"{pad}  ⮑ justified by hypothesis literal {idx} (the induction hypothesis)"
        | .branchTest =>
          IO.println s!"{pad}  ⮑ justified by the enclosing unresolved-if's test (assume-true-false branch)"
        | .segment =>
          IO.println s!"{pad}  ⮑ justified by the enclosing clausify-branch segment hypothesis (:CONTEXT-SUBST)"
        | .typeSetDerived =>
          IO.println s!"{pad}  ⮑ justified by a type-set verdict under the enclosing branch facts (type-set-derived)"
      if !children.isEmpty then
        printProofNodes children (indent + 1)

/-- Render a clause step's branch tree: literals (with their rewrite chains),
    clause-level steps (branch substitutions / rewrites), and nested case
    branches. -/
partial def printClauseItems (items : List ACL2.ClauseItem)
    (pad : String) (rwIndent : Nat) : IO Unit := do
  for item in items do
    match item with
    | .literal lp =>
      if lp.nodes.isEmpty then
        IO.println s!"{pad}  │    literal {lp.index}: {lp.literal} ⇒ {lp.result}"
      else
        IO.println s!"{pad}  │    literal {lp.index}: {lp.literal} ⇒ {lp.result}  ({lp.nodes.length}-step rewrite)"
        printProofNodes lp.nodes rwIndent
    | .step (.node rune lhs rhs children _) =>
      IO.println s!"{pad}  │    {rune.ty}: {lhs} ⇒ {rhs}"
      -- A clause-level step (e.g. a termination conjecture's bare rewrite chain)
      -- can have adopted inner-rewrite children; render them too.
      if !children.isEmpty then printProofNodes children rwIndent
    | .clausify info =>
      IO.println s!"{pad}  │    clausify: {info.input}"
      IO.println s!"{pad}  │      ¬-clause: {info.negClause}"
      for (lit, cl) in info.splits do
        IO.println s!"{pad}  │      split {lit} ⇒ {cl}"
      IO.println s!"{pad}  │      out: {info.out}"
      if info.expanded then
        IO.println s!"{pad}  │      (expand-and-or fired — replay frontier)"
    | .fcDerivations derivs =>
      IO.println s!"{pad}  │    fc-derivations: {derivs.length} record(s)"
    | .complementClose lit =>
      IO.println s!"{pad}  │    complement-close: {lit}"
    | .useHint hyps ccl appC _lmis =>
      IO.println s!"{pad}  │    :use hint — {hyps.length} instantiated hyp(s):"
      for h in hyps do
        IO.println s!"{pad}  │      hyp: {h}"
      IO.println s!"{pad}  │      constraint-cl: {ccl}"
      IO.println s!"{pad}  │      application clauses: {appC}"
    | .branch segment subitems =>
      IO.println s!"{pad}  │    ┌ case branch: {segment}"
      printClauseItems subitems (pad ++ "    ") rwIndent

partial def printClauseNode (node : ACL2.ClauseNode) (indent : Nat) : IO Unit := do
  let pad := String.ofList (List.replicate indent ' ')
  -- The clause this node proves.
  let clauseStr := match node.inputClause with
    | [] => "(no clause recorded — synthesized)"
    | [lit] => s!"{lit}"
    | lits => "{" ++ String.intercalate " ∨ " (lits.map (s!"{·}")) ++ "}"
  IO.println s!"{pad}{node.idStr}:  {clauseStr}"
  -- The processors applied to this clause, in order.
  for st in node.steps do
    let res := match st.result with | .proved => "proved" | .subgoals => s!"{st.newClauses.length} subgoal(s)"
    let runeStr := if st.runes.isEmpty then "" else
      "  runes: " ++ String.intercalate ", " (st.runes.map (·.tag))
    IO.println s!"{pad}  ├─ {st.processor} ⇒ {res}{runeStr}"
    -- Processor-specific justification (fertilize target/bullet, eliminate-
    -- destructors elim sequence, generalize term→var map, …).
    for (k, v) in st.extraFields do
      IO.println s!"{pad}  │    {k}: {v}"
    -- Rewriter detail: the clause's branch tree (literals, clause-level steps,
    -- nested case branches).
    printClauseItems st.items pad (indent / 2 + 4)
    -- For processors with no branch tree (generalize, eliminate-destructors,
    -- fertilize, …), show the clauses they produced so the step isn't opaque.
    if st.result == ACL2.ProofResult.subgoals && st.items.isEmpty then
      for nc in st.newClauses do
        IO.println s!"{pad}  │    ⇒ {nc}"
  -- Induction applied here: the measure justification (what decreases, under which
  -- well-founded relation) and the per-case structure (tests + IH substitutions); the
  -- subgoals are the children below.
  if let some ind := node.induction then
    IO.println s!"{pad}  ╫ INDUCTION on {ind.term}  ({ind.subgoalCount} subgoals)"
    if ind.measure != .nil then
      let ctrlStr := String.intercalate ", " (ind.controllers.map (·.name))
      IO.println s!"{pad}      measure {ind.measure} decreases under {ind.mp}/{ind.rel}; on: {ctrlStr}"
    for c in ind.cases do
      let testsStr := String.intercalate " ∧ " (c.tests.map (·.toString))
      if c.alists.isEmpty then
        IO.println s!"{pad}      case [{testsStr}]: base (no IH)"
      else
        IO.println s!"{pad}      case [{testsStr}]:"
        for al in c.alists do
          let subst := String.intercalate ", " (al.map (fun (v, t) => s!"{v.name} := {t}"))
          IO.println s!"{pad}        IH: {subst}"
    for cl in ind.scheme do
      IO.println s!"{pad}      scheme clause: {cl}"
  -- Children (subgoal clauses).
  for c in node.children do
    printClauseNode c (indent + 4)

/-- Render a theorem/termination clause proof (its goal + clause-tree root). -/
def printClauseProof (cp : ACL2.ClauseProof) (indent : Nat) : IO Unit := do
  let pad := String.ofList (List.replicate indent ' ')
  -- The formula is the defthm statement for theorems; for termination proofs it
  -- is nil (the measure conjecture shows as the root clause below), so skip it.
  if cp.formula != .nil then IO.println s!"{pad}goal: {cp.formula}"
  match cp.root with
  | none => IO.println s!"{pad}(no logged proof — imported or trivial)"
  | some root => printClauseNode root (indent + 2)

/-- Render the whole development as one scoped proof tree: each world event in
    file order (definitions bind over the theorems that follow). -/
partial def printDevelopment : ACL2.Development → IO Unit
  | .done => pure ()
  | .bind event rest => do
    match event with
    | .encapsulateBegin sigs =>
      IO.println s!"\n── encapsulate begin (sigs: \
        {String.intercalate " " (sigs.map (·.name))}) ──"
    | .encapsulateEnd =>
      IO.println "── encapsulate end ──"
    | .groundZeroRecognizerTuples specs =>
      IO.println s!"── ground-zero recognizer tuples: {specs.length} ──"
    | .includeBookEdge book parent =>
      IO.println s!"── include-book edge: {book} ←         {parent.getD "<top>"} ──"
    | .captureEnd _ =>
      IO.println "── capture end (complete) ──"
    | .constraints fns formulas =>
      IO.println s!"── constraints for \
        {String.intercalate " " (fns.map (·.name))}: \
        {formulas.length} formula(s) ──"
    | .defun name formals body just termination =>
      let fs := String.intercalate " " (formals.map (·.name))
      IO.println s!"\n── def {name} ({fs}) ──"
      IO.println s!"  body: {body}"
      if let some j := just then
        let ms := String.intercalate " " (j.measuredSubset.map (·.name))
        IO.println s!"  admission: measure {j.measure} under {j.wfRel.name}; measured: ({ms})"
        for c in j.terminationClauses do
          IO.println s!"    obligation: {c}"
      if let some t := termination then
        IO.println "  termination proof:"
        printClauseProof t 4
    | .groundZeroDefun name formals body just =>
      let fs := String.intercalate " " (formals.map (·.name))
      IO.println s!"\n── ground-zero def {name} ({fs}) ──"
      IO.println s!"  body: {body}"
      if let some j := just then
        let ms := String.intercalate " " (j.measuredSubset.map (·.name))
        IO.println s!"  admission: measure {j.measure} under {j.wfRel.name}; measured: ({ms})"
        for c in j.terminationClauses do
          IO.println s!"    obligation (recomputed): {c}"
    | .groundZeroRules specs =>
      IO.println s!"\n── ground-zero rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        let hyps := if r.hyps.isEmpty then "" else s!" (hyps: {hs})"
        let mf := r.matchFree.elim "" (fun v => s!" (match-free {v})")
        IO.println s!"  {r.name} [{r.equiv}]: {r.lhs} ⇒ {r.rhs}{hyps}{mf}"
    | .groundZeroFcRules specs =>
      IO.println s!"\n── ground-zero FC rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        let cs := String.intercalate " ∧ " (r.concls.map (·.toString))
        IO.println s!"  {r.name}: trigger {r.trigger}; hyps {hs} ⇒ concls {cs}"
    | .groundZeroLinearRules specs =>
      IO.println s!"\n── ground-zero LINEAR rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        IO.println s!"  {r.name}: hyps {hs} ⇒ {r.concl} (max-term {r.maxTerm})"
    | .typePrescription name cor _ _ =>
      IO.println s!"\n── type-prescription {name} ──"
      IO.println s!"  {cor}"
    | .rules specs =>
      IO.println s!"\n── stored rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        let hyps := if r.hyps.isEmpty then "" else s!" (hyps: {hs})"
        IO.println s!"  {r.name} [{r.equiv}]: {r.lhs} ⇒ {r.rhs}{hyps}"
    | .theorem proof =>
      IO.println s!"\n══ THEOREM {proof.name} ══"
      printClauseProof proof 2
    | .includedTheorem name formula cls =>
      IO.println s!"\n── included theorem {name} (certified in its own book) ──"
      IO.println s!"  {formula}"
      if let some c := cls then
        IO.println s!"  :CLASSES {c}"
    | .witnessDefun name formals body _ termination =>
      let fstr := String.intercalate " " (formals.map (·.name))
      IO.println s!"\n── witness defun {name} ({fstr}) — scoped, EXCLUDED from the world ──"
      IO.println s!"  {body}"
      if let some t := termination then
        IO.println s!"  (admission proof recorded: {t.name})"
    printDevelopment rest


end ACL2
