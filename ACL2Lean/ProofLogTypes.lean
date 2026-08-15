import ACL2Lean.Syntax
import ACL2Lean.Parser

/-! # Proof-log TYPES (split from ProofLog.lean, endgame-arc weight trim)

The structured-trace datatypes — `RewriteStep`, `TraceEvent`, `ProofStep`,
`Justification`, the rule-spec records, `ProofEvent`, `ProofLog` — with no
parsing code; `ProofLog.lean` holds the parsers over these. -/

namespace ACL2

/-- Result of a waterfall step: the goal was either proved or split into subgoals. -/
inductive ProofResult where
  | proved
  | subgoals
  deriving Repr, BEq, Inhabited

/-- One frame of a rewrite's congruence path (from the log's `:PATH`),
    literal-root-first. `.arg n fn` = this frame's term (head `fn`) sits at the
    one-based argument position `n` of its parent — a real congruence position.
    `.boundary kind fn` = a descent through an unfold / rule-RHS (symbolic bkptr,
    e.g. `BODY`/`RHS`/`EXPANSION`), where the term structure changed; these align
    with the proof tree's child-nesting. Emitted by `structured-rewrite-path` in
    the instrumented ACL2 (read from the rewriter's gstack). -/
inductive PathFrame where
  | arg (idx : Nat) (fn : Symbol)
  | boundary (kind : Symbol) (fn : Symbol)
  /-- A descent into argument `idx` of a LAMBDA APPLICATION: the frame's fn
      position carries the whole `(LAMBDA (formals) body)` term (the
      `let`/`mv-let` translation — S2 2026-07-24; body descents arrive
      separately as `.boundary LAMBDA-BODY <head>`). -/
  | argLam (idx : Nat) (lam : SExpr)
  deriving Repr, Inhabited, BEq

/-- A rune identity. ACL2 prints a rune as `(:TYPE name)` or — when one event
    stores SEVERAL rules (a `:rule-classes` with multiple corollaries, e.g.
    community arithmetic's `FLOOR-ZERO`) — as `(:TYPE name . k)`. The index k
    selects WHICH stored rule the step applied, so it is part of rune identity:
    display and RuleSpec matching both carry it (J7). Any other dotted shape is
    a malformed rune and hard-fails at the parse sites. -/
structure Rune where
  /-- Rune type (`:REWRITE`/`:DEFINITION`/…), lowercased at the boundary — a
      fixed keyword-vocabulary dispatch tag (see `parseRune?`). -/
  ty : String
  /-- Rune name — an ACL2 SYMBOL IDENTITY, kept UPCASED (see `parseRune?`). -/
  name : String
  /-- The rule index for multi-rule events (`(:REWRITE FOO . 2)`); `none` for
      the plain two-element rune shape. -/
  idx : Option Nat := none
  deriving DecidableEq, Inhabited

instance : ToString Rune where
  toString r := match r.idx with
    | none => s!"(\"{r.ty}\", \"{r.name}\")"
    | some k => s!"(\"{r.ty}\", \"{r.name}\" . {k})"

/-- Repr matches the display format (and the pre-J7 pair rendering for
    index-free runes), so frontier messages stay stable. -/
instance : Repr Rune where
  reprPrec r _ := toString r

/-- Compact display form `ty:name` (with ` . k` appended for indexed runes) —
    used by the dump commands. -/
def Rune.tag (r : Rune) : String :=
  match r.idx with
  | none => s!"{r.ty}:{r.name}"
  | some k => s!"{r.ty}:{r.name} . {k}"

/-- One IF-leaf entry of an emitted `(:TYPE-PRESCRIPTION … :LEAVES …)`
    (R2 fork batch, 2026-08-14 — GAP-1/GAP-2): ACL2's own verdict for a
    return-path leaf of the fn's body, computed IN CONTEXT by the
    collector that mirrors `type-set-rec`'s `'if` case.

    Nothing here is derived Lean-side. `ts` is the CONTEXT-REFINED
    type-set (INTEGER-ABS's `(UNARY-- X)` leaf reads 6, not the
    context-free 127); `tests` are the governing IF tests outermost-first
    (negated on a false branch) — the leaf's ADDRESS, which distinguishes
    two identical leaf terms in different branches; `typeAlist` is ACL2's
    OWN derivation from those tests, emitted VERBATIM WITH SHADOWING
    (lookup is `assoc-equal`: FIRST hit wins, so `List.lookup` on this
    field is the faithful reader); `subterms` are the per-OCCURRENCE
    verdicts for the leaf's proper function-call subterms — the only type
    facts that exist for the primitives ACL2 stores no rule for
    (`DENOMINATOR`/`NUMERATOR`/`REALPART`/`IMAGPART`), with `*ts-unknown*`
    entries dropped at the emitter as carrying no fact.

    `ts = 0` (`*ts-empty*`) marks a VACUOUS leaf: ACL2's own
    contradictory-context encoding, emitted for the branches
    `assume-true-false-rec` proved unreachable. -/
structure TpLeaf where
  term : SExpr
  ts : Int
  tests : List SExpr := []
  typeAlist : List (SExpr × Int) := []
  subterms : List (SExpr × Int) := []
  deriving Repr, Inhabited, BEq

/-- `(term type-set-bits)` pairs — the shape the emitted leaf type-alists
    and subterm verdicts share. Hard-fails on any other entry. -/
private def tpTsPairs (fn what : String) (l : SExpr) :
    Except String (List (SExpr × Int)) :=
  match l.toList? with
  | some items => items.mapM fun pair =>
    match pair.toList? with
    | some [term, .atom (.number (.int ts))] => pure (term, ts)
    | _ => throw s!"TYPE-PRESCRIPTION {fn}: bad {what} entry: {repr pair}"
  | none => throw s!"TYPE-PRESCRIPTION {fn}: {what} not a list: {repr l}"

/-- Read a `:LEAVES` field: each entry is
    `(term ts ruling-tests type-alist subterm-verdicts)`. -/
def TpLeaf.parseList (fn : String) (l : SExpr) :
    Except String (List TpLeaf) :=
  match l.toList? with
  | some items => items.mapM fun entry =>
    match entry.toList? with
    | some [term, .atom (.number (.int ts)), tests, ta, subs] => do
      let some testL := tests.toList?
        | throw s!"TYPE-PRESCRIPTION {fn}: leaf ruling tests not a list: \
            {repr tests}"
      pure { term := term, ts := ts, tests := testL,
             typeAlist := ← tpTsPairs fn "leaf :type-alist" ta,
             subterms := ← tpTsPairs fn "leaf subterm-verdict" subs }
    | _ => throw s!"TYPE-PRESCRIPTION {fn}: bad leaf: {repr entry}"
  | none => throw s!"TYPE-PRESCRIPTION {fn}: :LEAVES not a list: {repr l}"

/-- A single rewrite application from ACL2's rewriter. -/
structure RewriteStep where
  /-- The rune applied, e.g. ("rewrite", "car-cons"). -/
  rune : Rune
  /-- The rule's equivalence relation ("equal", "iff", or a user equivalence) —
      non-"equal" steps route through the R-parameterized judgment (G1).
      Absent on events from sites not yet emitting `:EQUIV` (defaults equal). -/
  equiv : String := "equal"
  /-- The term before rewriting. -/
  lhs : SExpr
  /-- The term AFTER rewriting — note (B3): for a `with-lemma`/recursive-definition
      step this is the rule's instantiated RHS *after it is itself recursively
      rewritten* (those inner rewrites are logged separately as this step's
      children, under BEGIN/END-INNER-REWRITE). So `rhs` is the cumulative result,
      NOT `(apply rune once to lhs)`. A replay must treat the children as the
      sub-derivation that produced `rhs`. -/
  rhs : SExpr
  /-- Which code path produced this step (e.g., "fncall/non-recursive"). -/
  origin : String := ""
  /-- `:SWAPPED-P` (fold-back audit 2026-07-31 V3): T on an if-record whose
      test/left/right are the POST-swap orientation of rewrite-if's
      `(if x nil t)` test normalization (the branches are exchanged
      relative to the source term). -/
  swapped : Bool := false
  /-- Note (B2): this is the CUMULATIVE rune set in the ttree on ENTRY to the
      step (`all-runes-in-ttree`), i.e. rules accumulated by prior steps — NOT
      the rule this step applied. THIS step's rule is `rune`. Do not read `runes`
      as "this step's dependencies." (Exception: on a `type-set` node — built by
      ProofTree, not from a RewriteStep — `runes` IS the per-step justification.) -/
  runes : List Rune := []
  /-- Clause literal parent indices from the ttree. -/
  parents : List SExpr := []
  /-- Formal→actual substitution for definition expansions. -/
  subst : List (SExpr × SExpr) := []
  /-- The equivalence formula for rewriting-equivalence steps. -/
  equivTerm : Option SExpr := none
  /-- `:CR-RUNE` (RT2, 2026-08-15 — `emit/solidify/rewriting-equiv`,
      acl2/rewrite.lisp): the CONGRUENCE/EQUIVALENCE rune that licensed
      THIS solidify step, i.e. ACL2's own
      `(geneqv-refinementp (ffn-symb equiv-term) geneqv wrld)` — the rune
      `find-rewriting-equivalence` computed and pushed into the ttree but
      did not return. Without it a replay can only anchor on the
      ENCLOSING step's cumulative `runes`, weaker than the BUG-023
      per-step discipline. `none` on every other origin and where no
      refinement rune exists (a lambda head); a consumer that needs the
      anchor fails closed rather than falling back. -/
  crRune : Option Rune := none
  /-- Type-set of the argument (for recognizer steps). -/
  typeSet : Option Int := none
  /-- True type-set of the recognizer (type-set bits where it returns T). -/
  trueTs : Option Int := none
  /-- False type-set of the recognizer (`:FALSETS`, fork-batch item 2,
      2026-08-06): type-set bits where it returns NIL — with `trueTs` and
      `strongp`, the recognizer verdict's full emitted basis. -/
  falseTs : Option Int := none
  /-- `:STRONGP` (fork-batch item 2): T iff true-ts is exactly the
      complement of false-ts. -/
  strongp : Option Bool := none
  /-- `:ARG-LEAVES` (RT2, 2026-08-15 — `infra/recognizer-arg-leaves`,
      acl2/rewrite.lisp): on a recognizer step whose ARGUMENT is an `IF`,
      the per-branch derivation behind the `typeSet` verdict — the same
      context-refined `TpLeaf` walk, run on the argument under the
      REWRITER'S OWN type-alist. `typeSet` is the UNION over these
      branches, and the union alone is not replayable: the replay must
      case-split the `IF` and use each branch's own verdict (the
      COUNT-DOWN / MY-EVENP / CD2 termination rows, argument
      `(IF (INTEGERP N) (IF (< N '0) '0 N) '0)`). `[]` on every non-`IF`
      argument (where the collector would only repeat `typeSet`) and on
      every non-recognizer origin. -/
  argLeaves : List TpLeaf := []
  /-- The equal/type-alist verdict BASIS (R1 retirement emission,
      2026-08-07): the canonical representatives of the two sides under
      the type-alist's equality equations. -/
  canon1 : Option SExpr := none
  canon2 : Option SExpr := none
  /-- The bound disequality entry's term (`:TA-ENTRY`; none when the
      verdict came from the quotep/canon-collapse shortcuts). -/
  taEntry : Option SExpr := none
  /-- The fn-restricted tau-database slice (`:TAU-BASIS`, fork-batch
      item I, ruled 2026-08-10): on a `preprocess/tau` verdict record,
      the raw per-fn slice — tau-pair, pos/neg-implicants, form-1/2
      signature rules — for exactly the clause's fn symbols, read off
      the tau database at the verdict site. The DP consumer takes the
      slice's rules' instances as premises (read-off, not matcher
      selection). `none` on every other origin and on pre-batch logs. -/
  tauBasis : Option SExpr := none
  /-- The AMBIENT geneqv's relation symbols at this step's redex
      (`:GENEQV`, the R-lane prerequisite — `emit/with-lemma`,
      acl2/rewrite.lisp): the relation the rewriter was ALLOWED to
      preserve here, which is the honest NET-step relation when the rhs
      chain used a weaker R (the rule's own `:EQUIV` under-reports that
      case). Lower-cased symbol names, in emission order; `[]` when the
      site emits none (non-with-lemma origins, pre-batch logs). The
      R-collapse REQUIRES this list to name the R it collapses
      (fail-closed) — see `NodeCore/Congruence.lean`. -/
  geneqv : List String := []
  /-- The redex's congruence path within the literal (from `:PATH`),
      literal-root-first. Lets a replay lift this step by composing congruences
      along the path instead of locating the redex by subterm match. -/
  path : List PathFrame := []
  deriving Repr

/-- Parse an emitted SYMBOL-LIST field (`:GENEQV (PERM)`) to lower-cased
    names. Absent reads `[]` (sites that emit none); `NIL` reads `[]` (the
    empty geneqv list). Any non-symbol element or improper list is a
    malformed emission and hard-fails — the checker never guesses at a
    relation name. -/
def parseSymbolListField (fieldName : String) (v : Option SExpr) :
    Except String (List String) :=
  match v with
  | none => .ok []
  | some s =>
    match s.toList? with
    | some items => items.mapM fun e => match e with
      | .atom (.symbol sym) => .ok (sym.name.map Char.toLower)
      | other => .error s!"REWRITE-STEP: malformed :{fieldName} element {repr other}"
    | none => .error s!"REWRITE-STEP: :{fieldName} not a list: {repr s}"

/-- Read a `:CR-RUNE` field (RT2). Absent — every origin but
    `solidify/rewriting-equiv` — reads `none`; `NIL` is the emitter's own
    "no refinement rune" (a lambda head) and also reads `none`. A present
    non-rune value is a malformed emission and hard-fails: the checker
    never guesses a licensing rune. `runeOf` is the log's ONE rune parser,
    passed in rather than cloned. -/
def parseCrRuneField (runeOf : SExpr → Option Rune) (v : Option SExpr) :
    Except String (Option Rune) :=
  match v with
  | none | some .nil => .ok none
  | some r => match runeOf r with
    | some rune => .ok (some rune)
    | none => .error s!"REWRITE-STEP: malformed :CR-RUNE {repr r}"

/-- Read an `:ARG-LEAVES` field (RT2): the recognizer argument's per-branch
    derivation, in the same emitted entry shape as a `:TYPE-PRESCRIPTION`
    event's `:LEAVES`. Absent (non-recognizer origins) and `NIL`
    (non-`IF` arguments) both read `[]`; any other shape hard-fails in the
    shared leaf reader. -/
def parseArgLeavesField (v : Option SExpr) : Except String (List TpLeaf) :=
  match v with
  | none | some .nil => .ok []
  | some r => TpLeaf.parseList "recognizer :ARG-LEAVES" r

/-- A trace event from ACL2's detailed rewriter output.
    These appear inside the :REWRITES field of a waterfall step. -/
inductive TraceEvent where
  | rewriteStep (step : RewriteStep)
  | ifTestTrue (test : SExpr) (unrewrittenTest : SExpr) (justification : SExpr)
  | ifTestFalse (test : SExpr) (unrewrittenTest : SExpr) (justification : SExpr)
  | ifTestUnknown (test : SExpr) (unrewrittenTest : SExpr) (justification : SExpr)
  | beginLiteral (index : Nat) (literal : SExpr) (notFlg : Bool)
  | endLiteral (index : Nat) (result : SExpr) (branches : Nat)
  | rewrittenLiteral (original : SExpr) (result : SExpr)
  | beginBranch (segment : SExpr)
  | endBranch
  | caseSplit (literalIndex : Nat) (numBranches : Nat)
  | branchSubstitution (equivalence : SExpr) (lhs : SExpr) (rhs : SExpr)
  | contextSubst (var : SExpr) (value : SExpr) (justification : SExpr)
  /-- A rule hypothesis relieved SILENTLY (no rewrite events): by a type-alist
      lookup, by type-set under the clause type-alist, or by the backchain
      ancestors stack (`emit/relieve-hyp/*`). `hyp` is the INSTANTIATED hyp;
      `origin` says how. Lands inside the adopting step's `:KIND HYP` block —
      the replay's rule recipe consumes it in place of a relief chain. -/
  | hypRelief (hyp : SExpr) (origin : String) (taRunes : List Rune)
      (parents : List SExpr := [])
      -- taDerivations: the entry's UNFLATTENED fc-derivation structure
      -- (:TA-DERIVATIONS, cluster item 4). NIL by construction at today's
      -- relief sites (fcds are expunged before the type-alist — the real
      -- provenance rides the clause-level :FC-DERIVATIONS event, joined by
      -- :CONCL); kept for a future unexpunged path.
      (taDerivations : List SExpr := [])
  /-- The clause's approved forward-chaining derivations, emitted where
      ACL2 flattens them (`emit/fc-derivations`, cluster item 4): raw
      per-derivation plists (:RUNE :CONCL :TRIGGER :SUBST :PARENTS
      :SUPPORTS). The Phase-6 consumer joins :CONCL with relieved
      hyps/entry terms. -/
  | fcDerivations (derivations : List SExpr)
  /-- The add-literal COMPLEMENT close (`emit/complement-close`,
      fork-batch item 7, 2026-08-06 — the B1 expiry's emission): adding
      `lit` to the clause under construction found its complement among
      the existing literals, so the clause is true. Replaces the
      inferred-from-absence reading in the replay's complement-tautology
      arm. -/
  | complementClose (lit : SExpr)
  /-- The add-literal DUPLICATE drop (`emit/dedup-drop`, fork-batch
      item E, 2026-08-10 — the close-out audit's D1 remedy): adding
      `lit` to the clause under construction found it already among the
      existing literals, so the clause is returned unchanged. Replaces
      the inferred-from-shape trigger in the replay's dedup-skip arm
      (`dedupSkipClose`, held under expiry until this record). -/
  | dedupDrop (lit : SExpr)
  /-- A DERIVED type-alist entry's provenance (`emit/ta-subst`,
      user-approved 2026-08-07): assume-true-false's substitution pass
      transformed the bound entry `from_` into `new_` by replacing
      `substOld` with `substNew` (the equality being assumed); `ts` is
      the entry's unchanged type-set. Directs the equation-closure
      replay's derived-entry class (R1 rung B). -/
  | taSubst (new_ : SExpr) (from_ : SExpr) (ts : Int)
      (substNew : SExpr) (substOld : SExpr)
  | typeSetReasoning (term : SExpr) (result : SExpr) (notFlg : Bool) (justification : SExpr)
  | beginInnerRewrite (kind : String) (swapped : Bool := false) (term : Option SExpr := none)
      (path : List PathFrame := [])
  | endInnerRewrite (kind : String)
  | beginIfRewrite (test : SExpr) (unrewrittenTest : SExpr)
  | endIfRewrite (test : SExpr) (result : SExpr)
  /-- A `:USE` hint's payload (`emit/use-hint`, apply-top-hints-clause):
      the instantiated lemma HYPS, the CONSTRAINT-CL the step's rewrite
      chain walks (its true root), and the surviving application clauses. -/
  | useHint (hyps : List SExpr) (constraintCl : List SExpr)
      (appClauses : List (List SExpr))
      -- lmiLst: the lemma instances that generated `hyps`, verbatim and
      -- positionally aligned (:LMI-LST, close-out cluster item 1): each a
      -- name, (:instance name (var . term)…), or (:functional-instance …).
      -- [] on pre-cluster logs — the R7a composition hard-fails on absence.
      (lmiLst : List SExpr := [])
  /-- Clausify checkpoints (preprocess formula → clause set; emit/clausify/*):
      the input term, the neg-clause pass, per-negated-literal splits, the
      conjoined output set, and the expand-and-or marker (a replay frontier). -/
  | clausifyInput (term : SExpr)
  | clausifyNeg (clause : List SExpr)
  | clausifySplit (lit : SExpr) (clause : List SExpr)
  | clausifyOut (clauses : List (List SExpr))
  | clausifyExpand (fromTerm toTerm : SExpr) (pos : Bool) (runes : List Rune)
  /-- Literal-clausify DECISION TRACE (emit/if-interp/test, partial logging —
      docs/notes/2026-07-03_branch-split-spine.md): one event per if-test
      decision while `rewrite-clause` clausifies a rewritten literal.
      `verdict` ∈ split/true/false, `how` ∈ constant/assumed/split; `path` is
      the tests split so far, outermost-first, as (assumed-true?, test). The
      justification of an `assumed` verdict is deliberately NOT recorded — the
      replay re-derives it fail-closed from the closed syntactic rule set. -/
  | clausifyTest (test : SExpr) (verdict : String) (how : String)
      (path : List (Bool × SExpr))
  /-- The LEAF of one assume-true-false path (emit/if-interp/leaf): its value
      and outcome — `dropped` (true leaf), `segment-false` (false leaf: the
      path's negations form the segment), `segment-open` (unresolved leaf:
      joins the segment as a literal). For the two SEGMENT outcomes, `segment`
      is the clause segment ACL2's converter constructed for this leaf (the
      exact leaf→child-clause link — the path alone does not determine it:
      the converter drops literals subsumed by an assumed constant equality). -/
  | clausifyLeaf (value : SExpr) (outcome : String) (path : List (Bool × SExpr))
      (segment : Option (List SExpr))
  /-- Fired-marker (emit/if-interp/satriani-fired,
      emit/clausify/subsumption-loop-fired): a post-pass RESHAPED the segment
      set beyond the decision trace — the replay hard-fails on it rather than
      mis-attributing segments. -/
  | clausifySetReshaped (which : String)
  /-- The strip-branches AND-shape conjunction split
      (emit/strip-branches/and-shape, S1.2 2026-07-23): `(IF left right
      'NIL)` clausifies as the UNION of the two sides' clause sets with no
      if-interp test event — this marker records the split so the two sides'
      leaves have explicit provenance (the ORDEREDP-ISORT pin). -/
  | clausifyConjunction (left : SExpr) (right : SExpr)
  deriving Repr

/-- A single waterfall step from ACL2's structured proof output. -/
structure ProofStep where
  clauseId : String
  processor : String
  result : ProofResult
  /-- Runes used in this step, e.g. ("rewrite", "car-cons"). -/
  runes : List Rune
  /-- Full detailed trace events from ACL2's rewriter. -/
  traceEvents : List TraceEvent := []
  /-- Input clause (disjunction of literals). -/
  inputClause : List SExpr := []
  /-- Output clauses if result is subgoals. -/
  newClauses : List SExpr := []
  /-- Every STEP plist field not otherwise modeled above, captured verbatim as
      (keyword, value) — so nothing is silently dropped. This is where the
      processor-specific justifications live: `:FERTILIZE` (:bullet/:target/
      :equiv), `:ELIMSEQUENCE`/`:ELIMVARS` (destructor elimination), `:GENERALIZE`
      (:terms/:vars). The replay reads these to mirror fertilize/eliminate/
      generalize steps. -/
  extraFields : List (String × SExpr) := []
  deriving Repr

namespace ProofStep

/-- Extract just the rewrite steps from the trace events. -/
def rewriteSteps (s : ProofStep) : List RewriteStep :=
  s.traceEvents.filterMap fun
    | .rewriteStep step => some step
    | _ => none

end ProofStep

/-- One case of an induction scheme: the governing `tests` (the conditions under which this
    case applies) and, per induction hypothesis, the substitution `alist` (var ↦ term) giving
    the IH instance. A base case has `alists = []`; a step case has one alist per recursive call.
    From ACL2's `tests-and-alists`. -/
structure InductionCase where
  tests : List SExpr
  alists : List (List (Symbol × SExpr))
  deriving Repr, Inhabited

/-- An induction scheme choice from ACL2, with its MEASURE JUSTIFICATION (from the winning
    candidate's `justification`): what decreases (`measure`) under the well-founded relation
    `rel` on domain `mp`, over the controller variables `controllers`; plus the per-case structure
    (`cases`: tests + IH substitutions). The justification fields default to empty so legacy
    proof-logs (pre measure-emission) still parse. -/
structure InductionStep where
  /-- The function call that triggered induction, e.g. (MY-APP A B). -/
  term : SExpr
  subgoalCount : Nat
  /-- The generated clause set (each clause is a disjunction of literals). -/
  scheme : List SExpr
  /-- User-level induction term (`:XTERM`; `term` may be an induction-rule alias). -/
  xterm : SExpr := .nil
  /-- The measure term that decreases, e.g. `(acl2-count x)`. -/
  measure : SExpr := .nil
  /-- The well-founded relation, e.g. `o<`. -/
  rel : SExpr := .nil
  /-- The relation's domain predicate, e.g. `o-p`. -/
  mp : SExpr := .nil
  /-- The conjecture-level controller variables the induction is on (the measure's measured
      formals, instantiated to the conjecture's actuals). -/
  controllers : List Symbol := []
  /-- Per-case tests + IH substitution alists. -/
  cases : List InductionCase := []
  /-- The clauses `remove-trivial-clauses` DELETED from the scheme
      (`:SCHEME-DROPPED`, emission arc audit 2026-07-22): each was certified
      trivially true by ACL2's verdict-only `trivial-clause-p`/`if-tautologyp`
      check — the POSITIVE per-clause record the replay's carve-out discharge
      of a dropped case branch is gated on. -/
  schemeDropped : List SExpr := []
  deriving Repr

/-- Where a theorem comes from in the proof log. -/
inductive TheoremSource where
  | local       -- proved in this file
  | includeBook -- imported from another book
  | unknown     -- source not specified (old trace format)
  deriving Repr, BEq

/-- The admission JUSTIFICATION a recursive defun carries (emitted from the
    world's `justification` record at admission): the measure term, the
    well-founded relation, and the measured formal subset — the data the
    replay needs to discharge `total:fn` hypotheses by well-founded induction
    on the admitted measure. -/
structure Justification where
  measure : SExpr
  wfRel : Symbol
  measuredSubset : List Symbol
  /-- The clique's RAW measure clauses (the complete per-recursive-call-site
      decrease obligations ACL2's termination-machine produced at admission,
      BEFORE clean-up could drop trivially-true members). Each entry is one
      clause (a disjunction of literals, as an s-expression list). -/
  terminationClauses : List SExpr
  /-- The admission's cited rune set (`:TERMINATION-RUNES`, fork-batch
      item H, 2026-08-10): `all-runes-in-ttree` of the admission proof's
      accumulated ttree, PER-ADMISSION granularity (one set for the whole
      clique — the ttree is not per-clause). `none` = the channel is
      absent (an include-book re-emission recomputes clauses without
      re-running admission, so no ttree exists); `some []` = the
      admission cited no rules (pure primitive reasoning). The DP
      premise passes gate rule-premise injection on this set wherever
      the channel exists. -/
  terminationRunes : Option (List Rune) := none
  deriving Repr

/-- A STORED rewrite rule exactly as ACL2 created it (`emit/rule` → the
    `(:RULES …)` event): the normalized hyps/equiv/lhs/rhs the rewriter
    actually applies — which can DIFFER from the defthm formula
    (implies-flattening, iff→equal strengthening, and-splitting;
    docs/plans/2026-07-05_theorem-dependency-hypotheses.md). The replay's
    `rule:<thm>` hypotheses state exactly this. -/
structure RuleSpec where
  name : String
  /-- The rune index for multi-rule events (J7) — part of the rule's identity:
      a step citing `(:REWRITE FOO . 2)` matches ONLY the spec with idx 2. -/
  idx : Option Nat := none
  hyps : List SExpr
  equiv : String
  lhs : SExpr
  rhs : SExpr
  /-- The rule's `:match-free` flag (`some "all"` / `some "once"` — lowercase
      dispatch tags — or `none`). Carried only by ground-zero rule SNAPSHOTS
      (design D5: e.g. `LEXORDER-TRANSITIVE` is `(:rewrite :match-free :all)`);
      the capture-time `(:RULES …)` entries do not emit it (their free-var
      relief is replayed from the recorded relief chains instead). -/
  matchFree : Option String := none
  /-- The rule's stored backchain-limit-lst, verbatim (`nil` = unlimited;
      else a per-hyp list) — capture-time entries only (S1.2 2026-07-23);
      gz snapshots default `nil` until their emitter carries it. -/
  backchainLimit : SExpr := .nil
  deriving Repr, Inhabited, BEq

/-- A FORWARD-CHAINING-class ground-zero rule snapshot entry
    (`(:GROUND-ZERO-FC-RULES ((rune trigger hyps concls match-free) …))`,
    emission arc 2026-07-21): the stored rule fields verbatim. Consumed by
    the FC-derived type-alist relief recipe. -/
structure FcRuleSpec where
  name : String
  trigger : SExpr
  hyps : List SExpr
  concls : List SExpr
  matchFree : Option String := none
  deriving Repr, Inhabited

/-- A RECOGNIZER-TUPLE snapshot entry
    (`(:GROUND-ZERO-RECOGNIZER-TUPLES ((fn rune true-ts false-ts strongp)
    …))`, fork-batch item 2, 2026-08-06): the recognizer-alist tuples of
    cited symbols — the verdict basis of ACL2's `type-set-recognizer`.
    Retires the Lean-side `builtinRecogFacts` registry (drift R2) and
    gates the ground-hyp discharge (user ruling R4). -/
structure RecognizerTupleSpec where
  fn : String
  rune : Rune
  trueTs : Int
  falseTs : Int
  strongp : Bool
  deriving Repr, Inhabited

/-- A LINEAR-class ground-zero rule snapshot entry
    (`(:GROUND-ZERO-LINEAR-RULES ((rune hyps concl max-term) …))`,
    sorting-absolute 2b): the stored `linear-lemma` fields verbatim.
    Consumed as the DP obligation's premise where simplify's linear
    arithmetic cites the rune (verdict-only). -/
structure LinearRuleSpec where
  name : String
  hyps : List SExpr
  concl : SExpr
  maxTerm : SExpr
  deriving Repr, Inhabited

/-- One entry of an emitted `(:TYPE-PRESCRIPTION … :ALL-TPS …)` (R2 fork
    batch item 3, 2026-08-14): a STORED type-prescription rule of the fn,
    verbatim. ACL2 keeps CONDITIONAL type-prescriptions (`hyps` is a field
    of its `type-prescription` defrec) and the strong facts live exactly
    there — `BINARY-APPEND` stores both its weak definitional
    cons-or-second-argument rule and the boot-strap `TRUE-LISTP-APPEND`
    (`(IMPLIES (TRUE-LISTP B) (TRUE-LISTP (BINARY-APPEND A B)))`), which
    the emitters' one-of-N definitional selectors used to discard. The
    event's `:COROLLARY`/`:BASICTS` fields still carry the DEFINITIONAL
    rule alone; this list is additive.

    RT2 (T1+2 sprint, 2026-08-15) added the last two fields, because
    rune/hyps/basicTs/corollary let a consumer SEE a strengthening but not
    ADMIT one. `term` is the rule's own pattern (`(BINARY-APPEND A B)`) —
    a stored rule's `hyps` and `corollary` speak the RULE's variables, not
    the fn's formals, and `leaves` is the fn's body instantiated through
    the formals→term-args substitution, so all four speak the same
    variables. `leaves` is the same context-refined `TpLeaf` shape as the
    event's `:LEAVES`, computed under the type-alist THIS RULE'S
    HYPOTHESES generate: `BINARY-APPEND`'s leaves are `(3072, *ts-unknown*)`
    unconditionally but `(1024, 1152)` under `((TRUE-LISTP B))`, both
    inside `TRUE-LISTP-APPEND`'s `basicTs` 1152.

    Honest caveat (emitter tag `infra/tp-all`): a rule proved by a real
    theorem rather than read off the body need NOT have its leaves inside
    its `basicTs`. The field reports what ACL2's type-set says in that
    context; a consumer that cannot admit a rule from it fails closed. -/
structure TpRuleSpec where
  rune : Rune
  hyps : List SExpr
  basicTs : Int
  corollary : SExpr
  /-- The rule's own pattern term, `(fn a₁ … aₙ)` — the variable space
      `hyps`, `corollary` and `leaves` are stated in. -/
  term : SExpr
  /-- The fn's body leaves under this rule's hypotheses (see above). -/
  leaves : List TpLeaf
  deriving Repr, Inhabited

/-- Read an `:ALL-TPS` field: each entry is
    `(rune hyps basic-ts corollary term leaves)`. `runeOf` is the log's ONE
    rune parser, passed in rather than cloned. The 4-field R2 shape is NOT
    accepted: a half-read entry would silently drop the admissibility data
    the last two fields carry, so an old log hard-fails here rather than
    parsing into an entry that means less than it says. -/
def TpRuleSpec.parseList (fn : String) (runeOf : SExpr → Option Rune)
    (l : SExpr) : Except String (List TpRuleSpec) :=
  match l.toList? with
  | some items => items.mapM fun entry =>
    match entry.toList? with
    | some [runeE, hypsE, .atom (.number (.int bts)), cor, term, leavesE] => do
      let some rune := runeOf runeE
        | throw s!"TYPE-PRESCRIPTION {fn}: bad :ALL-TPS rune: {repr runeE}"
      let some hyps := hypsE.toList?
        | throw s!"TYPE-PRESCRIPTION {fn}: :ALL-TPS hyps not a list: \
            {repr hypsE}"
      pure { rune := rune, hyps := hyps, basicTs := bts, corollary := cor,
             term := term, leaves := ← TpLeaf.parseList fn leavesE }
    | _ => throw s!"TYPE-PRESCRIPTION {fn}: bad :ALL-TPS entry: {repr entry}"
  | none => throw s!"TYPE-PRESCRIPTION {fn}: :ALL-TPS not a list: {repr l}"

/-- The spec's identity key for name-keyed maps/tags: the rune name, with the
    multi-rule index appended in ACL2's own print form (`FOO . 2`). Distinct
    stored rules of one event get distinct keys (spaces cannot occur in an
    unescaped ACL2 symbol name, so this cannot collide with a plain name). -/
def RuleSpec.runeKey (r : RuleSpec) : String :=
  match r.idx with
  | none => r.name
  | some k => s!"{r.name} . {k}"

/-- A single event in the proof log. -/
inductive ProofEvent where
  | defun (name : String) (formals : List Symbol) (body : SExpr)
          (just : Option Justification := none)
  /-- A `local` WITNESS defun (`:SOURCE :LOCAL-WITNESS`, R6/Phase 4):
      admitted inside an encapsulate whose world effects ACL2 discards at
      scope close. Recorded SCOPED — `buildDevelopment` requires an open
      bracket, and `Development.toWorld` excludes it by construction
      (BUG-019's resolution by tag+scope: the certified world never
      contains witness bodies). -/
  | witnessDefun (name : String) (formals : List Symbol) (body : SExpr)
      (just : Option Justification := none)
  /-- Encapsulate bracket OPEN (`:ENCAPSULATE-BEGIN`, cluster item 2 /
      R6): everything to the matching END belongs to the scope; BOTH
      passes' events are inside — per-scope :DEFTHM dedup is a PHASE-4
      obligation (recorded in TODO; audit 2026-08-03 F5 corrected an
      earlier present-tense claim). Scope SEMANTICS (toWorld witness
      handling, ScopeHolds, dedup) land with Phase 4's scoped
      extensions — until then Development records the brackets and
      `buildDevelopment` enforces BALANCE (a stray END or an unclosed
      BEGIN at EOF hard-fails — audit F3). -/
  | encapsulateBegin (sigs : List Symbol)
  | encapsulateEnd
  /-- The scope's constraint axioms (`:CONSTRAINTS`, verbatim from ACL2's
      constraint-lst). `:UNKNOWN-CONSTRAINTS` hard-fails at parse. -/
  | constraints (fns : List Symbol) (formulas : List SExpr)
  | defthm (name : String) (formula : SExpr := .nil) (source : TheoremSource := .unknown)
      -- classes: the RAW rule-classes, verbatim (:CLASSES, cluster item 5).
      -- `none` = pre-cluster log (no :CLASSES key); `some .nil` = the
      -- event DECLARED `:rule-classes nil` — distinct by design (audit
      -- 2026-08-03 F6: conflating them made the ratified
      -- absence-vs-presence gating unimplementable). The
      -- equivalence/congruence gates consume the declared class once
      -- present.
      (classes : Option SExpr := none)
  | typePrescription (name : String) (corollary : SExpr)
      (basicTs : Option Int := none) (leaves : List TpLeaf := [])
      (allTps : List TpRuleSpec := [])
  /-- The stored rewrite rules created since the previous flush (in creation
      order; emitted before the next :DEFTHM, hence before any use). -/
  | rules (specs : List RuleSpec)
  /-- A ground-zero defun SNAPSHOT (`(:DEFUN … :SOURCE :GROUND-ZERO)`,
      design D3): a boot-strap definition read off ACL2's world at capture
      end because the captured events cite it — same payload as `defun`,
      with the recursive case carrying RECOMPUTED termination clauses. -/
  | groundZeroDefun (name : String) (formals : List Symbol) (body : SExpr)
          (just : Option Justification := none)
  /-- The cited ground-zero REWRITE rules read off ACL2's world at capture
      end (`(:GROUND-ZERO-RULES …)`, design D5) — same entry shape as
      `rules` plus the `:match-free` flag. -/
  | groundZeroRules (specs : List RuleSpec)
  /-- The cited ground-zero FORWARD-CHAINING rules (`(:GROUND-ZERO-FC-RULES
      …)`, emission arc 2026-07-21): stored trigger/hyps/concls verbatim. -/
  | groundZeroFcRules (specs : List FcRuleSpec)
  /-- The cited ground-zero LINEAR rules (`(:GROUND-ZERO-LINEAR-RULES …)`,
      sorting-absolute 2b): stored hyps/concl/max-term verbatim. Since
      fork-batch item 1 (2026-08-06) the snapshot also covers cited LOCAL
      :LINEAR rules (the predefined-only gate dropped). -/
  | groundZeroLinearRules (specs : List LinearRuleSpec)
  /-- The cited recognizer-alist tuples
      (`(:GROUND-ZERO-RECOGNIZER-TUPLES …)`, fork-batch item 2). -/
  | groundZeroRecognizerTuples (specs : List RecognizerTupleSpec)
  /-- An include GRAPH edge (`(:INCLUDE-BOOK-EDGE :BOOK … :PARENT …)`,
      fork-batch item 6): `book` is the included book's familiar name,
      `parent` the including book (none at top level). One event per
      ENCOUNTER — redundant includes still contribute their edge. -/
  | includeBookEdge (book : String) (parent : Option String)
  /-- The post-`ld` capture manifest (`(:CAPTURE-END :BOOKS … :STATUS
      :COMPLETE)`, fork-batch item 8): ACL2's own record of the loaded
      books (include-book-alist, kept opaque) + the explicit completion
      marker. A parse REQUIRES `:STATUS :COMPLETE` — any other status
      hard-fails. -/
  | captureEnd (books : SExpr)
  /-- Pool-processing events (`emit/pool-consider` / `emit/pool-subsumed`):
      pop-clause CONSIDERS pool roots in its own (subsumption-reordered)
      order — the steps/induction after a `poolConsider` belong to that pool
      root; a `poolSubsumed` root was regarded as proved pending the MORE
      GENERAL `by_` root. Names are pool-lsts, e.g. `[1, 1, 1]` = `*1.1.1`. -/
  | poolConsider (name : List Nat)
  | poolSubsumed (name : List Nat) (by_ : List Nat)
  | step (s : ProofStep)
  | induction (i : InductionStep)
  | qed
  deriving Repr

/-- Complete proof log, a sequence of proof events. -/
structure ProofLog where
  events : List ProofEvent
  deriving Repr

end ACL2
