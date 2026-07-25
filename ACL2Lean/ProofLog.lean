import ACL2Lean.Syntax
import ACL2Lean.Parser

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
  /-- Type-set of the argument (for recognizer steps). -/
  typeSet : Option Int := none
  /-- True type-set of the recognizer (type-set bits where it returns T). -/
  trueTs : Option Int := none
  /-- The redex's congruence path within the literal (from `:PATH`),
      literal-root-first. Lets a replay lift this step by composing congruences
      along the path instead of locating the redex by subterm match. -/
  path : List PathFrame := []
  deriving Repr

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
  | typeSetReasoning (term : SExpr) (result : SExpr) (notFlg : Bool) (justification : SExpr)
  | beginInnerRewrite (kind : String)
  | endInnerRewrite (kind : String)
  | beginIfRewrite (test : SExpr) (unrewrittenTest : SExpr)
  | endIfRewrite (test : SExpr) (result : SExpr)
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
  deriving Repr, Inhabited

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
  | defthm (name : String) (formula : SExpr := .nil) (source : TheoremSource := .unknown)
  | typePrescription (name : String) (corollary : SExpr)
      (basicTs : Option Int := none) (leaves : List (SExpr × Int) := [])
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

namespace ProofLog

/-- Look up a keyword in a plist-style s-expression list.
    Given `[:key1, val1, :key2, val2, ...]`, returns `val` for the matching key. -/
private def lookupKeyword (kw : String) : List SExpr → Option SExpr
  | .atom (.keyword k) :: v :: rest =>
    if k == kw then some v else lookupKeyword kw rest
  | _ :: rest => lookupKeyword kw rest
  | [] => none

/-- All (keyword, value) pairs of a plist whose key is NOT in `known` — used to
    capture unmodeled fields verbatim rather than silently dropping them. -/
private def plistExtras (known : List String) : List SExpr → List (String × SExpr)
  | .atom (.keyword k) :: v :: rest =>
    -- keyword names are stored upcased (readtable :upcase); the extra-field
    -- KEYS are internal dispatch tags looked up with lowercase literals
    -- (`.lookup "poolname"` etc.), so canonicalize to lowercase here.
    let k := k.map Char.toLower
    if known.contains k then plistExtras known rest
    else (k, v) :: plistExtras known rest
  | _ :: rest => plistExtras known rest
  | [] => []

/-- Extract a string from a symbol or string atom. -/
private def atomString? : SExpr → Option String
  | .atom (.symbol s) => some s.name
  | .atom (.string s) => some s
  | .atom (.keyword k) => some k
  | _ => none

/-- Parse a single rune like `(:REWRITE CAR-CONS)` — or the multi-rule shape
    `(:REWRITE FLOOR-ZERO . 3)` (J7) — into a `Rune`.
    The rune TYPE (`:REWRITE`/`:DEFINITION`/…) is a fixed keyword-vocabulary
    dispatch tag — we canonicalize it to LOWERCASE at the boundary (analogous
    to `normalizeKey` for theorem-option keys). The rune NAME is an ACL2
    SYMBOL IDENTITY (a theorem/function name — `car-cons`, `perm-symmetric`,
    `my-app`) that must match the same symbol as it is stored elsewhere
    (World keys, theorem names, dependency-proof keys), so it stays UPCASED
    (readtable :upcase) exactly as the parser produced it. A dotted tail that
    is not a nonnegative integer is malformed (fail-closed at the callers). -/
private def parseRune? : SExpr → Option Rune
  | .cons (.atom (.keyword runeType)) (.cons nameExpr tail) =>
    let ty := runeType.map Char.toLower
    let name := match atomString? nameExpr with
      | some name => name
      | none => toString (repr nameExpr)
    match tail with
    | .nil => some { ty, name }
    | .atom (.number (.int k)) =>
      if k ≥ 0 then some { ty, name, idx := some k.toNat } else none
    | _ => none
  | _ => none

/-- Parse a rune list like `((:REWRITE FOO) (:DEFINITION BAR))`. Hard-fails on a
    malformed rune or a non-list (no silent drop). -/
def parseRunes (s : SExpr) : Except String (List Rune) :=
  match s.toList? with
  | some items => items.mapM fun r => match parseRune? r with
    | some rune => pure rune
    | none => throw s!"bad rune in rune list: {repr r}"
  | none => throw s!"rune list is not a list: {repr s}"

/-- Parse one `(bkptr . fn)` frame of a `:PATH`. Numeric `bkptr` → `.arg`; symbolic
    `bkptr` (BODY/RHS/EXPANSION/…) → `.boundary`. Hard-fails on a non-symbol `fn`
    (lambda/quote paths not yet supported) or a malformed pair (no silent drop). -/
private def parsePathFrame (pair : SExpr) : Except String PathFrame := do
  -- Each frame is the dotted pair `(bkptr . fn)` = `.cons bkptr fn`.
  let (bk, fn) ← match pair with
    | .cons bk fn => pure (bk, fn)
    | _ => throw s!"REWRITE-STEP :PATH frame not a (bkptr . fn) pair: {repr pair}"
  match fn with
    | .atom (.symbol s) =>
      match bk with
      | .atom (.number (.int n)) => pure (.arg n.toNat s)
      | .atom (.symbol k) => pure (.boundary k s)
      | _ => throw s!"REWRITE-STEP :PATH frame bkptr not a number/symbol: {repr bk}"
    | .cons (.atom (.symbol lam)) _ =>
      -- a LAMBDA-application frame (S2 2026-07-24): the fn position is the
      -- whole lambda term; only NUMERIC bkptrs are attested (arg descents —
      -- body descents come as `.boundary LAMBDA-BODY <head>` instead)
      if lam.isNamed "LAMBDA" then
        match bk with
        | .atom (.number (.int n)) => pure (.argLam n.toNat fn)
        | _ => throw s!"REWRITE-STEP :PATH lambda frame bkptr not a number \
                        (unattested shape): {repr bk}"
      else
        throw s!"REWRITE-STEP :PATH frame fn not a symbol/lambda: {repr fn}"
    | _ => throw s!"REWRITE-STEP :PATH frame fn not a symbol/lambda \
                    (quote unsupported): {repr fn}"

/-- Parse a single (:REWRITE-STEP :RUNE r :LHS l :RHS r …) s-expression. -/
private def parseRewriteStep? (s : SExpr) : Except String RewriteStep := do
  match s.toList? with
  | some items =>
    match items with
    | .atom (.keyword "REWRITE-STEP") :: rest =>
      let rune ← match lookupKeyword "RUNE" rest with
        | some r => match parseRune? r with
          | some rune => pure rune
          | none => throw s!"REWRITE-STEP: bad :RUNE: {repr r}"
        | none => throw "REWRITE-STEP: missing :RUNE"
      let lhs ← match lookupKeyword "LHS" rest with
        | some s => pure s
        | none => throw "REWRITE-STEP: missing :LHS"
      let rhs ← match lookupKeyword "RHS" rest with
        | some s => pure s
        | none => throw "REWRITE-STEP: missing :RHS"
      -- Optional provenance fields. ABSENT :ORIGIN is normal (older/plain
      -- steps); a PRESENT-but-non-symbol :ORIGIN is a malformed emission and
      -- hard-fails — origin is a primary replay dispatch key, and "" would
      -- route the node down the wrong recipe (fail-closed audit N2).
      let origin ← match lookupKeyword "ORIGIN" rest with
        -- origin is a dispatch tag (e.g. "preprocess/if-iff"); lowercase it.
        | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
        | some other => throw s!"REWRITE-STEP: malformed :ORIGIN {repr other}"
        | none => pure ""
      -- :EQUIV is REQUIRED: the emitter states every step's equivalence
      -- relation explicitly (all 65 push sites emit it; the two IFF-flavored
      -- ones are labeled 'iff). The checker does NO inference — a missing or
      -- malformed :EQUIV is an emission gap and hard-fails (audited 2026-06-10;
      -- the old default-to-"equal" was fail-open).
      let equiv ← match lookupKeyword "EQUIV" rest with
        | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
        | some (.cons a rest') =>
          -- a COMPOUND geneqv (S2b option B, 2026-07-25): the emitter could
          -- not summarize the generated relation in one symbol and emitted
          -- the verbatim equiv-name list (e.g. a PERM congruence context).
          -- Parsed CANONICALLY — "(perm)", "(iff same-len2)" — so the step
          -- fails at ITS node's equiv gate (G1 frontier, named), not here:
          -- a parser hard-fail has BOOK granularity and killed six unrelated
          -- ordered-perms rows. Non-symbol elements still hard-fail.
          match (SExpr.cons a rest').toList? with
          | some l => do
            let names ← l.mapM fun e => match e with
              | .atom (.symbol s) => pure (s.name.map Char.toLower)
              | other => throw s!"REWRITE-STEP: malformed :EQUIV list element {repr other}"
            pure ("(" ++ String.intercalate " " names ++ ")")
          | none => throw s!"REWRITE-STEP: malformed :EQUIV (improper list) {repr (SExpr.cons a rest')}"
        | some other => throw s!"REWRITE-STEP: malformed :EQUIV {repr other}"
        | none => throw "REWRITE-STEP: missing :EQUIV — the emitter must state \
                         the step's equivalence; the checker does not infer it"
      let runes ← match lookupKeyword "RUNES" rest with
        | some r => match r.toList? with
          | some items => items.mapM fun r => match parseRune? r with
            | some rune => pure rune
            | none => throw s!"REWRITE-STEP: bad rune in :RUNES: {repr r}"
          | none => throw s!"REWRITE-STEP: :RUNES not a list: {repr r}"
        | none => pure []
      -- :PARENTS gates solidify/IH linking; a present-but-non-list value
      -- must hard-fail like :RUNES/:SUBST/:PATH, not default to [] (which
      -- would push a parent-tagged node into the IH-matching path —
      -- fail-closed audit N3).
      let parents ← match lookupKeyword "PARENTS" rest with
        | some r => match r.toList? with
          | some items => pure items
          | none => throw s!"REWRITE-STEP: :PARENTS not a list: {repr r}"
        | none => pure []
      let subst ← match lookupKeyword "SUBST" rest with
        | some r => match r.toList? with
          | some items => items.mapM fun pair =>
            match pair.toList? with
            | some [k, v] => pure (k, v)
            | _ => match pair with  -- dotted pair (k . v) or (k . (v ...))
              | .cons k v => pure (k, v)
              | _ => throw s!"REWRITE-STEP: bad :SUBST pair: {repr pair}"
          | none => throw s!"REWRITE-STEP: :SUBST not a list: {repr r}"
        | none => pure []
      let equivTerm := lookupKeyword "EQUIV-TERM" rest
      let typeSet := match lookupKeyword "TYPESET" rest with
        | some (.atom (.number (.int n))) => some n
        | _ => none
      let trueTs := match lookupKeyword "TRUETS" rest with
        | some (.atom (.number (.int n))) => some n
        | _ => none
      let path ← match lookupKeyword "PATH" rest with
        | some r => match r.toList? with
          | some items => items.mapM parsePathFrame
          | none => throw s!"REWRITE-STEP: :PATH not a list: {repr r}"
        | none => pure []
      pure { rune, equiv, lhs, rhs, origin, runes, parents, subst, equivTerm, typeSet, trueTs, path }
    | _ => throw s!"REWRITE-STEP: expected :REWRITE-STEP keyword, got {repr s}"
  | none => throw s!"REWRITE-STEP: expected list, got {repr s}"

/-- Parse a clausify decision-trace `:PATH` — a list of `(:t . test)` /
    `(:f . test)` conses, outermost-first — into (assumed-true?, test)
    pairs. Hard-fails on any other shape. -/
private def parseClausifyPath (s : SExpr) : Except String (List (Bool × SExpr)) := do
  let some items := s.toList?
    | throw s!"clausify :PATH is not a list: {repr s}"
  items.mapM fun
    | .cons (.atom (.keyword "T")) test => pure (true, test)
    | .cons (.atom (.keyword "F")) test => pure (false, test)
    | e => throw s!"clausify :PATH entry is not (:t/:f . test): {repr e}"

/-- Parse a single trace event from the :REWRITES field. -/
private def parseTraceEvent (s : SExpr) : Except String TraceEvent := do
  match s.toList? with
  | some items =>
    match items with
    | .atom (.keyword "REWRITE-STEP") :: _ =>
        pure (.rewriteStep (← parseRewriteStep? s))
    | .atom (.keyword "IF-TEST-TRUE") :: rest =>
        let test ← lookupKeyword "TEST" rest |>.elim (throw "IF-TEST-TRUE: missing :TEST") pure
        let unrewritten ← lookupKeyword "UNREWRITTEN-TEST" rest
          |>.elim (throw "IF-TEST-TRUE: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.ifTestTrue test unrewritten justification)
    | .atom (.keyword "IF-TEST-FALSE") :: rest =>
        let test ← lookupKeyword "TEST" rest |>.elim (throw "IF-TEST-FALSE: missing :TEST") pure
        let unrewritten ← lookupKeyword "UNREWRITTEN-TEST" rest
          |>.elim (throw "IF-TEST-FALSE: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.ifTestFalse test unrewritten justification)
    | .atom (.keyword "IF-TEST-UNKNOWN") :: rest =>
        let test ← lookupKeyword "TEST" rest |>.elim (throw "IF-TEST-UNKNOWN: missing :TEST") pure
        let unrewritten ← lookupKeyword "UNREWRITTEN-TEST" rest
          |>.elim (throw "IF-TEST-UNKNOWN: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.ifTestUnknown test unrewritten justification)
    | .atom (.keyword "BEGIN-LITERAL") :: rest =>
        let index ← match lookupKeyword "INDEX" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"BEGIN-LITERAL: bad :INDEX: {repr s}"
          | none => throw "BEGIN-LITERAL: missing :INDEX"
        let literal ← lookupKeyword "LITERAL" rest
          |>.elim (throw "BEGIN-LITERAL: missing :LITERAL") pure
        let notFlg := match lookupKeyword "NOT-FLG" rest with
          | some .nil => false
          | _ => true
        pure (.beginLiteral index literal notFlg)
    | .atom (.keyword "END-LITERAL") :: rest =>
        let index ← match lookupKeyword "INDEX" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"END-LITERAL: bad :INDEX: {repr s}"
          | none => throw "END-LITERAL: missing :INDEX"
        let result ← lookupKeyword "RESULT" rest
          |>.elim (throw "END-LITERAL: missing :RESULT") pure
        let branches ← match lookupKeyword "BRANCHES" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"END-LITERAL: bad :BRANCHES: {repr s}"
          | none => throw "END-LITERAL: missing :BRANCHES"
        pure (.endLiteral index result branches)
    | .atom (.keyword "REWRITTEN-LITERAL") :: rest =>
        let original ← lookupKeyword "ORIGINAL" rest
          |>.elim (throw "REWRITTEN-LITERAL: missing :ORIGINAL") pure
        let result ← lookupKeyword "RESULT" rest
          |>.elim (throw "REWRITTEN-LITERAL: missing :RESULT") pure
        pure (.rewrittenLiteral original result)
    | .atom (.keyword "BEGIN-BRANCH") :: rest =>
        let segment := (lookupKeyword "SEGMENT" rest).getD .nil
        pure (.beginBranch segment)
    | .atom (.keyword "END-BRANCH") :: _ =>
        pure .endBranch
    | .atom (.keyword "CASE-SPLIT") :: rest =>
        let litIdx ← match lookupKeyword "LITERAL-INDEX" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"CASE-SPLIT: bad :LITERAL-INDEX: {repr s}"
          | none => throw "CASE-SPLIT: missing :LITERAL-INDEX"
        let numBranches ← match lookupKeyword "NUM-BRANCHES" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"CASE-SPLIT: bad :NUM-BRANCHES: {repr s}"
          | none => throw "CASE-SPLIT: missing :NUM-BRANCHES"
        pure (.caseSplit litIdx numBranches)
    | .atom (.keyword "BRANCH-SUBSTITUTION") :: rest =>
        let equivalence ← lookupKeyword "EQUIVALENCE" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :EQUIVALENCE") pure
        let lhs ← lookupKeyword "LHS" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :LHS") pure
        let rhs ← lookupKeyword "RHS" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :RHS") pure
        pure (.branchSubstitution equivalence lhs rhs)
    | .atom (.keyword "CONTEXT-SUBST") :: rest =>
        let var ← lookupKeyword "VARIABLE" rest
          |>.elim (throw "CONTEXT-SUBST: missing :VARIABLE") pure
        let value ← lookupKeyword "VALUE" rest
          |>.elim (throw "CONTEXT-SUBST: missing :VALUE") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.contextSubst var value justification)
    | .atom (.keyword "HYP-RELIEF") :: rest =>
        let hyp ← lookupKeyword "HYP" rest
          |>.elim (throw "HYP-RELIEF: missing :HYP") pure
        let origin ← match lookupKeyword "ORIGIN" rest with
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"HYP-RELIEF: bad :ORIGIN: {repr s}"
          | none => throw "HYP-RELIEF: missing :ORIGIN"
        -- :TA-RUNES (optional; free-type-alist markers only): the matched
        -- type-alist ENTRY's ttree runes — a DERIVED entry's provenance
        -- (e.g. forward-chaining LEXORDER-TOTAL; emission arc 2026-07-21)
        let taRunes ← match lookupKeyword "TA-RUNES" rest with
          | none => pure []
          | some rs =>
            match rs.toList? with
            | none => throw s!"HYP-RELIEF: :TA-RUNES not a list: {repr rs}"
            | some l => l.mapM fun r =>
                match parseRune? r with
                | some rn => pure rn
                | none => throw s!"HYP-RELIEF: bad :TA-RUNES rune: {repr r}"
        -- :PARENTS (optional; known-true markers, S1 2026-07-23): the
        -- verdict ttree's 'pt tags — the clause literals the type-set
        -- derivation descended from (same convention as REWRITE-STEP)
        let parents ← match lookupKeyword "PARENTS" rest with
          | none => pure []
          | some r =>
            match r.toList? with
            | none => throw s!"HYP-RELIEF: :PARENTS not a list: {repr r}"
            | some l => pure l
        pure (.hypRelief hyp origin taRunes parents)
    | .atom (.keyword "CLAUSIFY-TEST") :: rest =>
        let test ← lookupKeyword "TEST" rest
          |>.elim (throw "CLAUSIFY-TEST: missing :TEST") pure
        -- VERDICT/HOW are internal dispatch tags (true/false, assumed/…),
        -- not symbol-identity values — lowercase at the boundary.
        let verdict ← match lookupKeyword "VERDICT" rest with
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-TEST: bad :VERDICT: {repr s}"
          | none => throw "CLAUSIFY-TEST: missing :VERDICT"
        let how ← match lookupKeyword "HOW" rest with
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-TEST: bad :HOW: {repr s}"
          | none => throw "CLAUSIFY-TEST: missing :HOW"
        let path ← parseClausifyPath ((lookupKeyword "PATH" rest).getD .nil)
        pure (.clausifyTest test verdict how path)
    | .atom (.keyword "CLAUSIFY-LEAF") :: rest =>
        let value ← lookupKeyword "VALUE" rest
          |>.elim (throw "CLAUSIFY-LEAF: missing :VALUE") pure
        let outcome ← match lookupKeyword "OUTCOME" rest with
          -- OUTCOME is an internal dispatch tag (segment-open/segment-false/
          -- dropped), not a symbol-identity value — lowercase at the boundary.
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-LEAF: bad :OUTCOME: {repr s}"
          | none => throw "CLAUSIFY-LEAF: missing :OUTCOME"
        let path ← parseClausifyPath ((lookupKeyword "PATH" rest).getD .nil)
        -- :SEGMENT — required for the two segment outcomes, forbidden for
        -- dropped (the emitter writes it exactly there; no leniency drift)
        let segment ← match lookupKeyword "SEGMENT" rest, outcome with
          | some s, "segment-false" | some s, "segment-open" =>
            match s.toList? with
            | some l => pure (some l)
            | none => throw s!"CLAUSIFY-LEAF: :SEGMENT is not a list: {repr s}"
          | none, "dropped" => pure none
          | none, o => throw s!"CLAUSIFY-LEAF: {o} outcome without :SEGMENT \
                                (stale log? recapture-all)"
          | some _, o => throw s!"CLAUSIFY-LEAF: unexpected :SEGMENT on a \
                                  {o} leaf"
        pure (.clausifyLeaf value outcome path segment)
    | .atom (.keyword "CLAUSIFY-CONJUNCTION") :: rest =>
        let l ← lookupKeyword "LEFT" rest
          |>.elim (throw "CLAUSIFY-CONJUNCTION: missing :LEFT") pure
        let r ← lookupKeyword "RIGHT" rest
          |>.elim (throw "CLAUSIFY-CONJUNCTION: missing :RIGHT") pure
        pure (.clausifyConjunction l r)
    | .atom (.keyword "CLAUSIFY-SATRIANI") :: rest =>
        let which ← match lookupKeyword "WHICH" rest with
          -- WHICH is an internal dispatch tag, not a symbol-identity value.
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-SATRIANI: bad :WHICH: {repr s}"
          | none => throw "CLAUSIFY-SATRIANI: missing :WHICH"
        pure (.clausifySetReshaped s!"satriani-{which}")
    | .atom (.keyword "CLAUSIFY-SUBSUMPTION-LOOP") :: _ =>
        pure (.clausifySetReshaped "subsumption-loop")
    | .atom (.keyword "TYPE-SET-REASONING") :: rest =>
        let term ← lookupKeyword "TERM" rest
          |>.elim (throw "TYPE-SET-REASONING: missing :TERM") pure
        let result ← lookupKeyword "RESULT" rest
          |>.elim (throw "TYPE-SET-REASONING: missing :RESULT") pure
        let notFlg := match lookupKeyword "NOT-FLG" rest with
          | some .nil => false
          | _ => true
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.typeSetReasoning term result notFlg justification)
    | .atom (.keyword "BEGIN-INNER-REWRITE") :: rest =>
        -- KIND is an internal dispatch tag (hyp/rhs/…), not a symbol-identity
        -- value — lowercase at the boundary.
        let kind := match lookupKeyword "KIND" rest with
          | some (.atom (.symbol s)) => s.name.map Char.toLower
          | some (.atom (.keyword k)) => k.map Char.toLower
          | _ => "unknown"
        pure (.beginInnerRewrite kind)
    | .atom (.keyword "END-INNER-REWRITE") :: rest =>
        -- KIND is an internal dispatch tag (hyp/rhs/…), not a symbol-identity
        -- value — lowercase at the boundary.
        let kind := match lookupKeyword "KIND" rest with
          | some (.atom (.symbol s)) => s.name.map Char.toLower
          | some (.atom (.keyword k)) => k.map Char.toLower
          | _ => "unknown"
        pure (.endInnerRewrite kind)
    | .atom (.keyword "BEGIN-IF-REWRITE") :: rest =>
        let test ← lookupKeyword "TEST" rest
          |>.elim (throw "BEGIN-IF-REWRITE: missing :TEST") pure
        let unrewrittenTest := (lookupKeyword "UNREWRITTEN-TEST" rest).getD .nil
        pure (.beginIfRewrite test unrewrittenTest)
    | .atom (.keyword "END-IF-REWRITE") :: rest =>
        let test ← lookupKeyword "TEST" rest
          |>.elim (throw "END-IF-REWRITE: missing :TEST") pure
        let result := (lookupKeyword "RESULT" rest).getD .nil
        pure (.endIfRewrite test result)
    | .atom (.keyword "CLAUSIFY-INPUT") :: rest =>
        let term ← lookupKeyword "TERM" rest
          |>.elim (throw "CLAUSIFY-INPUT: missing :TERM") pure
        pure (.clausifyInput term)
    | .atom (.keyword "CLAUSIFY-NEG") :: rest =>
        let cl ← lookupKeyword "CLAUSE" rest
          |>.elim (throw "CLAUSIFY-NEG: missing :CLAUSE") pure
        match cl.toList? with
        | some lits => pure (.clausifyNeg lits)
        | none => throw s!"CLAUSIFY-NEG: clause is not a proper list: {repr cl}"
    | .atom (.keyword "CLAUSIFY-SPLIT") :: rest =>
        let lit ← lookupKeyword "LIT" rest
          |>.elim (throw "CLAUSIFY-SPLIT: missing :LIT") pure
        let cl ← lookupKeyword "CLAUSE" rest
          |>.elim (throw "CLAUSIFY-SPLIT: missing :CLAUSE") pure
        match cl.toList? with
        | some lits => pure (.clausifySplit lit lits)
        | none => throw s!"CLAUSIFY-SPLIT: clause is not a proper list: {repr cl}"
    | .atom (.keyword "CLAUSIFY-OUT") :: rest =>
        let cls ← lookupKeyword "CLAUSES" rest
          |>.elim (throw "CLAUSIFY-OUT: missing :CLAUSES") pure
        match cls.toList? with
        | some clList =>
          let parsed ← clList.mapM fun c =>
            match c.toList? with
            | some lits => pure lits
            | none => throw s!"CLAUSIFY-OUT: clause is not a proper list: {repr c}"
          pure (.clausifyOut parsed)
        | none => throw s!"CLAUSIFY-OUT: clauses is not a proper list: {repr cls}"
    | .atom (.keyword "CLAUSIFY-EXPAND") :: rest =>
        let toTerm ← lookupKeyword "TO" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :TO") pure
        let fromTerm ← lookupKeyword "FROM" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :FROM (stale log — \
                          recapture with the S1 fork)") pure
        let boolS ← lookupKeyword "BOOL" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :BOOL") pure
        let pos ← if boolS == SExpr.t then pure true
          else if boolS == SExpr.nil then pure false
          else throw s!"CLAUSIFY-EXPAND: :BOOL {repr boolS} is neither T nor NIL"
        let runesS ← lookupKeyword "RUNES" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :RUNES (stale log — \
                          recapture with the S1 fork)") pure
        let some runeList := runesS.toList?
          | throw s!"CLAUSIFY-EXPAND: :RUNES not a list: {repr runesS}"
        let runes ← runeList.mapM fun r =>
          (parseRune? r).elim
            (throw s!"CLAUSIFY-EXPAND: bad rune {repr r}") pure
        pure (.clausifyExpand fromTerm toTerm pos runes)
    | _ => throw s!"Unknown trace event: {repr s}"
  | none => throw s!"Expected list trace event, got: {repr s}"

/-- Parse a list of trace events from the :REWRITES field. -/
private def parseTraceEvents (s : SExpr) : Except String (List TraceEvent) := do
  match s.toList? with
  | some items =>
    let mut result := #[]
    for item in items do
      result := result.push (← parseTraceEvent item)
    pure result.toList
  | none => throw s!"REWRITES: expected list, got {repr s}"

/-- Parse a (:STEP ...) s-expression. -/
private def parseStep? (items : List SExpr) : Except String ProofStep := do
  let clauseId ← match lookupKeyword "CLAUSEID" items with
    | some s => match atomString? s with
      | some str => pure str
      | none => throw s!"STEP: bad :CLAUSE-ID value: {repr s}"
    | none => throw "STEP: missing :CLAUSE-ID"
  let processor ← match lookupKeyword "PROCESSOR" items with
    -- processor is a dispatch tag (compared against lowercase literals like
    -- "push-clause"/"preprocess"); lowercase at the boundary (names are upcased).
    | some s => match atomString? s with
      | some str => pure (str.map Char.toLower)
      | none => throw s!"STEP: bad :PROCESSOR value: {repr s}"
    | none => throw "STEP: missing :PROCESSOR"
  let result ← match lookupKeyword "RESULT" items with
    | some (.atom (.keyword "PROVED")) => pure ProofResult.proved
    | some (.atom (.keyword "SUBGOALS")) => pure ProofResult.subgoals
    | some s => throw s!"STEP: bad :RESULT value: {repr s}"
    | none => throw "STEP: missing :RESULT"
  let runes ← match lookupKeyword "RUNES" items with
    | some s => parseRunes s
    | none => pure []
  let traceEvents ← match lookupKeyword "REWRITES" items with
    | some s => parseTraceEvents s
    | none => pure []
  let inputClause ← match lookupKeyword "INPUTCLAUSE" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"STEP: :INPUTCLAUSE is not a list: {repr s}"
    | none => pure []
  let newClauses ← match lookupKeyword "NEWCLAUSES" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"STEP: :NEWCLAUSES is not a list: {repr s}"
    | none => pure []
  let extraFields := plistExtras
    ["clauseid", "processor", "result", "runes", "rewrites", "inputclause", "newclauses"] items
  pure { clauseId, processor, result, runes, traceEvents, inputClause, newClauses, extraFields }

/-- Parse a pool-lst `(1 1 1)` (naturals). -/
private def parsePoolLst (s : SExpr) : Except String (List Nat) := do
  match s.toList? with
  | some items => items.mapM fun i => match i with
      | .atom (.number (.int n)) =>
        if n ≥ 0 then pure n.toNat
        else throw s!"pool-lst entry negative: {repr i}"
      | _ => throw s!"pool-lst entry not a natural: {repr i}"
  | none => throw s!"pool-lst not a list: {repr s}"

/-- Parse one IH substitution alist `((var . term) …)`. ACL2 prints a pair `(v . t)` as
    `(v . t)` or, when `t` is a list, as `(v t…)` — both are `.cons (symbol v) t`. -/
private def parseAlist (s : SExpr) : Except String (List (Symbol × SExpr)) := do
  match s.toList? with
  | some pairs => pairs.mapM fun p => match p with
      | .cons (.atom (.symbol v)) term => pure (v, term)
      | _ => throw s!"INDUCTION :ALISTS: bad pair (expected (var . term)): {repr p}"
  | none => throw s!"INDUCTION :ALISTS: alist not a list: {repr s}"

/-- Parse one `(:TESTS (test…) :ALISTS (alist…))` induction case. -/
private def parseCase (s : SExpr) : Except String InductionCase := do
  match s.toList? with
  | some items =>
    let tests ← match lookupKeyword "TESTS" items with
      | some t => t.toList?.elim (throw s!"INDUCTION case :TESTS not a list: {repr t}") pure
      | none => pure []
    let alists ← match lookupKeyword "ALISTS" items with
      | some a => match a.toList? with
        | some als => als.mapM parseAlist
        | none => throw s!"INDUCTION case :ALISTS not a list: {repr a}"
      | none => pure []
    pure { tests, alists }
  | none => throw s!"INDUCTION case not a plist: {repr s}"

/-- Parse a (:INDUCTION ...) s-expression. The measure-justification fields
    (:XTERM/:MEASURE/:REL/:MP/:SUBSET/:CASES) are optional — absent in legacy logs. -/
private def parseInduction? (items : List SExpr) : Except String InductionStep := do
  let term ← match lookupKeyword "TERM" items with
    | some s => pure s
    | none => throw "INDUCTION: missing :TERM"
  let subgoalCount ← match lookupKeyword "SUBGOALS" items with
    | some (.atom (.number (.int n))) => pure n.toNat
    | some s => throw s!"INDUCTION: bad :SUBGOALS: {repr s}"
    | none => throw "INDUCTION: missing :SUBGOALS"
  let scheme ← match lookupKeyword "SCHEME" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"INDUCTION: :SCHEME is not a list: {repr s}"
    | none => pure []
  let xterm := (lookupKeyword "XTERM" items).getD .nil
  let measure := (lookupKeyword "MEASURE" items).getD .nil
  let rel := (lookupKeyword "REL" items).getD .nil
  let mp := (lookupKeyword "MP" items).getD .nil
  let controllers ← match lookupKeyword "CONTROLLERS" items with
    | some s => match s.toList? with
      | some xs => xs.mapM fun x => match x with
        | .atom (.symbol v) => pure v
        | _ => throw s!"INDUCTION: :CONTROLLERS non-symbol element: {repr x}"
      | none => throw s!"INDUCTION: :CONTROLLERS not a list: {repr s}"
    | none => pure []
  let cases ← match lookupKeyword "CASES" items with
    | some c => match c.toList? with
      | some cs => cs.mapM parseCase
      | none => throw s!"INDUCTION: :CASES not a list: {repr c}"
    | none => pure []
  -- REQUIRED whenever :SCHEME is present (same emitter, emission arc audit
  -- 2026-07-22): a missing key means a stale pre-audit log — recapture
  let schemeDropped ← match lookupKeyword "SCHEME-DROPPED" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"INDUCTION: :SCHEME-DROPPED is not a list: {repr s}"
    | none =>
      if scheme.isEmpty then pure []
      else throw "INDUCTION: missing :SCHEME-DROPPED (stale log? recapture-all)"
  pure { term, subgoalCount, scheme, xterm, measure, rel, mp, controllers, cases,
         schemeDropped }

/-- Parse one stored-rule entry: `(rune hyps equiv lhs rhs)` for the
    capture-time `(:RULES …)` events (`withMatchFree = false`), or
    `(rune hyps equiv lhs rhs match-free)` for ground-zero rule snapshots
    (`withMatchFree = true`; match-free is `:ALL`/`:ONCE`/`NIL`). The two
    arities are exact — a mismatched entry hard-fails. -/
private def parseFcRuleSpecEntry (e : SExpr) : Except String FcRuleSpec := do
  let some items := e.toList?
    | throw s!"GROUND-ZERO-FC-RULES: bad entry (not a list): {repr e}"
  let [runeS, triggerS, hypsS, conclsS, mfS] := items
    | throw s!"GROUND-ZERO-FC-RULES: bad entry (want (rune trigger hyps \
              concls match-free)): {repr e}"
  let some rune := parseRune? runeS
    | throw s!"GROUND-ZERO-FC-RULES: bad rune: {repr runeS}"
  unless rune.ty == "forward-chaining" do
    throw s!"GROUND-ZERO-FC-RULES: rune class {rune.ty} unexpected"
  let hyps ← hypsS.toList?.elim
    (throw s!"GROUND-ZERO-FC-RULES {rune.name}: :HYPS not a list: {repr hypsS}") pure
  let concls ← conclsS.toList?.elim
    (throw s!"GROUND-ZERO-FC-RULES {rune.name}: :CONCLS not a list: {repr conclsS}") pure
  let matchFree ← match mfS with
    | .nil => pure none
    | .atom (.keyword k) => pure (some (k.map Char.toLower))
    | other => throw s!"GROUND-ZERO-FC-RULES {rune.name}: bad match-free: {repr other}"
  return { name := rune.name, trigger := triggerS, hyps, concls, matchFree }

private def parseRuleSpecEntry (ctx : String) (withMatchFree : Bool)
    (e : SExpr) : Except String RuleSpec := do
  let some items := e.toList?
    | throw s!"{ctx}: bad entry (not a list): {repr e}"
  -- capture-time entries carry the rule's backchain-limit-lst as a 6th
  -- element (emit/rule, S1.2 2026-07-23 — previously OMITTED, the
  -- cov-backchain-limit emission pin); gz snapshots carry match-free instead
  -- (their limit emission is a tracked follow-up).
  let (runeS, hypsS, equivS, lhsS, rhsS, mf?, bclS) ←
    match withMatchFree, items with
    | false, [r, h, q, l, rh, bcl] => pure (r, h, q, l, rh, none, bcl)
    | true, [r, h, q, l, rh, mf] => pure (r, h, q, l, rh, some mf, SExpr.nil)
    | false, _ =>
      throw s!"{ctx}: bad entry (want (rune hyps equiv lhs rhs \
              backchain-limit) — stale log? recapture-all): {repr e}"
    | true, _ =>
      throw s!"{ctx}: bad entry (want (rune hyps equiv lhs rhs match-free)): \
              {repr e}"
  -- The entry's rune goes through the same parse as step runes (J7: the
  -- dotted multi-rule shape carries the index into the spec's identity) —
  -- but a rule-spec rune NAME must be a SYMBOL (a theorem name); the step
  -- path's lenient repr-fallback does not apply here (parse-time hard-fail
  -- restored, audit 2026-07-18).
  match runeS with
  | .cons _ (.cons (.atom (.symbol _)) _) => pure ()
  | _ => throw s!"{ctx}: rule-spec rune name is not a symbol: {repr runeS}"
  match parseRune? runeS with
  | some rune => do
    let rname := rune.name
    -- rune type + equiv are lowercase dispatch tags (see parseRune?).
    unless rune.ty == "rewrite" do
      throw s!"{ctx}: rune class {rune.ty} unsupported (frontier)"
    let hyps ← hypsS.toList?.elim
      (throw s!"{ctx} {rname}: :HYPS not a list: {repr hypsS}") pure
    let equiv ← match equivS with
      | .atom (.symbol s) => pure (s.name.map Char.toLower)
      | other => throw s!"{ctx} {rname}: bad equiv: {repr other}"
    let matchFree ← match mf? with
      | none => pure none
      | some .nil => pure none
      | some (.atom (.keyword k)) => pure (some (k.map Char.toLower))
      | some other =>
        throw s!"{ctx} {rname}: bad match-free: {repr other}"
    -- rune NAME is a symbol identity (theorem name), stored UPCASED
    -- like parseRune?'s name and the dependency-proof keys.
    pure ({ name := rname, idx := rune.idx, hyps, equiv,
            lhs := lhsS, rhs := rhsS, matchFree,
            backchainLimit := bclS } : RuleSpec)
  | _ => throw s!"{ctx}: bad rune: {repr runeS}"

/-- Parse a single top-level s-expression from the proof log. -/
private def parseEvent (s : SExpr) : Except String ProofEvent := do
  match s with
  | .cons (.atom (.keyword "STEP")) rest =>
    match rest.toList? with
    | some items => return .step (← parseStep? items)
    | none => throw s!"STEP: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "INDUCTION")) rest =>
    match rest.toList? with
    | some items => return .induction (← parseInduction? items)
    | none => throw s!"INDUCTION: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "QED")) _ =>
    return .qed
  | .cons (.atom (.keyword "DEFTHM")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match atomString? nameExpr with
      | some name =>
        let formula ← (lookupKeyword "FORMULA" fields).elim
          (throw s!"DEFTHM {name}: missing :FORMULA") pure
        let source := match lookupKeyword "SOURCE" fields with
          | some (.atom (.keyword "INCLUDE-BOOK")) => TheoremSource.includeBook
          | some (.atom (.keyword "LOCAL")) => TheoremSource.local
          | _ => TheoremSource.unknown
        return .defthm name formula source
      | none => throw s!"DEFTHM: bad name: {repr nameExpr}"
    | some [] => throw s!"DEFTHM: missing name"
    | none => throw s!"DEFTHM: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "DEFUN")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match nameExpr with
      | .atom (.symbol nameSym) =>
        -- The name's PACKAGE is discarded downstream (`WorldEvent.defun.name` is a
        -- String; `Development.toWorld` rebuilds the symbol in the default package)
        -- — so a non-default package would silently rename the function. Hard-fail
        -- instead (frontier; no corpus example uses one).
        unless nameSym.package == ({ name := "X" } : Symbol).package do
          throw s!"DEFUN {nameSym.name}: non-default package \
                  {nameSym.package} unsupported (would be lost downstream)"
        let name := nameSym.name
        -- :FORMALS is REQUIRED and every formal must be a symbol — a malformed or
        -- absent list hard-fails (no silent drop, no default-to-nullary).
        let formalsSExpr ← (lookupKeyword "FORMALS" fields).elim
          (throw s!"DEFUN {name}: missing :FORMALS") pure
        let formalsList ← formalsSExpr.toList?.elim
          (throw s!"DEFUN {name}: :FORMALS is not a list: {repr formalsSExpr}") pure
        let formals ← formalsList.mapM fun
          | .atom (.symbol s) => pure s
          | other => throw s!"DEFUN {name}: non-symbol formal: {repr other}"
        let body ← (lookupKeyword "BODY" fields).elim
          (throw s!"DEFUN {name}: missing :BODY") pure
        -- :SOURCE :GROUND-ZERO marks a boot-strap-world SNAPSHOT (design D3)
        -- rather than a captured admission. Any other :SOURCE value is
        -- malformed (fail-closed).
        let groundZero ← match lookupKeyword "SOURCE" fields with
          | none => pure false
          | some (.atom (.keyword "GROUND-ZERO")) => pure true
          | some other => throw s!"DEFUN {name}: unsupported :SOURCE \
                                  {repr other}"
        -- The admission justification: :MEASURE/:WFREL/:MEASURED travel
        -- together (recursive defun) or are all absent (non-recursive); a
        -- PARTIAL set is a malformed emission and hard-fails.
        let just ← match lookupKeyword "MEASURE" fields,
                         lookupKeyword "WFREL" fields,
                         lookupKeyword "MEASURED" fields with
          | none, none, none =>
            -- a non-recursive defun also has no obligations
            match lookupKeyword "TERMINATION-CLAUSES" fields with
            | none => pure none
            | some c => throw s!"DEFUN {name}: :TERMINATION-CLAUSES without a \
                                justification: {repr c}"
          | some m, some r, some sub => do
            let rel ← match r with
              | .atom (.symbol s) => pure s
              | other => throw s!"DEFUN {name}: :WFREL is not a symbol: {repr other}"
            let subL ← sub.toList?.elim
              (throw s!"DEFUN {name}: :MEASURED is not a list: {repr sub}") pure
            let subSyms ← subL.mapM fun
              | .atom (.symbol s) => pure s
              | other => throw s!"DEFUN {name}: non-symbol measured formal: {repr other}"
            -- a RECURSIVE defun must carry its decrease obligations — an
            -- admission the log cannot justify is an emission gap
            -- (hard-fail; the emitter attaches the clique's RAW measure
            -- clauses). Since the J2 fork change (2026-07-16) this holds
            -- for INCLUDE-BOOK'd defuns too: the re-emission RECOMPUTES the
            -- clauses (gz-termination-clauses — the R2 follow-up), so
            -- :INCLUDED T now travels WITH :TERMINATION-CLAUSES; an
            -- :INCLUDED defun without clauses is a stale-fork capture
            -- (hard-fail, prompting recapture).
            match lookupKeyword "TERMINATION-CLAUSES" fields,
                  lookupKeyword "INCLUDED" fields with
            | some clausesExpr, included? =>
              (do match included? with
                  | none => pure ()
                  | some (.atom (.symbol tS)) =>
                    if tS.name == "T" then
                      if groundZero then
                        throw s!"DEFUN {name}: :SOURCE :GROUND-ZERO with \
                                :INCLUDED (snapshots are not include \
                                re-emissions)"
                      else pure ()
                    else throw s!"DEFUN {name}: malformed :INCLUDED value"
                  | some other =>
                    throw s!"DEFUN {name}: malformed :INCLUDED value: \
                            {repr other}")
              let clauses ← clausesExpr.toList?.elim
                (throw s!"DEFUN {name}: :TERMINATION-CLAUSES is not a list: \
                         {repr clausesExpr}") pure
              pure (some { measure := m, wfRel := rel, measuredSubset := subSyms,
                           terminationClauses := clauses })
            | none, some _ =>
              throw s!"DEFUN {name}: :INCLUDED without :TERMINATION-CLAUSES \
                      — stale-fork capture (the include re-emission \
                      recomputes clauses since J2); recapture the log"
            | none, none =>
              throw s!"DEFUN {name}: recursive (has a justification) but no \
                      :TERMINATION-CLAUSES and no :INCLUDED marker — emission gap"
          | _, _, _ => throw s!"DEFUN {name}: partial admission justification \
                               (:MEASURE/:WFREL/:MEASURED must travel together)"
        return if groundZero then .groundZeroDefun name formals body just
               else .defun name formals body just
      | _ => throw s!"DEFUN: bad name: {repr nameExpr}"
    | _ => throw s!"DEFUN: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "RULES")) rest =>
    match rest.toList? with
    | some [rulesList] =>
      let some entries := rulesList.toList?
        | throw s!"RULES: payload is not a list: {repr rulesList}"
      return .rules (← entries.mapM (parseRuleSpecEntry "RULES" false))
    | _ => throw s!"RULES: expected a single payload list, got {repr rest}"
  | .cons (.atom (.keyword "GROUND-ZERO-RULES")) rest =>
    -- Cited ground-zero rewrite rules read off the world at capture end
    -- (design D5) — the (:RULES …) entry shape plus the match-free flag.
    match rest.toList? with
    | some [rulesList] =>
      let some entries := rulesList.toList?
        | throw s!"GROUND-ZERO-RULES: payload is not a list: {repr rulesList}"
      return .groundZeroRules
        (← entries.mapM (parseRuleSpecEntry "GROUND-ZERO-RULES" true))
    | _ => throw s!"GROUND-ZERO-RULES: expected a single payload list, \
                   got {repr rest}"
  | .cons (.atom (.keyword "GROUND-ZERO-FC-RULES")) rest =>
    match rest.toList? with
    | some [rulesList] =>
      let some entries := rulesList.toList?
        | throw s!"GROUND-ZERO-FC-RULES: payload is not a list: {repr rulesList}"
      return .groundZeroFcRules (← entries.mapM parseFcRuleSpecEntry)
    | _ => throw s!"GROUND-ZERO-FC-RULES: expected a single payload list, \
                   got {repr rest}"
  | .cons (.atom (.keyword "POOL-CONSIDER")) rest =>
    let some nameS := lookupKeyword "NAME" (rest.toList?.getD [])
      | throw "POOL-CONSIDER: missing :NAME"
    return .poolConsider (← parsePoolLst nameS)
  | .cons (.atom (.keyword "POOL-SUBSUMED")) rest =>
    let items := rest.toList?.getD []
    let some nameS := lookupKeyword "NAME" items
      | throw "POOL-SUBSUMED: missing :NAME"
    let some byS := lookupKeyword "BY" items
      | throw "POOL-SUBSUMED: missing :BY"
    return .poolSubsumed (← parsePoolLst nameS) (← parsePoolLst byS)
  | .cons (.atom (.keyword "TYPE-PRESCRIPTION")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match atomString? nameExpr with
      | some name =>
        let corollary ← (lookupKeyword "COROLLARY" fields).elim
          (throw s!"TYPE-PRESCRIPTION {name}: missing :COROLLARY") pure
        let basicTs := match lookupKeyword "BASICTS" fields with
          | some (.atom (.number (.int n))) => some n
          | _ => none
        let leaves ← match lookupKeyword "LEAVES" fields with
          | some l => match l.toList? with
            | some items => items.mapM fun pair =>
              -- Each leaf is a proper list (term type-set-bits)
              match pair.toList? with
              | some [term, .atom (.number (.int ts))] => pure (term, ts)
              | _ => throw s!"TYPE-PRESCRIPTION {name}: bad leaf: {repr pair}"
            | none => throw s!"TYPE-PRESCRIPTION {name}: :LEAVES not a list: {repr l}"
          | none => pure []
        return .typePrescription name corollary basicTs leaves
      | none => throw s!"TYPE-PRESCRIPTION: bad name: {repr nameExpr}"
    | _ => throw s!"TYPE-PRESCRIPTION: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "EVENT-FAILED")) rest =>
    -- emit/event-failed (S1, 2026-07-23): an event FAILED in ACL2 and its
    -- error output was inhibited by :structured mode — the log is
    -- authoritative about the failure but INCOMPLETE about the book.
    -- Fail the PARSE with the ctx: a log containing a failed event must be
    -- fixed at the book/capture, never processed partially.
    let ctx := (lookupKeyword "CTX" (rest.toList?.getD [])).getD .nil
    throw s!"proof log records a FAILED ACL2 event (ctx: {repr ctx}) — the \
             book's event was rejected/failed and the log is incomplete; fix \
             the book (or the capture) and recapture"
  | .cons (.atom (.keyword "VERIFY-GUARDS")) rest =>
    -- emit/verify-guards (S1.2, 2026-07-23): the guard-obligation waterfall's
    -- wrapper (previously its :STEP/(:QED) events were ORPHANS). Replay of
    -- guard obligations is a named frontier — fail the parse precisely.
    let names := (lookupKeyword "NAMES" (rest.toList?.getD [])).getD .nil
    throw s!"proof log contains a VERIFY-GUARDS obligation proof for \
             {repr names} — guard-obligation replay is an unsupported frontier"
  | .cons (.atom (.keyword "FORCING-ROUND")) rest =>
    -- emit/forcing-round (S1, 2026-07-23): the structured forcing-round
    -- boundary (was untagged English prose that broke parsing —
    -- cov-force-round pin). Reconstruction of forcing rounds is a named
    -- frontier: parse hard-fails here, precisely, until round support lands.
    let round := (lookupKeyword "ROUND" (rest.toList?.getD [])).getD .nil
    throw s!"proof log contains a FORCING ROUND (round {repr round}) — \
             forcing-round replay is an unsupported frontier"
  | _ => throw s!"Unknown proof log event: {repr s}"

/-- Parse a proof log from raw ACL2 output.
    Finds the (:BEGIN-PROOF-LOG) marker in the raw text and parses only
    the s-expressions after it. Everything before the marker (SBCL banner,
    ACL2 startup, prompts) is discarded as raw text.
    Everything after the marker must be valid proof log s-expressions. -/
def parse (input : String) : Except String ProofLog := do
  let marker := "(:BEGIN-PROOF-LOG)"
  let parts := input.splitOn marker
  if parts.length < 2 then
    throw "No (:BEGIN-PROOF-LOG) marker found in input"
  let proofText := String.intercalate marker parts.tail!
  let sexprs ← Parse.parseAll proofText
  let mut events := #[]
  for s in sexprs do
    events := events.push (← parseEvent s)
  pure { events := events.toList }

/-- Pretty-print a proof log summary. -/
def summary (log : ProofLog) : String :=
  let steps := log.events.filter fun e => match e with | .step _ => true | _ => false
  let inductions := log.events.filter fun e => match e with | .induction _ => true | _ => false
  let qeds := log.events.filter fun e => match e with | .qed => true | _ => false
  let defthms := log.events.filterMap fun e => match e with | .defthm n _ _ => some n | _ => none
  let processors := steps.filterMap fun e => match e with
    | .step s => some s.processor | _ => none
  let procPairs := processors.foldl (init := ([] : List (String × Nat)))
    fun acc p =>
      match acc.find? (fun (k, _) => k == p) with
      | some _ => acc.map fun (k, n) => if k == p then (k, n + 1) else (k, n)
      | none => acc ++ [(p, 1)]
  let lines := #[
    s!"Proof log: {log.events.length} events",
    s!"  Theorems: {defthms.length} ({String.intercalate ", " defthms})",
    s!"  Steps: {steps.length}",
    s!"  Inductions: {inductions.length}",
    s!"  QEDs: {qeds.length}",
    "  By processor:"
  ]
  let procLines := procPairs.map fun (p, n) => s!"    {p}: {n}"
  "\n".intercalate (lines.toList ++ procLines)

/-- Split a proof log into named per-theorem segments.
    Each segment starts with a (:DEFTHM name) event and ends with (:QED).
    Returns (name, events) pairs. -/
def splitByTheorem (log : ProofLog) : List (String × List ProofEvent) :=
  let rec go (events : List ProofEvent) (curName : Option String)
      (current : List ProofEvent) (acc : List (String × List ProofEvent)) :
      List (String × List ProofEvent) :=
    match events with
    | [] =>
      match curName with
      | some n => ((n, current.reverse) :: acc).reverse
      | none => acc.reverse
    | .defthm name _ _ :: rest =>
      -- Start a new theorem segment; flush any previous
      let acc := match curName with
        | some n => (n, current.reverse) :: acc
        | none => acc
      go rest (some name) [] acc
    | .qed :: rest =>
      match curName with
      | some n => go rest none [] ((n, (.qed :: current).reverse) :: acc)
      | none => go rest none [] acc  -- QED without defthm, skip
    | e :: rest => go rest curName (e :: current) acc
  go log.events none [] []

end ProofLog
end ACL2
