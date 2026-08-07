/-
  Driver/NodeCore — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  ReplayCtx/ReplayConfig, registries, value characterization, and the
  node-level recipes (replayRecognizer; the replayDefinition/replayNode/
  replayRewrites knot).
-/
import ACL2Lean.Replay.Driver.Reflect

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ## The recursive driver (`replayClause` / `replayNode`).

A recursive function over the reconstructed tree, per
`docs/notes/2026-06-07_driver-design.md`. It reads every term/rune/subst/scheme FROM
the tree — nothing transcribed. FAIL-CLOSED: each `replay*` returns a real
kernel-checkable `Expr` or `throwError`s; NEVER `sorry`.

S1 (dummy) = every node `throwError`s. S2 adds the single `equal-self` terminal. -/

/-- Carried info for a defined (1-arg) function `fn`: its formal and body, plus the
    proof terms about the concrete world that `re_unfold1_conv` needs. Established once
    when the config is built (test harness now, `gen-world` later). -/
structure DefInfo where
  formal : Symbol
  body : SExpr
  /-- `w.defs.get? fn = some ([formal], body)`. -/
  defFact : Expr
  /-- `∀ s ∈ freeVars body, s ∈ [formal]`. -/
  closedFact : Expr
  /-- `WellScoped body = true`. -/
  wellScopedFact : Expr

/-- Ambient config: the `World` (as both an `Expr` for proof terms and a `World` value
    so the driver can read formals/bodies) and the `Env` `Expr`. The structural world
    facts (`defs.get? fn = …`, builtin-not-shadowed, freeVars⊆formals, WellScoped) are NOT
    carried — the driver **derives each one on demand by kernel decision**
    (`proveNoShadow` / `deriveDefInfo`), since `World.defs` is now a reduction-friendly
    `DefMap`. No hand-marshalled facts, no per-example config. This is NOT inference: a
    `decide` over a concrete map is evaluation, not search. -/
structure ReplayConfig where
  worldExpr : Expr
  envExpr : Expr
  worldVal : World := {}
  /-- The development's ground-zero SNAPSHOT defuns — (name, formals, emitted
      body) as EMITTED (`Development.groundZeroSnapshotDefs`, D3/WP1-WP2).
      Two consumers: the totality prover's lazy `upTo` bound treats these
      names as always-in-scope (they logically precede the whole
      development), and the D4 definition-fact route reads a builtin's
      recorded body from here (builtin-named snapshots are EXCLUDED from the
      world — no-shadow — so this is the only place their emission lives).
      Empty for synthetic test worlds. -/
  gzDefs : List (Symbol × List Symbol × SExpr) := []
  /-- The development's admission justifications (fn ↦ measure/wfrel/
      measured-subset + RAW termination clauses) — the I4 covering join
      reads a scheme fn's emitted decrease clauses from here (J2; the
      totality prover receives the same data as a parameter). Empty for
      synthetic test worlds — an induction replay then hard-fails at the
      covering check, never guesses. -/
  justs : List (String × Justification) := []
  /-- The development's ground-zero FORWARD-CHAINING rule snapshots
      (`(:GROUND-ZERO-FC-RULES …)`, emission arc 2026-07-21): trigger/hyps/
      concls verbatim. The FC-derived type-alist relief recipe pins its
      registered Lean lemma against the emitted shape (audit-F2 style) —
      an unlisted or drifted rule hard-fails. -/
  fcRules : List FcRuleSpec := []
  /-- The development's ground-zero LINEAR rule snapshots
      (`(:GROUND-ZERO-LINEAR-RULES …)`, sorting-absolute 2b): hyps/concl/
      max-term verbatim. Consumed by `replayDischargeNode` as DP-obligation
      premises where simplify's linear arithmetic cites the rune
      (verdict-only) — instantiated by max-term match against the
      obligation's opaques, backed by the `linear:` hypothesis class. -/
  linearRules : List LinearRuleSpec := []
  /-- RECORDED-TERMINATION mirrors (sorting arc 2026-07-28): per defun with
      a replayed admission waterfall, its replayed-statement constant, condition names,
      and root goal clause. Consumed by the totality prover (via the
      threaded `buildTotalEnv` params) AND the theorem-side induction's
      IH-decrease fallback (`replayInduction`, which resolves the conditions
      from the ambient `ReplayCtx`). -/
  termReplayed : List (String × Name × List String × List SExpr) := []
  /-- The development's emitted `:TYPE-PRESCRIPTION` corollaries for
      BUILTIN-NAMED ground-zero fns (world-defined fns get theirs as `tp:`
      hypotheses instead — `replayProofConditional`). Consumed by the builtin
      TP pin route in `pinTermOpaques`: a registered builtin (`builtinIntTps`)
      is int-pinned ONLY when its emitted corollary matches the registered
      shape exactly (type facts from ACL2, proof from the trusted core);
      an emitted-but-drifted corollary hard-fails. -/
  gzTps : List (String × SExpr) := []
  /-- (fn, :BASICTS) from the emitted TP events (R2 gate). -/
  gzTpBasicTs : List (String × Int) := []
  /-- The cited recognizer-alist tuple snapshot
      ((:GROUND-ZERO-RECOGNIZER-TUPLES), fork-batch item 2): the
      DATA-DRIVEN gate for recognizer verdicts — e.g. never-a-cons =
      the fn's TP :BASICTS numerically disjoint from CONSP's true-ts,
      both numbers EMITTED. -/
  recogTuples : List RecognizerTupleSpec := []

/-- A CONGRUENCE rule consumed by the R-collapse (G2 rung 2), shape-parsed
    from a defcong-style defthm formula
    `(IMPLIES (R x y) (EQUAL (fn a₁…x…aₙ) (fn a₁…y…aₙ)))` — all args
    distinct variables, the two sides differing at exactly position `pos`
    (0-based), `y` fresh. The hypothesis states the WHOLE formula
    (`∀ env', EvTrue w env' formula` — `mkCongHypType`); nothing is derived
    from the shape except the (fn, pos, R) index and the σ construction at
    the use site, both recompute-and-checked there. -/
structure CongSpec where
  name : String
  formula : SExpr
  /-- The equivalence relation's fn symbol (the formula hyp's head). -/
  rel : Symbol
  /-- The congruent fn and the 0-based differing arg position. -/
  fn : Symbol
  pos : Nat
  /-- The lhs application's arg variables (x at `pos`) and the rhs-side
      variable y. -/
  argVars : List Symbol
  vy : Symbol
  /-- The formula pieces, for recompute-and-check at the use site. -/
  hyp : SExpr
  lhsApp : SExpr
  rhsApp : SExpr
  deriving BEq, Repr

/-- Shape-parse a defcong-style formula into a `CongSpec`. `none` when the
    formula is not congruence-shaped — the theorem is then simply not
    offered as a congruence (never mis-stated). -/
def congSpecOfFormula? (name : String) (formula : SExpr) : Option CongSpec := do
  let .cons (.atom (.symbol imp)) (.cons hyp (.cons concl .nil)) := formula
    | none
  guard (imp.name == "IMPLIES")
  let .cons (.atom (.symbol rel))
      (.cons (.atom (.symbol vx)) (.cons (.atom (.symbol vy)) .nil)) := hyp
    | none
  let .cons (.atom (.symbol eqS)) (.cons lhsApp (.cons rhsApp .nil)) := concl
    | none
  guard (eqS.name == "EQUAL")
  let .cons (.atom (.symbol fnL)) argsLs := lhsApp | none
  let .cons (.atom (.symbol fnR)) argsRs := rhsApp | none
  guard (fnL == fnR)
  let aL ← argsLs.toList?
  let aR ← argsRs.toList?
  guard (aL.length == aR.length)
  let argVars ← aL.mapM fun a => match a with
    | .atom (.symbol s) => some s
    | _ => none
  let argVarsR ← aR.mapM fun a => match a with
    | .atom (.symbol s) => some s
    | _ => none
  -- pairwise-distinct lhs vars; y fresh; sides differ at exactly one
  -- position, with x left / y right there
  guard (argVars.length == argVars.eraseDups.length)
  guard (!argVars.contains vy && vx != vy)
  let diffs := (argVars.zip argVarsR).zipIdx.filter fun ((l, r), _) => l != r
  let [((l, r), pos)] := diffs | none
  guard (l == vx && r == vy)
  return { name, formula, rel, fn := fnL, pos, argVars, vy,
           hyp, lhsApp, rhsApp }

/-- A `:use`-cited theorem's hypothesis surface (R7a, close-out Phase 2):
    the theorem NAME and its Goal-clause formula. The hypothesis states the
    WHOLE formula (`∀ env', EvTrue w env' formula` — `mkUseHypType`);
    nothing is derived from the shape — the emitted `:HYPS` instance is the
    recompute-and-check at the use site (`substTerm σ formula` must equal
    it verbatim). -/
structure UseSpec where
  name : String
  formula : SExpr
  deriving BEq, Repr

/-- Parse one `:LMI-LST` entry of the PLAIN-`:use` classes (R7a): a bare
    theorem symbol (empty σ), or `(:INSTANCE thm (var term)…)` with a
    variable-to-term substitution. `none` for every other lmi form —
    `:functional-instance`, `:theorem`, nested `:instance` — which the
    consuming arm hard-fails as the R7b frontier (never silently skipped). -/
def lmiInstance? : SExpr → Option (String × List (Symbol × SExpr))
  | .atom (.symbol s) => some (s.name, [])
  | .cons (.atom (.keyword "INSTANCE"))
      (.cons (.atom (.symbol s)) pairsS) => do
    let pairs ← pairsS.toList?
    let σ ← pairs.mapM fun p => match p with
      | .cons (.atom (.symbol v)) (.cons t .nil) => some (v, t)
      | _ => none
    some (s.name, σ)
  | _ => none

/-- An EQUIVALENCE rule's REFLEXIVITY component (sorting-completion-2
    Class A, ORDERED-PERMS): shape-parsed from the RAW equivalence defthm
    formula `(AND (BOOLEANP (R x y)) (R x x) …)` — ACL2's defequiv shape.
    The offered hypothesis states only the reflexivity conjunct
    (`∀ env', EvTrue w env' (R x x)`) — the stored :EQUIVALENCE rule's
    refl content, consumed by the type-alist truthy arm on a syntactically
    reflexive application. -/
structure EquivReflSpec where
  name : String
  rel : Symbol
  vx : Symbol
  deriving BEq, Repr

/-- The FULL defequiv statement surface (`equivfull:<thm>`, the R-solidify
    lane): the equivalence theorem's TRANSLATED Goal clause with the
    variable names of all four conjuncts, offered as the whole-formula
    replayed statement. Consumed by the equivalence-rune own-position
    congruence (`equivOwnPosCongr`): ACL2's geneqv treats an :EQUIVALENCE
    rule as a congruence at the relation's own argument positions, so the
    license cites the equivalence rune and NO defcong — the kernel content
    is the conjuncts (booleanp pins both applications two-valued, sym +
    trans give mutual truthiness). -/
structure EquivFullSpec where
  name : String
  /-- The TRANSLATED Goal-clause formula (the IF-conjunction). -/
  formula : SExpr
  rel : Symbol
  vx : Symbol
  vy : Symbol
  vz : Symbol
  deriving BEq, Repr

/-- Shape-parse a TRANSLATED defequiv Goal clause:
    `(IF (BOOLEANP (R x y)) (IF (R x x) (IF (IMPLIES (R x y) (R y x))
    (IMPLIES (IF (R x y) (R y z) 'NIL) (R x z)) 'NIL) 'NIL) 'NIL)`.
    `none` when not exactly this shape (never mis-stated). -/
def equivFullSpecOfGoal? (name : String) (formula : SExpr) :
    Option EquivFullSpec := do
  let qNil : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons .nil .nil)
  let rApp (r : Symbol) (p q : Symbol) : SExpr :=
    .cons (.atom (.symbol r))
      (.cons (.atom (.symbol p)) (.cons (.atom (.symbol q)) .nil))
  let .cons (.atom (.symbol if1)) (.cons c1 (.cons rest1 (.cons e1 .nil)))
    := formula | none
  guard (if1.isNamed "IF" && e1 == qNil)
  -- c1 = (BOOLEANP (R x y))
  let .cons (.atom (.symbol bS)) (.cons (.cons (.atom (.symbol rel))
      (.cons (.atom (.symbol vx)) (.cons (.atom (.symbol vy)) .nil))) .nil)
    := c1 | none
  guard (bS.isNamed "BOOLEANP" && vx != vy)
  let .cons (.atom (.symbol if2)) (.cons c2 (.cons rest2 (.cons e2 .nil)))
    := rest1 | none
  guard (if2.isNamed "IF" && e2 == qNil && c2 == rApp rel vx vx)
  let .cons (.atom (.symbol if3)) (.cons c3 (.cons c4 (.cons e3 .nil)))
    := rest2 | none
  guard (if3.isNamed "IF" && e3 == qNil)
  -- c3 = (IMPLIES (R x y) (R y x))
  let .cons (.atom (.symbol imp3)) (.cons h3 (.cons con3 .nil)) := c3 | none
  guard (imp3.isNamed "IMPLIES" && h3 == rApp rel vx vy
         && con3 == rApp rel vy vx)
  -- c4 = (IMPLIES (IF (R x y) (R y z) 'NIL) (R x z))
  let .cons (.atom (.symbol imp4)) (.cons h4 (.cons con4 .nil)) := c4 | none
  guard (imp4.isNamed "IMPLIES")
  let .cons (.atom (.symbol if4)) (.cons a4 (.cons b4 (.cons e4 .nil)))
    := h4 | none
  guard (if4.isNamed "IF" && e4 == qNil && a4 == rApp rel vx vy)
  let .cons (.atom (.symbol rel4)) (.cons (.atom (.symbol vy4))
      (.cons (.atom (.symbol vz)) .nil)) := b4 | none
  guard (rel4 == rel && vy4 == vy && vz != vx && vz != vy
         && con4 == rApp rel vx vz)
  return { name, formula, rel, vx, vy, vz }

/-- Shape-parse a RAW equivalence formula. `none` if not the defequiv
    shape (never mis-stated). -/
def equivReflSpecOfFormula? (name : String) (formula : SExpr) :
    Option EquivReflSpec := do
  let .cons (.atom (.symbol andS)) (.cons c1 (.cons c2 _)) := formula | none
  guard (andS.name == "AND")
  let .cons (.atom (.symbol bS))
      (.cons (.cons (.atom (.symbol rel1))
        (.cons (.atom (.symbol vx1)) (.cons (.atom (.symbol _)) .nil))) .nil)
      := c1 | none
  guard (bS.name == "BOOLEANP")
  let .cons (.atom (.symbol rel2))
      (.cons (.atom (.symbol vx2)) (.cons (.atom (.symbol vx3)) .nil)) := c2
    | none
  guard (rel1 == rel2 && vx1 == vx2 && vx2 == vx3)
  return { name, rel := rel1, vx := vx1 }

/-- Collect the RECORDED equal/type-alist verdict bases from a literal's
    proof nodes (R1 retirement): (equal-term, canon1, canon2, taEntry)
    for every equal/type-alist-nil step carrying the emitted basis. -/
partial def taBasesOfNodes :
    List ProofNode → List (SExpr × SExpr × SExpr × Option SExpr)
  | [] => []
  | .node _ lhs _ children prov :: rest =>
    (match prov.origin, prov.canon1, prov.canon2 with
     | "equal/type-alist-nil", some c1, some c2 => [(lhs, c1, c2, prov.taEntry)]
     | _, _, _ => []) ++ taBasesOfNodes children ++ taBasesOfNodes rest

/-- The proof context in scope at a node. All entries are VALUE-CHARACTERIZED
    facts over the ambient env, established by the surrounding structure (the
    induction scaffold, the clause spine) and consumed by the node replays:

    - `varVals`: variable ↦ (value `Expr`, proof `∃N∀f≥N, eval (var s) = some value`).
      The induction scaffold binds the controller's value here (`xv`); unlisted
      variables are resolved on demand (`re_val_var`, value `(env.get? s).getD nil`).
    - `vals`: term ↦ (value, convergence proof) — opaque user-fn occurrences
      (obtained from totality hypotheses at clause entry) and any other term whose
      value is pinned in scope.
    - `nilFacts`: literal term ↦ (its value `Expr`, proof `value = .nil`) — the
      clause spine's accumulated "earlier literals are false" hypotheses; feeds
      recognizer/false nodes and the solidify IH bridge.
    - `ih`: the induction hypothesis (the scaffold's `P (cdr xv)` instance), when
      inside a step case. -/
structure ReplayCtx where
  varVals : List (Symbol × Expr × Expr) := []
  vals : List (SExpr × Expr × Expr) := []
  /-- The clause spine's accumulated falsity facts: (1-based literal index, the
      literal's current — post-rewrite — term, proof that its `dpValExpr` value
      `= .nil`). Solidify nodes consume by `equivSource` index; recognizer nodes
      by term (directly, or through a `(not …)` wrapper). -/
  litFacts : List (Nat × SExpr × Expr) := []
  /-- ENCLOSING UNRESOLVED-IF test facts (the if-finish branch context,
      ACL2's assume-true-false): the test term, its value expr, the branch
      sign (`true` = then-branch, value `≠ nil`; `false` = else-branch, value
      `= nil`), and the value fact. Solidify `.branchTest` nodes consume
      these. -/
  branchFacts : List (SExpr × Expr × Bool × Expr) := []
  /-- ENCLOSING CLAUSIFY-BRANCH segment facts (the branch-split composer,
      W3): each entered branch's segment literal with the proof that its
      `dpValExpr` value `= .nil` (assumed false in the branch's continuation).
      Consumed by `litFactByTerm?` (recognizer/type-alist nodes) and by
      solidify `.segment` nodes (ACL2's `:CONTEXT-SUBST` hypotheses). -/
  segFacts : List (SExpr × Expr) := []
  /-- RECORDED equal/type-alist verdict BASES in scope (R1 retirement,
      2026-08-07): the (EQUAL a b) term ↦ (canon1, canon2, taEntry) read
      off the emitted :CANON1/:CANON2/:TA-ENTRY fields — populated from
      the literal's own equal/type-alist-nil steps before its chain
      replays. The walker's equation rung is DIRECTED by these; no
      recorded basis for the class means hard-fail, never search. -/
  taBases : List (SExpr × SExpr × SExpr × Option SExpr) := []
  /-- RECORDED derived-entry provenance in scope (`emit/ta-subst`,
      2026-08-07): (new, from, ts, substNew, substOld) — the
      substitution that manufactured a derived type-alist entry. Directs
      the equation-closure replay's derived-entry class (R1 rung B'). -/
  taSubsts : List (SExpr × SExpr × Int × SExpr × SExpr) := []
  /-- Harness-offered DP-FACT hypotheses (condition threading): clause term ↦
      the `hdpfact` fvar whose type is that discharge leaf's obligation
      (`dpFactStmtOfClause`). Consulted by `replayDischargeNode` when the
      obligation is unprovable — the row then reports ASSUMED:dp-fact. -/
  dpFactHyps : List (SExpr × Expr) := []
  /-- The bound CONDITIONAL hypotheses (the generic mirror's telescope):
      per defined fn, its totality hypothesis; and — when the development emitted
      a :TYPE-PRESCRIPTION — its lifted-corollary hypothesis (with the corollary
      term). The pinning step consumes these. -/
  totalHyps : List (String × Expr) := []
  tpHyps : List (String × SExpr × Expr) := []
  /-- ARGS-VALUED TP hypotheses (G1 arc 2026-07-29): (fn, corollary, hyp
      fvar) for emitted corollaries whose scrubbed residue mentions FORMALS
      bare (the BINARY-APPEND `(EQUAL (fn X Y) Y)` disjunct class) — the
      hypothesis binds the argument VALUES alongside the application's
      (`mkTpHypTypeAv`), so those occurrences lift to them. -/
  tpHypsAv : List (String × SExpr × Expr) := []
  /-- Theorem-dependency hypotheses (`rule:<thm>`, the third telescope
      species): per emitted STORED rewrite rule, the spec and the bound
      hypothesis stating its mirror (`mkRuleHypType`). Consumed by the
      with-lemma node recipe; discharged lazily from the dependency's own
      replayed statement (docs/plans/2026-07-05_theorem-dependency-hypotheses.md). -/
  ruleHyps : List (RuleSpec × Expr) := []
  /-- LINEAR-rule hypotheses (`linear:<rune>`, sorting-absolute 2b): per
      cited ground-zero :LINEAR rule snapshot (content-deduped), the spec
      and the bound hypothesis stating `∀ env', EvTrue hyps → EvTrue
      concl` (`mkLinearHypType`). Consumed by `replayDischargeNode` as a
      DP-obligation premise (max-term-matched instantiation); kept as an
      honest D6 condition until an Imported-side discharger proves it. -/
  linearHyps : List (LinearRuleSpec × Expr) := []
  /-- Congruence-rule hypotheses (`cong:<thm>`, G2 rung 2): per
      congruence-shaped in-scope defthm, the spec and the bound hypothesis
      stating its whole-formula mirror (`mkCongHypType`). Consumed by the
      R-collapse at a user-equivalence step's congruence frame; discharged
      lazily from the dependency's replayed statement like `rule:` hyps. -/
  congHyps : List (CongSpec × Expr) := []
  /-- `:use`-cited theorem hypotheses (`use:<thm>`, R7a): per LMI-cited
      theorem in THIS theorem's tree (demand-driven — the offer set is read
      off the tree's `:USE-HINT` payloads, keeping the telescope narrow),
      the spec and the bound hypothesis stating its whole-formula replayed
      statement (`mkUseHypType`). Consumed by the plain-`:use` composition
      at an `apply-top-hints-clause` node; discharged lazily from the
      dependency's replayed statement like `cong:` hyps. -/
  useHyps : List (UseSpec × Expr) := []
  /-- FULL-defequiv hypotheses (`equivfull:<thm>`, the R-solidify lane):
      per equivalence theorem whose TRANSLATED Goal parses as the defequiv
      IF-conjunction, the spec and the bound whole-formula hypothesis.
      Consumed by the equivalence-rune own-position congruence
      (`equivOwnPosCongr`); discharged like `cong:` hyps. -/
  equivFullHyps : List (EquivFullSpec × Expr) := []
  /-- Equivalence-REFLEXIVITY hypotheses (`equivrefl:<thm>`): per
      equivalence-shaped in-scope defthm (incl. INCLUDE-BOOK'd ones), the
      spec and the bound hypothesis `∀ env', EvTrue w env' (R x x)`.
      Include-book instances stay KEPT conditions (D6-honest). -/
  equivReflHyps : List (EquivReflSpec × Expr) := []
  ih : Option Expr := none

def ReplayCtx.empty : ReplayCtx := {}

/-- Look up a pinned value fact for `t` in the context. -/
def ReplayCtx.val? (ctx : ReplayCtx) (t : SExpr) : Option (Expr × Expr) :=
  (ctx.vals.find? (fun (o, _, _) => o == t)).map fun (_, v, p) => (v, p)

/-- Look up a spine falsity fact by literal index / by term. -/
def ReplayCtx.litFact? (ctx : ReplayCtx) (idx : Nat) : Option (SExpr × Expr) :=
  (ctx.litFacts.find? (fun (i, _, _) => i == idx)).map fun (_, t, p) => (t, p)
def ReplayCtx.litFactByTerm? (ctx : ReplayCtx) (t : SExpr) : Option Expr :=
  ((ctx.litFacts.find? (fun (_, lt, _) => lt == t)).map fun (_, _, p) => p).orElse
    fun _ => (ctx.segFacts.find? (fun (st, _) => st == t)).map (·.2)

/-- `litFactByTerm?` with each candidate proof's TYPE checked against the
    expected proposition (G1 arc 2026-07-29): a term-keyed hit whose proof
    lives in ANOTHER env context (e.g. a pre-elim fact surviving an env
    change) is skipped instead of crashing the composition — and a
    well-typed fact later in the lists still wins. -/
def ReplayCtx.litFactByTermChecked? (ctx : ReplayCtx) (t : SExpr)
    (expectedTy : Expr) : Lean.Meta.MetaM (Option Expr) := do
  let cands := (ctx.litFacts.filterMap fun (_, lt, p) =>
      if lt == t then some p else none)
    ++ (ctx.segFacts.filterMap fun (st, p) => if st == t then some p else none)
  for p in cands do
    if ← Lean.Meta.isDefEq (← Lean.Meta.inferType p) expectedTy then
      return some p
  return none

/-- The destructor-chain reach test — ONE definition for the two former
    near-clones (S7/D7 fix, 2026-08-05): the recorded-termination DEMAND
    filter (Runner, `allowCons := false` — the admission pre-pass demand
    stays wide) and the μ-route discrimination (Induction,
    `allowCons := true` — CONS-of-chains is inside the Count kit's
    reach). The deliberate reach difference is now an explicit parameter,
    not a silent divergence.
    DRIFT MARKER (branch drift audit 2026-08-05, item R3): as a μ-route
    discriminator this is a CALIBRATED HEURISTIC — it predicts which
    route can discharge, rather than reading a recorded route choice.
    Held pending the fork-batch review; if it ever misclassifies, emit
    the route instead of widening the predicate. -/
partial def destructorChainOk (allowCons : Bool) : SExpr → Bool
  | .atom (.symbol _) => true
  | .cons (.atom (.symbol d)) (.cons u .nil) =>
    (d.name == "CDR" || d.name == "CAR" || d.name == "EVENS"
      || d.name == "ODDS") && destructorChainOk allowCons u
  | .cons (.atom (.symbol c)) (.cons a (.cons d .nil)) =>
    allowCons && c.name == "CONS" && destructorChainOk allowCons a
      && destructorChainOk allowCons d
  | _ => false

/-- The ASSUMED-dp-fact condition LABEL — one named constant for the
    guard sites (verifier residual N2, 2026-08-05: a rename of the raw
    string at any one site would silently disable the others' guards). -/
def assumedDpFactCond : String := "ASSUMED:dp-fact"

/-- View `(equal X X)` as `X`. -/
def asEqualSelf : SExpr → Option SExpr
  | .cons (.atom (.symbol s)) (.cons x (.cons x' .nil)) =>
    if s.name == "EQUAL" && x == x' then some x else none
  | _ => none

def runeOf : ProofNode → Rune | .node r _ _ _ _ => r
def nodeLhsRhs : ProofNode → SExpr × SExpr | .node _ lhs rhs _ _ => (lhs, rhs)
def nodePath : ProofNode → List PathFrame | .node _ _ _ _ p => p.path
def nodeOrigin : ProofNode → String | .node _ _ _ _ p => p.origin
/-- The node's enclosing-window kind ("" = none / literal level). -/
def innerKindOf : ProofNode → String | .node _ _ _ _ p => p.innerKind
/-- The node's enclosing-window input term (path-emission Phase 1). -/
def innerTermOf : ProofNode → Option SExpr | .node _ _ _ _ p => p.innerTerm
/-- The node's enclosing-window entry path (path-emission Phase 1). -/
def innerPathOf : ProofNode → List PathFrame | .node _ _ _ _ p => p.innerPath
/-- The node's own record's `:SWAPPED-P` (fold-back audit V3). -/
def swappedOf : ProofNode → Bool | .node _ _ _ _ p => p.swapped
/-- The enclosing window's `:SWAPPED-P` (fold-back audit V3). -/
def innerSwappedOf : ProofNode → Bool | .node _ _ _ _ p => p.innerSwapped
/-- ALL occurrence positions of `sub` in `t` as PathFrame lists (never
    descending QUOTE). Deterministic; the inline-window handler uses the
    UNIQUE-occurrence case only (ambiguity hard-fails).
    A LAMBDA application descends its ARGUMENTS (numeric positions, like
    `navigateFrames`) but not the lambda body: a body position is not
    expressible as an `.arg` frame, and an inline window inside the body
    sits behind its own `lambda-body` boundary, so it is never resolved
    against this start term (fold-back audit 2026-07-31 V4 — the
    symbol-head-only match made lambda-app subtrees invisible, so a term
    with one visible and one lambda-hidden occurrence passed the
    uniqueness check at possibly the wrong occurrence). -/
partial def occurrencePaths (t sub : SExpr) : List (List PathFrame) :=
  if t == sub then [[]]
  else
    let argsOf : SExpr → Option SExpr
      | .cons (.atom (.symbol f)) args =>
        if f.name == "QUOTE" then none else some args
      | .cons (.cons _ _) args => some args  -- lambda application
      | _ => none
    match argsOf t with
    | some args =>
      let rec go (rest : SExpr) (i : Nat) : List (List PathFrame) :=
        match rest with
        | .cons a r =>
          (occurrencePaths a sub |>.map fun p =>
            (PathFrame.arg i (match a with
              | .cons (.atom (.symbol h)) _ => h
              | .cons (.cons _ _) _ => { name := "LAMBDA" }
              | _ => { name := "QUOTE" })) :: p) ++ go r (i + 1)
        | _ => []
      go args 1
    | none => []

/-- Strip the window tag — recipes that CONSUME a window (the if-finish
    branch partition; the inline-window group handler) clear it before
    handing the nodes to a sub-walk anchored at the window term. -/
def clearWindowTag : ProofNode → ProofNode
  | .node rune lhs rhs children prov =>
    .node rune lhs rhs children
      { prov with innerKind := "", innerTerm := none, innerPath := [],
                  innerSwapped := false }
/-- RE-ROOT a whole-if finishing child at the if: keep the path's entry
    frame, drop the `k` window→if frames after it, so the post-walk's
    uniform drop-1 navigates from the if itself. VALIDATED by the caller
    (the child's window-local path must equal the if-finish node's own)
    — an `if-post` fork window would retire this (fold-back audit note). -/
def retargetAtIf (n : ProofNode) (k : Nat) : ProofNode :=
  match n with
  | .node rune lhs rhs children prov =>
    .node rune lhs rhs children
      { prov with path := prov.path.take 1 ++ prov.path.drop (1 + k) }

/-- `worldExpr.defs.get? s` as an `Expr` (a `DefMap.get?` application). -/
private def mkDefsGet (cfg : ReplayConfig) (s : Symbol) : MetaM Expr := do
  mkAppM ``ACL2.DefMap.get? #[← mkAppM ``ACL2.World.defs #[cfg.worldExpr], reflectSymbol s]

/-- Derive `worldExpr.defs.get? s = none` (builtin `s` not shadowed by a defun) by kernel
    decision. Replaces the hand-carried `noShadow` fact: the lookup REDUCES on the concrete
    `DefMap`, so `decide` settles it. Hard-fails (via `proveByDecide`) if `s` IS defined. -/
def proveNoShadow (cfg : ReplayConfig) (s : Symbol) : MetaM Expr := do
  let lookup ← mkDefsGet cfg s
  let elemTy := (← inferType lookup).appArg!
  let noneE := mkApp (mkConst ``Option.none [0]) elemTy
  proveByDecide (← mkEq lookup noneE) s!"no-shadow {s.name}"

/-- Derive a defined (1-arg) function's `DefInfo` on demand from the World, with all three
    structural facts proved by kernel decision (no hand-written theorems):
    - `defFact`   : `worldExpr.defs.get? fn = some ([formal], body)`
    - `closedFact`: `∀ s ∈ freeVars body, s ∈ [formal]`
    - `wellScopedFact` : `WellScoped body = true`
    `formal`/`body` are read from `cfg.worldVal` (the concrete World); `proveByDecide`
    re-checks each fact against `worldExpr`, so a `worldVal`/`worldExpr` mismatch hard-fails.
    Multi-arg / not-defined hard-fail (1-arg unfold is the current frontier). -/
def deriveDefInfo (cfg : ReplayConfig) (fn : Symbol) : MetaM DefInfo := do
  match cfg.worldVal.defs.get? fn with
  | none => throwError "deriveDefInfo: {fn.name} not defined in the world"
  | some (formals, body) =>
    let formal ← match formals with
      | [f] => pure f
      | _ => throwError "deriveDefInfo: {fn.name} has {formals.length} formals; only 1-arg \
                         definition-unfold is supported (frontier)"
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let bodyE := reflectSExpr body
    -- defFact : worldExpr.defs.get? fn = some (formals, body)
    let someE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[formalsE, bodyE]]
    let defFact ← proveByDecide (← mkEq (← mkDefsGet cfg fn) someE) s!"def {fn.name}"
    -- closedFact : ∀ s ∈ freeVars body, s ∈ formals
    let fvE ← mkAppM ``ACL2.Replay.freeVars #[bodyE]
    let closedProp ← withLocalDeclD `s (mkConst ``ACL2.Symbol) fun sv => do
      let memFv ← mkAppM ``Membership.mem #[fvE, sv]
      let memFm ← mkAppM ``Membership.mem #[formalsE, sv]
      mkForallFVars #[sv] (← mkArrow memFv memFm)
    let closedFact ← proveByDecide closedProp s!"closed {fn.name}"
    -- wellScopedFact : WellScoped body = true
    let wellScopedFact ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[bodyE]) (mkConst ``Bool.true)) s!"well-scoped {fn.name}"
    return { formal, body, defFact, closedFact, wellScopedFact }

/-- Prove `s.isNamed name = false` by kernel decision. -/
def proveIsNamedFalse (s : Symbol) (name : String) : MetaM Expr :=
  proveByDecide
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``Symbol.isNamed) (reflectSymbol s) (mkStrLit name)) (mkConst ``Bool.false))
    s!"{s.name}.isNamed {name} = false"

/-- Prove `s.isNamed name = true` by kernel decision. -/
def proveIsNamedTrue (s : Symbol) (name : String) : MetaM Expr :=
  proveByDecide
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``Symbol.isNamed) (reflectSymbol s) (mkStrLit name)) (mkConst ``Bool.true))
    s!"{s.name}.isNamed {name} = true"

/-- DP-lift primitives (unary): ACL2 name → (Logic function, `callBuiltin` rfl lemma). -/
def dpUnary : List (String × Name × Name) :=
  [("NOT",      ``Logic.not,      ``callBuiltin_not),
   ("ZP",       ``Logic.zp,       ``callBuiltin_zp),
   ("CONSP",    ``Logic.consp,    ``callBuiltin_consp),
   ("INTEGERP", ``Logic.integerp, ``callBuiltin_integerp),
   ("ACL2-NUMBERP", ``Logic.acl2Numberp, ``callBuiltin_acl2_numberp),
   ("TRUE-LISTP", ``Logic.trueListp, ``callBuiltin_true_listp),
   ("CAR",      ``Logic.car,      ``callBuiltin_car),
   ("CDR",      ``Logic.cdr,      ``callBuiltin_cdr),
   ("SYMBOLP",  ``Logic.symbolp,  ``callBuiltin_symbolp),
   ("STRINGP",  ``Logic.stringp,  ``callBuiltin_stringp),
   ("RATIONALP", ``Logic.rationalp, ``callBuiltin_rationalp),
   ("BOOLEANP", ``Logic.booleanp, ``callBuiltin_booleanp),
   ("NFIX",     ``Logic.nfix,     ``callBuiltin_nfix),
   -- ordinal-on-naturals family, layer 1 (consumer-queue 2026-08-04: the
   -- non-ACL2-COUNT measure obligations' conjuncts — POSP/NATP are
   -- already callBuiltin builtins; pure registration)
   ("POSP",     ``Logic.posp,     ``callBuiltin_posp),
   ("NATP",     ``Logic.natp,     ``callBuiltin_natp),
   ("FIX",      ``Logic.fix,      ``callBuiltin_fix),
   ("LEN",      ``Logic.len,      ``callBuiltin_len),
   ("ENDP",     ``Logic.endp,     ``callBuiltin_endp),
   ("ATOM",     ``Logic.atom,     ``callBuiltin_atom),
   ("NUMERATOR", ``Logic.numerator, ``callBuiltin_numerator),
   ("DENOMINATOR", ``Logic.denominator, ``callBuiltin_denominator),
   ("UNARY--",  ``Logic.neg,      ``callBuiltin_unary_minus),
   ("REALPART", ``Logic.realpart, ``callBuiltin_realpart),
   ("IMAGPART", ``Logic.imagpart, ``callBuiltin_imagpart),
   ("COMPLEX-RATIONALP", ``Logic.complexRationalp,
    ``callBuiltin_complex_rationalp)]

/-- DP-lift primitives (binary). -/
def dpBinary : List (String × Name × Name) :=
  [("EQUAL",    ``Logic.equal,   ``callBuiltin_equal),
   ("<",        ``Logic.lt,      ``callBuiltin_lt),
   ("LEXORDER", ``ACL2.lexorder, ``callBuiltin_lexorder),
   ("BINARY-+", ``Logic.plus,    ``callBuiltin_plus),
   ("BINARY-*", ``Logic.times,   ``callBuiltin_times),
   ("COERCE",   ``Logic.coerce,  ``callBuiltin_coerce),
   ("CONS",     ``SExpr.cons,    ``callBuiltin_cons),
   ("IMPLIES",  ``Logic.implies, ``callBuiltin_implies),
   ("IFF",      ``Logic.iff,     ``callBuiltin_iff)]

-- INVARIANT (load-bearing — the G3 audit's dpOpqKeyOk↔collectOpaques matrix):
-- `dpLiftHeads` must be EXACTLY the names of `dpUnary ++ dpBinary`. The meta
-- walkers (`dpValExpr`, `collectOpaques` via `dpKnownHead`) dispatch off the
-- registries, while the verified lift (`dpLiftF`, `dpOpqKeyOk`) dispatches off
-- `dpLiftHeads`; extending one side without the other silently desynchronizes
-- the lift premise from the collected opaque set. Set equality, both directions:
#guard dpLiftHeads.all (fun n => (dpUnary.lookup n).isSome || (dpBinary.lookup n).isSome)
#guard (dpUnary.map (·.1) ++ dpBinary.map (·.1)).all (dpLiftHeads.contains ·)

/-- D4 DEFINITION-FACT registry (external-knowledge design §D4, WP2): builtins
    that ACL2 itself defines by defun. Their `(:DEFINITION <fn>)` runes replay
    through the registered `gz_def_<fn>` body lemma (EvalLemmas) instead of a
    world entry — builtin-named ground-zero snapshots are EXCLUDED from the
    world (no-shadow, `builtinNames`), so `evalOpt` dispatches them to
    `callBuiltin` and the unfold is the lemma's callBuiltin-vs-emitted-body
    agreement (`replayBuiltinDefUnfold`). Every entry must also be in
    `dpUnary` (which supplies the `Logic` value function and the `callBuiltin`
    rfl lemma) — guarded below. -/
def d4DefFacts : List (String × Name) :=
  [("TRUE-LISTP", ``gz_def_true_listp),
   ("NOT",        ``gz_def_not),
   ("LEN",        ``gz_def_len),
   ("NFIX",       ``gz_def_nfix),
   ("FIX",        ``gz_def_fix),
   ("BOOLEANP",   ``gz_def_booleanp),
   ("ENDP",       ``gz_def_endp),
   ("ATOM",       ``gz_def_atom)]

#guard d4DefFacts.all (fun e => (dpUnary.lookup e.1).isSome)
#guard d4DefFacts.all (fun e => builtinNames.contains e.1)

/-- Is this head a DP-lift special form or primitive? (Anything else with a symbol
    head is an OPAQUE user-fn application.) -/
def dpKnownHead (name : String) : Bool :=
  name == "QUOTE" || name == "IF" ||
  (dpUnary.lookup name).isSome || (dpBinary.lookup name).isSome


/-- Prove a term CONVERGES (v-fixed totality): `∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v`
    — a single definite value (`evalOpt` is fuel-monotone), so callers can `obtain` the
    witness and feed any value-specific lemma. The value may be env-dependent (a free
    variable) but is still fixed across fuel. S2 handles a free variable (via `re_conv_var`,
    valid for ALL `env`) and a `(quote v)` constant; any other shape is an unimplemented
    frontier → `throwError` (the full convergence analyzer, G1, lands in a later stage). -/
partial def proveConv (cfg : ReplayConfig) (envExpr : Expr) (ctx : ReplayCtx) (t : SExpr) :
    MetaM Expr := do
  -- a pinned ctx fact covers any term (uniform with the value layer)
  if let some (_, p) := ctx.val? t then
    return ← mkAppM ``conv_vfix_of_val #[p]
  match t with
  | .atom (.symbol s) =>
    let hNotT ← proveIsNamedFalse s "t"
    mkAppM ``re_conv_var #[cfg.worldExpr, envExpr, reflectSymbol s, hNotT]
  | .cons (.atom (.symbol qs)) (.cons v .nil) =>
    if qs.name == "QUOTE" then
      mkAppM ``re_conv_quote #[cfg.worldExpr, envExpr, reflectSExpr v]
    else match dpUnary.lookup qs.name with
      | some (fn, cbLemma) =>
        -- REGISTRY-GENERIC: any registered (total) builtin converges when its
        -- operand does; the registry equation supplies the value function.
        let ha ← proveConv cfg envExpr ctx v
        let hNs ← proveNotSpecial qs
        let hNo ← proveNoShadow cfg qs
        let hReg ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
          mkLambdaFVars #[av] (← mkAppM cbLemma #[av])
        mkAppM ``re_conv_builtin1_reg
          #[cfg.worldExpr, envExpr, reflectSymbol qs, reflectSExpr v,
            mkConst fn, hNs, hNo, hReg, ha]
      | none => throwError "proveConv: unary {qs.name} not in the builtin registry \
                            (frontier): {repr t}"
  | .cons (.atom (.symbol bs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup bs.name with
    | some (fn, cbLemma) =>
      let ha ← proveConv cfg envExpr ctx a
      let hb ← proveConv cfg envExpr ctx b
      let hNs ← proveNotSpecial bs
      let hNo ← proveNoShadow cfg bs
      let hReg ← withLocalDeclD `av (mkConst ``SExpr) fun av =>
        withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          mkLambdaFVars #[av, bv] (← mkAppM cbLemma #[av, bv])
      mkAppM ``re_conv_builtin2_reg
        #[cfg.worldExpr, envExpr, reflectSymbol bs, reflectSExpr a, reflectSExpr b,
          mkConst fn, hNs, hNo, hReg, ha, hb]
    | none => throwError "proveConv: binary {bs.name} not in the builtin registry \
                          (frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      let hc ← proveConv cfg envExpr ctx c
      let ht ← proveConv cfg envExpr ctx th
      let he ← proveConv cfg envExpr ctx e
      mkAppM ``re_conv_if
        #[cfg.worldExpr, envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e, hc, ht, he]
    else throwError "proveConv: ternary {fs.name} not supported (frontier): {repr t}"
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- LAMBDA application (translated `let`, S2b): converges because its
    -- actuals and its beta-reduct do (`re_conv_lam*` — the same shape and
    -- certificates as the dpValProof arm; arity dispatch FIRST).
    if lam.name == "LAMBDA" then
      unless ACL2.Replay.WellScoped lamBody do
        throwError "proveConv: LAMBDA body is not closed/regular (WellScoped \
                    fails) — malformed input: {repr t}"
      match ACL2.lamFormals? formalsE, argsExpr.toList? with
      | some lformals, some actuals =>
        let certs (lfs : List Symbol) : MetaM (Expr × Expr × Expr) := do
          let lformalsE ← mkListLit (mkConst ``Symbol) (lfs.map reflectSymbol)
          let hlam ← proveIsNamedTrue lam "LAMBDA"
          let hform ← proveByDecide
            (← mkEq (← mkAppM ``ACL2.lamFormals? #[reflectSExpr formalsE])
                    (← mkAppM ``Option.some #[lformalsE])) "conv-lambda formals"
          let hnl ← proveByDecide
            (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr lamBody])
                    (mkConst ``Bool.true)) "conv-lambda body scoped"
          return (hlam, hform, hnl)
        match lformals, actuals with
        | [lf], [a1] =>
          let (hlam, hform, hnl) ← certs [lf]
          let ha ← proveConv cfg envExpr ctx a1
          let hsub ← proveConv cfg envExpr ctx
            (ACL2.Replay.substTerm [lf] [a1] lamBody)
          mkAppM ``re_conv_lam1
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1, reflectSymbol lf,
              hlam, hform, hnl, ha, hsub]
        | [f1, f2], [a1, a2] =>
          let (hlam, hform, hnl) ← certs [f1, f2]
          let ha ← proveConv cfg envExpr ctx a1
          let hb ← proveConv cfg envExpr ctx a2
          let hsub ← proveConv cfg envExpr ctx
            (ACL2.Replay.substTerm [f1, f2] [a1, a2] lamBody)
          mkAppM ``re_conv_lam2
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1, reflectSExpr a2,
              reflectSymbol f1, reflectSymbol f2, hlam, hform, hnl, ha, hb, hsub]
        | _, _ =>
          throwError "proveConv: LAMBDA binder of {lformals.length} formals / \
                      {actuals.length} actuals unsupported (frontier): {repr t}"
      | _, _ => throwError "proveConv: malformed LAMBDA application: {repr t}"
    else throwError "proveConv: no convergence rule for {repr t}"
  | _ => throwError "proveConv: no convergence rule for {repr t}"

/-- Prove a term converges in EVERY environment: `∀ env', ∃ N, ∃ v, ∀ f ≥ N,
    evalOpt f w env' t = some v`. Runs `proveConv` under a quantified `env'` and
    λ-abstracts. (Used for a definition body, whose convergence `re_unfold1_conv` needs
    at the `bindArgs` env.) -/
def proveConvAllEnv (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``Env) fun env' => do
    let p ← proveConv cfg env' ctx t
    mkLambdaFVars #[env'] p

/-! ## Value characterization (shared by clause-spine replay and the DP lift)

The driver's value layer: every primitive-only term (with opaque user-fn
occurrences and scaffold-bound variables resolved through the `ReplayCtx`) has an
explicit `Logic`-primitive VALUE expression, and a proof that it evaluates to that
value. Moved here from `DischargeLeaf` and generalized with a variable override so
the induction scaffold can pin the controller's value (`xv`). -/

/-- Collect the MAXIMAL opaque subterms (user-fn applications) of a term, in
    first-occurrence order, deduplicated. -/
partial def collectOpaques (t : SExpr) : List SExpr :=
  go t |>.eraseDups
where
  go : SExpr → List SExpr
    | .cons (.atom (.symbol fs)) args =>
      if dpKnownHead fs.name then goSpine args
      else [.cons (.atom (.symbol fs)) args]
    | _ => []
  goSpine : SExpr → List SExpr
    | .cons a rest => go a ++ goSpine rest
    | _ => []

/-- Collect the SYMBOL-HEADED application subterms of a term (primitive-headed
    AND opaque), first-occurrence order, deduplicated; `QUOTE` stops the walk
    and LAMBDA applications are not descended (mirroring `collectOpaques` —
    neither body nor actuals contribute targets). These are the match targets
    for the RULE-content premise pass: a stored rule's LHS can be headed by a
    DP-lift PRIMITIVE (`(TRUE-LISTP (RM E A))` — `TRUE-LISTP` lifts to
    `Logic.trueListp`, so only the inner `RM` application is opaque and
    `collectOpaques` never surfaces the match target). -/
partial def collectAppSubterms (t : SExpr) : List SExpr :=
  go t |>.eraseDups
where
  go : SExpr → List SExpr
    | .cons (.atom (.symbol fs)) args =>
      if fs.name == "QUOTE" then []
      else .cons (.atom (.symbol fs)) args :: goSpine args
    | _ => []
  goSpine : SExpr → List SExpr
    | .cons a rest => go a ++ goSpine rest
    | _ => []

/-- The `Logic`-primitive VALUE of a term: opaque subterms via `opq` (term ↦ value
    expr), variables via `varVal`. -/
partial def dpValExpr (opq : List (SExpr × Expr)) (varVal : Symbol → MetaM Expr)
    (t : SExpr) : MetaM Expr := do
  if let some (_, v) := opq.find? (fun (o, _) => o == t) then return v
  match t with
  | .atom (.symbol s) => varVal s
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    if fs.name == "QUOTE" then return reflectSExpr a
    else match dpUnary.lookup fs.name with
      | some (fn, _) => return mkApp (mkConst fn) (← dpValExpr opq varVal a)
      | none =>
        -- a head KNOWN at another arity is malformed input, not a capability
        -- limit (S2 audit F2-narrowing, 2026-07-25): keep it loud
        if dpKnownHead fs.name then
          throwError "dpValExpr: {fs.name} applied at arity 1 but registered at a \
                      different arity — malformed application: {repr t}"
        else throwFrontier m!"dpValExpr: unary {fs.name} is not a DP-lift primitive (frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, _) =>
      return mkApp2 (mkConst fn) (← dpValExpr opq varVal a) (← dpValExpr opq varVal b)
    | none =>
      if dpKnownHead fs.name then
        throwError "dpValExpr: {fs.name} applied at arity 2 but registered at a \
                    different arity — malformed application: {repr t}"
      else throwFrontier m!"dpValExpr: binary {fs.name} is not a DP-lift primitive (frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      let vc ← dpValExpr opq varVal c
      let vt ← dpValExpr opq varVal th
      let ve ← dpValExpr opq varVal e
      mkAppM ``cond #[mkApp (mkConst ``Logic.toBool) vc, vt, ve]
    else if dpKnownHead fs.name then
      throwError "dpValExpr: {fs.name} applied at arity 3 but registered at a \
                  different arity — malformed application: {repr t}"
    else throwFrontier m!"dpValExpr: ternary {fs.name} is not a DP-lift primitive (frontier): {repr t}"
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- a LAMBDA application (ACL2's translated LET) has the value of its
    -- BETA-REDUCT (`re_lam_beta*_val`), so the walker descends into the
    -- substituted body — the very term the rewriter records at the
    -- LAMBDA-BODY frame. Malformed binders hard-fail; a wider binder is a
    -- capability FRONTIER, not a defect.
    if lam.name == "LAMBDA" then
      -- the SAME scoping certificate the proof twin discharges by kernel
      -- decision (S2 audit F3, 2026-07-25): a non-`WellScoped` body means the
      -- substitution below could capture — malformed input (ACL2's translate
      -- closes every lambda body), never descend
      unless ACL2.Replay.WellScoped lamBody do
        throwError "dpValExpr: LAMBDA body is not closed/regular (WellScoped fails) — \
                    malformed input (translate closes lambda bodies): {repr t}"
      match ACL2.lamFormals? formalsE, argsExpr.toList? with
      | some lformals, some actuals =>
        if lformals.length == actuals.length
            && 1 ≤ lformals.length && lformals.length ≤ 2 then
          dpValExpr opq varVal (ACL2.Replay.substTerm lformals actuals lamBody)
        else
          throwFrontier m!"dpValExpr: LAMBDA binder of {lformals.length} formals / \
                          {actuals.length} actuals unsupported (frontier): {repr t}"
      | _, _ => throwError "dpValExpr: malformed LAMBDA application: {repr t}"
    else throwError "dpValExpr: unsupported term shape: {repr t}"
  | _ => throwError "dpValExpr: unsupported term shape: {repr t}"

/-- A clause variable's default concrete value: `(env.get? s).getD nil`. -/
def dpConcVar (envExpr : Expr) (s : Symbol) : MetaM Expr := do
  mkAppM ``Option.getD
    #[← mkAppM ``Env.get? #[envExpr, reflectSymbol s], mkConst ``SExpr.nil]

/-- Value-characterized convergence of a term:
    `∃N ∀f≥N, evalOpt f w env t = some (dpValExpr concrete t)`. Opaque subterms use
    their convergence proofs (`opqP`); variables use `varP` when bound (the
    scaffold's controller) else `re_val_var`. -/
partial def dpValProof (cfg : ReplayConfig) (envExpr : Expr)
    (opq : List (SExpr × Expr)) (opqP : List (SExpr × Expr))
    (varP : Symbol → Option (Expr × Expr) := fun _ => none)
    (t : SExpr) : MetaM Expr := do
  if let some (_, h) := opqP.find? (fun (o, _) => o == t) then return h
  match t with
  | .atom (.symbol s) =>
    match varP s with
    | some (_, h) => return h
    | none =>
      let hNotT ← proveIsNamedFalse s "t"
      mkAppM ``re_val_var #[cfg.worldExpr, envExpr, reflectSymbol s, hNotT]
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    if fs.name == "QUOTE" then
      mkAppM ``re_val_quote #[cfg.worldExpr, envExpr, reflectSExpr a]
    else match dpUnary.lookup fs.name with
      | some (fn, cbLemma) =>
        let pa ← dpValProof cfg envExpr opq opqP varP a
        let va ← dpValExpr opq (dpVarVal envExpr varP) a
        let rv := mkApp (mkConst fn) va
        let hNs ← proveNotSpecial fs
        let hNo ← proveNoShadow cfg fs
        let hr ← mkAppM cbLemma #[va]
        mkAppM ``conv_builtin1
          #[cfg.worldExpr, envExpr, reflectSymbol fs, reflectSExpr a, va, rv, hNs, hNo, pa, hr]
      | none =>
        if dpKnownHead fs.name then
          throwError "dpValProof: {fs.name} applied at arity 1 but registered at a \
                      different arity — malformed application: {repr t}"
        else throwFrontier m!"dpValProof: unary {fs.name} is not a DP-lift primitive (frontier)"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, cbLemma) =>
      let pa ← dpValProof cfg envExpr opq opqP varP a
      let pb ← dpValProof cfg envExpr opq opqP varP b
      let va ← dpValExpr opq (dpVarVal envExpr varP) a
      let vb ← dpValExpr opq (dpVarVal envExpr varP) b
      let rv := mkApp2 (mkConst fn) va vb
      let hNs ← proveNotSpecial fs
      let hNo ← proveNoShadow cfg fs
      let hr ← mkAppM cbLemma #[va, vb]
      mkAppM ``conv_builtin2
        #[cfg.worldExpr, envExpr, reflectSymbol fs, reflectSExpr a, reflectSExpr b,
          va, vb, rv, hNs, hNo, pa, pb, hr]
    | none =>
      if dpKnownHead fs.name then
        throwError "dpValProof: {fs.name} applied at arity 2 but registered at a \
                    different arity — malformed application: {repr t}"
      else throwFrontier m!"dpValProof: binary {fs.name} is not a DP-lift primitive (frontier)"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      let pc ← dpValProof cfg envExpr opq opqP varP c
      let pt ← dpValProof cfg envExpr opq opqP varP th
      let pe ← dpValProof cfg envExpr opq opqP varP e
      let vc ← dpValExpr opq (dpVarVal envExpr varP) c
      let vt ← dpValExpr opq (dpVarVal envExpr varP) th
      let ve ← dpValExpr opq (dpVarVal envExpr varP) e
      mkAppM ``re_val_if
        #[cfg.worldExpr, envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
          vc, vt, ve, pc, pt, pe]
    else if dpKnownHead fs.name then
      throwError "dpValProof: {fs.name} applied at arity 3 but registered at a \
                  different arity — malformed application: {repr t}"
    else throwFrontier m!"dpValProof: ternary {fs.name} is not a DP-lift primitive (frontier)"
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- LAMBDA application (translated LET): the BETA-REDUCT's convergence,
    -- lifted by `re_lam_beta*_val` (see the dpValExpr twin arm).
    if lam.name == "LAMBDA" then
      match ACL2.lamFormals? formalsE, argsExpr.toList? with
      | some lformals, some actuals => do
        -- arity dispatch FIRST (S2 audit F4, 2026-07-25): a mismatched or
        -- unsupported binder must not recurse into a bogus reduct before the
        -- shape is checked — the walkers state the same predicate
        match lformals, actuals with
        | [lf], [a1] =>
          let (hlam, hform, hnl) ← lamCerts lam formalsE lamBody [lf]
          let substBody := ACL2.Replay.substTerm [lf] [a1] lamBody
          let pSub ← dpValProof cfg envExpr opq opqP varP substBody
          let vSub ← dpValExpr opq (dpVarVal envExpr varP) substBody
          let pa ← dpValProof cfg envExpr opq opqP varP a1
          let va ← dpValExpr opq (dpVarVal envExpr varP) a1
          mkAppM ``re_lam_beta1_val
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1,
              reflectSymbol lf, va, vSub, hlam, hform, hnl, pa, pSub]
        | [f1, f2], [a1, a2] =>
          let (hlam, hform, hnl) ← lamCerts lam formalsE lamBody [f1, f2]
          let substBody := ACL2.Replay.substTerm [f1, f2] [a1, a2] lamBody
          let pSub ← dpValProof cfg envExpr opq opqP varP substBody
          let vSub ← dpValExpr opq (dpVarVal envExpr varP) substBody
          let pa ← dpValProof cfg envExpr opq opqP varP a1
          let pb ← dpValProof cfg envExpr opq opqP varP a2
          let va ← dpValExpr opq (dpVarVal envExpr varP) a1
          let vb ← dpValExpr opq (dpVarVal envExpr varP) a2
          mkAppM ``re_lam_beta2_val
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1,
              reflectSExpr a2, reflectSymbol f1, reflectSymbol f2, va, vb, vSub,
              hlam, hform, hnl, pa, pb, pSub]
        | _, _ =>
          throwFrontier m!"dpValProof: LAMBDA binder of {lformals.length} formals / \
                          {actuals.length} actuals unsupported (frontier): {repr t}"
      | _, _ => throwError "dpValProof: malformed LAMBDA application: {repr t}"
    else throwError "dpValProof: unsupported term shape: {repr t}"
  | _ => throwError "dpValProof: unsupported term shape: {repr t}"
where
  /-- Variable values consistent with `varP` (fall back to the env lookup). -/
  dpVarVal (envExpr : Expr) (varP : Symbol → Option (Expr × Expr)) (s : Symbol) :
      MetaM Expr :=
    match varP s with
    | some (v, _) => pure v
    | none => dpConcVar envExpr s
  /-- The three kernel-decided beta certificates: head is LAMBDA, formals as
      recorded, body regular/closed (`WellScoped`). -/
  lamCerts (lam : Symbol) (formalsE lamBody : SExpr) (lformals : List Symbol) :
      MetaM (Expr × Expr × Expr) := do
    let lformalsE ← mkListLit (mkConst ``Symbol) (lformals.map reflectSymbol)
    let hlam ← proveIsNamedTrue lam "LAMBDA"
    let hform ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.lamFormals? #[reflectSExpr formalsE])
              (← mkAppM ``Option.some #[lformalsE])) "lambda-val formals"
    let hnl ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr lamBody]) (mkConst ``Bool.true))
      "well-scoped lambda-val body"
    return (hlam, hform, hnl)

/-- Ctx-driven value/proof for a term: ctx.vals as the opaque maps, ctx.varVals as
    the variable override. -/
def ctxValExpr (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) : MetaM Expr :=
  dpValExpr (ctx.vals.map fun (o, v, _) => (o, v))
    (fun s => match ctx.varVals.find? (fun (v, _, _) => v == s) with
      | some (_, v, _) => pure v
      | none => dpConcVar cfg.envExpr s) t

def ctxValProof (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) : MetaM Expr :=
  dpValProof cfg cfg.envExpr
    (ctx.vals.map fun (o, v, _) => (o, v))
    (ctx.vals.map fun (o, _, p) => (o, p))
    (fun s => (ctx.varVals.find? (fun (v, _, _) => v == s)).map fun (_, v, p) => (v, p))
    t


/-- TWO-VALUEDNESS disjunction (`v = t ∨ v = nil`) for a test term's pinned
    value (G1 rung 1, inc-2 — the IF-headed `if1/boolean` test): quoted
    t/nil constants, `equal`/`lexorder` values, boolean-TP fn applications,
    and IFs with two-valued branches (recursively). `none` when no source
    applies — the caller names the frontier (never a silent success). -/
partial def boolDisj? (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) :
    MetaM (Option Expr) := do
  if t == quoteT then return some (mkConst ``t_t_or_nil)
  if t == quoteNil then return some (mkConst ``nil_t_or_nil)
  let v ← ctxValExpr cfg ctx t
  if v.isAppOfArity ``Logic.equal 2 then
    return some (← mkAppM ``logic_equal_t_or_nil #[v.appFn!.appArg!, v.appArg!])
  if v.isAppOfArity ``ACL2.lexorder 2 then
    return some (← mkAppM ``lexorder_boolean #[v.appFn!.appArg!, v.appArg!])
  if v.isAppOfArity ``Logic.lt 2 then
    return some (← mkAppM ``logic_lt_t_or_nil #[v.appFn!.appArg!, v.appArg!])
  match t with
  | .cons (.atom (.symbol hs)) (.cons c (.cons a (.cons b .nil))) =>
    if hs.name == "IF" then do
      let some ha ← boolDisj? cfg ctx a | return none
      let some hb ← boolDisj? cfg ctx b | return none
      let vc ← ctxValExpr cfg ctx c
      try
        return some (← mkAppM ``cond_t_or_nil
          #[mkApp (mkConst ``Logic.toBool) vc, ha, hb])
      catch _ => return none
    else boolDisjFnTp t
  | .cons (.atom (.symbol _)) _ => boolDisjFnTp t
  | _ => return none
where
  /-- fn application with a boolean-TP hypothesis (the emitted
      `(IF (EQUAL (fn X) 'T) 'T (EQUAL (fn X) 'NIL))` corollary shape). -/
  boolDisjFnTp (t : SExpr) : MetaM (Option Expr) := do
    let .cons (.atom (.symbol fs)) argsSpine := t | return none
    let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
      | return none
    let some (formals, _) := cfg.worldVal.defs.get? fs | return none
    let args := (argsSpine.toList?).getD []
    unless formals.length == args.length do return none
    let some (v, conv) := ctx.val? t | return none
    let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
      ++ (args.map reflectSExpr).toArray ++ #[v, conv])
    try
      return some (← mkAppM ``tp_boolean_t_or_nil #[v, fact])
    catch _ => return none

/-- N-ary definition info (the c3 generalization of `DefInfo`). -/
structure DefInfoN where
  formals : List Symbol
  body : SExpr
  defFact : Expr
  closedFact : Expr
  wellScopedFact : Expr

/-- Derive an n-ary defined function's facts on demand (kernel decision). -/
def deriveDefInfoN (cfg : ReplayConfig) (fn : Symbol) : MetaM DefInfoN := do
  match cfg.worldVal.defs.get? fn with
  | none => throwError "deriveDefInfoN: {fn.name} not defined in the world"
  | some (formals, body) =>
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let bodyE := reflectSExpr body
    let someE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[formalsE, bodyE]]
    let defFact ← proveByDecide (← mkEq (← mkDefsGet cfg fn) someE) s!"def {fn.name}"
    let fvE ← mkAppM ``ACL2.Replay.freeVars #[bodyE]
    let closedProp ← withLocalDeclD `s (mkConst ``ACL2.Symbol) fun sv => do
      let memFv ← mkAppM ``Membership.mem #[fvE, sv]
      let memFm ← mkAppM ``Membership.mem #[formalsE, sv]
      mkForallFVars #[sv] (← mkArrow memFv memFm)
    let closedFact ← proveByDecide closedProp s!"closed {fn.name}"
    let wellScopedFact ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[bodyE]) (mkConst ``Bool.true)) s!"well-scoped {fn.name}"
    return { formals, body, defFact, closedFact, wellScopedFact }

/-- Destructure an int-atom value `Expr` (`SExpr.atom (Atom.number (Number.int k))`)
    into its `k`. Hard-fails on any other shape. -/
def intValExpr? (v : Expr) : MetaM Expr := do
  let v ← instantiateMVars v
  unless v.isAppOfArity ``SExpr.atom 1 do throwError "expected int-atom value, got {v}"
  let a := v.appArg!
  unless a.isAppOfArity ``Atom.number 1 do throwError "expected int-atom value, got {v}"
  let n := a.appArg!
  unless n.isAppOfArity ``Number.int 1 do throwError "expected int-atom value, got {v}"
  return n.appArg!

/-- The `(:DEFINITION implies)` GROUND-ZERO recipe: `(implies A B) ⇒
    (if A (if B 't 'nil) 't)` — ACL2's bootstrap defun unfold, proved against
    the BUILTIN semantics (`Logic.implies` + `logic_implies_cond`), because
    `evalOpt` models `implies` as a builtin; adding it to the world would
    shadow the `callBuiltin`/no-shadow facts. The recorded rhs must be EXACTLY
    the unfold body instance. -/
def replayImpliesDef (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  unless children.isEmpty do
    throwError "definition:implies — children on the ground-zero unfold (frontier)"
  let .cons (.atom (.symbol impS)) (.cons A (.cons B .nil)) := lhs
    | throwError "definition:implies — lhs is not (implies A B): {repr lhs}"
  unless impS.name == "IMPLIES" do
    throwError "definition:implies — lhs head {impS.name}"
  let expectedRhs : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons A (.cons (.cons (.atom (.symbol { name := "IF" }))
        (.cons B (.cons quoteT (.cons quoteNil .nil))))
        (.cons quoteT .nil)))
  unless rhs == expectedRhs do
    throwError "definition:implies — rhs {repr rhs} is not the unfold body instance"
  let vA ← ctxValExpr cfg ctx A
  let vB ← ctxValExpr cfg ctx B
  let pA ← ctxValProof cfg ctx A
  let pB ← ctxValProof cfg ctx B
  let hNs ← proveNotSpecial { name := "IMPLIES" }
  let hNo ← proveNoShadow cfg { name := "IMPLIES" }
  let hr ← mkAppM ``callBuiltin_implies #[vA, vB]
  let pL ← mkAppM ``conv_builtin2
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "IMPLIES" },
      reflectSExpr A, reflectSExpr B, vA, vB,
      mkApp2 (mkConst ``Logic.implies) vA vB, hNs, hNo, pA, pB, hr]
  let pR ← ctxValProof cfg ctx rhs
  let valueEq ← mkAppM ``logic_implies_cond #[vA, vB]
  mkAppM ``fuel_eq_of_conv #[pL, pR, valueEq]

/-- The `(:DEFINITION iff)` GROUND-ZERO recipe: `(iff A B) ⇒
    (if A (if B 't 'nil) (if B 'nil 't))` — the preprocess boot-strap
    non-rec arm's body adoption (`emit/expand-abbreviations/nonrec-body`,
    G1 iff rung), proved against the BUILTIN semantics (`Logic.iff` +
    `logic_iff_cond`) exactly as `replayImpliesDef` does for `implies`.
    The recorded rhs must be EXACTLY the unfold body instance. -/
def replayIffDef (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  unless children.isEmpty do
    throwError "definition:iff — children on the ground-zero unfold (frontier)"
  let .cons (.atom (.symbol iffS)) (.cons A (.cons B .nil)) := lhs
    | throwError "definition:iff — lhs is not (iff A B): {repr lhs}"
  unless iffS.name == "IFF" do
    throwError "definition:iff — lhs head {iffS.name}"
  let expectedRhs : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons A (.cons (.cons (.atom (.symbol { name := "IF" }))
        (.cons B (.cons quoteT (.cons quoteNil .nil))))
        (.cons (.cons (.atom (.symbol { name := "IF" }))
          (.cons B (.cons quoteNil (.cons quoteT .nil)))) .nil)))
  unless rhs == expectedRhs do
    throwError "definition:iff — rhs {repr rhs} is not the unfold body instance"
  let vA ← ctxValExpr cfg ctx A
  let vB ← ctxValExpr cfg ctx B
  let pA ← ctxValProof cfg ctx A
  let pB ← ctxValProof cfg ctx B
  let hNs ← proveNotSpecial { name := "IFF" }
  let hNo ← proveNoShadow cfg { name := "IFF" }
  let hr ← mkAppM ``callBuiltin_iff #[vA, vB]
  let pL ← mkAppM ``conv_builtin2
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "IFF" },
      reflectSExpr A, reflectSExpr B, vA, vB,
      mkApp2 (mkConst ``Logic.iff) vA vB, hNs, hNo, pA, pB, hr]
  let pR ← ctxValProof cfg ctx rhs
  let valueEq ← mkAppM ``logic_iff_cond #[vA, vB]
  mkAppM ``fuel_eq_of_conv #[pL, pR, valueEq]

/-- Ground `executable-counterpart` computation: ACL2 ran the executable
    counterpart of a CLOSED term `lhs`, recording the result `v`. The kernel
    re-checks the SAME computation by reducing `evalOpt` at a concrete fuel
    (found by running the evaluator) and lifts by fuel monotonicity. Returns
    `∃N∀f≥N, eval lhs = some v`. Hard-fails if `lhs` is open or the evaluator
    diverges from ACL2's recorded result — this is the carve-out's faithful
    mirror (ACL2 records only a verdict; we re-run the same closed computation),
    NOT a license to compute through open terms. -/
def replayExecGround (cfg : ReplayConfig) (lhs v : SExpr) : MetaM Expr := do
  unless (ACL2.Replay.freeVars lhs).isEmpty do
    throwError "executable-counterpart: lhs {repr lhs} has free variables"
  -- find a sufficient fuel by running the SAME evaluator the theorem is about
  -- (ground term: the env is never consulted, so any env works)
  let mut F := 8
  let mut v? : Option SExpr := none
  while v?.isNone && F ≤ 65536 do
    v? := ACL2.evalOpt F cfg.worldVal {} lhs
    if v?.isNone then F := F * 2
  let some vComputed := v?
    | throwError "executable-counterpart: {repr lhs} does not converge by fuel 65536"
  unless vComputed == v do
    throwError "executable-counterpart: evalOpt computes {repr vComputed}, \
                the recorded result is {repr v} — evaluator/ACL2 divergence on {repr lhs}"
  let lhsApp := mkApp4 (mkConst ``evalOpt) (mkNatLit F) cfg.worldExpr cfg.envExpr
    (reflectSExpr lhs)
  let someV ← mkAppM ``Option.some #[reflectSExpr v]
  unless ← isDefEq lhsApp someV do
    throwError "executable-counterpart: evalOpt {F} … {repr lhs} does not REDUCE \
                to {repr v} (env-dependence or reflected-world mismatch?)"
  let hAt ← mkExpectedTypeHint (← mkEqRefl someV) (← mkEq lhsApp someV)
  mkAppM ``conv_of_eval_at
    #[mkNatLit F, cfg.worldExpr, cfg.envExpr, reflectSExpr lhs, reflectSExpr v, hAt]

/-- Expr-level SExpr application `(fn a₁ … aₙ)` from argument `Expr`s. -/
def mkAppListExpr (fn : Symbol) (args : Array Expr) : Expr :=
  let spine := args.foldr (fun a acc => mkApp2 (mkConst ``SExpr.cons) a acc)
    (mkConst ``SExpr.nil)
  mkApp2 (mkConst ``SExpr.cons)
    (mkApp (mkConst ``SExpr.atom) (mkApp (mkConst ``Atom.symbol) (reflectSymbol fn)))
    spine

/-- `∃ N, ∃ v, ∀ f ≥ N, evalOpt f w e t = some v` with the term as an `Expr`. -/
def mkConvPropEx (w e tE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let inner ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
        let ge ← mkAppM ``GE.ge #[fV, nV]
        let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, tE]
        let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vV
        mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
      mkAppM ``Exists #[← mkLambdaFVars #[vV] body]
    mkAppM ``Exists #[← mkLambdaFVars #[nV] inner]

/-- `∃ N, ∀ f ≥ N, evalOpt f w e t = some v` with term and value as `Expr`s. -/
def mkValConvPropEx (w e tE vE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
      let ge ← mkAppM ``GE.ge #[fV, nV]
      let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, tE]
      let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
      mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nV] body]

/-- `∃ N, ∀ f ≥ N, evalOpt f w e a = evalOpt f w e b` (the chain Prop) with
    both terms as `Expr`s. -/
def mkEvalEqPropEx (w e aE bE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
      let ge ← mkAppM ``GE.ge #[fV, nV]
      let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, aE]
      let rhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, bE]
      mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nV] body]

/-- `∃N∀f≥N, eval (quote t) = some SExpr.t` (the constant, not the reflection). -/
def quoteTFact (cfg : ReplayConfig) : MetaM Expr := do
  let pq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
  let hv ← proveByDecide
    (← mkEq (reflectSExpr SExpr.t) (mkConst ``SExpr.t)) "quote-t is SExpr.t"
  mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr quoteT, reflectSExpr SExpr.t,
      mkConst ``SExpr.t, pq, hv]

/-! ## Shared composition helpers (de-dup pass, 2026-07-21)

Single homes for compositions that had grown near-clones across the clause
walkers — extracted behavior-preserving (see CLAUDE.md's engineering-quality
policy; the risk managed is a fix landing in one clone and missing its twin). -/

/-- Chain a fuel-eq with an OPTIONAL continuation: `a` alone, or
    `fuel_chain_eq a b`. The ubiquitous chain-tail idiom (quality pass Q1). -/
def chainWith (a : Expr) (b? : Option Expr) : MetaM Expr :=
  match b? with
  | none => pure a
  | some b => mkAppM ``fuel_chain_eq #[a, b]

/-- Chain an OPTIONAL accumulated fuel-eq BEFORE a step: `b` alone, or
    `fuel_chain_eq a b`. -/
def chainAfter (a? : Option Expr) (b : Expr) : MetaM Expr :=
  match a? with
  | none => pure b
  | some a => mkAppM ``fuel_chain_eq #[a, b]

/-- Combine two OPTIONAL fuel-eq chains. -/
def chainOptWith (a? b? : Option Expr) : MetaM (Option Expr) :=
  match a?, b? with
  | none, b? => pure b?
  | some a, none => pure (some a)
  | some a, some b => some <$> mkAppM ``fuel_chain_eq #[a, b]

/-- `EvTrue` transport along an OPTIONAL R-TAGGED chain (backward: the
    chain's START is proved true from its END — `evtrue_of_fuel_eq` /
    `evtrue_of_evrel_siff` per relation). -/
def evtrueWithR (ch? : Option (Expr × Bool)) (p : Expr) : MetaM Expr :=
  match ch? with
  | none => pure p
  | some (ch, false) => mkAppM ``evtrue_of_fuel_eq #[ch, p]
  | some (ch, true) => mkAppM ``evtrue_of_evrel_siff #[ch, p]

/-- Chain an IFF head with an optional R-TAGGED rest (the rest's FINAL
    term's convergence injects an eq rest into the SIff lane). -/
def chainIffWithR (cfg : ReplayConfig) (ctx : ReplayCtx) (head : Expr)
    (final : SExpr) (rest : Option (Expr × Bool)) : MetaM (Expr × Bool) := do
  match rest with
  | none => return (head, true)
  | some (r, true) =>
    return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, head, r], true)
  | some (r, false) => do
    let pConv ← ctxValProof cfg ctx final
    let rS ← mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, r, pConv]
    return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, head, rS], true)

/-- Require an EVAL-EQUALITY chain (G1 rung 1, inc-2b): the chain payload
    carries its relation flag (`false` = fuel-eq, `true` = `EvRel SIff`);
    a consumer that composes with eq-only machinery names the frontier
    instead of mis-composing. -/
def chainReqEq (c? : Option (Expr × Bool)) : MetaM (Option Expr) :=
  match c? with
  | none => pure none
  | some (c, false) => pure (some c)
  | some (_, true) => throwError "chain: IFF composite where an \
      eval-equality is required (G1 rung-1 frontier)"

/-- Chain an EQ head with an optional R-TAGGED rest: eq·eq stays eq;
    eq·iff injects the head into the SIff lane via the MID term's
    convergence (the preprocess chain core's mixed compose). -/
def chainWithR (cfg : ReplayConfig) (ctx : ReplayCtx) (head : Expr)
    (mid : SExpr) (rest : Option (Expr × Bool)) : MetaM (Expr × Bool) := do
  match rest with
  | none => return (head, false)
  | some (r, false) => return (← mkAppM ``fuel_chain_eq #[head, r], false)
  | some (r, true) => do
    let pConv ← ctxValProof cfg ctx mid
    let headS ← mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, head, pConv]
    return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, headS, r], true)

/-- `EvTrue` transport along an OPTIONAL fuel-eq chain:
    `p` alone, or `evtrue_of_fuel_eq ch p`. -/
def evtrueWith (ch? : Option Expr) (p : Expr) : MetaM Expr :=
  match ch? with
  | none => pure p
  | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]

/-- Falsity of a segment literal from the composer's byCases `facts`:
    a ¬sign fact for the literal itself, or — for a `(not T)` literal — a
    sign fact for `T` lifted by `not_nil_of_truthy` (if-interp's
    convert-assumptions rule set). The FACTS-based core shared by the
    branch-selection and vacuous-residual paths; callers layer their own
    extra sources (the open leaf's own falsity, `ctx.litFactByTerm?`). -/
def segFactFalsity (facts : List (SExpr × Expr × Bool × Expr)) (L : SExpr) :
    MetaM (Option Expr) := do
  if let some (_, _, _, hf) :=
      facts.find? (fun (T, _, sign, _) => !sign && L == T) then
    return some hf
  match L with
  | .cons (.atom (.symbol ns)) (.cons T .nil) =>
    if ns.name == "NOT" then
      match facts.find? (fun (T', _, sign, _) => sign && T' == T) with
      | some (_, _, _, hf) => return some (← mkAppM ``not_nil_of_truthy #[hf])
      | none => return none
    else return none
  | _ => return none

/-- `eval t` converges to `nil`: the pinned convergence cast along a falsity
    fact `hf : v(t) = nil` (`re_val_cast` plumbing, quality pass Q2). -/
def castConvToNil (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr)
    (hf : Expr) : MetaM Expr := do
  mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, ← ctxValExpr cfg ctx t,
      mkConst ``SExpr.nil, ← ctxValProof cfg ctx t, hf]

/-- Peel the leading literals of a proved disjunction along their falsity
    facts (`evtrue_extract_else` fold), leaving `EvTrue` of the LAST
    literal. `deriveF` supplies each peeled literal's falsity proof
    (throwing if unavailable). Shared by the residual-peel paths. -/
def peelToLast (cfg : ReplayConfig) (ctx : ReplayCtx) (lits : List SExpr)
    (pChild : Expr) (deriveF : SExpr → MetaM Expr) : MetaM Expr := do
  let mut p := pChild
  for L in lits.dropLast do
    p ← mkAppM ``evtrue_extract_else
      #[← castConvToNil cfg ctx L (← deriveF L), p]
  return p

/-- Ex-falso closure of a VACUOUS residual: the pushed child's clause
    (`expected`, proved as `pChild`) is all-false in scope — peel it to its
    last literal and refute (`absurd`), producing `EvTrue goalTerm`.
    Shared by the spine walker's and composeSplit's vacuous arms. -/
def vacuousResidualClose (cfg : ReplayConfig) (ctx : ReplayCtx)
    (expected : List SExpr) (pChild : Expr) (goalTerm : SExpr)
    (deriveF : SExpr → MetaM Expr) : MetaM Expr := do
  let p ← peelToLast cfg ctx expected pChild deriveF
  let some lastL := expected.getLast?
    | throwError "vacuousResidualClose: empty residual clause"
  let hfLast ← deriveF lastL
  let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[p, ← ctxValProof cfg ctx lastL]
  let goalTy ← mkAppM ``EvTrue
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr goalTerm]
  mkAppOptM ``absurd #[none, some goalTy, some hfLast, some hNe]

/-- `(if <c> thn els) ≡ <taken branch>` for a QUOTED-CONSTANT test `c`
    (quote term around value `cv`): `re_if_false` on nil (via `re_val_cast`),
    else `re_if_true`. Branch value/proof from the ctx pins. Returns the
    equality and the taken branch. Shared by the identity-arm and
    folded-collapse display-fold recipes and collapseEval's constant arm. -/
def mkConstTestCollapse (cfg : ReplayConfig) (ctx : ReplayCtx)
    (c cv thn els : SExpr) : MetaM (Expr × SExpr) := do
  let hc ← mkAppM ``re_val_quote
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
  if cv == SExpr.nil then
    let hcNil ← mkAppM ``re_val_cast
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr cv,
        mkConst ``SExpr.nil, hc, ← proveByDecide
          (← mkEq (reflectSExpr cv) (mkConst ``SExpr.nil)) "cv is nil"]
    let vb ← ctxValExpr cfg ctx els
    let hb ← ctxValProof cfg ctx els
    let _ := vb
    let p ← mkAppM ``re_if_false
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
        reflectSExpr els, vb, hcNil, hb]
    return (p, els)
  else
    let hcv ← proveByDecide
      (← mkEq (mkApp (mkConst ``Logic.toBool) (reflectSExpr cv))
              (mkConst ``Bool.true)) "toBool of the constant test"
    let va ← ctxValExpr cfg ctx thn
    let ha ← ctxValProof cfg ctx thn
    let _ := va
    let p ← mkAppM ``re_if_true
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
        reflectSExpr els, reflectSExpr cv, va, hc, hcv, ha]
    return (p, thn)

/-- Close `EvTrue (disjoin (lit :: restLits))` from the closing literal's
    `pclose : ∃N∀f≥N, eval lit = some t`: bare literal when `restLits` is
    empty, else `conv_if_true` short-circuits the tail. Shared by the
    quoteT-closer and ground-'T-closer paths. -/
def closeOnTrueLit (cfg : ReplayConfig) (lit : SExpr) (restLits : List SExpr)
    (pclose : Expr) : MetaM Expr := do
  if restLits.isEmpty then
    mkAppM ``evtrue_of_eq_t #[pclose]
  else
    let restTerm := disjoinTerm restLits
    let hq ← mkAppM ``re_val_quote
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    let hcv ← proveByDecide
      (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t))
              (mkConst ``Bool.true)) "toBool t"
    let hIf ← mkAppM ``conv_if_true
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr lit, reflectSExpr quoteT,
        reflectSExpr restTerm, mkConst ``SExpr.t, mkConst ``SExpr.t, pclose,
        hcv, hq]
    mkAppM ``evtrue_of_eq_t #[hIf]


/-- Unary BUILTINS whose ground-zero `:TYPE-PRESCRIPTION` corollary is the
    standard nonneg-int shape `(IF (INTEGERP (fn v)) (NOT (< (fn v) '0)) 'NIL)`,
    with the kernel lemma proving the lifted `Logic.integerp` fact against the
    builtin's own `Logic` semantics. The pin route applies an entry ONLY when
    the development EMITTED that exact corollary for the fn (`cfg.gzTps`) —
    the type fact is consumed from ACL2's emission; only its proof is the
    trusted core's (for a builtin, the `Logic` fn IS its semantics here). -/
def builtinIntTps : List (String × Name) :=
  [("LEN", ``logic_len_integerp)]

#guard builtinIntTps.all (fun e => (dpUnary.lookup e.1).isSome)

/-- Trusted-core VALUE lemmas for int-valued BUILTINS (BNEXT-SIZE route
    layer 3): (fn, consp-nil lemma, natp-t lemma) — the ratified
    per-function-EVALUATION-lemma class (kernel facts about `Logic.len`
    etc., which no emission can supply). R2 EXPIRY DISCHARGED BY GATE
    MOVE (2026-08-07, interpretation flagged for user review in the
    commit): the drift was the NAME-KEYED OPT-IN deciding which fns take
    this route; the GATE is now the EMITTED DATA — the fn's TP :BASICTS
    numerically against the cited recognizer tuple's true-ts
    (`recogVerdictGate`), both numbers from the artifact. This table
    supplies only the kernel proof for a fn the gate has already
    admitted; a gated fn with no lemma here fails loudly. -/
def builtinRecogFacts : List (String × Name × Name) :=
  [("LEN", ``logic_consp_len_nil, ``logic_natp_len_t)]

/-- Two's-complement bitwise AND on `Int` — ACL2's type-set encoding
    (a negative number is the complemented bit-set): NOT y = -y-1, and
    the four sign cases reduce to Nat bitwise ops. -/
def tsAnd : Int → Int → Int
  | .ofNat x, .ofNat y => .ofNat (x &&& y)
  | .ofNat x, .negSucc y => .ofNat (x ^^^ (x &&& y))
  | .negSucc x, .ofNat y => .ofNat (y ^^^ (x &&& y))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)

/-- The R2 DATA-DRIVEN verdict gate, rewired per audit 2026-08-07 S4 to
    ACL2's OWN `type-set-recognizer` semantics: with `ts` the argument's
    type-set — the STEP's recorded `:TYPESET` when present (the exact
    value ACL2 consulted), else the fn's emitted TP `:BASICTS` — a TRUE
    verdict demands `ts ∩ falseTs = ∅` (with a nonempty `ts ∩ trueTs`),
    a FALSE verdict `ts ∩ trueTs = ∅`. Every number is EMITTED; zero
    Lean-side type knowledge. -/
def recogVerdictGate (cfg : ReplayConfig) (fn recog : String)
    (wantTrue : Bool) (stepTs : Option Int := none) : MetaM Unit := do
  let ts ← match stepTs with
    | some t => pure t
    | none =>
      match cfg.gzTpBasicTs.lookup fn with
      | some bts => pure bts
      | none => throwError "recogVerdictGate: {fn} has no recorded step \
          :TYPESET and no emitted TP :BASICTS (emission gap — recapture \
          with the item-2 fork)"
  let some tup := cfg.recogTuples.find? (fun t => t.fn == recog)
    | throwError "recogVerdictGate: no cited recognizer tuple for \
        {recog} (emission gap — the fn was not cited at capture)"
  -- Int bitwise: two's-complement semantics match ACL2's type-set
  -- encoding (negative numbers = complemented sets).
  if wantTrue then
    unless tsAnd ts tup.falseTs == 0 do
      throwError "recogVerdictGate: ts {ts} intersects {recog}'s \
          false-ts {tup.falseTs} — the emitted data does not support \
          the TRUE verdict (frontier)"
    unless tsAnd ts tup.trueTs != 0 do
      throwError "recogVerdictGate: ts {ts} does not intersect {recog}'s \
          true-ts {tup.trueTs} — the emitted data does not support the \
          TRUE verdict (frontier)"
  else
    unless tsAnd ts tup.trueTs == 0 do
      throwError "recogVerdictGate: ts {ts} intersects {recog}'s \
          true-ts {tup.trueTs} — the emitted data does not support the \
          FALSE verdict (frontier)"

#guard builtinRecogFacts.all (fun e => (dpUnary.lookup e.1).isSome)

/-- The standard nonneg-int TP corollary at application `app`:
    `(IF (INTEGERP app) (NOT (< app '0)) 'NIL)`. -/
def intTpCorollary (app : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "INTEGERP" })) (.cons app .nil))
      (.cons (.cons (.atom (.symbol { name := "NOT" }))
          (.cons (.cons (.atom (.symbol { name := "<" }))
              (.cons app (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons (.atom (.number (.int 0))) .nil)) .nil))) .nil))
        (.cons quoteNil .nil)))

/-- Can the DP value walkers (`dpValExpr`/`dpValProof`) produce a value for `t`
    from the ctx pins, env variable lookups, and builtin registries alone?
    PROVISIONING guard for the builtin TP pin arm: declining just means no pin
    is offered (a replay that needs it fails at its use site) — provisioning
    itself must never throw on an unsupported shape. -/
partial def valueOfferable (ctx : ReplayCtx) (t : SExpr) : Bool :=
  (ctx.val? t).isSome ||
  match t with
  | .atom (.symbol s) => s.name != "T"   -- `re_val_var` needs ¬isNamed "t"
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    fs.name == "QUOTE" ||
    ((dpUnary.lookup fs.name).isSome && valueOfferable ctx a)
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    (dpBinary.lookup fs.name).isSome && valueOfferable ctx a && valueOfferable ctx b
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    fs.name == "IF" && valueOfferable ctx c && valueOfferable ctx th &&
      valueOfferable ctx e
  | _ => false

/-- Derive the INT-ATOM value + convergence proof of a registered unary
    BUILTIN's application (`builtinIntTps`), gated on the development having
    EMITTED the standard nonneg-int TP corollary for it (`cfg.gzTps`). Used as
    a LOCAL fallback at the use sites that need an int-shaped value for a term
    with no ctx pin (the unicity-of-0 recipe, the acl2-numberp recognizer) —
    deliberately NOT a `pinTermOpaques` arm: entering the shared `ctx.vals`
    map would make every later `dpValExpr` of the term opaque, breaking
    consumers that compute the builtin's STRUCTURAL value (e.g. the
    `definition:LEN` unfold against `gz_def_len`). Returns `none` when not
    registered / not emitted / the argument value is unofferable (the caller's
    existing hard-fail stands); an emitted corollary that DRIFTS from the
    registered shape hard-fails. -/
def builtinIntVal? (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) :
    MetaM (Option (Expr × Expr)) := do
  let .cons (.atom (.symbol fs)) argSpine := t | return none
  let some intLemma := builtinIntTps.lookup fs.name | return none
  let some cor := cfg.gzTps.lookup fs.name | return none
  -- recover the corollary's formal application from the INTEGERP arm, then
  -- pin the WHOLE corollary to the standard shape at it (drift hard-fails)
  let .cons _ (.cons (.cons _ (.cons app _)) _) := cor
    | throwError "builtinIntVal?: emitted TP corollary of {fs.name} does not \
                  destructure: {repr cor}"
  unless cor == intTpCorollary app do
    throwError "builtinIntVal?: emitted TP corollary of {fs.name} drifted from \
                the registered nonneg-int shape: {repr cor}"
  let .cons arg .nil := argSpine
    | throwError "builtinIntVal?: {fs.name} not applied to exactly one arg: {repr t}"
  unless valueOfferable ctx arg do return none
  let opq := ctx.vals.map fun (o, v, _) => (o, v)
  let opqP := ctx.vals.map fun (o, _, p) => (o, p)
  let varP := fun s =>
    (ctx.varVals.find? (fun (v, _, _) => v == s)).map fun (_, v, p) => (v, p)
  let varVal := fun s => match varP s with
    | some (v, _) => pure v
    | none => dpConcVar cfg.envExpr s
  let conv ← dpValProof cfg cfg.envExpr opq opqP varP t
  let value ← dpValExpr opq varVal t
  let hInt ← mkAppM intLemma #[← dpValExpr opq varVal arg]
  let hkEx ← mkAppM ``logic_integerp_int #[value, hInt]
  let k ← mkAppM ``Exists.choose #[hkEx]
  let hvk ← mkAppM ``Exists.choose_spec #[hkEx]
  let value' := mkApp (mkConst ``SExpr.atom)
    (mkApp (mkConst ``Atom.number) (mkApp (mkConst ``Number.int) k))
  let conv' ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, value, value', conv, hvk]
  return some (value', conv')

/-- PIN the value of every user-fn application occurring in `t` (bottom-up) from
    the bound totality hypotheses, refining to the int-atom shape when the fn's
    emitted TP corollary has the standard `(IF (INTEGERP app) … 'NIL)` shape. -/
partial def pinTermOpaques (cfg : ReplayConfig) (envExpr : Expr) (ctx : ReplayCtx)
    (t : SExpr) : MetaM ReplayCtx := do
  match t with
  | .cons (.atom (.symbol fs)) argSpine =>
    if fs.name == "QUOTE" then return ctx
    let args := (argSpine.toList?).getD []
    let mut ctx := ctx
    for a in args do
      ctx ← pinTermOpaques cfg envExpr ctx a
    if (cfg.worldVal.defs.get? fs).isNone then return ctx
    if (ctx.val? t).isSome then return ctx
    -- PROVISIONING, not consumption: with no totality hypothesis bound (the
    -- unconditional harness) the value is simply not offered — a replay that
    -- NEEDS it hard-fails at the use site (`dpValExpr`), never silently.
    let some hyp := ctx.totalHyps.lookup fs.name
      | return ctx
    let argConvs ← args.mapM (fun a => proveConv cfg envExpr ctx a)
    let exConv := mkAppN hyp
      ((#[envExpr] : Array Expr) ++ (args.map reflectSExpr).toArray ++ argConvs.toArray)
    let value ← mkAppM ``pinVal #[exConv]
    let conv ← mkAppM ``pinVal_spec #[exConv]
    match ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) with
    | some (_, cor, tpHyp) =>
      match cor with
      | .cons (.atom (.symbol ifS))
          (.cons (.cons (.atom (.symbol intS)) (.cons _ .nil))
            (.cons thenC (.cons _ .nil))) =>
        unless ifS.name == "IF" && intS.name == "INTEGERP" do
          -- unsupported corollary shape: pin unrefined
          return { ctx with vals := ctx.vals ++ [(t, value, conv)] }
        -- fact : lifted-corollary(value) = t
        let fact := mkAppN tpHyp
          ((#[envExpr] : Array Expr) ++ (args.map reflectSExpr).toArray ++ #[value, conv])
        -- X = the lifted then-branch at `value` (for the extraction lemma);
        -- the application pattern is the corollary's integerp argument
        let .cons _ (.cons (.cons _ (.cons appPat2 .nil)) _) := cor
          | throwError "pinTermOpaques: corollary destructure failed: {repr cor}"
        let xLift ← dpValExpr [(appPat2, value)]
          (fun s => throwError "pinTermOpaques: corollary free var {s.name}") thenC
        let hInt ← mkAppM ``tp_cond_integerp_t #[value, xLift, fact]
        let hkEx ← mkAppM ``logic_integerp_int #[value, hInt]
        let k ← mkAppM ``Exists.choose #[hkEx]
        let hvk ← mkAppM ``Exists.choose_spec #[hkEx]
        let value' := mkApp (mkConst ``SExpr.atom)
          (mkApp (mkConst ``Atom.number) (mkApp (mkConst ``Number.int) k))
        let conv' ← mkAppM ``re_val_cast
          #[cfg.worldExpr, envExpr, reflectSExpr t, value, value', conv, hvk]
        return { ctx with vals := ctx.vals ++ [(t, value', conv')] }
      | _ => return { ctx with vals := ctx.vals ++ [(t, value, conv)] }
    | none => return { ctx with vals := ctx.vals ++ [(t, value, conv)] }
  | _ => return ctx

/-- A type-fact REQUEST for the bounded value-level type-set walker. -/
inductive TsReq where
  /-- `v(t) = nil` -/
  | isNil (t : SExpr)
  /-- `v(t) ≠ nil` -/
  | isTruthy (t : SExpr)
  /-- `Logic.consp v(t) = SExpr.t` -/
  | isConspT (t : SExpr)

/-- ONE view of the clause-context FALSITY channels (segment literals,
    clause literals, false branch facts) — every walker rung and no one
    else scans these (the whole-clause dedup of the epicycle
    consolidation, docs/notes/2026-07-31_type-set-walker-design.md). -/
def falsitySources (ctx : ReplayCtx) : List (SExpr × Expr) :=
  ctx.segFacts ++ ctx.litFacts.map (fun (_, l, h) => (l, h)) ++
  ctx.branchFacts.filterMap (fun (bt, _, sign, h) =>
    if !sign then some (bt, h) else none)

/-- A fact for syntactic term `st` whose PROOF type-checks against
    `expected` (the fail-closed lookup every rung uses). -/
def findFactChecked (sources : List (SExpr × Expr)) (st : SExpr)
    (expected : Expr) : MetaM (Option Expr) := do
  let mut r : Option Expr := none
  for (t', h) in sources do
    if r.isNone && t' == st then
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType h) expected then
        r := some h
  pure r

/-- A clause-context equation literal `(not (equal A B))`, viewed as its sides. -/
def notEqualSides? : SExpr → Option (SExpr × SExpr)
  | .cons (.atom (.symbol ns))
      (.cons (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) .nil) =>
    if ns.name == "NOT" && es.name == "EQUAL" then some (a, b) else none
  | _ => none

/-- The in-scope clause-context EQUATIONS: every litFact/segFact of shape
    `(not (equal A B))`, as side pairs with the recorded falsity proof. This
    set's equivalence closure IS ACL2's type-alist class structure over the
    clause (assume-true-false on every literal). -/
def inScopeEquations (ctx : ReplayCtx) :
    List (SExpr × SExpr × Expr × Bool) :=
  -- an edge is (a, b, proof, truthy): a FALSE `(not (equal a b))` fact
  -- (proof : v(not(equal a b)) = nil), or — truthy = true — a TRUE
  -- `(equal a b)` branch fact (proof : v(equal a b) ≠ nil, the assumed
  -- if-test of an enclosing branch — PERM-CONS's (EQUAL X1 A) then-branch)
  (ctx.litFacts.filterMap fun (_, t, h) =>
    (notEqualSides? t).map fun (a, b) => (a, b, h, false)) ++
  (ctx.segFacts.filterMap fun (t, h) =>
    (notEqualSides? t).map fun (a, b) => (a, b, h, false)) ++
  (ctx.branchFacts.filterMap fun (bt, _, sign, h) =>
    if sign then
      match bt with
      | .cons (.atom (.symbol es)) (.cons a (.cons b .nil)) =>
        if es.name == "EQUAL" then some (a, b, h, true) else none
      | _ => none
    else none)

/-- BFS a chain `src → dst` through the equation edges, each usable in either
    orientation. DETERMINISTIC, not search: the closure of a finite equation
    set is canonical, edges are tried in fact order, and the first (shortest)
    path is taken — any valid chain proves the same pinned equation. Each step
    is `(a, b, falsityProof, flipped)` (`flipped` = walked b→a). -/
def eqChain? (eqs : List (SExpr × SExpr × Expr × Bool)) (src dst : SExpr) :
    Option (List (SExpr × SExpr × Expr × Bool × Bool)) := Id.run do
  if src == dst then return some []
  let mut paths : List (SExpr × List (SExpr × SExpr × Expr × Bool × Bool)) :=
    [(src, [])]
  let mut visited : List SExpr := [src]
  for _ in List.range (eqs.length + 1) do
    let mut next : List (SExpr × List (SExpr × SExpr × Expr × Bool × Bool)) := []
    for (t, path) in paths do
      for (a, b, h, truthy) in eqs do
        let step? :=
          if a == t && !visited.contains b then
            some (b, (a, b, h, truthy, false))
          else if b == t && !visited.contains a then
            some (a, (a, b, h, truthy, true))
          else none
        if let some (t', edge) := step? then
          let path' := path ++ [edge]
          if t' == dst then return some path'
          visited := visited ++ [t']
          next := next ++ [(t', path')]
    paths := next
  return none

/-- Compose the value-level equality `val(src) = val(dst)` along an equation
    chain (TRANSITIVE type-alist equivalence, MDD-ratified 2026-07-23: ACL2's
    type-alist stores equivalence CLASSES, never a chain — the composition is
    derived deterministically here, its target pinned by the solidify node's
    emitted `:EQUIV-TERM`). Returns `none` on an empty chain. -/
def composeEqChain (cfg : ReplayConfig) (ctx : ReplayCtx)
    (chain : List (SExpr × SExpr × Expr × Bool × Bool)) :
    MetaM (Option Expr) := do
  let mut acc : Option Expr := none
  for (a, b, hf, truthy, flipped) in chain do
    let va ← ctxValExpr cfg ctx a
    let vb ← ctxValExpr cfg ctx b
    let hEq ←
      if truthy then
        -- a TRUE (equal a b) branch fact: v(equal a b) ≠ nil decodes to
        -- va = vb directly
        mkAppM ``Logic.eq_of_equal_ne_nil #[hf]
      else
        mkAppM ``logic_not_equal_nil_eq #[va, vb, hf]
    let hEq ← if flipped then mkAppM ``Eq.symm #[hEq] else pure hEq
    acc := some (← match acc with
      | none => pure hEq
      | some p => mkAppM ``Eq.trans #[p, hEq])
  return acc

end ACL2.Replay.Driver
