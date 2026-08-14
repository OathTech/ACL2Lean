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
  /-- PARAMETRIC-REPLAY hypothesis tables (Phase 2, the R6 scope
      abstraction): over an ABSTRACT `worldExpr` (a bound `w : World`),
      the on-demand kernel decisions below cannot evaluate — these
      tables carry the BOUND HYPOTHESES instead. `defFactHyps`: fn ↦
      proof of `w.defs.get? fn = some (formals, body)` (formals/body
      still read from `worldVal`, the canonical model — the hypothesis
      TYPE is exactly what the derivation would state). `noShadowHyps`:
      builtin ↦ proof of `w.defs.get? s = none`. Empty on concrete
      replays (decide path unchanged). A SIG fn deliberately has NO
      entry — an unfold demand on it hard-fails, which IS the
      witness-dereference guard (design item 5). -/
  defFactHyps : List (Symbol × Expr) := []
  noShadowHyps : List (Symbol × Expr) := []
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
  /-- RECORDED-TERMINATION replayed statements (sorting arc 2026-07-28): per defun with
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
  /-- (fn, :LEAVES) from the emitted TP events, ALL fns (unlike `gzTps`):
      ACL2's own return-path leaf enumeration, each leaf carrying its
      context-refined verdict, ruling tests, type-alist and subterm
      verdicts (see `TpLeaf`). The TP prover's return-path arms admit a
      leaf only when ACL2 emitted it here with a covering verdict. -/
  tpLeaves : List (String × List TpLeaf) := []
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

/-- Deterministic ONE-WAY first-order matching of `term` against `pattern`:
    bind the pattern's ARGUMENT-position variables (bare symbols) to
    subterms so the instantiated pattern equals the term; application HEADS
    must match exactly; QUOTE subterms are opaque constants; bindings must
    be consistent. `none` on any mismatch — the consumer's loud frontier.
    Used where ACL2 emits NO substitution (type-set TP-rule applications):
    unique first-order matching is a read-off, not search, and the caller
    recompute-checks `substTerm σ pattern == term`.
    (RESURRECTED, final-closeout: killed at 910785a for lacking a green
    consumer; its consumer chain is now reachable — the tpthm audit
    2026-08-04 verified this matcher under 11 adversarial probes.) -/
partial def matchPatternGo (p t : SExpr) (σ : List (Symbol × SExpr)) :
    Option (List (Symbol × SExpr)) :=
  match p, t with
  | .atom (.symbol v), _ =>
    match σ.find? (fun (w, _) => w == v) with
    | some (_, t') => if t' == t then some σ else none
    | none => some ((v, t) :: σ)
  | .cons (.atom (.symbol pf)) pargs, .cons (.atom (.symbol tf)) targs =>
    if pf.name == "QUOTE" then if p == t then some σ else none
    else if pf != tf then none
    else
      pargs.toList?.bind fun pl =>
      targs.toList?.bind fun tl =>
      if pl.length != tl.length then none
      else (pl.zip tl).foldlM (fun σ (pp, tt) => matchPatternGo pp tt σ) σ
  | _, _ => if p == t then some σ else none

def matchPattern? (pattern term : SExpr) :
    Option (List (Symbol × SExpr)) :=
  matchPatternGo pattern term []

/-- A THEOREM-classed :TYPE-PRESCRIPTION rule's hypothesis surface
    (`tpthm:<thm>`, the FIRST `:CLASSES` consumer): the theorem name and
    its Goal-clause formula, offered as the whole-formula replayed
    statement. Consumed by `replayRecognizer`'s cited-rune fallback (a
    recognizer verdict whose ttree cites a `(:TYPE-PRESCRIPTION <thm>)`
    rune naming a defthm, not a defun admission TP — RM has none;
    TRUE-LISTP-RM is the anchor case). -/
structure TpThmSpec where
  name : String
  formula : SExpr
  deriving BEq, Repr

/-- Does an emitted `:CLASSES` value name :TYPE-PRESCRIPTION — either the
    bare keyword (TRUE-LISTP-RM's shape) or a member of the class list
    (each entry a keyword or a `(keyword …)` spec)? -/
def classesNameTP : Option SExpr → Bool
  | some (.atom (.keyword k)) => k == "TYPE-PRESCRIPTION"
  | some l =>
    match l.toList? with
    | some items => items.any fun it =>
        match it with
        | .atom (.keyword k) => k == "TYPE-PRESCRIPTION"
        | .cons (.atom (.keyword k)) _ => k == "TYPE-PRESCRIPTION"
        | _ => false
    | none => false
  | none => false

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

/-- A FUNCTIONAL-INSTANCE LMI (R7b): `(:FUNCTIONAL-INSTANCE thm
    (fn (LAMBDA (formals…) body)) …)` → the cited theorem's name and the
    functional substitution. Non-lambda substituents are the frontier
    (ACL2 also allows bare fn names — not in the corpus; hard-fail there,
    never guess). -/
def lmiFnInstance? : SExpr → Option (String × List (Symbol × List Symbol × SExpr))
  | .cons (.atom (.keyword "FUNCTIONAL-INSTANCE"))
      (.cons (.atom (.symbol s)) pairsS) => do
    let pairs ← pairsS.toList?
    let σ ← pairs.mapM fun p => match p with
      | .cons (.atom (.symbol fn))
          (.cons (.cons (.atom (.symbol lam))
            (.cons formalsE (.cons body .nil))) .nil) => do
        guard (lam.name == "LAMBDA")
        let formals ← (← formalsE.toList?).mapM fun f => match f with
          | .atom (.symbol v) => some v
          | _ => none
        some (fn, formals, body)
      | _ => none
    some (s.name, σ)
  | _ => none

/-- A functional-instance `use` offer (R7b): the cited theorem, the
    EMITTED functional substitution (kept for keying/display), and the
    INSTANTIATED formula (recomputed `substFnCalls` of the dependency's
    translated Goal, verbatim-checked against the emitted `:HYPS`
    instance at the offer-derivation site). -/
structure UseFiSpec where
  name : String
  subst : List (Symbol × List Symbol × SExpr)
  formula : SExpr
  deriving BEq, Repr

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
  /-- Recorded add-literal duplicate drops seen so far in the clause item
      walk (`emit/dedup-drop`, item E): the spine's dedup-skip arm fires
      ONLY for a literal recorded here (read-off, not inference). -/
  dedupDrops : List SExpr := []
  /-- The current discharge leaf's recorded `:TAU-BASIS` slice (item I) —
      set by the discharge call sites from the verdict node; gates and
      widens `replayDischargeNode`'s rule-premise pass. -/
  tauBasis : Option SExpr := none
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
  /-- The bound CONDITIONAL hypotheses (the generic replayed statement's telescope):
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
      hypothesis stating its replayed statement (`mkRuleHypType`). Consumed by the
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
      stating its whole-formula replayed statement (`mkCongHypType`). Consumed by the
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
  useFiHyps : List (UseFiSpec × Expr) := []
  /-- FULL-defequiv hypotheses (`equivfull:<thm>`, the R-solidify lane):
      per equivalence theorem whose TRANSLATED Goal parses as the defequiv
      IF-conjunction, the spec and the bound whole-formula hypothesis.
      Consumed by the equivalence-rune own-position congruence
      (`equivOwnPosCongr`); discharged like `cong:` hyps. -/
  equivFullHyps : List (EquivFullSpec × Expr) := []
  /-- THEOREM-classed :TYPE-PRESCRIPTION hypotheses (`tpthm:<thm>`): per
      dependency theorem whose emitted `:CLASSES` names :TYPE-PRESCRIPTION,
      the spec and the bound whole-formula hypothesis. Consumed by
      `replayRecognizer`'s cited-rune fallback; discharged like `cong:`
      hyps. -/
  tpThmHyps : List (TpThmSpec × Expr) := []
  /-- Equivalence-REFLEXIVITY hypotheses (`equivrefl:<thm>`): per
      equivalence-shaped in-scope defthm (incl. INCLUDE-BOOK'd ones), the
      spec and the bound hypothesis `∀ env', EvTrue w env' (R x x)`.
      Include-book instances stay KEPT conditions (D6-honest). -/
  equivReflHyps : List (EquivReflSpec × Expr) := []
  /-- The clause's emitted `(:FC-DERIVATIONS …)` records (Phase-6
      consumer, final-closeout item C): each derivation is the raw
      plist `(:RUNE r :CONCL c :TRIGGER t :SUBST σ :FC-ROUND n
      :PARENTS p :SUPPORTS s)` — the forward-chaining provenance that
      put a fact on ACL2's type-alist. Consulted by the marker-relief
      arm when a marker's own `:TA-RUNES` are empty (the cumulative
      set adds nothing at some sites); the record anchors the relief
      to the EMITTED instance (BUG-023 discipline). -/
  fcDerivs : List SExpr := []
  ih : Option Expr := none

def ReplayCtx.empty : ReplayCtx := {}

/-- Read one field of an emitted FC-derivation plist (`:RUNE`,
    `:CONCL`, `:TRIGGER`, …). `none` if the key is absent or the
    plist shape is broken (callers hard-fail on their required
    fields — never a silent default). -/
partial def fcDerivField? (deriv : SExpr) (key : String) : Option SExpr :=
  match deriv with
  | .cons (.atom (.keyword k)) (.cons v rest) =>
    if k == key then some v else fcDerivField? rest key
  | _ => none

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

/-- View `(equal X X)` as `X`. -/
def asEqualSelf : SExpr → Option SExpr
  | .cons (.atom (.symbol s)) (.cons x (.cons x' .nil)) =>
    if s.name == "EQUAL" && x == x' then some x else none
  | _ => none

def runeOf : ProofNode → Rune | .node r _ _ _ _ => r
def nodeLhsRhs : ProofNode → SExpr × SExpr | .node _ lhs rhs _ _ => (lhs, rhs)
def nodePath : ProofNode → List PathFrame | .node _ _ _ _ p => p.path
def nodeOrigin : ProofNode → String | .node _ _ _ _ p => p.origin

/-- The recorded tau-database slice on a `preprocess/tau` discharge node
    (`:TAU-BASIS`, fork-batch item I). -/
def nodeTauBasis : ProofNode → Option SExpr | .node _ _ _ _ p => p.tauBasis

/-- Is this literal item an IDENTITY display? Its result is the literal
    unchanged and its nodes are at most an equal-descent PROBE (item A +
    the restructure arc): identity decision records, window-tagged
    scratch (synthesized redexes only), and provenance-gated nested
    verdict nodes — `result == literal` pins the net effect. Replaces
    the bare `lp.nodes.isEmpty` at the walkers' identity guards. -/
def identityLiteralItem (lp : LiteralProof) : Bool :=
  lp.result == lp.literal && lp.nodes.all fun n =>
    ((nodeOrigin n == "equal/cars-decision" ||
      nodeOrigin n == "equal/cdrs-decision") &&
     (nodeLhsRhs n).1 == (nodeLhsRhs n).2)
    -- (`innerKindOf` is defined below — read the provenance directly)
    || (match n with
        | .node _ _ _ _ p =>
          p.innerKind == "equal-cars" || p.innerKind == "equal-cdrs")
    -- a NESTED verdict node / resolved record inside the probe
    -- (*1/4.1.3's 9-step shape). PROVENANCE-GATED (restructure audit,
    -- both reviewers): verdict-class origins only — shape alone would
    -- accept a real root-level refutation.
    || (match n with
        | .node _ l r _ p =>
          (p.origin == "equal/self" || p.origin == "equal/type-alist-nil"
           || p.origin == "equal/cars-decision"
           || p.origin == "equal/cdrs-decision")
          && (match l with
              | .cons (.atom (.symbol eqS)) (.cons _ (.cons _ .nil)) =>
                eqS.name == "EQUAL"
              | _ => false)
          && (r == l ||
              r == .cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil) ||
              r == .cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.nil .nil)))
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
  -- parametric route (Phase 2): the bound hypothesis, when present
  if let some h := cfg.noShadowHyps.find? (fun (t, _) => t == s) then
    return h.2
  unless cfg.noShadowHyps.isEmpty do
    throwError "proveNoShadow (parametric): no-shadow demand on {s.name}, \
      which is outside the bound builtin hypothesis set"
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
    -- defFact : worldExpr.defs.get? fn = some (formals, body) — the
    -- bound hypothesis on a parametric replay, kernel decision on a
    -- concrete one
    let defFact ← match cfg.defFactHyps.find? (fun (t, _) => t == fn) with
      | some h => pure h.2
      | none =>
        -- parametric mode + no pin = a definition-unfold demand on a SIG fn:
        -- the witness-dereference guard (R6 design item 5) — a
        -- post-encapsulate tree must never open a witness body
        unless cfg.defFactHyps.isEmpty do
          throwError "deriveDefInfo (parametric): unfold demand on unpinned \
            fn {fn.name} — witness dereference (R6 item 5)"
        let someE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[formalsE, bodyE]]
        proveByDecide (← mkEq (← mkDefsGet cfg fn) someE) s!"def {fn.name}"
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
    let defFact ← match cfg.defFactHyps.find? (fun (t, _) => t == fn) with
      | some h => pure h.2
      | none => do
        unless cfg.defFactHyps.isEmpty do
          throwError "deriveDefInfoN (parametric): unfold demand on unpinned \
            fn {fn.name} — witness dereference (R6 item 5)"
        proveByDecide (← mkEq (← mkDefsGet cfg fn) someE) s!"def {fn.name}"
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

/-- The convergence statement `∃ N, ∀ f ≥ N, evalOpt f worldExpr envExpr t = some v`. -/
def mkConvStmt (cfg : ReplayConfig) (t v : SExpr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
      let ge ← mkAppM ``GE.ge #[fV, nV]
      let app := mkApp4 (mkConst ``evalOpt) fV cfg.worldExpr cfg.envExpr (reflectSExpr t)
      let eq ← mkEq app (← mkAppM ``Option.some #[reflectSExpr v])
      mkForallFVars #[fV] (← mkArrow ge eq)
    mkAppM ``Exists #[← mkLambdaFVars #[nV] body]

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
  -- PARAMETRIC route (Phase 2 item c): over an abstract `worldExpr` the
  -- reduction check below cannot run — derive the convergence
  -- COMPOSITIONALLY instead (`dpValProof`: quote/IF/registered-builtin
  -- steps, whose only world dependence is the no-shadow hypotheses), then
  -- pin it to the recorded value's statement (defeq for a ground term —
  -- the dp value form and the recorded constant are both closed).
  unless cfg.noShadowHyps.isEmpty do
    let p ← dpValProof cfg cfg.envExpr [] [] (fun _ => none) lhs
    let target ← mkConvStmt cfg lhs v
    unless ← isDefEq (← inferType p) target do
      throwError "executable-counterpart (parametric): the compositional \
        convergence proof for {repr lhs} does not state the recorded value \
        {repr v} (dp value form/recorded constant mismatch)"
    return ← mkExpectedTypeHint p target
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

end ACL2.Replay.Driver
