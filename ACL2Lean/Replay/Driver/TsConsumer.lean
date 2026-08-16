/-
  Driver/TsConsumer — the TP prover's EMITTED-DATA layer: the corollary
  CLASS recognizer, the value-closure / class-implication registries, the
  emitted-leaf admissibility rule, and the D-A TYPE-SET CONSUMER (T1+2
  sprint phase 1, 2026-08-14).

  Split out of Driver/Provers when the D-A consumer landed (the module-size
  norm). The division is the natural one: THIS module is what ACL2's
  emission licenses and what our value model contributes for it; Provers
  is the WALKERS that consume it.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- The EMITTED type-prescription corollary's CLASS — the shape of the
    value predicate `P` the TP prover builds from it. A return-path
    PRIMITIVE can only be admitted for a recognized class, because the
    Lean-side content of such a step is exactly that class's value-CLOSURE
    lemma (`tpClosure2`); an unrecognized corollary keeps the honest
    frontier. -/
inductive TpCorClass where
  /-- `(IF (INTEGERP (f …)) (NOT (< (f …) '0)) 'NIL)` — ACL2's
      `*ts-non-negative-integer*` (the emitted `:BASICTS 7`). -/
  | nonNegInt
  /-- `(CONSP (f …))` — ACL2's `*ts-cons*` (the emitted `:BASICTS 3072`). -/
  | consp
  /-- `(TRUE-LISTP (f …))` — ACL2's `*ts-true-list*` (`:BASICTS 1152`). -/
  | trueListp
  /-- `(IF (CONSP (f …)) 'T (EQUAL (f …) 'NIL))` — ACL2's
      `*ts-cons*` ∪ `*ts-nil*` (the emitted `:BASICTS 3200`), the
      "a list, possibly empty" prescription of a list-returning
      recursion (TP-replay arc increment 3). -/
  | conspOrNil
  /-- `(IF (CONSP (f …)) 'T (EQUAL (f …) <formal>))` — the ARGS-VALUED
      class (TP-replay arc increment 5): ACL2's prescription for
      `BINARY-APPEND`/`APP`, whose else-disjunct names a FORMAL, so the
      lifted predicate is indexed by that argument's VALUE
      (`mkTpHypTypeAv`'s hypothesis shape). The emitted `:BASICTS` is
      `*ts-cons*` (3072) — the corollary's TYPE-SET part; the equality
      disjunct is what covers the residue leaf (verdict `-1`), and it is
      carried by `tpArgLeafFact`, never by a mask. Which formal it is
      comes from `tpCorArgVar?`, off the emitted corollary. -/
  | conspOrArg
  deriving BEq, Repr, Inhabited

/-- ACL2's basic type-set MASK the class covers (`acl2/type-set-a.lisp`'s
    `def-basic-type-sets` bit order: 2^0 `*ts-zero*`, 2^1 `*ts-one*`, 2^2
    `*ts-integer>1*`, 2^3 positive-ratio, 2^4 negative-integer, 2^5
    negative-ratio, 2^6 complex-rational, 2^7 `*ts-nil*`, 2^8 `*ts-t*`,
    2^9 non-t-non-nil-symbol, 2^10 `*ts-proper-cons*`, 2^11
    `*ts-improper-cons*`, 2^12 string, 2^13 character). A leaf whose
    EMITTED verdict has a bit outside the mask is not covered by the
    corollary — frontier. Each mask is the ACL2 constant the corollary's
    recognizer names: `*ts-non-negative-integer*` = 0|1|2 = 7,
    `*ts-cons*` = proper|improper = 1024|2048 = 3072, `*ts-true-list*` =
    nil|proper-cons = 128|1024 = 1152, and the consp-or-nil `IF` =
    `*ts-cons*`|`*ts-nil*` = 3072|128 = 3200. -/
def TpCorClass.tsMask : TpCorClass → Int
  | .nonNegInt => 7
  | .consp => 3072
  | .trueListp => 1152
  | .conspOrNil => 3200
  | .conspOrArg => 3072

/-- Does the class's lifted predicate mention an ARGUMENT value (the
    args-valued corollaries — `mkTpHypTypeAv`'s shape)? Such a class's
    closure/leaf facts take that value as their leading parameter, and its
    hypothesis shape binds the argument values alongside the
    application's. -/
def TpCorClass.argIndexed : TpCorClass → Bool
  | .conspOrArg => true
  | _ => false

/-- Is the emitted leaf verdict `ts` inside the class's type-set `mask`?
    A NEGATIVE `ts` is a complement type-set (ACL2's `-1` = every type) and
    is never inside a finite mask. -/
def tsSubsumed (ts mask : Int) : Bool :=
  0 ≤ ts && (Nat.land ts.toNat mask.toNat == ts.toNat)

/-- The RESIDUE ARGUMENT of an args-valued corollary (TP-replay arc
    increment 5): the bare variable `Y` in
    `(IF (CONSP (f …)) 'T (EQUAL (f …) Y))`. The single matcher for that
    shape — `tpCorClass?` recognizes the class through it, and the walk
    reads the variable through it, so the two can never disagree. A
    QUOTED else-argument (`'NIL`) does not match here: it is the
    value-only `.conspOrNil` class. -/
def tpCorArgVar? (appPat cor : SExpr) : Option Symbol :=
  let app1 (f : String) (a : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a .nil)
  match cor with
  | .cons (.atom (.symbol ifS))
      (.cons c (.cons th (.cons (.cons (.atom (.symbol eqS))
        (.cons l (.cons (.atom (.symbol v)) .nil))) .nil))) =>
    if ifS.name == "IF" && eqS.name == "EQUAL" && c == app1 "CONSP" appPat
        && th == app1 "QUOTE" SExpr.t && l == appPat then some v
    else none
  | _ => none

/-- Recognize the EMITTED corollary's class. `appPat` is the fn's own
    application `(f formal…)` — the corollary's only non-constant part
    (except the args-valued class's residue formal, `tpCorArgVar?`).
    Exact-shape match: a corollary ACL2 emits in any other shape is
    unrecognized (frontier), never approximated. -/
def tpCorClass? (appPat cor : SExpr) : Option TpCorClass :=
  let app1 (f : String) (a : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a .nil)
  let app2 (f : String) (a b : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a (.cons b .nil))
  let quo (v : SExpr) : SExpr := app1 "QUOTE" v
  let ifE (c th e : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons c (.cons th (.cons e .nil)))
  if cor == ifE (app1 "INTEGERP" appPat)
      (app1 "NOT" (app2 "<" appPat (quo (.atom (.number (.int 0))))))
      (quo .nil) then some .nonNegInt
  else if cor == app1 "CONSP" appPat then some .consp
  else if cor == app1 "TRUE-LISTP" appPat then some .trueListp
  else if cor == ifE (app1 "CONSP" appPat) (quo SExpr.t)
      (app2 "EQUAL" appPat (quo .nil)) then some .conspOrNil
  else if (tpCorArgVar? appPat cor).isSome then some .conspOrArg
  else none

/-- Which ARGUMENTS of a registered return-path primitive must themselves
    satisfy the corollary predicate (TP-replay arc increment 2,
    2026-08-13). The profile is a property of the (class, primitive) PAIR,
    not of any function: `CONSP`×`CONS` constrains NEITHER argument (any
    cons is a cons), `TRUE-LISTP`×`CONS` constrains the TAIL only (the head
    is arbitrary), `NON-NEGATIVE-INTEGER`×`BINARY-+` constrains BOTH.
    Unconstrained positions still have to CONVERGE — they carry
    `TpArgAny`, discharged by the plain walk. -/
inductive TpArgProfile where
  /-- neither argument constrained -/
  | neither
  /-- the second argument only (the constructor's tail) -/
  | sndOnly
  /-- both arguments -/
  | both
  deriving BEq, Repr, Inhabited

/-- Is the FIRST argument constrained by the corollary predicate? -/
def TpArgProfile.fstConstrained : TpArgProfile → Bool
  | .both => true
  | _ => false

/-- Is the SECOND argument constrained by the corollary predicate? -/
def TpArgProfile.sndConstrained : TpArgProfile → Bool
  | .neither => false
  | _ => true

/-- Value-CLOSURE registry, (corollary class, 2-ary primitive) ↦ the
    argument-obligation PROFILE plus the Lean fact
    `∀ u v, Pa u → Pb v → P (g u v)` for that class's predicate (`Pa`/`Pb`
    being `P` at the profile's constrained positions and `TpArgAny`
    elsewhere). The driver RECOMPUTES the obligation from its own `P` and
    the profile, then type-hints the registered constant against it, so a
    drifted lift OR a mis-registered profile fails closed. -/
def tpClosure2 : List ((TpCorClass × String) × TpArgProfile × Name) :=
  [((.nonNegInt, "BINARY-+"), .both, ``ACL2.Replay.nonNegIntCor_closed_plus),
   ((.consp, "CONS"), .neither, ``ACL2.Replay.conspCor_closed_cons),
   ((.trueListp, "CONS"), .sndOnly,
    ``ACL2.Replay.trueListpCor_closed_cons),
   ((.conspOrNil, "CONS"), .neither,
    ``ACL2.Replay.conspOrNilCor_closed_cons),
   ((.conspOrArg, "CONS"), .neither,
    ``ACL2.Replay.conspOrArgCor_closed_cons)]

/-- RESIDUE-LEAF registry (TP-replay arc increment 5, 2026-08-13): for an
    ARG-INDEXED class, the Lean fact `∀ y, P y` at the residue argument's
    own value — the `Y` return leaf of `BINARY-APPEND`/`APP`, which the
    corollary covers by its EQUALITY disjunct (ACL2 emits that leaf with
    the unknown verdict `-1`, so no type-set mask applies or is used).
    The driver recomputes `P` at the bound argument value and type-hints
    the registered constant against it. -/
def tpArgLeafFact : List (TpCorClass × Name) :=
  [(.conspOrArg, ``ACL2.Replay.conspOrArgCor_at_arg)]

/-- CLASS-IMPLICATION registry (TP-replay arc increment 3, 2026-08-13):
    (callee's corollary class, position's corollary class) ↦ the Lean
    fact `∀ v, P_from v → P_to v`. A CALLEE-TP return-path step whose
    callee's emitted corollary is in the SAME class as the caller's needs
    nothing here (the predicates coincide); a callee in a STRICTLY
    STRONGER class needs exactly one such fact — e.g. `SORTFN1`'s
    consp-or-nil prescription is supplied at its `SORTFN1-INSERT` leaf by
    that callee's bare `CONSP` prescription. Both corollaries are
    EMITTED; the entry states only that our value model agrees the one
    implies the other. The driver RECOMPUTES the obligation from its own
    `P` and the callee's, type-hints the registered constant against it,
    and separately checks the classes' emitted type-set MASKS are
    contained the same way — a drifted lift or a backwards entry fails
    closed. -/
def tpClassImp : List ((TpCorClass × TpCorClass) × Name) :=
  [((.consp, .conspOrNil), ``ACL2.Replay.conspOrNilCor_of_conspCor)]

/-- CLASS-IMPLICATION registry, ARGS-VALUED callee form (TP-replay arc
    increment 5, 2026-08-13): (callee's arg-indexed class, position's
    class) ↦ the Lean fact `∀ y v, P_to y → P_from[y] v → P_to v`. The
    extra premise is the position's OWN predicate at the callee's residue
    ARGUMENT value — the driver proves it by walking that argument term
    with the same walker (never assumed), so the entry adds no type
    content beyond "our value model agrees". Mask containment is
    cross-checked exactly as for `tpClassImp`. NOTE the asymmetry with
    `tpClassImp`: there is NO identity shortcut here even when the two
    classes coincide, because an arg-indexed callee's predicate is
    indexed by the CALLEE's argument values, not the caller's — such a
    position needs its own registered entry (frontier until one exists). -/
def tpClassImpAv : List ((TpCorClass × TpCorClass) × Name) :=
  [((.conspOrArg, .conspOrNil),
    ``ACL2.Replay.conspOrNilCor_of_conspOrArgCor)]

/-! ### CONDITIONAL stored type-prescription rules (T1+2 sprint P5b)

The event's `:COROLLARY`/`:LEAVES` report ONE stored rule — the
definitional one. ACL2 keeps others, and the strong facts live exactly
there: `BINARY-APPEND`'s definitional rule is the weak
`(IF (CONSP …) 'T (EQUAL … Y))`, while the boot-strap `TRUE-LISTP-APPEND`
— `(IMPLIES (TRUE-LISTP B) (TRUE-LISTP (BINARY-APPEND A B)))` — is a
SECOND stored rule of the same fn, emitted in `:ALL-TPS` with its own
hypotheses, its own `basicTs`, its own pattern `term`, and its own
context-refined `leaves` (computed under those hypotheses).

Consuming one is not trusting it: the rule's CONCLUSION is re-proved from
the fn's body by the same walker, under its hypotheses, and each
hypothesis is discharged at the call site by the same walker. What the
emission licenses is ADMISSIBILITY — which rule may be attempted, and
which leaves the walk may admit under it. -/

/-- A stored `:ALL-TPS` rule, renamed into the fn's FORMAL variable space
    and split into the parts the prover consumes. Built only by
    `tpStoredRuleFor?`, which fail-closes on every shape it cannot
    recompute. -/
structure TpStoredRule where
  /-- The rule's rune name (`TRUE-LISTP-APPEND`) — diagnostics only. -/
  runeName : String
  /-- The rule's HYPOTHESES, in the fn's formal variable space. -/
  hyps : List SExpr
  /-- The rule's CONCLUSION (the corollary's `IMPLIES` consequent, or the
      corollary itself when there are no hypotheses), formal space. -/
  concl : SExpr
  /-- The recognized class of `concl` against the fn's own application
      pattern. -/
  cls : TpCorClass
  /-- The rule's OWN context-refined body leaves, formal space — what the
      walk's return-path admissibility is checked against under THIS rule
      (the event's unconditional leaves do not apply). -/
  leaves : List TpLeaf
  /-- Per hypothesis, in `hyps` order: the formal it constrains and the
      corollary CLASS its shape is. A hypothesis in any other shape makes
      the rule inadmissible. -/
  hypCls : List (Symbol × TpCorClass)
  deriving Repr, Inhabited

/-- Rename every `SExpr` field of an emitted leaf through `σ`. -/
private def TpLeaf.rename (σ : SExpr → SExpr) (l : TpLeaf) : TpLeaf :=
  { l with term := σ l.term, tests := l.tests.map σ,
           typeAlist := l.typeAlist.map (fun (t, n) => (σ t, n)),
           subterms := l.subterms.map (fun (t, n) => (σ t, n)) }

/-- ACL2's `and`-antecedent spine, `(IF A rest 'NIL)` right-nested → the
    conjunct list; anything else is a single hypothesis. (Same shape rule
    as the rule-hypothesis flattener; kept here because the stored-rule
    reader must run before the provers module.) -/
private partial def tpFlattenAnd : SExpr → List SExpr
  | t@(.cons (.atom (.symbol ifS)) (.cons a (.cons rest (.cons e .nil)))) =>
    if ifS.name == "IF" && e == quoteNil then a :: tpFlattenAnd rest else [t]
  | t => [t]

/-- Select a stored `:ALL-TPS` rule of `fn` whose CONCLUSION is in the
    class `want` — the CALLEE-TP arm's route when the fn's definitional
    corollary does not reach the position's class.

    Everything is recompute-checked against the emitted entry, and every
    check fails CLOSED (returns `none`, so the caller keeps its honest
    frontier):

    * the rule's pattern `term` must be `(fn v₁ … vₙ)` at distinct
      VARIABLES, and renaming those to the fn's formals must reproduce the
      fn's own application pattern — that is what puts hyps/corollary/
      leaves in one variable space (the emitter's J-RT2b invariant,
      re-derived here rather than assumed);
    * the corollary must RECONSTRUCT from the emitted `hyps` and the
      conclusion (`(IMPLIES <and-spine> concl)`, or bare when there are
      none) — a corollary that does not is not being read correctly;
    * every emitted leaf verdict must lie inside the rule's OWN `basicTs`,
      and that `basicTs` inside the wanted class's mask. The emitter's
      honest caveat is that a rule proved by a REAL THEOREM need not have
      its leaves inside its `basicTs` — such a rule is not re-provable from
      the body by this walker, and this is where it is refused;
    * every hypothesis must be a recognized CLASS shape over a single
      formal (`(TRUE-LISTP B)`), which is what lets the call site discharge
      it with the same walker. -/
def tpStoredRuleFor? (allTps : List (String × List TpRuleSpec))
    (fn : Symbol) (formals : List Symbol) (appPat : SExpr)
    (want : TpCorClass) : Option TpStoredRule := do
  let rules ← allTps.lookup fn.name
  rules.findSome? fun r => do
    -- the rule's pattern term: `(fn v₁ … vₙ)` at distinct variables
    let .cons (.atom (.symbol rf)) argSpine := r.term | none
    guard (rf == fn)
    let args ← argSpine.toList?
    let vars ← args.mapM fun a => match a with
      | .atom (.symbol s) => some s
      | _ => none
    guard (vars.length == formals.length)
    guard (vars.eraseDups.length == vars.length)
    let σ : SExpr → SExpr :=
      substTerm vars (formals.map (SExpr.atom ∘ Atom.symbol))
    -- the renaming must reproduce the fn's OWN application pattern
    guard (σ r.term == appPat)
    let hyps := r.hyps.map σ
    -- RECONSTRUCT the corollary from hyps + conclusion
    let concl ←
      match hyps with
      | [] => some (σ r.corollary)
      | _ =>
        match σ r.corollary with
        | .cons (.atom (.symbol impS)) (.cons ante (.cons c .nil)) =>
          if impS.name == "IMPLIES" && tpFlattenAnd ante == hyps then some c
          else none
        | _ => none
    let cls ← tpCorClass? appPat concl
    guard (cls == want)
    -- ADMISSIBILITY off the emitted numbers (see the docstring)
    guard (tsSubsumed r.basicTs cls.tsMask)
    let leaves := r.leaves.map (TpLeaf.rename σ)
    guard (leaves.all (fun l => tsSubsumed l.ts r.basicTs))
    -- every hypothesis a recognized class shape over ONE formal
    let hypCls ← hyps.mapM fun h => do
      let .cons _ (.cons (.atom (.symbol v)) .nil) := h | none
      guard (formals.contains v)
      let hc ← tpCorClass? (.atom (.symbol v)) h
      some (v, hc)
    some { runeName := r.rune.name, hyps, concl, cls, leaves, hypCls }

/-- A stored-rule HYPOTHESIS as a value predicate: `fun v => <the
    hypothesis lifted, its constrained formal ↦ v> = t`. The ONE builder —
    `proveTp` uses it for the carrier's `H` and the callee arm for the
    obligation it discharges at the argument's value, so the two cannot
    state different things. A hypothesis mentioning anything but its own
    formal is a frontier (`tpStoredRuleFor?` already refuses those; this
    is the fail-closed twin). -/
def tpHypPred (h : SExpr) (hv : Symbol) : MetaM Expr :=
  withLocalDeclD `v (mkConst ``SExpr) fun vV => do
    let lifted ← dpValExpr [(.atom (.symbol hv), vV)]
      (fun s => throwFrontier m!"proveTp: stored-rule hypothesis {repr h} \
          mentions {s.name} outside its constrained formal (frontier)") h
    mkLambdaFVars #[vV] (← mkEq lifted (mkConst ``SExpr.t))

/-- The hypotheses of a conditional stored rule, IN FORCE inside the body
    walk that proves it (T1+2 sprint P5b). Three consumers, all in the
    walk: a return-path leaf that IS a constrained formal is closed by its
    `facts` entry; a SELF-CALL must re-establish `hExpr` at the call's
    argument values (checked twice — the hypothesis terms must be
    invariant under the call's own substitution, and the ambient proof
    must type-hint against the instantiated predicate); and nothing else
    may use them. -/
structure TpHypCarrier where
  /-- The rule's hypothesis TERMS, in the fn's formal variable space. -/
  hyps : List SExpr
  /-- Per hypothesis, in `hyps` order: the constrained formal, its
      corollary class, and the proof of that class's predicate at the
      formal's bound VALUE. -/
  facts : List (Symbol × TpCorClass × Expr)
  /-- The hypothesis CONJUNCTION as a λ over the argument values (`H` of
      `tp_2_rec_hyp_mu`), and its proof at the walk's own binders. -/
  hExpr : Expr
  hProof : Expr

/-- The per-function EMITTED type-prescription data the TP walk consumes on
    its return paths (TP-replay arc increment 1, 2026-08-12): the fn's
    name, ACL2's OWN `:LEAVES` enumeration (return-path leaf term + the
    type-set verdict ACL2 computed for it), and the corollary's recognized
    class. Nothing here is derived Lean-side. -/
structure TpKit where
  fnName : String
  leaves : List TpLeaf
  cls : Option TpCorClass
  /-- The development's admission justifications, as the CALLER passed
      them to `proveTp` — threaded so the CALLEE-TP arm can invoke the
      prover on a callee with exactly the same data (increment 3). -/
  justs : List (String × Justification) := []
  /-- The EMITTED `:TYPE-PRESCRIPTION` corollaries (fn ↦ corollary) the
      caller offered as `tp:` hypotheses — the SAME table, so the
      CALLEE-TP arm can only consume a corollary the harness itself
      offered. Empty (the default) makes that arm a frontier. -/
  cors : List (String × SExpr) := []
  /-- The CALLEE-TP recursion stack, innermost last: the fns whose type
      prescriptions are currently being proved. A call to a fn already on
      the stack is a CYCLE (mutual/self TP dependence) and is a tagged
      frontier — the prover never loops and never assumes. -/
  seen : List String := []
  /-- The RESIDUE ARGUMENT of an args-valued corollary (increment 5) —
      `tpCorArgVar?` of the fn's OWN emitted corollary. `none` for every
      value-only class, which makes the residue-leaf arm a frontier. -/
  argVar : Option Symbol := none
  /-- The STORED-RULE hypotheses in force for this walk (T1+2 sprint P5b);
      `none` for the ordinary unconditional walk. -/
  hyp : Option TpHypCarrier := none
  /-- The RECORDED-TERMINATION bundle of the fn being proved, when its
      admission waterfall was replayed (T1+2 sprint P5b). Present ⇒ the
      induction measure is the INTERPRETED count and a self-call whose
      MEASURED actual is opaque (`QSORT`'s `(FILTER 'GTE (CDR X) (CAR X))`)
      takes the recorded decrease route instead of the destructor walk. -/
  recTerm : Option RecTermInfo := none

/-- Does `t` occur in `u` (as `u` itself or as a subterm)? The CALLEE-TP
    arm's containment check against ACL2's emitted `:LEAVES`. -/
def sexprOccurs (t : SExpr) : SExpr → Bool
  | u@(.cons a d) => u == t || sexprOccurs t a || sexprOccurs t d
  | u => u == t

/-- ACL2'S OWN LEAF DATA — the admissibility check every return-path arm
    shares (increment 3's rule, generalized to the primitive arm in
    increment 5): a term that IS one of the fn's emitted `:LEAVES` must
    carry a verdict inside the class's type-set; a term that merely
    OCCURS INSIDE a leaf is a NESTED position, covered by the enclosing
    leaf's own check in the arm that admitted it (the args-valued callee
    step walks the residue ARGUMENT, e.g. `REV`'s `(CONS (CAR X) 'NIL)`
    inside its `(APP …)` leaf); a term in neither place is a frontier. -/
def tpEmittedLeafOk (kit : TpKit) (cls : TpCorClass) (t : SExpr) :
    MetaM Unit := do
  -- OCCURRENCE-CLOSED: the same leaf TERM can be emitted more than once,
  -- once per branch, and (since the R2 fork batch) with DIFFERENT
  -- context-refined verdicts. The walk does not carry the leaf's address,
  -- so admitting on the first hit could ride a verdict ACL2 computed for
  -- another occurrence: EVERY entry for the term must be inside the class.
  match kit.leaves.filter (fun l => l.term == t) with
  | [] =>
    unless kit.leaves.any (fun l => sexprOccurs t l.term) do
      throwFrontier m!"proveTp: {repr t} occurs in no emitted \
          :TYPE-PRESCRIPTION leaf of {kit.fnName} (frontier)"
  | hits =>
    for l in hits do
      unless tsSubsumed l.ts cls.tsMask do
        throwFrontier m!"proveTp: emitted leaf verdict {l.ts} of {repr t} \
            (under {repr l.tests}) is not inside the {repr cls} corollary \
            class's type-set {cls.tsMask} (frontier)"

/-! ### The D-A CONSUMER — ACL2's own type-set derivation, replayed
    (T1+2 sprint phase 1, 2026-08-14)

The R2 fork batch made ACL2's `type-set-rec` walk visible per leaf: the
CONTEXT-REFINED verdict, the GOVERNING TESTS (the leaf's address), the
derived TYPE-ALIST, and the per-occurrence SUBTERM VERDICTS. The arm
below discharges a return-path obligation from exactly that data plus the
proved ts-algebra (`Replay/Lemmas/TsAlgebra.lean`), instead of keeping the
`tp:` hypothesis.

The division of labour is the ratified one, one level deeper: ACL2's
emission says WHICH type-set a term has in a context (and the walk refuses
any term it did not emit one for); the Lean side contributes only proved
implications about the value model, and every mask it composes is
cross-checked against ACL2's own emitted entry. -/

/-- CLASS-BRIDGE registry: (corollary class) ↦ the ts-algebra fact
    `∀ (m : Int) (v), tsSubsumedM m <the class's mask> = true → InTs m v →
    P v`. The class's `tsMask` is BAKED INTO the registered lemma, and the
    driver builds the containment side-condition from `TpCorClass.tsMask`
    — so a lemma registered against a different mask fails to apply. -/
def tpClassFromTs : List (TpCorClass × Name) :=
  [(.nonNegInt, ``ACL2.Replay.nonNegIntCor_of_inTs)]

/-- The RETURN-PATH UNARY PRIMITIVE ts-algebra: primitive ↦ (the in-mask
    its fact demands of the argument — `none` when the fact is
    unconditional, the out-mask it establishes, the proved fact). This is
    ACL2's `type-set-primitive` mirrored one entry at a time; ACL2 stores
    no rule for these (the fork audit probed all 32 primitives), so its
    only statement about such an occurrence is the emitted verdict, and
    the implication is ours to prove.

    DEMAND-DRIVEN: an entry exists only where the corpus's emitted leaves
    actually need it (`UNARY--` on INTEGER-ABS's negative branch;
    `DENOMINATOR` in ACL2-COUNT's non-integer-rational leaf). An
    unregistered primitive is an honest frontier. -/
def tpTsUnary : List (String × Option Int × Int × Name) :=
  [("UNARY--", some 16, 6, ``ACL2.Replay.inTs_neg_of_negInt),
   ("DENOMINATOR", none, 6, ``ACL2.Replay.inTs_denominator),
   ("LEN", none, 7, ``ACL2.Replay.inTs_len)]

-- `tsQuotedZero` / `tsFactOf` MOVED to Driver/TsFacts (T1+2 sprint P3b):
-- the clause-context consumer `inTsFromCtx` needs the SAME masks and
-- proved facts, and it sits upstream of this module.

/-- `tsSubsumedM m m' = true`, by ground kernel decision on the closed
    masks. -/
private def tsSubsumedProof (m m' : Int) : MetaM Expr := do
  mkDecideProof (← mkEq (← mkAppM ``ACL2.Replay.tsSubsumedM
    #[Lean.toExpr m, Lean.toExpr m']) (mkConst ``Bool.true))

/-- Prove `InTs target <tv>` for the term `t` from the in-scope BRANCH
    FACTS — the Lean-side replay of what ACL2's `assume-true-false` did to
    reach the emitted type-alist entry `target`. One fact (weakened) or
    two (intersected); anything else is a frontier rather than a guess. -/
def tsFromFacts (facts : TotFacts) (t : SExpr) (tv : Expr)
    (target : Int) : MetaM Expr := do
  let cands := facts.filterMap fun (f, pos, hb, _) =>
    match tsFactOf f pos with
    | some (a, m, nm) => if a == t then some (m, nm, hb) else none
    | none => none
  let base (m : Int) (nm : Name) (hb : Expr) : MetaM Expr := do
    mkExpectedTypeHint (← mkAppM nm #[hb])
      (← mkAppM ``ACL2.Replay.InTs #[Lean.toExpr m, tv])
  for (m, nm, hb) in cands do
    if ACL2.Replay.tsSubsumedM m target then
      return ← mkAppM ``ACL2.Replay.inTs_weaken
        #[← tsSubsumedProof m target, ← base m nm hb]
  for (m1, nm1, hb1) in cands do
    for (m2, nm2, hb2) in cands do
      if ACL2.Replay.tsInter2Subsumed m1 m2 target then
        let hsub ← mkDecideProof (← mkEq
          (← mkAppM ``ACL2.Replay.tsInter2Subsumed
            #[Lean.toExpr m1, Lean.toExpr m2, Lean.toExpr target])
          (mkConst ``Bool.true))
        return ← mkAppM ``ACL2.Replay.inTs_inter2
          #[hsub, ← base m1 nm1 hb1, ← base m2 nm2 hb2]
  throwFrontier m!"proveTp: the in-scope branch facts do not establish \
      ACL2's emitted type-set {target} for {repr t} (frontier)"

/-- ACL2'S ADDRESSED LEAF for a return-path term (the GAP-1 payoff): among
    the fn's emitted `:LEAVES`, the one whose GOVERNING TESTS the in-scope
    branch facts establish — so two identical leaf terms in different
    branches are told apart and the type-alist consumed is the one ACL2
    derived HERE. Returns the leaf plus ACL2's verdict for `t` (the leaf's
    own verdict when `t` IS the leaf, else its emitted SUBTERM verdict —
    the GAP-2 payoff). -/
def tpAddressedLeaf (kit : TpKit) (facts : TotFacts)
    (t : SExpr) : Option (TpLeaf × Int) :=
  let fs := facts.map (fun (f, pos, _) => (f, pos))
  let ruled := kit.leaves.filter fun l =>
    l.tests.all (fun c => branchEstablishes fs c true)
  match ruled.find? (fun l => l.term == t) with
  | some l => some (l, l.ts)
  | none =>
    ruled.findSome? fun l => (List.lookup t l.subterms).map fun ts => (l, ts)

/-- THE TS-ALGEBRA RETURN-PATH ARM. `t` is a value-liftable return-path
    term ACL2 emitted a verdict for; the proof is assembled as

      emitted verdict ⊆ class mask                      (ADMISSIBILITY)
      → emitted type-alist entry proved from the branch  (`tsFromFacts`)
      → the primitive's ts-algebra fact                  (`tpTsUnary`)
      → composed mask ⊆ class mask → the class predicate (`tpClassFromTs`)

    Every mask is either ACL2's own (the type-alist / the verdict) or the
    registered fact's, and each step is recompute-checked by a type hint,
    so a drifted lift or a mis-registered mask fails closed. -/
def tpTsLeaf (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (kit : TpKit) (cls : TpCorClass) (P : Expr) (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  let some bridge := tpClassFromTs.lookup cls
    | throwFrontier m!"proveTp: the {repr cls} corollary class has no \
        ts-algebra bridge (frontier)"
  unless totLiftable t do
    throwFrontier m!"proveTp: ts-algebra return path {repr t} is not \
        value-liftable (frontier)"
  let some (leaf, verdict) := tpAddressedLeaf kit facts t
    | throwFrontier m!"proveTp: {repr t} is covered by no emitted \
        :TYPE-PRESCRIPTION leaf of {kit.fnName} whose governing tests the \
        branch establishes (frontier)"
  unless tsSubsumed verdict cls.tsMask do
    throwFrontier m!"proveTp: ACL2's emitted verdict {verdict} for \
        {repr t} (under {repr leaf.tests}) is not inside the {repr cls} \
        corollary class's type-set {cls.tsMask} (frontier)"
  let tv ← dpValExpr [] (dpValProof.dpVarVal envE varP) t
  let inTsTy (m : Int) : MetaM Expr :=
    mkAppM ``ACL2.Replay.InTs #[Lean.toExpr m, tv]
  let (mask, hIn) ← (do
    match t with
    | .atom (.symbol _) =>
      -- a return-path FORMAL: ACL2's own type-alist entry for it, proved
      -- from the branch facts
      let some mA := List.lookup t leaf.typeAlist
        | throwFrontier m!"proveTp: ACL2's emitted leaf type-alist carries \
            no entry for the return-path variable {repr t} (frontier)"
      pure (mA, ← tsFromFacts facts t tv mA)
    | .cons (.atom (.symbol g)) (.cons a .nil) =>
      let some (_, inMask?, outMask, fact) :=
          tpTsUnary.find? (fun (n, _, _, _) => n == g.name)
        | throwFrontier m!"proveTp: return-path unary {g.name} has no \
            ts-algebra fact (frontier)"
      let av ← dpValExpr [] (dpValProof.dpVarVal envE varP) a
      let e ← match inMask? with
        | none => mkAppM fact #[av]
        | some inMask =>
          -- ACL2's own entry for the argument must be inside what the
          -- registered fact demands — its verdict LICENSES the step
          let some mA := List.lookup a leaf.typeAlist
            | throwFrontier m!"proveTp: ACL2's emitted leaf type-alist \
                carries no entry for {repr a}, which the {g.name} \
                ts-algebra fact needs typed (frontier)"
          unless ACL2.Replay.tsSubsumedM mA inMask do
            throwFrontier m!"proveTp: ACL2's emitted type-set {mA} for \
                {repr a} is not inside the {inMask} the {g.name} \
                ts-algebra fact demands (frontier)"
          mkAppM fact #[← tsFromFacts facts a av inMask]
      pure (outMask, ← mkExpectedTypeHint e (← inTsTy outMask))
    | _ =>
      throwFrontier m!"proveTp: ts-algebra return path {repr t} unsupported \
          (frontier)")
  unless ACL2.Replay.tsSubsumedM mask cls.tsMask do
    throwFrontier m!"proveTp: the composed type-set {mask} for {repr t} is \
        not inside the {repr cls} corollary class's type-set {cls.tsMask} \
        (frontier)"
  let hP ← mkExpectedTypeHint
    (← mkAppM bridge
      #[Lean.toExpr mask, tv, ← tsSubsumedProof mask cls.tsMask, hIn])
    (mkApp P tv).headBeta
  let hconv ← dpValProof cfg envE [] [] varP t
  mkAppOptM ``convP_of_val
    #[cfg.worldExpr, envE, reflectSExpr t, P, tv, hP, hconv]


end ACL2.Replay.Driver
