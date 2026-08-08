/-
  Driver/NodeCore/Compose — positional slice of the former NodeCore
  monolith (Phase 2 re-slice, 2026-08-08: Ctx regrew past its baseline
  with the parametric-replay routes, so its tail — from the shared
  composition helpers section — moved here MOVE-ONLY; the boundaries
  remain the file's own def-before-use order, so the import chain IS
  the dependency order).
-/
import ACL2Lean.Replay.Driver.NodeCore.Ctx

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

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
