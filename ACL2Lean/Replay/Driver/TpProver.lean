/-
  Driver/TpProver — THE TP PROVER, split out of Driver/Provers (T1+2
  sprint P5b, 2026-08-16). MOVE-ONLY, at the file's own seam: the
  predicate-carrying body walk (`tpWalk`), its call arms (`tpWalkCall` /
  `tpWalkCallee`), the argument-value pinner (`tpArgValues`) and
  `proveTp` itself. Everything else — `proveTotality`/`buildTotalEnv`,
  the D5 ground-zero rule dischargers and the D1 replayed registry —
  stays in Provers.

  The split is the module-size ratchet's doing (the conditional
  stored-rule route pushed the combined file past the 1500-line cap) and
  it lands on the seam the old module docstring already drew: Provers is
  TOTALITY from admission, this is the TYPE-PRESCRIPTION prover.
  `bindArgsVarProofs` stays upstream — it is the one piece BOTH provers
  share, which is exactly why it must not move with either.
-/
import ACL2Lean.Replay.Driver.Provers

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Pin every argument term of a return-path call to a VALUE plus its
    convergence proof, then run the continuation (TP-replay arc increment
    5, 2026-08-13). A liftable argument is pinned by the DP value lift; an
    OPAQUE one (a user-fn call, e.g. `REV`'s `(REV (CDR X))`) by
    ∃-elimination over the plain totality walk — the same device the
    self-call arm uses for its non-measured argument. Needed because the
    ARGS-VALUED hypothesis shape (`mkTpHypTypeAv`) is stated at the
    argument VALUES, so a callee step must supply them. -/
partial def tpArgValues (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (args : List SExpr) (acc : List (Expr × Expr))
    (k : List (Expr × Expr) → MetaM Expr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  match args with
  | [] => k acc.reverse
  | a :: rest =>
    if totLiftable a then
      let v ← dpValExpr [] (dpValProof.dpVarVal envE varP) a
      let p ← dpValProof cfg envE [] [] varP a
      tpArgValues cfg envE vals facts totalEnv rest ((v, p) :: acc) k
    else
      let hcEx ← totWalk cfg envE vals facts totalEnv none a
      let cont ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let convTy ← mkAppM ``ConvTo
          #[cfg.worldExpr, envE, reflectSExpr a, av]
        withLocalDeclD `hcv convTy fun hcv => do
          mkLambdaFVars #[av, hcv]
            (← tpArgValues cfg envE vals facts totalEnv rest
              ((av, hcv) :: acc) k)
      mkAppM ``exists_conv_elim #[hcEx, cont]

-- THE TP PROVER (mutual since increment 3): the body walk, its call
-- arms, the CALLEE-TP arm, and `proveTp` itself — the callee arm proves
-- the CALLEE's prescription by re-entering the prover.
mutual

/-- The TP body walk: a proof of `ConvToP w envE t P` — the body converges
    to a value SATISFYING the lifted-corollary predicate `P` (the TP prover,
    lifter sprint 2026-07-06; the `memb_body_bool` route, mechanized).
    Return-path arms: quote leaves (`P` by kernel decision), `if`-splits
    (liftable or OPAQUE tests — tests need only CONVERGENCE, from the plain
    walk over `totalEnv`), self-calls (the admission-licensed strong IH),
    2-ary registered PRIMITIVES over ACL2's own emitted leaves (`kit`), and
    CALLEE calls whose own emitted type prescription supplies the position
    (`tpWalkCallee`, increment 3). Every other body shape is a tagged
    frontier (D6: the `tp:` hypothesis stays). -/
partial def tpWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (kit : TpKit) (P : Expr) (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  match t with
  | .cons (.atom (.symbol qs)) (.cons qv .nil) =>
    if qs.name == "QUOTE" then
      -- leaf constant: the corollary holds of it by ground kernel decision
      let hP ← proveByDecide (mkApp P (reflectSExpr qv)).headBeta
        s!"tp corollary at leaf {repr qv}"
      return ← mkAppM ``convP_quote
        #[cfg.worldExpr, envE, reflectSExpr qv, P, hP]
    else
      -- RETURN-PATH UNARY PRIMITIVE (the D-A consumer, 2026-08-14):
      -- ACL2 stores no type-prescription for its primitives, so the only
      -- statement it makes about such an occurrence is the emitted
      -- verdict (leaf or SUBTERM) — `tpTsLeaf` consumes exactly that plus
      -- the emitted type-alist. An unregistered head falls through to the
      -- call arms, which keep the honest frontier.
      match kit.cls with
      | some cls =>
        if tpTsUnary.any (fun (n, _, _, _) => n == qs.name) then
          tpTsLeaf cfg envE vals facts kit cls P t
        else tpWalkCall cfg envE vals facts totalEnv self kit P t
      | none => tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      if totLiftable c then
        let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
        let hc ← dpValProof cfg envE [] [] varP c
        let toBoolVc ← mkAppM ``Logic.toBool #[vc]
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr := do
          withLocalDeclD `hb (← mkEq toBoolVc (mkConst bval)) fun hb => do
            let p ← tpWalk cfg envE vals ((c, pos, hb, none) :: facts)
              totalEnv self kit P branch
            mkLambdaFVars #[hb] p
        let ht ←
          if ← isDefEq vc (mkConst ``SExpr.nil) then
            -- VACUOUS truthy branch (`mkVacuousTruthyBranch`, shared with
            -- the totality walk): `(COMPLEX-RATIONALP _)` in ACL2-COUNT's
            -- own body is definitionally nil on the complex-free value
            -- space, so the branch hypothesis refutes itself. ACL2 emits a
            -- real verdict for that leaf — the vacuity is OURS (BUG-009's
            -- pinned domain restriction), and it fails CLOSED if complex
            -- values are ever modelled.
            mkVacuousTruthyBranch toBoolVc
              (← mkAppM ``ConvToP
                #[cfg.worldExpr, envE, reflectSExpr th, P])
          else mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, vc, P, hc, ht, he]
      else
        -- OPAQUE (user-fn) test: converge it by the PLAIN walk (the fn's
        -- own totality is in totalEnv — buildTpEnv runs after totality),
        -- split on the existential verdict
        let hcEx ← totWalk cfg envE vals facts totalEnv none c
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr :=
          withLocalDeclD `vc (mkConst ``SExpr) fun vc => do
            let convTy ← mkAppM ``ConvTo
              #[cfg.worldExpr, envE, reflectSExpr c, vc]
            withLocalDeclD `hcv convTy fun hcv => do
              let hbTy ← mkEq (← mkAppM ``Logic.toBool #[vc]) (mkConst bval)
              withLocalDeclD `hb hbTy fun hb => do
                let p ← tpWalk cfg envE vals
                  ((c, pos, hb, some (vc, hcv)) :: facts)
                  totalEnv self kit P branch
                mkLambdaFVars #[vc, hcv, hb] p
        let ht ← mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split_ex
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, P, hcEx, ht, he]
    else
      tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    -- RETURN-PATH PRIMITIVE (TP-replay arc increments 1–2, 2026-08-12): a
    -- 2-ary registered builtin ACL2 itself enumerated as a return-path
    -- LEAF of this fn's type prescription. ADMISSIBILITY IS ENTIRELY
    -- EMITTED — the term must be one of ACL2's `:LEAVES` and the type-set
    -- verdict ACL2 computed for it must lie inside the corollary class's
    -- type-set. The Lean side contributes only the class's value CLOSURE
    -- lemma and its ARG-OBLIGATION PROFILE; it never derives a type.
    -- Anything unregistered falls through to the call arms (self-call,
    -- else frontier).
    match dpBinary.lookup fs.name, kit.cls with
    | some (fn, cb), some cls =>
      let some (prof, closure) := tpClosure2.lookup (cls, fs.name)
        | throwFrontier m!"proveTp: return-path {fs.name} has no value-closure \
            lemma for the {repr cls} corollary class (frontier)"
      tpEmittedLeafOk kit cls t
      -- PER-ARGUMENT obligation, off the registered PROFILE: a constrained
      -- position carries `P` (the TP walk); an unconstrained one carries
      -- only `TpArgAny`, i.e. plain convergence by the totality walk — the
      -- Lean side never invents a type for it
      let argOf (constrained : Bool) (u : SExpr) : MetaM (Expr × Expr) := do
        if constrained then
          return (P, ← tpWalk cfg envE vals facts totalEnv self kit P u)
        else
          let hEx ← totWalk cfg envE vals facts totalEnv none u
          return (mkConst ``ACL2.Replay.TpArgAny, ← mkAppM ``convP_any #[hEx])
      let (pA, pa) ← argOf prof.fstConstrained a
      let (pB, pb) ← argOf prof.sndConstrained b
      let hNs ← proveNotSpecial fs
      let hNo ← proveNoShadow cfg fs
      -- the CLOSURE obligation, RECOMPUTED from the driver's own `P` and
      -- the profile's per-argument predicates — a registered lemma that
      -- does not state exactly this (wrong class, or a profile claiming
      -- more/less than the lemma proves) fails here
      let clTy ← withLocalDeclD `u (mkConst ``SExpr) fun u =>
        withLocalDeclD `v (mkConst ``SExpr) fun v => do
          let pg := (mkApp P (mkApp2 (mkConst fn) u v)).headBeta
          mkForallFVars #[u, v]
            (← mkArrow (mkApp pA u).headBeta
              (← mkArrow (mkApp pB v).headBeta pg))
      -- an ARG-INDEXED class's facts take the residue argument's VALUE as
      -- their leading parameter (increment 5); the type hint below is
      -- still the whole check
      let closureE ←
        if cls.argIndexed then
          let some (av, _) := kit.argVar.bind varP
            | throwFrontier m!"proveTp: the {repr cls} residue argument has \
                no bound value in {kit.fnName}'s walk (frontier)"
          pure (mkApp (mkConst closure) av)
        else pure (mkConst closure)
      let hcl ← mkExpectedTypeHint closureE clTy
      return ← mkAppM ``convP_builtin2
        #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a,
          reflectSExpr b, mkConst fn, P, pA, pB, hNs, hNo, mkConst cb,
          hcl, pa, pb]
    | _, _ => tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .atom (.symbol vsym) =>
    -- RESIDUE-ARGUMENT LEAF (TP-replay arc increment 5, 2026-08-13):
    -- `BINARY-APPEND`/`APP` return their second argument `Y` on the
    -- base path, and ACL2's own corollary covers exactly that leaf by
    -- its EQUALITY disjunct `(EQUAL (fn X Y) Y)` — which is why the
    -- emitted verdict there is the unknown `-1` and no mask applies.
    -- ADMISSIBILITY IS EMITTED: the variable must BE the corollary's
    -- residue argument (`tpCorArgVar?` of the fn's own corollary) and
    -- must be one of ACL2's enumerated `:LEAVES`. Any other return-path
    -- variable is a frontier.
    let some cls := kit.cls
      | throwFrontier m!"proveTp: return-path variable {vsym.name} under an \
          UNRECOGNIZED corollary class for {kit.fnName} (frontier)"
    -- STORED-RULE HYPOTHESIS LEAF (T1+2 sprint P5b): under a CONDITIONAL
    -- stored rule, a return-path leaf that IS a hypothesis-constrained
    -- formal is closed BY that hypothesis — `TRUE-LISTP-APPEND`'s
    -- `(NOT (CONSP A))` leaf is the bare `B`, and `(TRUE-LISTP B)` is
    -- exactly what the rule assumes, which is why ACL2's own leaf verdict
    -- there is 1152 under those hypotheses and *ts-unknown* without them.
    -- Admissibility is still ACL2's (the leaf must be one the RULE's own
    -- `:LEAVES` enumerates, verdict inside the class) and the fact is
    -- RECOMPUTED against the driver's own `P` at the bound value.
    if let some (_, _, hpf) := kit.hyp.bind (fun hc =>
        hc.facts.find? (fun (v, hcls, _) => v == vsym && hcls == cls)) then
      tpEmittedLeafOk kit cls t
      let some (av, hav) := varP vsym
        | throwFrontier m!"proveTp: hypothesis-constrained return-path \
            variable {vsym.name} has no bound value (frontier)"
      let hP ← mkExpectedTypeHint hpf (mkApp P av).headBeta
      return ← mkAppOptM ``convP_of_val
        #[cfg.worldExpr, envE, reflectSExpr t, P, av, hP, hav]
    -- NOT the args-valued residue argument: the variable is an ordinary
    -- return-path leaf, and ACL2's own type-alist for the ADDRESSED leaf
    -- says what it is on this branch (the D-A consumer, 2026-08-14) —
    -- INTEGER-ABS's `X` leaf under `(INTEGERP X) ∧ ¬(< X '0)`.
    unless kit.argVar == some vsym do
      return ← tpTsLeaf cfg envE vals facts kit cls P t
    let some leafFact := tpArgLeafFact.lookup cls
      | throwFrontier m!"proveTp: the {repr cls} corollary class has no \
          residue-leaf fact — a return-path variable {vsym.name} is not \
          covered by it (frontier)"
    unless kit.argVar == some vsym do
      throwFrontier m!"proveTp: return-path variable {vsym.name} is not \
          {kit.fnName}'s corollary residue argument (frontier)"
    unless kit.leaves.any (fun l => l.term == t) do
      throwFrontier m!"proveTp: {repr t} is not an emitted \
          :TYPE-PRESCRIPTION leaf of {kit.fnName} (frontier)"
    let some (av, hav) := varP vsym
      | throwFrontier m!"proveTp: residue argument {vsym.name} has no bound \
          value (frontier)"
    -- RECOMPUTED against the driver's own `P` at that value
    let hP ← mkExpectedTypeHint (mkApp (mkConst leafFact) av)
      (mkApp P av).headBeta
    -- every implicit given (the predicate is higher-order: inference from
    -- `hP`'s concrete type alone would mis-solve `P`/`v`)
    return ← mkAppOptM ``convP_of_val
      #[cfg.worldExpr, envE, reflectSExpr t, P, av, hP, hav]
  | _ => tpWalkCall cfg envE vals facts totalEnv self kit P t
/-- Call arms: the SELF-call via the strong IH; a call to ANOTHER
    function via that callee's own type prescription (`tpWalkCallee`);
    everything else a frontier. -/
partial def tpWalkCall (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (kit : TpKit) (P : Expr) (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  let .cons (.atom (.symbol fs)) argsSpine := t
    | throwFrontier m!"proveTp: body shape {repr t} unsupported (frontier)"
  let args := (argsSpine.toList?).getD []
  -- NOT the self-call: the only admissible route is the CALLEE's OWN
  -- emitted type prescription (increment 3). Reachable from a
  -- non-recursive body too — `self` is consulted only to recognize the
  -- self-call, never to license the callee route.
  let isSelfCall : Bool := match self with
    | some (selfName, _, _, _) => fs.name == selfName
    | none => false
  unless isSelfCall do
    return ← tpWalkCallee cfg envE vals facts totalEnv self kit P t fs args
  let some (selfName, measuredFormal, ih, just) := self
    | throwFrontier m!"proveTp: call to {fs.name} on the return path of a \
        non-recursive body (frontier)"
  unless fs.name == selfName do
    throwFrontier m!"proveTp: return-path call to {fs.name} (not the \
        self-call) unsupported (frontier)"
  match cfg.worldVal.defs.get? fs with
  | none => throwFrontier m!"proveTp: self {fs.name} not in world"
  | some (formals, body) =>
    unless args.length == formals.length do
      throwFrontier m!"proveTp: self-call arity mismatch {repr t}"
    let mIdx := formals.findIdx (· == measuredFormal)
    unless vals.any (fun (f, _, _) => f == measuredFormal) do
      throwFrontier m!"proveTp: measured formal has no bound value"
    let hNs ← proveNotSpecial fs
    let hDef ← totWalk.totDefFact cfg fs formals body
    -- THE IH's HYPOTHESIS PREMISE under a conditional stored rule (T1+2
    -- sprint P5b). The IH carries `H` at ITS argument values, so the
    -- self-call must RE-ESTABLISH it — that is what keeps a conditional
    -- rule honest instead of assumed. Two independent fail-closed checks:
    -- the rule's hypothesis TERMS must be invariant under THIS call's own
    -- substitution (`BINARY-APPEND`'s `(BINARY-APPEND (CDR X) Y)` passes
    -- `Y` through unchanged, so `(TRUE-LISTP Y)` is), and the ambient
    -- proof is then type-hinted against `H` at the call's argument values.
    -- `argVals` is in FORMAL order, matching the `tp_*_rec_hyp_mu` shape.
    let hypArgsAt (argVals : List Expr) : MetaM (Array Expr) := do
      match kit.hyp with
      | none => pure #[]
      | some hc =>
        for h in hc.hyps do
          unless substTerm formals args h == h do
            throwFrontier m!"proveTp: the self-call {repr t} does not \
                preserve the stored rule's hypothesis {repr h} (frontier)"
        pure #[← mkExpectedTypeHint hc.hProof
          (mkAppN hc.hExpr argVals.toArray).headBeta]
    -- THE OPAQUE MEASURED ACTUAL (T1+2 sprint P5b). `QSORT`'s self-call
    -- passes `(FILTER 'GTE (CDR X) (CAR X))`: a world-fn call the value
    -- lift cannot render and `chainLt` cannot walk. Both are answered by
    -- the SAME devices the totality prover already uses for this very
    -- defun — the argument is converged by the plain walk and its value
    -- ∃-ELIMINATED, and the decrease is read off QSORT's own REPLAYED
    -- admission waterfall (`recordedDecreaseAtCall`, shared with
    -- `totWalk`). 1-ary only, as on the totality side; without a recorded
    -- admission the old frontier stands.
    if !totLiftable args[mIdx]! then
      let some recInfo := kit.recTerm
        | throwFrontier m!"proveTp: self-call MEASURED argument not \
            liftable {repr t}, and no recorded admission replay to take \
            its decrease from (frontier)"
      let [f1] := formals
        | throwFrontier m!"proveTp: opaque measured self-call at arity \
            {formals.length} unsupported (frontier)"
      let [a1] := args
        | throwFrontier m!"proveTp: opaque measured self-call arity \
            mismatch {repr t} (frontier)"
      let hcEx ← totWalk cfg envE vals facts totalEnv none a1
      let kLam ← withLocalDeclD `vs (mkConst ``SExpr) fun vσ => do
        let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr a1) vσ
        withLocalDeclD `hcs convTy fun hconvσ => do
          let dec ← recordedDecreaseAtCall cfg envE vals facts
            (walkConv := fun u =>
              totWalk cfg envE vals facts totalEnv none u)
            recInfo measuredFormal a1 hconvσ
          let hbody ← mkAppM' ih (#[vσ, dec] ++ (← hypArgsAt [vσ]))
          let p ← mkAppM ``convP_defn_1
            #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1, vσ,
              reflectSymbol f1, reflectSExpr body, P, hNs, hDef, hconvσ,
              hbody]
          mkLambdaFVars #[vσ, hconvσ] p
      return ← mkAppM ``exists_conv_elim #[hcEx, kLam]
    let dkit : DecreaseKit := {
      cfg := cfg, envE := envE
      facts := facts.map (fun (f, pos, _) => (f, pos))
      valOf := fun u => dpValExpr [] (dpValProof.dpVarVal envE varP) u
      convOf := fun u => dpValProof cfg envE [] [] varP u
      conspTrueOf := fun b => do
        let conspTest : SExpr :=
          .cons (.atom (.symbol { name := "CONSP" })) (.cons b .nil)
        match facts.find? (fun (f, pos, _) => f == conspTest && pos) with
        | some (_, _, pf, _) => pure pf
        | none => throwFrontier m!"dischargeDecrease: decrease at \
            {repr b} needs an in-scope (consp {repr b}) fact (frontier)"
      endpFalseOf := fun b => do
        let endpTest : SExpr :=
          .cons (.atom (.symbol { name := "ENDP" })) (.cons b .nil)
        match facts.find? (fun (f, pos, _) => f == endpTest && !pos) with
        | some (_, _, pf, _) => pure pf
        | none => throwFrontier m!"dischargeDecrease: registry decrease \
            at {repr b} needs a refuted (endp {repr b}) fact (frontier)"
      -- the GENERAL accessor: the TP walk's facts carry each ruling test's
      -- `toBool = <sign>` proof, so an arbitrary ruler is a direct lookup
      factOf? := fun test pos => pure
        ((facts.find? (fun (f, p, _) => f == test && p == pos)).map
          (fun (_, _, pf, _) => pf)) }
    let dec ← dischargeDecrease just
      formals (formals.map (fun f => .atom (.symbol f)))
      formals args dkit
    match formals, args with
    | [f1], [a1] =>
      let av ← dpValExpr [] (dpValProof.dpVarVal envE varP) a1
      let ap ← dpValProof cfg envE [] [] varP a1
      let hbody ← mkAppM' ih (#[av, dec] ++ (← hypArgsAt [av]))
      return ← mkAppM ``convP_defn_1
        #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1, av,
          reflectSymbol f1, reflectSExpr body, P, hNs, hDef, ap, hbody]
    | [f1, f2], [a1, a2] =>
      let aM := args[mIdx]!
      let vM ← dpValExpr [] (dpValProof.dpVarVal envE varP) aM
      let pM ← dpValProof cfg envE [] [] varP aM
      let aO := args[1 - mIdx]!
      let assemble (vO pO : Expr) : MetaM Expr := do
        let (v1, v2, p1, p2) :=
          if mIdx == 0 then (vM, vO, pM, pO) else (vO, vM, pO, pM)
        let hbody ← mkAppM' ih (#[vM, dec, vO] ++ (← hypArgsAt [v1, v2]))
        mkAppM ``convP_defn_2
          #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1,
            reflectSExpr a2, v1, v2, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr body, P, hNs, hDef, p1, p2, hbody]
      if totLiftable aO then
        let vO ← dpValExpr [] (dpValProof.dpVarVal envE varP) aO
        let pO ← dpValProof cfg envE [] [] varP aO
        return ← assemble vO pO
      else
        -- opaque non-measured argument: plain-walk convergence, value
        -- bound by ∃-elimination (as in the totality prover)
        let hcEx ← totWalk cfg envE vals facts totalEnv none aO
        let k ← withLocalDeclD `vo (mkConst ``SExpr) fun vO => do
          let convTy ← mkAppM ``ConvTo
            #[cfg.worldExpr, envE, reflectSExpr aO, vO]
          withLocalDeclD `hcv convTy fun hcv => do
            mkLambdaFVars #[vO, hcv] (← assemble vO hcv)
        return ← mkAppM ``exists_conv_elim #[hcEx, k]
    | [f1, f2, f3], [a1, a2, a3] =>
      -- 3-ary self-call (TP-replay arc increment 4, 2026-08-13):
      -- `(ALL-REL FN (CDR X) E)` / `(ZIP3 (CDR X) (CDR Y) (CDR Z))`. The
      -- IH's argument order is (measured value, decrease, the remaining
      -- values in FORMAL order) — the `tp_3_rec`/`tp_3_rec_snd` shape,
      -- mirroring `proveTotality`'s 3-ary scaffold. A non-measured
      -- argument that is not liftable is a frontier here (the 2-ary
      -- opaque ∃-elimination has no 3-ary customer yet).
      let vals3 ← [a1, a2, a3].mapM fun a => do
        unless totLiftable a do
          throwFrontier m!"proveTp: 3-ary self-call argument {repr a} not \
              liftable (frontier)"
        let v ← dpValExpr [] (dpValProof.dpVarVal envE varP) a
        let p ← dpValProof cfg envE [] [] varP a
        pure (v, p)
      let vs := vals3.map (·.1)
      let ps := vals3.map (·.2)
      let others := (List.range 3).filter (· != mIdx)
      let hbody ← mkAppM' ih (#[vs[mIdx]!, dec] ++
        (others.map (vs[·]!)).toArray ++ (← hypArgsAt vs))
      return ← mkAppM ``convP_defn_3
        #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1,
          reflectSExpr a2, reflectSExpr a3, vs[0]!, vs[1]!, vs[2]!,
          reflectSymbol f1, reflectSymbol f2, reflectSymbol f3,
          reflectSExpr body, P, hNs, hDef, ps[0]!, ps[1]!, ps[2]!, hbody]
    | _, _ =>
      throwFrontier m!"proveTp: self-call arity {args.length} unsupported \
          (frontier)"

/-- The CALLEE-TP return-path arm (TP-replay arc increment 3, 2026-08-13):
    a return-path call to a function OTHER than the one whose prescription
    is being proved — `SORTFN1`'s `(SORTFN1-INSERT (CAR X) (SORTFN1 (CDR X)))`
    leaf, or the `BINARY-+` summand `(HOW-MANY-SMALLER (CAR X) (CDR X))`
    inside `BNEXT-SIZE`'s. ADMISSIBILITY IS ENTIRELY EMITTED:
    * the callee is a world fn with its OWN emitted `:TYPE-PRESCRIPTION`
      corollary (`kit.cors` — the caller's own offer table), in a
      recognized class;
    * that class either IS the position's class, or IMPLIES it by a
      registered `tpClassImp` fact whose direction is cross-checked
      against ACL2's own emitted type-set masks;
    * the call OCCURS in ACL2's `:LEAVES` enumeration for the fn being
      proved and — when the call IS one of those leaves — the verdict
      ACL2 computed for it lies inside the position class's type-set (a
      NESTED position is covered by the enclosing leaf's own check, in
      the arm that admitted it).
    The P-fact is not assumed: the prover runs RECURSIVELY on the callee
    (cycle-guarded by `kit.seen`, with the caller's own justification and
    totality data), so the callee's prescription is proved from ITS body
    and ITS emitted corollary by exactly this machinery. The call's
    CONVERGENCE is the plain totality walk.

    When the callee's DEFINITIONAL corollary reaches the position's class
    by neither route, the CONDITIONAL STORED RULES are tried
    (`tpStoredRuleFor?`, T1+2 sprint P5b) — see the block below.
    `self` is the CALLER's recursion data, threaded so a hypothesis
    obligation may mention the caller's own self-call; the pre-existing
    arms keep passing `none` there, exactly as before. -/
partial def tpWalkCallee (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (kit : TpKit) (P : Expr) (t : SExpr) (fs : Symbol) (args : List SExpr) :
    MetaM Expr := do
  let some cls := kit.cls
    | throwFrontier m!"proveTp: return-path call to {fs.name} under an \
        UNRECOGNIZED corollary class for {kit.fnName} (frontier)"
  let some (gFormals, _) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: return-path call to {fs.name}, which is not \
        a world fn (frontier)"
  unless args.length == gFormals.length do
    throwFrontier m!"proveTp: return-path call arity mismatch {repr t} \
        (frontier)"
  let some gcor := kit.cors.lookup fs.name
    | throwFrontier m!"proveTp: {fs.name} has no emitted \
        :TYPE-PRESCRIPTION corollary (frontier)"
  let gAppPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((gFormals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let some gcls := tpCorClass? gAppPat gcor
    | throwFrontier m!"proveTp: {fs.name}'s emitted corollary {repr gcor} is \
        not a recognized class (frontier)"
  -- ACL2'S OWN LEAF DATA (shared with the primitive arm)
  tpEmittedLeafOk kit cls t
  -- CYCLE GUARD: never re-enter a prescription already on the stack
  if kit.seen.contains fs.name then
    throwFrontier m!"proveTp: CYCLE in the callee-TP chain {kit.seen} → \
        {fs.name} (frontier)"
  -- the direction check both implication registries share: a registered
  -- entry whose direction ACL2's own emitted type-set masks contradict is
  -- refused
  let checkedImp (reg : List ((TpCorClass × TpCorClass) × Name)) :
      MetaM Name := do
    let some n := reg.lookup (gcls, cls)
      | throwFrontier m!"proveTp: {fs.name}'s corollary class {repr gcls} \
          neither matches nor implies the {repr cls} class \
          {kit.fnName}'s prescription needs (frontier)"
    unless tsSubsumed gcls.tsMask cls.tsMask do
      throwFrontier m!"proveTp: registered class implication {repr gcls} ⇒ \
          {repr cls} contradicts the emitted type-set masks \
          ({gcls.tsMask} not inside {cls.tsMask}) (frontier)"
    pure n
  let hEx ← totWalk cfg envE vals facts totalEnv none t
  -- THE CONDITIONAL STORED-RULE ROUTE (T1+2 sprint P5b). ACL2 stores more
  -- type-prescription rules for a fn than the event's `:COROLLARY` reports,
  -- and the strong ones are exactly the CONDITIONAL ones: `BINARY-APPEND`'s
  -- definitional rule is the weak `(IF (CONSP …) 'T (EQUAL … Y))`, while
  -- `(IMPLIES (TRUE-LISTP B) (TRUE-LISTP (BINARY-APPEND A B)))` — the class
  -- `QSORT`'s own prescription needs at its `BINARY-APPEND` leaf — is a
  -- second stored rule, emitted with its own hypotheses and its own
  -- context-refined leaves.
  --
  -- Tried ONLY when the definitional corollary reaches the position's class
  -- by neither route, so every pre-existing step keeps its exact route.
  -- Nothing is trusted: the rule's CONCLUSION is re-proved from the callee's
  -- body under its hypotheses (`proveTp` with the carrier), and each
  -- HYPOTHESIS is proved here at its argument's value by the same walker.
  let defnReaches : Bool :=
    gcls == cls ||
    (if gcls.argIndexed then (tpClassImpAv.lookup (gcls, cls)).isSome
     else (tpClassImp.lookup (gcls, cls)).isSome)
  if !defnReaches then
    if let some sr := tpStoredRuleFor? cfg.tpAllTps fs gFormals gAppPat cls then
      let gTp ← proveTp cfg totalEnv kit.justs fs.name sr.concl
        (cors := kit.cors) (seen := kit.seen) (storedRule? := some sr)
      return ← tpArgValues cfg envE vals facts totalEnv args [] fun avs => do
        -- THE HYPOTHESES, each PROVED at its argument's value by the same
        -- walker under that hypothesis's OWN class predicate. The walk runs
        -- with the caller's leaves but the hypothesis's class, so its
        -- return-path admissibility is checked against the mask the
        -- hypothesis actually demands.
        let mut hHyps : Array Expr := #[]
        for (hterm, hv, hcls) in sr.hyps.zip sr.hypCls do
          let some hi := gFormals.findIdx? (· == hv)
            | throwFrontier m!"proveTp: stored rule {sr.runeName}'s \
                hypothesis variable {hv.name} is not a formal of \
                {fs.name} (frontier)"
          let Ph ← tpHypPred hterm hv
          let hwalk ← tpWalk cfg envE vals facts totalEnv self
            { kit with cls := some hcls } Ph args[hi]!
          hHyps := hHyps.push
            (← mkAppM ``convP_at_val #[hwalk, avs[hi]!.2])
        let hP ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
          let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr t) vV
          withLocalDeclD `hc convTy fun hc => do
            let inst := mkAppN gTp
              (#[envE] ++ (args.map reflectSExpr).toArray ++
               (avs.map (·.1)).toArray ++ #[vV] ++
               (avs.map (·.2)).toArray ++ hHyps ++ #[hc])
            mkLambdaFVars #[vV, hc]
              (← mkExpectedTypeHint inst (mkApp P vV).headBeta)
        return mkAppN (mkConst ``ACL2.Replay.convP_of_conv_ex)
          #[cfg.worldExpr, envE, reflectSExpr t, P, hEx, hP]
  if gcls.argIndexed then
    -- ARGS-VALUED CALLEE (TP-replay arc increment 5, 2026-08-13):
    -- `REV`'s `(APP (REV (CDR X)) (CONS (CAR X) 'NIL))` leaf. The callee's
    -- own prescription is the args-valued shape — "a cons, OR the residue
    -- ARGUMENT's value" — so the position's predicate follows only once it
    -- holds of that argument's value too. That premise is PROVED, by
    -- walking the residue argument under the position's own predicate
    -- (the same walker, the same registries); nothing is assumed about it.
    let some gArgVar := tpCorArgVar? gAppPat gcor
      | throwFrontier m!"proveTp: {fs.name}'s corollary is arg-indexed but \
          its residue argument does not resolve (frontier)"
    let some gArgIdx := gFormals.findIdx? (· == gArgVar)
      | throwFrontier m!"proveTp: {fs.name}'s residue argument \
          {gArgVar.name} is not one of its formals (frontier)"
    let impName ← checkedImp tpClassImpAv
    let gTp ← proveTp cfg totalEnv kit.justs fs.name gcor
      (cors := kit.cors) (seen := kit.seen) (argValued := true)
    tpArgValues cfg envE vals facts totalEnv args [] fun avs => do
      let (yv, hyConv) := avs[gArgIdx]!
      -- the POSITION's predicate at the residue argument's value
      let hresWalk ← tpWalk cfg envE vals facts totalEnv none kit P
        args[gArgIdx]!
      let hresY ← mkAppM ``convP_at_val #[hresWalk, hyConv]
      let hP ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
        let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr t) vV
        withLocalDeclD `hc convTy fun hc => do
          let inst := mkAppN gTp
            (#[envE] ++ (args.map reflectSExpr).toArray ++
             (avs.map (·.1)).toArray ++ #[vV] ++
             (avs.map (·.2)).toArray ++ #[hc])
          let body := mkAppN (mkConst impName) #[yv, vV, hresY, inst]
          mkLambdaFVars #[vV, hc]
            (← mkExpectedTypeHint body (mkApp P vV).headBeta)
      return mkAppN (mkConst ``ACL2.Replay.convP_of_conv_ex)
        #[cfg.worldExpr, envE, reflectSExpr t, P, hEx, hP]
  else
    -- CLASS MATCH: same class, or a registered implication whose direction
    -- ACL2's own emitted type-set masks confirm
    let imp? : Option Name ←
      if gcls == cls then pure none else pure (some (← checkedImp tpClassImp))
    let gTp ← proveTp cfg totalEnv kit.justs fs.name gcor
      (cors := kit.cors) (seen := kit.seen)
    -- the position's obligation, RECOMPUTED from the driver's own `P`:
    -- `∀ v, (the call converges to v) → P v`. A callee proof of the wrong
    -- statement, or a class implication that does not close the gap, fails
    -- at this type hint (kernel-backed at `Meta.check`).
    let hP ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr t) vV
      withLocalDeclD `hc convTy fun hc => do
        let inst := mkAppN gTp
          (#[envE] ++ (args.map reflectSExpr).toArray ++ #[vV, hc])
        let body := match imp? with
          | none => inst
          | some n => mkApp2 (mkConst n) vV inst
        mkLambdaFVars #[vV, hc]
          (← mkExpectedTypeHint body (mkApp P vV).headBeta)
    return mkAppN (mkConst ``ACL2.Replay.convP_of_conv_ex)
      #[cfg.worldExpr, envE, reflectSExpr t, P, hEx, hP]

/-- Prove `tp:fn` (the `mkTpHypType` statement) from the fn's body and its
    EMITTED `:TYPE-PRESCRIPTION` corollary — the TP prover. The corollary is
    CONSUMED (ACL2's emitted type fact — never inferred); the walk proves the
    body's value satisfies it; argument strictness + determinism pin every
    convergence value (`tp_hyp_*_of_body`). Frontier failures are tagged
    (D6: the hypothesis stays visible).
    `seen` is the CALLEE-TP recursion stack (increment 3): the prescriptions
    already being proved further up. An empty stack is the ordinary entry
    point; `tpWalkCallee` re-enters with the caller's stack, and a fn that
    is already on it is a cycle (frontier, never an assumption).
    `argValued` (increment 5) targets the ARGS-VALUED hypothesis shape
    instead (`mkTpHypTypeAv`): the corollary's bare-formal occurrences —
    `BINARY-APPEND`'s `(EQUAL (BINARY-APPEND X Y) Y)` disjunct — lift to
    the ARGUMENT VALUES, so the predicate is built under the walk's own
    argument binders and the assembly is the `*_av` lemma family.

    `storedRule?` (T1+2 sprint P5b) proves a CONDITIONAL stored rule
    instead of the event's definitional corollary: `cor` is then the
    rule's own conclusion, the return-path admissibility runs against the
    RULE's own emitted `:LEAVES`, and the rule's hypotheses are carried
    through the induction (`tp_*_rec_hyp_mu`) and stated on the argument
    values (`tp_hyp_2_cond_of_body`). The caller — `tpWalkCallee` — then
    discharges those hypotheses at its own call site.

    `recTerm?` is the fn's REPLAYED admission waterfall: present, the
    induction measure is the INTERPRETED count and a self-call with an
    OPAQUE measured actual takes the recorded decrease route (design I1 —
    μ is proof bookkeeping and appears in no statement either way). The
    same switch `proveTotality` makes, so the two provers cannot disagree
    about a measure. -/
partial def proveTp (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (justs : List (String × Justification))
    (name : String) (cor : SExpr)
    (cors : List (String × SExpr) := []) (seen : List String := [])
    (argValued : Bool := false)
    (storedRule? : Option TpStoredRule := none)
    (recTerm? : Option RecTermInfo := none) :
    MetaM Expr := do
  let fs : Symbol := { name := name }
  let some (formals, body) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: {name} not defined in the world (frontier)"
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  -- P := fun v => <corollary, (fn formals…) ↦ v, value-lifted> = SExpr.t —
  -- EXACTLY mkTpHypType's conclusion, so the proof inhabits the offered
  -- type. In the ARGS-VALUED mode a bare FORMAL occurrence lifts to that
  -- argument's bound VALUE instead of frontiering — exactly
  -- `mkTpHypTypeAv`'s lift, so `mkP avs` at the walk's binders IS the
  -- offered hypothesis's predicate at those arguments.
  let appPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let mkP (avs : List Expr) : MetaM Expr :=
    withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let lifted ← dpValExpr [(appPat, vV)]
        (fun s => do
          unless argValued do
            throwFrontier m!"proveTp: corollary of {name} mentions the \
                free variable {s.name} outside the application (frontier)"
          let some i := formals.findIdx? (· == s)
            | throwFrontier m!"proveTp: corollary of {name} mentions the \
                free variable {s.name} outside the application/formals \
                (frontier)"
          let some e := avs[i]?
            | throwFrontier m!"proveTp: corollary of {name} mentions the \
                formal {s.name}, which has no bound argument value here \
                (frontier)"
          pure e) cor
      mkLambdaFVars #[vV] (← mkEq lifted (mkConst ``SExpr.t))
  -- the EMITTED return-path data this fn's walk may consume: ACL2's own
  -- `:LEAVES` (leaf term + type-set verdict) and the corollary's class
  let kit : TpKit :=
    { fnName := name
      -- under a CONDITIONAL stored rule the return-path admissibility runs
      -- against THAT rule's OWN context-refined leaves: the event's are a
      -- different rule's, and they differ exactly where it matters —
      -- `BINARY-APPEND`'s definitional leaves are `(3072, *ts-unknown*)`
      -- where `TRUE-LISTP-APPEND`'s are `(1024, 1152)` (RT2's per-entry
      -- `:LEAVES`).
      leaves := match storedRule? with
        | some sr => sr.leaves
        | none => (cfg.tpLeaves.lookup name).getD []
      cls := tpCorClass? appPat cor
      justs := justs, cors := cors, seen := name :: seen
      recTerm := recTerm?
      argVar := if argValued then tpCorArgVar? appPat cor else none }
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) :
      MetaM (List (Symbol × Expr × Expr)) :=
    bindArgsVarProofs cfg "proveTp" envE formals avs
  -- the D5 admission scope shared by both modes: `o<` on a measure the
  -- UNIFIED MEASURE TABLE registers (R3, 2026-08-14), classified through
  -- the SAME table as `proveTotality` so the two provers cannot disagree
  -- about what a measure shape IS.
  --
  -- The `tp_*_rec_mu` wrappers are μ-GENERIC (T1+2 sprint P4b — they were
  -- `consCount`-hardcoded, which is exactly the widening this comment used
  -- to defer, and it frontiered every non-`count` row: `CD2`'s `nfix`
  -- among them). So any row with a SINGLE measured variable and a
  -- registered μ is assemblable; a `userFn` row (no μ at all — the
  -- recorded-termination route interprets those) and the two-variable
  -- `sumCount` row keep their own honest frontiers. μ is proof
  -- bookkeeping (design I1): it appears in no statement produced here.
  let measuredOf (just : Justification) :
      MetaM (Symbol × Option Lean.Name) := do
    unless just.wfRel.name == "O<" do
      throwFrontier m!"proveTp: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some row := MeasureShape.ofJustification? just
      | throwFrontier m!"proveTp: measure {repr just.measure} with measured \
          subset {repr (just.measuredSubset.map (·.name))} is not a \
          registered measure-table row (frontier)"
    match row.vars, row.muHeads, recTerm? with
    | [v], some [h], _ => pure (v, some h)
    -- the RECORDED route interprets the measure instead of naming a μ
    -- head, so a row with no registered μ is still assemblable there
    | [v], _, some _ => pure (v, none)
    | _, _, _ =>
      throwFrontier m!"proveTp: measure-table row {row.headName} has no \
          single-variable registered μ for the TP assembly (frontier)"
  -- ONE μ for every assembly below: the table row's registered head, or —
  -- on the RECORDED route — the INTERPRETED count of the admission's own
  -- measure fn (exactly `proveTotality`'s switch; design I1, μ appears in
  -- no statement either way).
  let countOfWith (muHead? : Option Lean.Name) (e : Expr) : MetaM Expr :=
    match recTerm? with
    | some info => mkAppM ``ACL2.Replay.interpCount
        #[cfg.worldExpr, reflectSymbol info.cntSym, e]
    | none =>
      match muHead? with
      | some h => mkAppM h #[e]
      | none => throwFrontier m!"proveTp: the measure row has no registered \
          μ and no recorded admission replay to interpret it (frontier)"
  -- THE HYPOTHESIS-CARRYING ASSEMBLY (T1+2 sprint P5b) — a CONDITIONAL
  -- stored rule. Only the shape the corpus demands is covered: 2-ary,
  -- recursive, measured on the FIRST formal, ONE hypothesis
  -- (`TRUE-LISTP-APPEND` on `BINARY-APPEND`). Everything else keeps the
  -- honest frontier rather than growing untested conjunction plumbing —
  -- the same rule the args-valued assembly follows.
  if let some sr := storedRule? then
    if !sr.hyps.isEmpty then
      let [hterm] := sr.hyps
        | throwFrontier m!"proveTp: stored rule {sr.runeName} has \
            {sr.hyps.length} hypotheses; only the single-hypothesis \
            assembly exists (frontier)"
      let [(hv, hcls)] := sr.hypCls
        | throwFrontier m!"proveTp: stored rule {sr.runeName}: hypothesis \
            and class counts disagree (internal)"
      let some hIdx := formals.findIdx? (· == hv)
        | throwFrontier m!"proveTp: stored rule {sr.runeName}'s hypothesis \
            variable {hv.name} is not a formal of {name} (frontier)"
      let some just := justs.lookup name
        | throwFrontier m!"proveTp: conditional stored rule {sr.runeName} \
            on the non-recursive {name} (frontier)"
      let (measuredFormal, muHead?) ← measuredOf just
      let countOf := countOfWith muHead?
      let μE : MetaM Expr :=
        withLocalDeclD `u (mkConst ``SExpr) fun u => do
          mkLambdaFVars #[u] (← countOf u)
      let hPred ← tpHypPred hterm hv
      match formals with
      | [f1, f2] =>
        unless measuredFormal == f1 do
          throwFrontier m!"proveTp: conditional 2-ary measured formal \
              {measuredFormal.name} is not the first formal (frontier)"
        let P ← mkP []
        -- `H` — the hypothesis predicate at ITS formal's argument value,
        -- λ-abstracted over ALL the argument values so the self-call's
        -- instantiation is a plain application
        let HE ← withLocalDeclD `u0 (mkConst ``SExpr) fun u0 =>
          withLocalDeclD `u1 (mkConst ``SExpr) fun u1 => do
            let avs := [u0, u1]
            mkLambdaFVars #[u0, u1] (mkApp hPred avs[hIdx]!).headBeta
        let step ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
          let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
            let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
            let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
              let hty := (mkAppN HE #[bv, cv]).headBeta
              let ty ← mkAppM ``ConvToP
                #[cfg.worldExpr, ← mkEnvE [bv, cv], reflectSExpr body, P]
              mkForallFVars #[cv] (← mkArrow hty ty)
            mkForallFVars #[bv] (← mkArrow lt inner)
          withLocalDeclD `ih ihType fun ih =>
            withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
              let hTy := (mkAppN HE #[av1, av2]).headBeta
              withLocalDeclD `hH hTy fun hH => do
                let envE ← mkEnvE [av1, av2]
                let vals ← varProofs envE [av1, av2]
                let carrier : TpHypCarrier :=
                  { hyps := sr.hyps, facts := [(hv, hcls, hH)]
                    hExpr := HE, hProof := hH }
                let p ← tpWalk cfg envE vals [] totalEnv
                  (some (name, measuredFormal, ih, just))
                  { kit with hyp := some carrier } P body
                mkLambdaFVars #[av1, ih, av2, hH] p
        let hbody ← mkAppM ``tp_2_rec_hyp_mu
          #[← μE, reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
            cfg.worldExpr, P, HE, step]
        return ← mkAppM ``tp_hyp_2_cond_of_body
          #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
            reflectSymbol f2, reflectSExpr body, P, HE, hNs, hDef, hbody]
      | _ =>
        throwFrontier m!"proveTp: conditional stored rule {sr.runeName} at \
            arity {formals.length} unsupported (frontier)"
  if argValued then
    -- THE ARGS-VALUED ASSEMBLY (increment 5). Only the shape the corpus
    -- demands is covered — 2-ary, recursive, measured on the FIRST formal
    -- (`BINARY-APPEND`/`APP`); anything else keeps the honest frontier.
    let some just := justs.lookup name
      | throwFrontier m!"proveTp: args-valued {name} is not recursive \
          (frontier)"
    let (measuredFormal, muHead?) ← measuredOf just
    let countOf := countOfWith muHead?
    let μE : MetaM Expr :=
      withLocalDeclD `u (mkConst ``SExpr) fun u => do
        mkLambdaFVars #[u] (← countOf u)
    match formals with
    | [f1, f2] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTp: args-valued 2-ary measured formal \
            {measuredFormal.name} is not the first formal (frontier)"
      let Pav ← withLocalDeclD `u0 (mkConst ``SExpr) fun u0 =>
        withLocalDeclD `u1 (mkConst ``SExpr) fun u1 => do
          mkLambdaFVars #[u0, u1] (← mkP [u0, u1])
      let step ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
          let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
            let ty ← mkAppM ``ConvToP #[cfg.worldExpr, ← mkEnvE [bv, cv],
              reflectSExpr body, ← mkP [bv, cv]]
            mkForallFVars #[cv] ty
          mkForallFVars #[bv] (← mkArrow lt inner)
        withLocalDeclD `ih ihType fun ih =>
          withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
            let envE ← mkEnvE [av1, av2]
            let vals ← varProofs envE [av1, av2]
            let p ← tpWalk cfg envE vals [] totalEnv
              (some (name, measuredFormal, ih, just)) kit (← mkP [av1, av2])
              body
            mkLambdaFVars #[av1, ih, av2] p
      let hbody ← mkAppM ``tp_2_rec_av_mu
        #[← μE, reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, Pav, step]
      return ← mkAppM ``tp_hyp_2_av_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, Pav, hNs, hDef, hbody]
    | _ =>
      throwFrontier m!"proveTp: args-valued arity {formals.length} \
          unsupported (frontier)"
  -- the VALUE-ONLY predicate (`mkTpHypType`'s): built with no argument
  -- values in scope, so a bare-formal occurrence is the honest frontier
  let P ← mkP []
  let mkConvToPTy (envB : Expr) : MetaM Expr :=
    mkAppM ``ConvToP #[cfg.worldExpr, envB, reflectSExpr body, P]
  match justs.lookup name with
  | none =>
    -- NON-RECURSIVE: the walk alone gives the ∀-body form
    match formals with
    | [f1] =>
      let hbody ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let envE ← mkEnvE [av]
        let vals ← varProofs envE [av]
        let p ← tpWalk cfg envE vals [] totalEnv none kit P body
        mkLambdaFVars #[av] p
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let envE ← mkEnvE [av1, av2]
          let vals ← varProofs envE [av1, av2]
          let p ← tpWalk cfg envE vals [] totalEnv none kit P body
          mkLambdaFVars #[av1, av2] p
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTp: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope, as in proveTotality)
    let (measuredFormal, muHead?) ← measuredOf just
    let countOf := countOfWith muHead?
    let μE : MetaM Expr :=
      withLocalDeclD `u (mkConst ``SExpr) fun u => do
        mkLambdaFVars #[u] (← countOf u)
    let selfC := fun (ih : Expr) => some (name, measuredFormal, ih, just)
    match formals with
    | [f1] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTp: measured formal mismatch"
      let step ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av]
          let cvty ← mkConvToPTy (← mkEnvE [bv])
          mkForallFVars #[bv] (← mkArrow lt cvty)
        withLocalDeclD `ih ihType fun ih => do
          let envE ← mkEnvE [av]
          let vals ← varProofs envE [av]
          let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
          mkLambdaFVars #[av, ih] p
      let hbody ← mkAppM ``tp_1_rec_mu
        #[← μE, reflectSymbol f1, reflectSExpr body, cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let step ←
        if measuredFormal == f1 then
          withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
            let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
              let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
                mkForallFVars #[cv] (← mkConvToPTy (← mkEnvE [bv, cv]))
              mkForallFVars #[bv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
                let envE ← mkEnvE [av1, av2]
                let vals ← varProofs envE [av1, av2]
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
                mkLambdaFVars #[av1, ih, av2] p
        else if measuredFormal == f2 then
          withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
            let ihType ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
              let lt ← mkAppM ``Nat.lt #[← countOf cv, ← countOf av2]
              let inner ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
                mkForallFVars #[bv] (← mkConvToPTy (← mkEnvE [bv, cv]))
              mkForallFVars #[cv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
                let envE ← mkEnvE [av1, av2]
                let vals ← varProofs envE [av1, av2]
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
                mkLambdaFVars #[av2, ih, av1] p
        else
          -- (unreached: the 2-ary arm's measured formal is f1 or f2 by
          -- construction) — TAGGED like proveTotality's twin, so a future
          -- reachable path keeps the hypothesis instead of aborting
          throwFrontier m!"proveTp: measured formal not among the formals \
              (frontier)"
      let recLemma :=
        if measuredFormal == f1 then ``tp_2_rec_mu else ``tp_2_rec_snd_mu
      let hbody ← mkAppM recLemma
        #[← μE, reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2, f3] =>
      -- 3-ary (TP-replay arc increment 4, 2026-08-13): the measured
      -- formal's POSITION is read off the emitted justification, never
      -- special-cased — `ZIP3` is measured on its first formal, `ALL-REL`
      -- and `FILTER` on their second (the `(fn x e)` shape). The third
      -- position has no corpus customer and stays a tagged frontier.
      let mIdx3 := [f1, f2, f3].findIdx (· == measuredFormal)
      let others := (List.range 3).filter (· != mIdx3)
      let step ←
        if mIdx3 ≥ 2 then
          throwFrontier m!"proveTp: 3-ary measured formal \
              {measuredFormal.name} is not the first or second formal \
              (frontier)"
        else
          withLocalDeclD `avm (mkConst ``SExpr) fun avm => do
            let envAt := fun (mv o1 o2 : Expr) => do
              let avs := (List.range 3).map fun i =>
                if i == mIdx3 then mv else if i == others[0]! then o1 else o2
              mkEnvE avs
            let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf avm]
              let inner ← withLocalDeclD `ov1 (mkConst ``SExpr) fun ov1 =>
                withLocalDeclD `ov2 (mkConst ``SExpr) fun ov2 => do
                  mkForallFVars #[ov1, ov2]
                    (← mkConvToPTy (← envAt bv ov1 ov2))
              mkForallFVars #[bv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
                withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
                  let envE ← envAt avm av1 av2
                  let avs := (List.range 3).map fun i =>
                    if i == mIdx3 then avm
                    else if i == others[0]! then av1 else av2
                  let vals ← varProofs envE avs
                  let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
                  mkLambdaFVars #[avm, ih, av1, av2] p
      let recLemma := if mIdx3 == 0 then ``tp_3_rec_mu else ``tp_3_rec_snd_mu
      let hbody ← mkAppM recLemma
        #[← μE, reflectSymbol f1, reflectSymbol f2, reflectSymbol f3,
          reflectSExpr body, cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_3_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSymbol f3, reflectSExpr body, P, hNs,
          hDef, hbody]
    | _ => throwFrontier m!"proveTp: recursive arity {formals.length} \
        unsupported (frontier)"

end

end ACL2.Replay.Driver
