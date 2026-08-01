/-
  THE EXEC-KIT GENERATOR (sorting-absolute arc 1b — the dominant
  industrialization item, docs/notes/2026-07-31_mirror-industrialization.md §1).

  `derive_exec%` mechanically emits, for one world defun, the two
  hand-written artifacts every mirror-consumed defun needs:

  - `<fn>Exec` — the shape-exact total Lean function: a pure syntax walk
    over the body (`IF` → `ite` on `Logic.toBool`, builtin call → the
    `Logic.*` twin, self call → recursion, defn call → the callee's
    registered exec), termination from the measure class (M1: `consCount`
    of the measured formal, destructor chains under a ruling CONSP test)
    with decreases discharged by the Count library.
  - `<fn>_exec_corr` (the optional `corr` clause) — the stage-1 walk: a
    `ConvTo` fold over the SAME body syntax. One `re_val_var_get` per
    formal (env-get facts from the generic `bindArgs_get_head/tail` pair —
    the env-binding boilerplate item §3, retired), `conv_builtin1/2` per
    builtin node with its `callBuiltin` bridge lemma, `conv_if_lift` per
    IF, `conv_defn_N` per defn call, and the `consCount_strong_induction`
    IH at self-call sites (decrease re-derived from the site's destructor
    chain against the ruling CONSP guard binder).

  HYPOTHESIS TELESCOPE (canonical, matches every hand kit): defn hyps in
  callee-first-occurrence order then self; builtin no-def hyps in the twin
  table's order filtered to those used (own body ∪ callees' telescopes).

  The generator's input body is the in-scope body CONSTANT (the same one
  the kit hypotheses mention); fidelity to the emitted `:DEFUN` is enforced
  exactly as for the hand kits — the `by decide` world facts at every
  consumer pin the constant to the log-derived world at build time.
  (Log-side extraction of the body constants is the v2 companion, with the
  ACL2 quotation macro — note §5.)

  `<fn>Exec_enc` (the NATIVE reading) is deliberately NOT generated: the
  choice of native counterpart is the mirror criterion's human fidelity
  judgment.

  VALIDATION PROTOCOL (the arc charter's 1b clause): the generator is
  validated by RETIREMENT — each hand kit's def/theorem is replaced by a
  generator invocation emitting the SAME NAME and SAME STATEMENT, so every
  existing consumer (assemblies, dischargers, `_enc` lemmas, golden
  mirrors) re-elaborates against the generated artifact. The build is the
  gate. No kit is generated "for later".

  Fail-closed throughout: an unknown head symbol, a free variable, a
  recursion site whose measured argument is not a destructor chain over the
  measured formal, a self-call outside the measured CONSP guard, or a
  measure shape outside v1 (M3: decrease through a defined function —
  msort's EVENS, qsort's FILTER) is a HARD elaboration error naming the
  frontier; those kits stay hand-written.
-/
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Imported.Lifting

namespace ACL2.ExecGen

open ACL2 ACL2.Replay Lean Lean.Meta Lean.Elab Lean.Elab.Command
  Lean.Parser.Term

/-! ## Generic support lemmas (the env-binding boilerplate, retired) -/

/-- `bindArgs` head lookup: the first formal binds the first value
    (`bindArgs` inserts the head LAST, i.e. outermost). -/
theorem bindArgs_get_head {f : Symbol} {fs : List Symbol} {v : SExpr}
    {vs : List SExpr} : (bindArgs (f :: fs) (v :: vs)).get? f = some v := by
  show ((bindArgs fs vs).insert f v).get? f = some v
  rw [Env.get?_insert, if_pos (by simp)]

/-- `bindArgs` tail lookup: a different symbol falls through the head
    binding. -/
theorem bindArgs_get_tail {g f : Symbol} {fs : List Symbol} {v : SExpr}
    {vs : List SExpr} (h : (g == f) = false) :
    (bindArgs (f :: fs) (v :: vs)).get? g = (bindArgs fs vs).get? g := by
  show ((bindArgs fs vs).insert f v).get? g = _
  rw [Env.get?_insert, if_neg (by simp_all)]

/-- `callBuiltin` bridge for LEXORDER (the trusted-core comparison). -/
theorem callBuiltin_lexorder_gen (a b : SExpr) :
    callBuiltin "LEXORDER" [a, b] = some (lexorder a b) := rfl

/-- `callBuiltin` bridge for CONS. -/
theorem callBuiltin_cons_gen (a b : SExpr) :
    callBuiltin "CONS" [a, b] = some (Logic.cons a b) := rfl

/-! ## The kit registry -/

/-- Registered kit metadata: what a CALLER's generated def and corr proof
    need to know about a callee's kit. Populated by `derive_exec%`;
    `register_exec_kit%` registers hand-written kits (M3 measures) for
    exec-side callee use (corr-side callee use additionally needs the corr
    fields — extend the registration when a generated corr first needs a
    hand callee). -/
structure KitInfo where
  /-- the ACL2 function name, e.g. "INSERT" -/
  aclName : String
  /-- the exec def's name -/
  execName : Name
  /-- arity (formal count) -/
  arity : Nat
  /-- the stage-1 corr theorem (`.anonymous` = none registered) -/
  corrName : Name := .anonymous
  /-- the Symbol constant naming the fn -/
  symC : Name := .anonymous
  /-- the formal Symbol constants, in order -/
  formalCs : List Name := []
  /-- the body constant -/
  bodyC : Name := .anonymous
  /-- the corr's defn-hypothesis ACL2 names, telescope order -/
  defnHyps : List String := []
  /-- the corr's builtin no-def hypothesis names, telescope order -/
  builtinHyps : List String := []
  deriving Inhabited, Repr

initialize execKitExt :
    SimplePersistentEnvExtension KitInfo (List KitInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => e :: s
    addImportedFn := fun ess => (ess.map (·.toList)).toList.flatten
  }

def findKit (env : Environment) (aclName : String) : Option KitInfo :=
  (execKitExt.getState env).find? (·.aclName == aclName)

/-- Register a kit, hard-failing on a duplicate ACL2 name (audit F2: with
    first-match lookup, a re-registration would silently redirect every
    later caller's callee resolution). -/
def registerKit (info : KitInfo) : CommandElabM Unit := do
  if let some prior := findKit (← getEnv) info.aclName then
    throwError "derive_exec%: {info.aclName} is already registered \
        (exec {prior.execName}) — duplicate registration would silently \
        redirect callee resolution (fail-closed); scope the registry \
        before generating same-named kits from another book"
  modifyEnv fun env => execKitExt.addEntry env info

/-- The builtin twin table: ACL2 builtin name → the `Logic`-level Lean
    function of the same semantics + the `callBuiltin` bridge lemma the
    corr side cites. TABLE ORDER IS THE CANONICAL TELESCOPE ORDER for
    `h_no_*` hypotheses (matches every hand kit). Extending to a new
    builtin is one row (+ a bridge lemma if none exists). Fail-closed: a
    head symbol not here, not IF/QUOTE, not the self/registered-callee
    set, is a hard error. -/
def builtinTwins : List (String × Name × Nat × Name) :=
  [ ("CONSP",    ``Logic.consp, 1, ``callBuiltin_consp),
    ("EQUAL",    ``Logic.equal, 2, ``callBuiltin_equal),
    ("CAR",      ``Logic.car, 1, ``callBuiltin_car),
    ("CDR",      ``Logic.cdr, 1, ``callBuiltin_cdr),
    ("CONS",     ``Logic.cons, 2, ``callBuiltin_cons_gen),
    ("LEXORDER", ``lexorder, 2, ``callBuiltin_lexorder_gen),
    ("BINARY-+", ``Logic.plus, 2, ``callBuiltin_plus) ]

/-! ## Body analysis -/

/-- SExpr list view of a cons chain (the argument list of an application). -/
partial def argList : SExpr → Option (List SExpr)
  | .nil => some []
  | .cons a rest => (argList rest).map (a :: ·)
  | _ => none

/-- Reflect an SExpr VALUE (a quoted constant) as term syntax. -/
partial def valueToStx (v : SExpr) : CommandElabM Term := do
  match v with
  | .nil => `($(mkCIdent ``SExpr.nil))
  | .atom (.symbol s) =>
    let pkg := Syntax.mkStrLit s.package
    let nm := Syntax.mkStrLit s.name
    `($(mkCIdent ``SExpr.atom) ($(mkCIdent ``Atom.symbol)
        { package := $pkg, name := $nm }))
  | .atom (.number (.int n)) =>
    let lit := Syntax.mkNumLit (toString n.natAbs)
    if n ≥ 0 then
      `($(mkCIdent ``SExpr.atom) ($(mkCIdent ``Atom.number)
          ($(mkCIdent ``ACL2.Number.int) $lit)))
    else
      `($(mkCIdent ``SExpr.atom) ($(mkCIdent ``Atom.number)
          ($(mkCIdent ``ACL2.Number.int) (-$lit))))
  | .cons a b => `($(mkCIdent ``SExpr.cons) $(← valueToStx a) $(← valueToStx b))
  | _ => throwError "derive_exec%: quoted value {repr v} beyond the v1 \
      reflector (frontier)"

/-- A destructor chain over a formal: `(CDR (CDR X))` ⇒ `some ([CDR, CDR], "X")`
    (outermost first). `none` when the term is not a pure CAR/CDR chain over a
    variable. -/
partial def destructorChain : SExpr → Option (List String × String)
  | .atom (.symbol s) => some ([], s.name)
  | .cons (.atom (.symbol d)) (.cons u .nil) =>
    if d.name == "CAR" || d.name == "CDR" then
      (destructorChain u).map fun (ds, v) => (d.name :: ds, v)
    else none
  | _ => none

/-- The recursion sites of a body: for each self-call, its argument list. -/
partial def selfCallSites (selfName : String) : SExpr → List (List SExpr)
  | .cons (.atom (.symbol hd)) args =>
    let here := if hd.name == selfName then
      match argList args with
      | some as => [as]
      | none => []
    else []
    let inner := match argList args with
      | some as =>
        if hd.name == "QUOTE" then []
        else as.flatMap (selfCallSites selfName)
      | none => []
    here ++ inner
  | _ => []

/-- Head symbols of a body that are neither IF/QUOTE, builtins, nor the fn
    itself — the CALLEES, in first-occurrence (pre-order) order. -/
partial def calleeNames (selfName : String) : SExpr → List String
  | .cons (.atom (.symbol hd)) args =>
    (match argList args with
     | some as =>
       let here :=
         if hd.name == "QUOTE" || hd.name == "IF" || hd.name == selfName ||
            (builtinTwins.find? (·.1 == hd.name)).isSome then []
         else [hd.name]
       if hd.name == "QUOTE" then here
       else here ++ as.flatMap (calleeNames selfName)
     | none => [])
  | _ => []

/-- Builtin head symbols used by a body (as a set; order comes from the
    twin table). -/
partial def usedBuiltins (selfName : String) : SExpr → List String
  | .cons (.atom (.symbol hd)) args =>
    (match argList args with
     | some as =>
       let here := if (builtinTwins.find? (·.1 == hd.name)).isSome
         then [hd.name] else []
       if hd.name == "QUOTE" then []
       else (here ++ as.flatMap (usedBuiltins selfName)).eraseDups
     | none => [])
  | _ => []

/-- Lean binder name for an ACL2 formal ("E" ⇒ `e`, "ACC-X" ⇒ `acc_x`). -/
def formalBinderName (aclVar : String) : Name :=
  Name.mkSimple <| aclVar.toLower.map fun c => if c == '-' then '_' else c

/-- Sanitized hypothesis-binder suffix for an ACL2 name. -/
def hypSuffix (acl : String) : String :=
  acl.toLower.map fun c => if c.isAlphanum then c else '_'

/-- Hard-fail on sanitization collisions (audit F1/F3: `A-B`/`A_B` formals
    both sanitize to `a_b` and would silently generate the WRONG function;
    `BINARY-+`/`BINARY-*` hyp binders collide the same way). -/
def ensureDistinct (what : String) (ids : Array Ident) :
    CommandElabM Unit := do
  let names := ids.map (·.getId)
  if names.toList.eraseDups.length != names.size then
    throwError "derive_exec%: sanitized {what} names collide ({names}) — \
        the generated artifact would silently mis-bind (fail-closed)"

/-! ## Exec-def generation -/

/-- The exec-def body walk: emitted `:BODY` syntax → the total Lean
    function's term syntax. Also the VALUE-PROJECTION walk for the corr
    side (formals mapped to value idents). Fail-closed on every
    unrecognized shape. -/
partial def execTerm (selfName : String) (selfId : Ident)
    (formals : List (String × Ident)) : SExpr → CommandElabM Term
  | .atom (.symbol s) =>
    match formals.lookup s.name with
    | some id => pure id
    | none => throwError "derive_exec%: free variable {s.name} (not a \
        formal of {selfName})"
  | .cons (.atom (.symbol hd)) args => do
    let some as := argList args
      | throwError "derive_exec%: improper argument list under {hd.name}"
    if hd.name == "QUOTE" then
      match as with
      | [v] => valueToStx v
      | _ => throwError "derive_exec%: malformed QUOTE"
    else if hd.name == "IF" then
      match as with
      | [c, t, e] => do
        let cS ← execTerm selfName selfId formals c
        let tS ← execTerm selfName selfId formals t
        let eS ← execTerm selfName selfId formals e
        `(if $(mkCIdent ``Logic.toBool) $cS = true then $tS else $eS)
      | _ => throwError "derive_exec%: IF with {as.length} arguments"
    else if hd.name == selfName then do
      let asS ← as.mapM (execTerm selfName selfId formals)
      `($selfId $(asS.toArray)*)
    else
      match builtinTwins.find? (·.1 == hd.name) with
      | some (_, twin, ar, _) => do
        unless as.length == ar do
          throwError "derive_exec%: {hd.name} arity {as.length} ≠ twin \
              arity {ar}"
        let asS ← as.mapM (execTerm selfName selfId formals)
        `($(mkCIdent twin) $(asS.toArray)*)
      | none => do
        match findKit (← getEnv) hd.name with
        | some kit => do
          unless as.length == kit.arity do
            throwError "derive_exec%: callee {hd.name} arity mismatch"
          let asS ← as.mapM (execTerm selfName selfId formals)
          `($(mkCIdent kit.execName) $(asS.toArray)*)
        | none =>
          throwError "derive_exec%: head symbol {hd.name} is not IF/QUOTE, \
              a v1 builtin twin, the function itself, or a registered exec \
              kit (frontier — extend the table or hand-write the kit)"
  | t => throwError "derive_exec%: unsupported body shape {repr t}"

/-- The M1 decrease TERM for one recursion site, against an explicit CONSP
    guard hypothesis: chain `[d₁, …, dₖ]` (outermost first) becomes
    `lt_of_le_of_lt (consCount_d₁_le _) (… (consCount_dₖ_lt_of_consp
    hguard))`. -/
def decreaseTerm (chain : List String) (guard : Term) :
    CommandElabM Term := do
  let lastLemma (d : String) : Name :=
    if d == "CDR" then ``consCount_cdr_lt_of_consp
    else ``consCount_car_lt_of_consp
  let leLemma (d : String) : Name :=
    if d == "CDR" then ``consCount_cdr_le else ``consCount_car_le
  match chain.reverse with
  | [] => throwError "derive_exec%: recursion site with an EMPTY destructor \
      chain (the measured argument is the formal itself — no decrease)"
  | dInner :: dsOuterRev => do
    let base ← `($(mkCIdent (lastLemma dInner)) $guard)
    dsOuterRev.foldlM (init := base) fun acc d =>
      `(lt_of_le_of_lt ($(mkCIdent (leLemma d)) _) $acc)

/-- The M1 decrease SCRIPT (for `decreasing_by`, guard via `assumption`). -/
def decreaseScript (chain : List String) :
    CommandElabM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let proof ← decreaseTerm chain (← `((by assumption)))
  `(Lean.Parser.Tactic.tacticSeq| exact $proof)

/-! ## Corr-proof generation -/

/-- The v1 measure classes: M1 = `(ACL2-COUNT formalᵢ)` with
    destructor-chain recursion; M2 = `(+ (ACL2-COUNT formalᵢ)
    (ACL2-COUNT formalⱼ))` with single-CDR one-side decreases (merge2's
    shape). -/
inductive MeasureSpec where
  | m1 (idx : Nat)
  | m2 (idx1 idx2 : Nat)
  deriving Repr, BEq

/-- Context of the corr body walk. -/
structure CorrCtx where
  wId : Ident
  selfAcl : String
  measure : MeasureSpec
  /-- ACL2 formal names, in order (index ↔ name) -/
  formalAcls : Array String
  /-- formal name → the `re_val_var_get` have -/
  hvMap : List (String × Ident)
  /-- formal name → value ident (for exec value projection) -/
  valMap : List (String × Ident)
  defnHypMap : List (String × Ident)
  builtinHypMap : List (String × Ident)
  execId : Ident
  ihId : Ident
  /-- M2 only: the `sum = n` hypothesis for the ▸-transport -/
  hnId : Ident
  /-- in-scope CONSP guards, per formal name -/
  guards : List (String × Ident) := []

private def holes (n : Nat) : CommandElabM (Array Term) :=
  (Array.range n).mapM fun _ => `(_)

/-- `conv_defn_N` application: N=1/2/3 with 7/10/13 value holes (after
    `w`), then `(by decide)` (the ns conjunction), the defn hypothesis,
    the arg proofs, the body continuation. -/
def mkConvDefn (wId : Ident) (n : Nat) (ps : List Term) (hDef : Ident)
    (cont : Term) : CommandElabM Term := do
  let (lem, holeN) ←
    match n with
    | 1 => pure (``conv_defn_1, 7)
    | 2 => pure (``conv_defn_2, 10)
    | 3 => pure (``conv_defn_3, 13)
    | _ => throwError "derive_exec% corr: defn arity {n} beyond \
        conv_defn_3 (frontier)"
  let hs ← holes holeN
  let nsP ← `((by decide))
  pure <| Syntax.mkApp (mkCIdent lem)
    (#[(wId : Term)] ++ hs ++ #[nsP, (hDef : Term)]
      ++ ps.toArray ++ #[cont])

/-- If this term is `(CONSP <formal>)`, the formal's name. -/
def conspTestFormal (formalAcls : Array String) : SExpr → Option String
  | .cons (.atom (.symbol c)) (.cons (.atom (.symbol v)) .nil) =>
    if c.name == "CONSP" && formalAcls.contains v.name then some v.name
    else none
  | _ => none

/-- The corr walk: body syntax → the `ConvTo` proof TERM (goal-driven —
    value-side arguments are holes filled by unification against the
    unfolded exec goal). `path` names the IF guard binders
    deterministically. -/
partial def corrTerm (ctx : CorrCtx) (path : String := "") :
    SExpr → CommandElabM Term
  | .atom (.symbol s) => do
    match ctx.hvMap.lookup s.name with
    | some hv => pure hv
    | none => throwError "derive_exec% corr: free variable {s.name}"
  | .cons (.atom (.symbol hd)) args => do
    let some as := argList args
      | throwError "derive_exec% corr: improper args under {hd.name}"
    if hd.name == "QUOTE" then
      match as with
      | [v] => do
        `($(mkCIdent ``re_val_quote) $(ctx.wId) _ $(← valueToStx v))
      | _ => throwError "derive_exec% corr: malformed QUOTE"
    else if hd.name == "IF" then
      match as with
      | [c, t, e] => do
        let pc ← corrTerm ctx (path ++ "c") c
        let hb := mkIdent (Name.mkSimple s!"hb{path}")
        let ctxT := match conspTestFormal ctx.formalAcls c with
          | some f => { ctx with guards := (f, hb) :: ctx.guards }
          | none => ctx
        let pt ← corrTerm ctxT (path ++ "t") t
        let pe ← corrTerm ctx (path ++ "e") e
        let hs ← holes 7
        `($(mkCIdent ``conv_if_lift) $(ctx.wId) $hs*
            $pc (fun $hb => $pt) (fun _ => $pe))
      | _ => throwError "derive_exec% corr: IF with {as.length} arguments"
    else if hd.name == ctx.selfAcl then do
      let ps ← as.mapM (corrTerm ctx (path ++ "s"))
      let proj := execTerm ctx.selfAcl ctx.execId ctx.valMap
      let ihApp ← match ctx.measure with
        | .m1 mIdx => do
          let mArg := as[mIdx]!
          let some (chain, root) := destructorChain mArg
            | throwError "derive_exec% corr: measured argument shape \
                (validated earlier — internal)"
          let some guard := ctx.guards.lookup root
            | throwError "derive_exec% corr: self-call outside a CONSP \
                guard on {root} (M1 frontier — hand-write this kit)"
          let decP ← decreaseTerm chain guard
          let mVal ← proj mArg
          let otherVals ← (as.zipIdx.filter (·.2 != mIdx)).mapM
            fun (a, _) => proj a
          pure <| Syntax.mkApp ctx.ihId
            (#[mVal, decP] ++ otherVals.toArray)
        | .m2 i j => do
          -- one side descends by a single CDR, the other is unchanged
          let ci := destructorChain as[i]!
          let cj := destructorChain as[j]!
          let (descFormal, sumLemma) ←
            match ci, cj with
            | some (["CDR"], fi), some ([], fj) => do
              unless fi == ctx.formalAcls[i]! && fj == ctx.formalAcls[j]! do
                throwError "derive_exec% corr: M2 site formals mismatch"
              pure (fi, ``consCount_cdr_sum_lt_left_consp)
            | some ([], fi), some (["CDR"], fj) => do
              unless fi == ctx.formalAcls[i]! && fj == ctx.formalAcls[j]! do
                throwError "derive_exec% corr: M2 site formals mismatch"
              pure (fj, ``consCount_cdr_sum_lt_right_consp)
            | _, _ =>
              throwError "derive_exec% corr: M2 site is not a single-CDR \
                  one-side decrease (frontier — hand-write this kit)"
          let some guard := ctx.guards.lookup descFormal
            | throwError "derive_exec% corr: M2 self-call outside a CONSP \
                guard on {descFormal} (frontier)"
          let sumT ← do
            let pi ← proj as[i]!
            let pj ← proj as[j]!
            `($(mkCIdent ``SExpr.consCount) $pi
                + $(mkCIdent ``SExpr.consCount) $pj)
          let decP ← `($(ctx.hnId) ▸ $(mkCIdent sumLemma) $guard)
          let argVals ← as.mapM proj
          let rflP ← `(rfl)
          pure <| Syntax.mkApp ctx.ihId
            (#[sumT, decP] ++ argVals.toArray ++ #[rflP])
      let some hSelf := ctx.defnHypMap.lookup ctx.selfAcl
        | throwError "derive_exec% corr: no self defn hyp (internal)"
      mkConvDefn ctx.wId as.length ps hSelf ihApp
    else
      match builtinTwins.find? (·.1 == hd.name) with
      | some (_, _, ar, bridge) => do
        unless as.length == ar do
          throwError "derive_exec% corr: {hd.name} arity mismatch"
        let ps ← as.mapM (corrTerm ctx (path ++ "b"))
        let some hNo := ctx.builtinHypMap.lookup hd.name
          | throwError "derive_exec% corr: no h_no hyp for {hd.name} \
              (internal — telescope derivation missed it)"
        let bridgeApp := Syntax.mkApp (mkCIdent bridge)
          (← holes ar)
        if ar == 1 then do
          let hs ← holes 5
          `($(mkCIdent ``conv_builtin1) $(ctx.wId) $hs* (by decide) $hNo
              $(ps[0]!) $bridgeApp)
        else do
          let hs ← holes 7
          `($(mkCIdent ``conv_builtin2) $(ctx.wId) $hs* (by decide) $hNo
              $(ps[0]!) $(ps[1]!) $bridgeApp)
      | none => do
        match findKit (← getEnv) hd.name with
        | some kit => do
          if kit.corrName == .anonymous then
            throwError "derive_exec% corr: callee {hd.name} has no \
                registered corr theorem (register or generate it first)"
          let ps ← as.mapM (corrTerm ctx (path ++ "k"))
          let hypIds ← (kit.defnHyps ++ kit.builtinHyps).mapM fun h => do
            let m := ctx.defnHypMap.lookup h <|> ctx.builtinHypMap.lookup h
            let some hId := m
              | throwError "derive_exec% corr: callee {hd.name} needs \
                  hypothesis {h}, absent from the caller telescope \
                  (internal — telescope derivation missed it)"
            pure (hId : Term)
          let envAndArgs ← holes (1 + 2 * kit.arity)
          pure <| Syntax.mkApp (mkCIdent kit.corrName)
            (#[(ctx.wId : Term)] ++ hypIds.toArray ++ envAndArgs
              ++ ps.toArray)
        | none =>
          throwError "derive_exec% corr: unregistered head {hd.name}"
  | t => throwError "derive_exec% corr: unsupported body shape {repr t}"

/-! ## Argument strictness + TP/totality discharger support (1c)

Moved (publicized) from `Imported/Sorting.lean`'s private copies so the
generated dischargers can cite them; `conv_args2_of_conv_app` stays in
EvalLemmas. -/

theorem evalOpt_app1_args (f : Nat) (w : World) (env : Env)
    (s : Symbol) (a1 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons a1 .nil)) = some v) :
    ∃ u, evalOpt f w env a1 = some u := by
  rw [show evalOpt (f + 1) w env
        (.cons (.atom (.symbol s)) (.cons a1 .nil))
        = evalOptStep (evalOpt f) w env
            (.cons (.atom (.symbol s)) (.cons a1 .nil)) from rfl] at h
  unfold evalOptStep at h
  simp only [Symbol.isNamed, SExpr.toList?] at h
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self,
             ↓reduceIte] at h
  cases hu1 : evalOpt f w env a1 with
  | none => simp [List.mapM, List.mapM.loop, hu1] at h
  | some u1 => exact ⟨u1, rfl⟩

theorem evalOpt_app3_args (f : Nat) (w : World) (env : Env)
    (s : Symbol) (a1 a2 a3 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
      = some v) :
    (∃ u, evalOpt f w env a1 = some u) ∧
    (∃ u, evalOpt f w env a2 = some u) ∧
    (∃ u, evalOpt f w env a3 = some u) := by
  rw [show evalOpt (f + 1) w env
        (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
        = evalOptStep (evalOpt f) w env
            (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
        from rfl] at h
  unfold evalOptStep at h
  simp only [Symbol.isNamed, SExpr.toList?] at h
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self,
             ↓reduceIte] at h
  cases hu1 : evalOpt f w env a1 with
  | none => simp [List.mapM, List.mapM.loop, hu1] at h
  | some u1 =>
    cases hu2 : evalOpt f w env a2 with
    | none => simp [List.mapM, List.mapM.loop, hu1, hu2] at h
    | some u2 =>
      cases hu3 : evalOpt f w env a3 with
      | none => simp [List.mapM, List.mapM.loop, hu1, hu2, hu3] at h
      | some u3 => exact ⟨⟨u1, rfl⟩, ⟨u2, rfl⟩, ⟨u3, rfl⟩⟩

theorem conv_args1_of_conv_app (w : World) (env : Env) (s : Symbol)
    (a1 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol s)) (.cons a1 .nil)) = some v) :
    ∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a1 = some u := by
  obtain ⟨N, hN⟩ := h
  exact ACL2.Replay.conv_fix ⟨N, fun f hf =>
    evalOpt_app1_args f w env s a1 v h_ns (hN (f + 1) (by omega))⟩

theorem conv_args3_of_conv_app (w : World) (env : Env) (s : Symbol)
    (a1 a2 a3 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
      = some v) :
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a1 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a2 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a3 = some u) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨ACL2.Replay.conv_fix ⟨N, fun f hf => ?_⟩,
          ACL2.Replay.conv_fix ⟨N, fun f hf => ?_⟩,
          ACL2.Replay.conv_fix ⟨N, fun f hf => ?_⟩⟩
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).1
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).2.1
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).2.2

/-! ## The commands -/


/-- Everything `derive_exec%` computes once per kit. -/
structure KitInput where
  execId : Ident
  symName : Name
  bodyName : Name
  formalNames : Array Name
  sym : Symbol
  body : SExpr
  formalSyms : Array Symbol
  measure : MeasureSpec
  recursive : Bool

/-- Generate the corr theorem for a kit; returns the telescope metadata
    (defn-hyp ACL2 names, builtin-hyp names) to register. -/
def genCorr (inp : KitInput) (corrId : Ident) :
    CommandElabM (List String × List String) := do
  let env ← getEnv
  let selfAcl := inp.sym.name
  -- callee kits, first-occurrence order (each must carry a corr)
  let calleeKits ← (calleeNames selfAcl inp.body).mapM fun c => do
    let some k := findKit env c
      | throwError "derive_exec% corr: unregistered callee {c}"
    if k.corrName == .anonymous || k.symC == .anonymous then
      throwError "derive_exec% corr: callee {c}'s kit has no corr/statement \
          metadata (generate its corr first, or extend its registration)"
    pure k
  -- canonical telescopes
  let defnAcls := (calleeKits.flatMap (·.defnHyps) ++ [selfAcl]).eraseDups
  let own := usedBuiltins selfAcl inp.body
  let builtinAcls := (builtinTwins.map (·.1)).filter fun b =>
    own.contains b || calleeKits.any (·.builtinHyps.contains b)
  -- statement pieces per defn hyp: (symC, formalCs, bodyC)
  let defnMeta ← defnAcls.mapM fun a => do
    if a == selfAcl then
      pure (inp.symName, inp.formalNames.toList, inp.bodyName)
    else
      let some k := findKit env a
        | throwError "derive_exec% corr: internal — {a} unregistered"
      pure (k.symC, k.formalCs, k.bodyC)
  let wId := mkIdent `w
  let defnHypIds := defnAcls.map fun a =>
    mkIdent (Name.mkSimple s!"h_{hypSuffix a}")
  let builtinHypIds := builtinAcls.map fun b =>
    mkIdent (Name.mkSimple s!"h_no_{hypSuffix b}")
  ensureDistinct "hypothesis binder"
    (defnHypIds.toArray ++ builtinHypIds.toArray)
  let sexprTy : Term := mkCIdent ``ACL2.SExpr
  let symTy : Term := mkCIdent ``ACL2.Symbol
  -- hypothesis binders
  let defnBinders ← (defnHypIds.zip defnMeta).mapM
    fun (hId, sC, fCs, bC) => do
      let fIds := (fCs.map mkCIdent).toArray
      `(bracketedBinderF| ($hId:ident :
          ($wId).defs.get? $(mkCIdent sC)
            = some ([$[$fIds],*], $(mkCIdent bC))))
  let builtinBinders ← (builtinAcls.zip builtinHypIds).mapM
    fun (b, hId) => do
      let bLit := Syntax.mkStrLit b
      `(bracketedBinderF| ($hId:ident :
          ($wId).defs.get? ({ name := $bLit } : $symTy) = none))
  -- conclusion: ∀ env aᵢ vᵢ, ConvTo … → ConvTo w env (fn a…) (Exec v…)
  let n := inp.formalSyms.size
  let envId := mkIdent `env
  let aIds := inp.formalSyms.map fun s =>
    mkIdent (Name.appendAfter `a s!"_{(formalBinderName s.name)}")
  let vIds := inp.formalSyms.map fun s =>
    mkIdent (Name.appendAfter `v s!"_{(formalBinderName s.name)}")
  let convTo : Term := mkCIdent ``ACL2.Replay.ConvTo
  let nilT : Term := mkCIdent ``SExpr.nil
  let appArgs ← aIds.foldrM (init := nilT)
    fun a acc => `($(mkCIdent ``SExpr.cons) $a $acc)
  let appT ← `($(mkCIdent ``SExpr.cons)
      ($(mkCIdent ``SExpr.atom) ($(mkCIdent ``Atom.symbol)
        $(mkCIdent inp.symName))) $appArgs)
  let execApp := Syntax.mkApp inp.execId (vIds.map (fun i => (i : Term)))
  let concl ← `($convTo $wId $envId $appT $execApp)
  let stmtCore ← (aIds.zip vIds).foldrM (init := concl) fun (a, v) acc =>
    `($convTo $wId $envId $a $v → $acc)
  let allIds := aIds ++ vIds
  let stmt ← `(∀ ($envId:ident : $(mkCIdent ``ACL2.Env))
      ($[$allIds:ident]* : $sexprTy), $stmtCore)
  -- proof pieces
  let benvSyms : Array Term := inp.formalNames.map fun n => (mkCIdent n : Term)
  let vTerms := vIds.map (fun i => (i : Term))
  let benv ← `($(mkCIdent ``bindArgs) [$[$benvSyms],*] [$[$vTerms],*])
  -- env-get proof for formal i: i tail steps then head
  let getProof (i : Nat) : CommandElabM Term := do
    let base : Term := mkCIdent ``bindArgs_get_head
    (List.range i).foldlM (init := base) fun acc _ =>
      `(($(mkCIdent ``bindArgs_get_tail) (by decide)).trans $acc)
  let hvIds := inp.formalSyms.map fun s =>
    mkIdent (Name.appendAfter `hv s!"_{(formalBinderName s.name)}")
  let hvHaves ← (Array.range n).mapM fun i => do
    let gp ← getProof i
    `(tactic| have $(hvIds[i]!):ident := $(mkCIdent ``re_val_var_get)
        $wId $benv $(mkCIdent inp.formalNames[i]!) $(vIds[i]!) $gp)
  let ihId := mkIdent `ih
  let hnId := mkIdent `hn
  let ctx : CorrCtx :=
    { wId := wId, selfAcl := selfAcl,
      measure := inp.measure,
      formalAcls := inp.formalSyms.map (·.name),
      hvMap := (inp.formalSyms.zip hvIds).toList.map
        fun (s, id) => (s.name, id),
      valMap := (inp.formalSyms.zip vIds).toList.map
        fun (s, id) => (s.name, id),
      defnHypMap := defnAcls.zip defnHypIds,
      builtinHypMap := builtinAcls.zip builtinHypIds,
      execId := inp.execId, ihId := ihId, hnId := hnId }
  let walk ← corrTerm ctx "" inp.body
  let eqDefId : Term :=
    mkCIdent ((← liftTermElabM <|
      realizeGlobalConstNoOverloadWithInfo inp.execId) ++ `eq_def)
  let hbodyId := mkIdent `hbody
  let hbodyGoal ← `($convTo $wId $benv $(mkCIdent inp.bodyName) $execApp)
  let natTy : Term := mkCIdent ``Nat
  let ccT : Term := mkCIdent ``SExpr.consCount
  let (hbodyStmt, hbodyTac) ← do
    match inp.recursive, inp.measure with
    | true, .m1 mIdx => do
      let vm := vIds[mIdx]!
      let others := (vIds.zipIdx.filter (·.2 != mIdx)).map (·.1)
      let stmt ←
        if others.isEmpty then
          `(∀ ($vm:ident : $sexprTy), $hbodyGoal)
        else
          `(∀ ($vm:ident : $sexprTy), ∀ ($[$others:ident]* : $sexprTy),
              $hbodyGoal)
      let motive ←
        if others.isEmpty then
          `(fun $vm:ident => $hbodyGoal)
        else
          `(fun $vm:ident => ∀ ($[$others:ident]* : $sexprTy), $hbodyGoal)
      let introIds := #[vm, ihId] ++ others
      let tac ← `(Lean.Parser.Tactic.tacticSeq|
          refine $(mkCIdent ``consCount_strong_induction) $motive ?_
          intro $[$introIds:ident]*
          $[$hvHaves:tactic]*
          rw [$eqDefId:term]
          exact $walk)
      pure (stmt, tac)
    | true, .m2 i j => do
      -- Nat strong induction over the pair-sum (merge2's shape)
      let nId := mkIdent `n
      let sumT ← `($ccT $(vIds[i]!) + $ccT $(vIds[j]!))
      let stmt ← `(∀ ($nId:ident : $natTy) ($[$vIds:ident]* : $sexprTy),
          $sumT = $nId → $hbodyGoal)
      let introIds := #[nId, ihId] ++ vIds ++ #[hnId]
      let tac ← `(Lean.Parser.Tactic.tacticSeq|
          refine fun $nId:ident => Nat.strong_induction_on $nId ?_
          intro $[$introIds:ident]*
          $[$hvHaves:tactic]*
          rw [$eqDefId:term]
          exact $walk)
      pure (stmt, tac)
    | false, _ => do
      -- plain defs have no equation lemma; delta-unfold instead
      let stmt ← `(∀ ($[$vIds:ident]* : $sexprTy), $hbodyGoal)
      let tac ← `(Lean.Parser.Tactic.tacticSeq|
          intro $[$vIds:ident]*
          $[$hvHaves:tactic]*
          unfold $(mkIdent (inp.execId.getId)):ident
          exact $walk)
      pure (stmt, tac)
  -- closing: conv_defn_N + hbody applied at (measured, others) order
  let hIds := inp.formalSyms.map fun s =>
    mkIdent (Name.appendAfter `h s!"_{(formalBinderName s.name)}")
  let hbodyApp ← do
    match inp.recursive, inp.measure with
    | true, .m1 mIdx =>
      let vm := vIds[mIdx]!
      let others := (vIds.zipIdx.filter (·.2 != mIdx)).map (·.1)
      pure <| Syntax.mkApp hbodyId
        (#[(vm : Term)] ++ others.map (fun i => (i : Term)))
    | true, .m2 i j => do
      let sumT ← `($ccT $(vIds[i]!) + $ccT $(vIds[j]!))
      let rflP ← `(rfl)
      pure <| Syntax.mkApp hbodyId (#[sumT] ++ vTerms ++ #[rflP])
    | false, _ => pure <| Syntax.mkApp hbodyId vTerms
  let some hSelfId := (defnAcls.zip defnHypIds).lookup selfAcl
    | throwError "derive_exec% corr: internal — self defn hyp missing"
  let closing ← mkConvDefn wId n (hIds.map (fun i => (i : Term))).toList
    hSelfId hbodyApp
  let introIds := #[envId] ++ aIds ++ vIds ++ hIds
  let proof ← `(by
      have $hbodyId:ident : $hbodyStmt := by $hbodyTac
      intro $[$introIds:ident]*
      exact $closing)
  let allBinders := defnBinders.toArray ++ builtinBinders.toArray
  let thm ← `(theorem $corrId ($wId:ident : $(mkCIdent ``ACL2.World))
      $allBinders* : $stmt := $proof)
  elabCommand thm
  return (defnAcls, builtinAcls)

syntax corrClause := &" corr " ident

syntax (name := deriveExecCmd)
  (docComment)? "derive_exec% " ident (corrClause)? " for " ident
  &" formals " "[" ident,* "]" &" body " ident
  (&" measured " num (num)?)? : command

/-- `derive_exec% <execName> [corr <corrName>] for <symConst> formals
    [<symConsts>] body <bodyConst> measured <i>` — generate the M1 exec
    def (+ optionally the stage-1 corr theorem) and register the kit.
    `measured i` is the 0-based index of the measured formal (from the
    emitted `:MEASURE (ACL2-COUNT <formal_i>)`). -/
@[command_elab deriveExecCmd] def elabDeriveExec : CommandElab := fun stx => do
    -- raw destructuring (two optional groups defeat the quotation-pattern
    -- lifter): [0] doc? [1] atom [2] exec [3] corrClause? [4] for [5] sym
    -- [6] formals [7] "[" [8] formal idents [9] "]" [10] body [11] bodyC
    -- [12] measured [13] num
    let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
      if stx[0].getNumArgs > 0 then some ⟨stx[0][0]⟩ else none
    let execId : Ident := ⟨stx[2]⟩
    let corrId? : Option Ident :=
      if stx[3].getNumArgs > 0 then some ⟨stx[3][0][1]⟩ else none
    let symId : Ident := ⟨stx[5]⟩
    let formalIds : Array Ident := stx[8].getSepArgs.map (⟨·⟩)
    let bodyId : Ident := ⟨stx[11]⟩
    -- optional measured clause: [12] is a null node wrapping
    -- (atom " measured ") num (num)?
    let measured? : Option (Nat × Option Nat) ← do
      if stx[12].getNumArgs == 0 then pure none
      else
        -- the optional group flattens: [0] atom " measured " [1] num
        -- [2] (num)?
        let mstx := stx[12]
        let some idxN := mstx[1].isNatLit?
          | throwError "derive_exec%: measured index must be a numeral"
        let idx2? : Option Nat :=
          if mstx[2].getNumArgs > 0 then mstx[2][0].isNatLit? else none
        pure (some (idxN, idx2?))
    let symName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo symId
    let bodyName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo bodyId
    let formalNames ← formalIds.mapM fun fid =>
      liftTermElabM <| realizeGlobalConstNoOverloadWithInfo fid
    -- evaluate the symbol/body constants (compiled defs in scope)
    let sym ← liftTermElabM <| unsafe evalExpr Symbol
      (mkConst ``ACL2.Symbol) (mkConst symName)
    let body ← liftTermElabM <| unsafe evalExpr SExpr
      (mkConst ``ACL2.SExpr) (mkConst bodyName)
    let formalSyms ← formalNames.mapM fun fn =>
      liftTermElabM <| unsafe evalExpr Symbol
        (mkConst ``ACL2.Symbol) (mkConst fn)
    -- F4b: the clause is a fidelity claim about the emitted :MEASURE —
    -- required exactly when the defun recurses
    let sitesEarly := selfCallSites sym.name body
    let measure : MeasureSpec ← do
      match measured?, sitesEarly.isEmpty with
      | some _, true =>
        throwError "derive_exec%: 'measured' supplied but {sym.name} is \
            non-recursive (no emitted :MEASURE — drop the clause)"
      | none, false =>
        throwError "derive_exec%: {sym.name} recurses but no 'measured' \
            clause was given (transcribe the emitted :MEASURE)"
      | none, true => pure (.m1 0)  -- unused: no sites, no measure
      | some (i, j?), false => pure (match j? with
        | some j => .m2 i j
        | none => .m1 i)
    let idxOk (k : Nat) : CommandElabM Unit := do
      unless k < formalSyms.size do
        throwError "derive_exec%: measured index {k} out of range \
            ({formalSyms.size} formals)"
    match measure with
    | .m1 k => idxOk k
    | .m2 k l => do idxOk k; idxOk l
    -- binder idents, in formal order
    let binderIds : Array Ident := formalSyms.map fun s =>
      mkIdent (formalBinderName s.name)
    ensureDistinct "formal binder" binderIds
    let formalMap : List (String × Ident) :=
      (formalSyms.zip binderIds).toList.map fun (s, id) => (s.name, id)
    -- measure-class validation of every self-call site, producing the
    -- decreasing_by script per site
    let sites := selfCallSites sym.name body
    let mut scripts : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[]
    for site in sites do
      unless site.length == formalSyms.size do
        throwError "derive_exec%: self-call arity {site.length} ≠ \
            {formalSyms.size}"
      match measure with
      | .m1 i => do
        -- M1: the measured argument is a destructor chain over the
        -- measured formal
        let measuredAcl := formalSyms[i]!.name
        let some (chain, v) := destructorChain site[i]!
          | throwError "derive_exec%: measured argument {repr site[i]!} \
              is not a destructor chain (M3 frontier — hand-write this \
              kit)"
        unless v == measuredAcl do
          throwError "derive_exec%: measured argument descends {v}, not \
              the measured formal {measuredAcl} (frontier)"
        scripts := scripts.push (← decreaseScript chain)
      | .m2 i j => do
        -- M2: exactly one measured side descends by a single CDR, the
        -- other is the bare formal
        let lemName ←
          match destructorChain site[i]!, destructorChain site[j]! with
          | some (["CDR"], fi), some ([], fj) => do
            unless fi == formalSyms[i]!.name && fj == formalSyms[j]!.name do
              throwError "derive_exec%: M2 site formals mismatch"
            pure ``consCount_cdr_sum_lt_left_consp
          | some ([], fi), some (["CDR"], fj) => do
            unless fi == formalSyms[i]!.name && fj == formalSyms[j]!.name do
              throwError "derive_exec%: M2 site formals mismatch"
            pure ``consCount_cdr_sum_lt_right_consp
          | _, _ =>
            throwError "derive_exec%: M2 site {repr site} is not a \
                single-CDR one-side decrease (frontier — hand-write this \
                kit)"
        let pf ← `($(mkCIdent lemName) (by assumption))
        scripts := scripts.push
          (← `(Lean.Parser.Tactic.tacticSeq| exact $pf))
    let bodyS ← execTerm sym.name execId formalMap body
    let sexprTy : Term := mkCIdent ``ACL2.SExpr
    let binders ← binderIds.mapM fun id =>
      `(bracketedBinderF| ($id:ident : $sexprTy))
    let cmd ← do
      if sites.isEmpty then
        -- non-recursive defun: a plain def, no measure
        `($[$doc?:docComment]? def $execId $binders* : $sexprTy := $bodyS)
      else do
        let measT ← match measure with
          | .m1 i => `($(mkCIdent ``SExpr.consCount) $(binderIds[i]!))
          | .m2 i j =>
            `($(mkCIdent ``SExpr.consCount) $(binderIds[i]!)
                + $(mkCIdent ``SExpr.consCount) $(binderIds[j]!))
        `($[$doc?:docComment]? def $execId $binders* : $sexprTy := $bodyS
          termination_by $measT
          decreasing_by all_goals first $[| $scripts]*)
    elabCommand cmd
    let inp : KitInput :=
      { execId := execId, symName := symName, bodyName := bodyName,
        formalNames := formalNames, sym := sym, body := body,
        formalSyms := formalSyms, measure := measure,
        recursive := !sites.isEmpty }
    -- corr (optional clause)
    let (corrName, defnAcls, builtinAcls) ←
      match corrId? with
      | some corrId => do
        let (d, b) ← genCorr inp corrId
        let cn ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo corrId
        pure (cn, d, b)
      | none => pure (Name.anonymous, [], [])
    -- register
    let execName ← liftTermElabM <|
      realizeGlobalConstNoOverloadWithInfo execId
    registerKit
      { aclName := sym.name, execName := execName,
        arity := formalSyms.size, corrName := corrName,
        symC := symName, formalCs := formalNames.toList,
        bodyC := bodyName, defnHyps := defnAcls,
        builtinHyps := builtinAcls }

/-! ## Discharger generation (1c)

`dis_<fn>_total` and the `dis_<fn>_tp` WRAPPER are mechanical given the
registered kit (docs/notes/2026-07-31_mirror-industrialization.md §2):
totality = corr + one witness triple; tp = argument strictness
(`conv_argsN_of_conv_app`) + corr + `val_unique`, then a HUMAN ending
(the value-shape argument — the fidelity-bearing part). Contract for the
tp ending: the argument-value binders are named `u0 … u(n-1)` and the
goal is the conclusion with `v` rewritten to `<fn>Exec u0 …`. -/

/-- Rebuild a registered kit's hypothesis telescope (binders + binder
    idents for application) from the registry. Every defn-hyp name must
    itself be registered with statement metadata. -/
def telescopeOfKit (kit : KitInfo) (wId : Ident) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
      × Array Ident) := do
  let env ← getEnv
  let symTy : Term := mkCIdent ``ACL2.Symbol
  let mut binders := #[]
  let mut hypIds := #[]
  for a in kit.defnHyps do
    let some k := findKit env a
      | throwError "discharger generation: defn hyp {a} unregistered"
    if k.symC == .anonymous then
      throwError "discharger generation: {a} registered without statement \
          metadata"
    let hId := mkIdent (Name.mkSimple s!"h_{hypSuffix a}")
    let fIds := (k.formalCs.map mkCIdent).toArray
    binders := binders.push <| ← `(bracketedBinderF| ($hId:ident :
        ($wId).defs.get? $(mkCIdent k.symC)
          = some ([$[$fIds],*], $(mkCIdent k.bodyC))))
    hypIds := hypIds.push hId
  for b in kit.builtinHyps do
    let hId := mkIdent (Name.mkSimple s!"h_no_{hypSuffix b}")
    let bLit := Syntax.mkStrLit b
    binders := binders.push <| ← `(bracketedBinderF| ($hId:ident :
        ($wId).defs.get? ({ name := $bLit } : $symTy) = none))
    hypIds := hypIds.push hId
  ensureDistinct "hypothesis binder" hypIds
  return (binders, hypIds)

/-- Shared discharger scaffolding: kit lookup + arg idents + the
    application term. -/
def dischargerParts (aclName : String) (wId : Ident) :
    CommandElabM (KitInfo
      × Array (TSyntax ``Lean.Parser.Term.bracketedBinder) × Array Ident
      × Array Ident × Term) := do
  let some kit := findKit (← getEnv) aclName
    | throwError "discharger generation: {aclName} is not a registered kit"
  if kit.corrName == .anonymous then
    throwError "discharger generation: {aclName} has no registered corr"
  let (binders, hypIds) ← telescopeOfKit kit wId
  let aIds := (Array.range kit.arity).map fun i =>
    mkIdent (Name.mkSimple s!"a{i}")
  let nilT : Term := mkCIdent ``SExpr.nil
  let appArgs ← aIds.foldrM (init := nilT)
    fun a acc => `($(mkCIdent ``SExpr.cons) $a $acc)
  let appT ← `($(mkCIdent ``SExpr.cons)
      ($(mkCIdent ``SExpr.atom) ($(mkCIdent ``Atom.symbol)
        $(mkCIdent kit.symC))) $appArgs)
  return (kit, binders, hypIds, aIds, appT)

syntax (name := deriveExecTotalCmd)
  (docComment)? "derive_exec_total% " ident " for " str : command

/-- `derive_exec_total% <name> for "<ACL2-NAME>"` — the driver-shape
    totality discharger from the registered kit's corr: converging
    arguments make the application converge (witness: the exec value). -/
@[command_elab deriveExecTotalCmd] def elabDeriveExecTotal : CommandElab :=
  fun stx => do
    let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
      if stx[0].getNumArgs > 0 then some ⟨stx[0][0]⟩ else none
    let name : Ident := ⟨stx[2]⟩
    let some acl := stx[4].isStrLit?
      | throwError "derive_exec_total%: expected a string literal"
    let wId := mkIdent `w
    let (kit, binders, hypIds, aIds, appT) ← dischargerParts acl wId
    let envId := mkIdent `env'
    let sexprTy : Term := mkCIdent ``ACL2.SExpr
    let evalT : Term := mkCIdent ``ACL2.evalOpt
    let fId := mkIdent `f
    let nId := mkIdent `N
    let vId := mkIdent `v
    let convOf (t : Term) : CommandElabM Term :=
      `(∃ $nId:ident, ∃ $vId:ident, ∀ $fId:ident ≥ $nId,
          $evalT $fId $wId $envId $t = some $vId)
    let concl ← convOf appT
    let stmtCore ← aIds.foldrM (init := concl) fun a acc => do
      `($(← convOf a) → $acc)
    let stmt ← `(∀ ($envId:ident : $(mkCIdent ``ACL2.Env))
        ($[$aIds:ident]* : $sexprTy), $stmtCore)
    -- intro patterns ⟨Ni, vi, hi⟩ per argument
    let triples ← (Array.range kit.arity).mapM fun i => do
      let n := mkIdent (Name.mkSimple s!"N{i}")
      let v := mkIdent (Name.mkSimple s!"v{i}")
      let h := mkIdent (Name.mkSimple s!"h{i}")
      pure (n, v, h)
    let introPats : Array (TSyntax `term) ← triples.mapM
      fun (n, v, h) => `(⟨$n, $v, $h⟩)
    let corrArgs : Array Term :=
      #[(wId : Term)] ++ hypIds.map (fun i => (i : Term))
      ++ #[(envId : Term)] ++ aIds.map (fun i => (i : Term))
      ++ triples.map (fun (_, v, _) => (v : Term))
    let corrConvs ← triples.mapM fun (n, _, h) => `(⟨$n, $h⟩)
    let corrApp := Syntax.mkApp (mkCIdent kit.corrName)
      (corrArgs ++ corrConvs)
    let execApp := Syntax.mkApp (mkCIdent kit.execName)
      (triples.map fun (_, v, _) => (v : Term))
    let hId := mkIdent `h
    let proof ← `(by
        intro $envId:ident $[$aIds:ident]* $[$introPats:term]*
        obtain ⟨$nId, $hId⟩ := $corrApp
        exact ⟨$nId, $execApp, $hId⟩)
    let thm ← `($[$doc?:docComment]? theorem $name
        ($wId:ident : $(mkCIdent ``ACL2.World)) $binders* : $stmt := $proof)
    elabCommand thm

syntax (name := deriveExecTpCmd)
  (docComment)? "derive_exec_tp% " ident " for " str
  " (" ident " => " term ")" &" ending " tacticSeq : command

/-- `derive_exec_tp% <name> for "<ACL2-NAME>" (v => <conclusion>) ending
    <tactics>` — the TP-corollary discharger wrapper: argument strictness
    recovers the argument values `u0 … u(n-1)`, the corr pins the
    application's value to `<fn>Exec u0 …`, `val_unique` rewrites the
    conclusion to it, and the ENDING (human — the value-shape argument)
    closes the goal. -/
@[command_elab deriveExecTpCmd] def elabDeriveExecTp : CommandElab :=
  fun stx => do
    let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
      if stx[0].getNumArgs > 0 then some ⟨stx[0][0]⟩ else none
    let name : Ident := ⟨stx[2]⟩
    let some acl := stx[4].isStrLit?
      | throwError "derive_exec_tp%: expected a string literal"
    let vBind : Ident := ⟨stx[6]⟩
    let concl : Term := ⟨stx[8]⟩
    let ending : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[11]⟩
    let wId := mkIdent `w
    let (kit, binders, hypIds, aIds, appT) ← dischargerParts acl wId
    let envId := mkIdent `e'
    let sexprTy : Term := mkCIdent ``ACL2.SExpr
    let evalT : Term := mkCIdent ``ACL2.evalOpt
    let fId := mkIdent `f
    let nId := mkIdent `N
    let hId := mkIdent `h
    let hypT ← `(∃ $nId:ident, ∀ $fId:ident ≥ $nId,
        $evalT $fId $wId $envId $appT = some $vBind)
    -- strictness obtain pattern + corr application over u0…
    let uTriples ← (Array.range kit.arity).mapM fun i => do
      pure (mkIdent (Name.mkSimple s!"N{i}"),
            mkIdent (Name.mkSimple s!"u{i}"),
            mkIdent (Name.mkSimple s!"h{i}"))
    let uPats : Array (TSyntax `rcasesPat) ← uTriples.mapM
      fun (n, u, h) => `(rcasesPat| ⟨$n, $u, $h⟩)
    let obtainPat ← match kit.arity with
      | 1 => pure uPats[0]!
      | 2 => `(rcasesPat| ⟨$(uPats[0]!), $(uPats[1]!)⟩)
      | 3 => `(rcasesPat| ⟨$(uPats[0]!), $(uPats[1]!), $(uPats[2]!)⟩)
      | n => throwError "derive_exec_tp%: arity {n} beyond \
          conv_args3_of_conv_app (frontier)"
    let convArgsLemma := match kit.arity with
      | 1 => ``conv_args1_of_conv_app
      | 3 => ``conv_args3_of_conv_app
      | _ => ``conv_args2_of_conv_app
    let nsP ← `((by decide))
    let strictApp := Syntax.mkApp (mkCIdent convArgsLemma)
      (#[(wId : Term), (envId : Term), (mkCIdent kit.symC : Term)]
        ++ aIds.map (fun i => (i : Term))
        ++ #[(vBind : Term), nsP, (hId : Term)])
    let corrArgs : Array Term :=
      #[(wId : Term)] ++ hypIds.map (fun i => (i : Term))
      ++ #[(envId : Term)] ++ aIds.map (fun i => (i : Term))
      ++ uTriples.map (fun (_, u, _) => (u : Term))
    let corrConvs ← uTriples.mapM fun (n, _, h) => `(⟨$n, $h⟩)
    let corrApp := Syntax.mkApp (mkCIdent kit.corrName)
      (corrArgs ++ corrConvs)
    let happId := mkIdent `happ
    let vuApp := Syntax.mkApp (mkCIdent ``val_unique)
      #[(hId : Term), (happId : Term)]
    let proof ← `(by
        obtain $obtainPat:rcasesPat := $strictApp
        have $happId:ident := $corrApp
        rw [$vuApp:term]
        ($ending))
    let thm ← `($[$doc?:docComment]? theorem $name
        ($wId:ident : $(mkCIdent ``ACL2.World)) $binders*
        ($envId:ident : $(mkCIdent ``ACL2.Env))
        ($[$aIds:ident]* $vBind:ident : $sexprTy)
        ($hId:ident : $hypT) : $concl := $proof)
    elabCommand thm

syntax (name := registerExecKitCmd)
  "register_exec_kit% " str " => " ident &" arity " num : command

/-- Register a HAND-WRITTEN exec kit (M3 measures — msort, qsort, evens'
    callers) so generated callers can reference it. -/
@[command_elab registerExecKitCmd] def elabRegisterExecKit : CommandElab :=
  fun stx => do
    match stx with
    | `(register_exec_kit% $acl:str => $execId:ident arity $n:num) => do
      let execName ← liftTermElabM <|
        realizeGlobalConstNoOverloadWithInfo execId
      registerKit
        { aclName := acl.getString, execName := execName,
          arity := n.getNat }
    | _ => throwUnsupportedSyntax

end ACL2.ExecGen
