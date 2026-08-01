/-
  THE EXEC-KIT GENERATOR (sorting-absolute arc 1b — the dominant
  industrialization item, docs/notes/2026-07-31_mirror-industrialization.md §1).

  `derive_exec%` mechanically emits, for one world defun, the shape-exact
  total Lean function that was previously hand-written per kit:

  - `<fn>Exec` — a pure syntax walk over the body (`IF` → `ite` on
    `Logic.toBool`, builtin call → the `Logic.*` twin, self call →
    recursion, defn call → the callee's registered exec), termination from
    the measure class (M1: `consCount` of the measured formal, destructor
    chains under a ruling CONSP test) with decreases discharged by the
    Count library.

  The generator's input body is the in-scope body CONSTANT (the same one
  the kit hypotheses mention); fidelity to the emitted `:DEFUN` is enforced
  exactly as for the hand kits — the `by decide` world facts at every
  consumer pin the constant to the log-derived world at build time.
  (Log-side extraction of the body constants is the v2 companion, with the
  ACL2 quotation macro — note §5.)

  `<fn>Exec_enc` (the NATIVE reading) is deliberately NOT generated: the
  choice of native counterpart is the mirror criterion's human fidelity
  judgment. The stage-1 `_exec_corr` generation is the next increment of
  this sub-arc.

  VALIDATION PROTOCOL (the arc charter's 1b clause): the generator is
  validated by RETIREMENT — each hand kit's def is replaced by a generator
  invocation emitting the SAME NAME, so every existing consumer (the hand
  corr proofs first of all, then assemblies, dischargers, `_enc` lemmas,
  golden mirrors) re-elaborates against the generated artifact. A generated
  def that diverges from the hand shape breaks its consumers — the build is
  the gate. No kit is generated "for later".

  Fail-closed throughout: an unknown head symbol, a free variable, a
  recursion site whose measured argument is not a destructor chain over the
  measured formal, or a measure shape outside v1 (M3: decrease through a
  defined function — msort's EVENS, qsort's FILTER) is a HARD elaboration
  error naming the frontier; those kits stay hand-written.
-/
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Imported.Lifting

namespace ACL2.ExecGen

open ACL2 Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Parser.Term

/-- Registered kit metadata: what a CALLER's generated def (and, next
    increment, corr proof) needs to know about a callee's kit. Populated by
    `derive_exec%` for generated kits and `register_exec_kit%` for the
    hand-written ones (M3 measures). -/
structure KitInfo where
  /-- the ACL2 function name, e.g. "INSERT" -/
  aclName : String
  /-- the exec def's name -/
  execName : Name
  /-- arity (formal count) -/
  arity : Nat
  deriving Inhabited, Repr

initialize execKitExt :
    SimplePersistentEnvExtension KitInfo (List KitInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => e :: s
    addImportedFn := fun ess => (ess.map (·.toList)).toList.flatten
  }

def findKit (env : Environment) (aclName : String) : Option KitInfo :=
  (execKitExt.getState env).find? (·.aclName == aclName)

/-- The builtin twin table: ACL2 builtin name → the `Logic`-level Lean
    function of the same semantics (the exec def calls the twin; the corr
    side will discharge `callBuiltin name [..] = some (twin ..)` by `rfl`).
    Extending to a new builtin is one row. Fail-closed: a head symbol not
    here, not IF/QUOTE, not the self/registered-callee set, is a hard
    error. -/
def builtinTwins : List (String × Name × Nat) :=
  [ ("CONSP",    ``Logic.consp, 1),
    ("CAR",      ``Logic.car, 1),
    ("CDR",      ``Logic.cdr, 1),
    ("CONS",     ``Logic.cons, 2),
    ("LEXORDER", ``lexorder, 2),
    ("EQUAL",    ``Logic.equal, 2),
    ("BINARY-+", ``Logic.plus, 2) ]

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

/-- Lean binder name for an ACL2 formal ("E" ⇒ `e`, "ACC-X" ⇒ `acc_x`). -/
def formalBinderName (aclVar : String) : Name :=
  Name.mkSimple <| aclVar.toLower.map fun c => if c == '-' then '_' else c

/-- The exec-def body walk: emitted `:BODY` syntax → the total Lean
    function's term syntax. Fail-closed on every unrecognized shape. -/
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
      | some (_, twin, ar) => do
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

/-- The M1 decrease script for one recursion site: the measured argument's
    destructor chain `[d₁, …, dₖ]` (outermost first) becomes
    `lt_of_le_of_lt (consCount_d₁_le _) (… (consCount_dₖ_lt_of_consp (by
    assumption)))` — k−1 `le` links and the innermost `lt` at the
    CONSP-ruled variable. -/
def decreaseScript (chain : List String) :
    CommandElabM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let lastLemma (d : String) : Name :=
    if d == "CDR" then ``consCount_cdr_lt_of_consp
    else ``consCount_car_lt_of_consp
  let leLemma (d : String) : Name :=
    if d == "CDR" then ``consCount_cdr_le else ``consCount_car_le
  match chain.reverse with
  | [] => throwError "derive_exec%: recursion site with an EMPTY destructor \
      chain (the measured argument is the formal itself — no decrease)"
  | dInner :: dsOuterRev => do
    let base ← `($(mkCIdent (lastLemma dInner)) (by assumption))
    let proof ← dsOuterRev.foldlM (init := base) fun acc d =>
      `(lt_of_le_of_lt ($(mkCIdent (leLemma d)) _) $acc)
    `(Lean.Parser.Tactic.tacticSeq| exact $proof)

syntax (name := deriveExecCmd)
  (docComment)? "derive_exec% " ident " for " ident &" formals "
  "[" ident,* "]" &" body " ident &" measured " num : command

/-- `derive_exec% <execName> for <symConst> formals [<symConsts>] body
    <bodyConst> measured <i>` — generate the M1 exec def and register the
    kit. `measured i` is the 0-based index of the measured formal (from the
    emitted `:MEASURE (ACL2-COUNT <formal_i>)`). -/
@[command_elab deriveExecCmd] def elabDeriveExec : CommandElab := fun stx => do
  match stx with
  | `($[$doc?:docComment]? derive_exec% $execId:ident for $symId:ident
        formals [$formalIds:ident,*] body $bodyId:ident
        measured $idx:num) => do
    let symName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo symId
    let bodyName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo bodyId
    let formalNames ← formalIds.getElems.mapM fun fid =>
      liftTermElabM <| realizeGlobalConstNoOverloadWithInfo fid
    -- evaluate the symbol/body constants (compiled defs in scope)
    let sym ← liftTermElabM <| unsafe evalExpr Symbol
      (mkConst ``ACL2.Symbol) (mkConst symName)
    let body ← liftTermElabM <| unsafe evalExpr SExpr
      (mkConst ``ACL2.SExpr) (mkConst bodyName)
    let formalSyms ← formalNames.mapM fun fn =>
      liftTermElabM <| unsafe evalExpr Symbol
        (mkConst ``ACL2.Symbol) (mkConst fn)
    let i := idx.getNat
    unless i < formalSyms.size do
      throwError "derive_exec%: measured index {i} out of range \
          ({formalSyms.size} formals)"
    -- binder idents, in formal order
    let binderIds : Array Ident := formalSyms.map fun s =>
      mkIdent (formalBinderName s.name)
    let formalMap : List (String × Ident) :=
      (formalSyms.zip binderIds).toList.map fun (s, id) => (s.name, id)
    -- M1 validation: every self-call's measured argument is a destructor
    -- chain over the measured formal; other arguments are unrestricted.
    let measuredAcl := formalSyms[i]!.name
    let sites := selfCallSites sym.name body
    let mut chains : List (List String) := []
    for site in sites do
      unless site.length == formalSyms.size do
        throwError "derive_exec%: self-call arity {site.length} ≠ \
            {formalSyms.size}"
      let some (chain, v) := destructorChain site[i]!
        | throwError "derive_exec%: measured argument {repr site[i]!} is \
            not a destructor chain (M3 frontier — hand-write this kit)"
      unless v == measuredAcl do
        throwError "derive_exec%: measured argument descends {v}, not the \
            measured formal {measuredAcl} (frontier)"
      chains := chains ++ [chain]
    let bodyS ← execTerm sym.name execId formalMap body
    let measuredId := binderIds[i]!
    let sexprTy : Term := mkCIdent ``ACL2.SExpr
    let binders ← binderIds.mapM fun id =>
      `(bracketedBinderF| ($id:ident : $sexprTy))
    let cmd ← do
      if sites.isEmpty then
        -- non-recursive defun: a plain def, no measure
        `($[$doc?:docComment]? def $execId $binders* : $sexprTy := $bodyS)
      else do
        let scripts := (← chains.mapM decreaseScript).toArray
        let measT ← `($(mkCIdent ``SExpr.consCount) $measuredId)
        `($[$doc?:docComment]? def $execId $binders* : $sexprTy := $bodyS
          termination_by $measT
          decreasing_by all_goals first $[| $scripts]*)
    elabCommand cmd
    -- register
    let execName ← liftTermElabM <|
      realizeGlobalConstNoOverloadWithInfo execId
    modifyEnv fun env => execKitExt.addEntry env
      { aclName := sym.name, execName := execName,
        arity := formalSyms.size }
  | _ => throwUnsupportedSyntax

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
      modifyEnv fun env => execKitExt.addEntry env
        { aclName := acl.getString, execName := execName, arity := n.getNat }
    | _ => throwUnsupportedSyntax

end ACL2.ExecGen
