/-
  THE ISO-LAYER GENERATOR — `derive_sim%` (mirror-closeout charter item 2;
  ruled in `docs/notes/2026-08-11_thin-lean-boundary.md` §1).

  `derive_exec%` (Imported/ExecGen.lean) generates the two ACL2-side
  artifacts of a waypoint-consumed defun — the shape-exact `<fn>Exec` and the
  stage-1 `<fn>_exec_corr`. This module generates the THIRD, the stage-2
  ISO (`<fn>Exec_enc`): `fooExec (enc xs) = <reading> (fooL xs)`.

  WHY IT MUST BE GENERATED (the thin-Lean ruling). The iso layer is P3
  content — a statement about Lean objects that ACL2 cannot state, so
  there is nothing to replay. UNLIKE P1/P2, P3 has no intrinsic bound on
  proof difficulty: it is the drift channel. A hand `_enc` proof can
  therefore smuggle in content ACL2 proves (a rev/append reassociation,
  say) while looking like plumbing. The gate is TEMPLATE FAILURE AS A HARD
  ERROR: the user supplies only the native reading (the fidelity
  judgment) and the macro proves the iso by ONE FIXED SCRIPT. If that
  script does not close the goal, the chosen native reading does not
  align with the exec's recursion — a hand correspondence would carry
  ACL2-derivable content — and the elaboration HARD-FAILS. The legal
  escape is an ACL2 book theorem for the bridging fact, routed through
  replay; never a hand proof.

  THREAT MODEL (two-standard rule, 2026-08-11): the template gate is a
  speedbump, not a content classifier. Its discriminating power is
  bounded by the closer's fixed lemma set: a reassociating reading
  whose bridging fact sits in Lean's DEFAULT simp/grind set (e.g.
  reverse_append) closes and therefore PASSES — known, accepted.
  THE VOCABULARY RULE (Mike, 2026-08-13 — resolving probe P1, which
  found `induct structural … generalizing` + a LIBRARY-vocabulary
  reading (xs.reverse ++ acc) closable by default-simp lemmas ABOUT
  THOSE LIBRARY NAMES): a native reading is an OWN-DEFINITION — its
  body built from constructors and our own functions, NEVER library
  functions — the same self-contained-vocabulary discipline the
  mirror spec layer already carries, extended down to waypoint
  readings. Under the rule the leak is unrepresentable: no library
  lemma exists about our names, so the template fails closed
  regardless of induct clause. MEASURED SCOPE (exit audit
  2026-08-13, correcting this note's earlier over-claim): FIVE
  pre-existing readings do NOT comply — Perm.lean's contains/erase/
  isPerm readings, Sorting.lean's count and append readings — and
  THIS module's closer (default simp_all + grind) is exactly the
  vocabulary-dependent lane, so the rule binds FORWARD and those
  five were a logged compliance pass (TODO). FOUR REMAIN: the
  HOW-MANY reading was converted to an own-definition
  (`Worlds.Sorting.howManyL`, ruling 2026-08-14 — it had surfaced in
  a mirror-square residual as `List.count_cons`); Perm.lean's
  contains/erase/isPerm and Sorting.lean's append readings are still
  library-spelled. The three shipped
  MIRRORS are unaffected (their glue verified content-free at the
  exit audit). The newer mirror_iso% lane is leak-free by its
  CLOSED ladder regardless of vocabulary. Enforcement remains
  expectations, reviewable in the def body at a glance. DO
  NOT HARDEN IT — no semantic classifiers, no lemma-set audits; the
  per-book-family provenance audit is the backstop.

  THE ONE TEMPLATE (measured off the 14 hand isos it retires, see the
  charter-item report): drive the induction off the NATIVE's own
  recursion, unfold ONE exec step, normalize to enc-normal form, close.

      <induction on the native> <;> rw [<fn>Exec.eq_def] <;> sim_iso_close [...]

  The observed T1 (aligned structural recursion) and T2 (measure change:
  the native recurses on `List.length`, the exec on `consCount`) collapse
  into this single script — `fun_induction <nativeL>` supplies exactly the
  induction hypotheses of the native's own recursion, whatever its
  measure, and the alignment check is "does one exec step land on them".

  CALLEE RESOLUTION is through the SAME kit registry `derive_exec%` uses:
  the callees of `<fn>Exec` are read off the compiled exec itself
  (transitively through its own satellites), looked up in the registry,
  and their registered `_enc` theorems join the rewrite set. This resolves
  CROSS-FILE as well as in-file (audit F1 fixed the imported-entry order
  that used to hand a downstream module the pre-iso copy of every kit).
  A callee whose exec carries no iso at all — a kit whose reading is a
  declared `simp` lemma rather than a generated `_enc` (e.g.
  `toBool_relExec` for the REL dispatch) — supplies its bridge through
  the invocation's `simp [...]` list; that is the MANUAL OVERRIDE route,
  not a licence to skip a registered iso.

  NAMED HARD FRONTIERS (each a hard elaboration error naming itself, in
  `derive_exec%`'s style): mutual recursion (exec or native), a result
  reading outside the derived table (`enc` / `boolEnc` / `intRep` /
  t-nil / the RAW ELEMENT reading), a noncomputable native, an
  unregistered exec kit, an arity or binder mismatch.

  VALIDATION BY RETIREMENT (the charter's protocol): every hand `_enc` in
  `Imported/Sorting.lean` and `Imported/Perm.lean` is replaced by a
  `derive_sim%` invocation emitting the SAME NAME and the SAME STATEMENT,
  so every consumer re-elaborates against the generated theorem. The
  build is the gate.
-/
import ACL2Lean.Imported.ExecGen

namespace ACL2.SimGen

open ACL2 ACL2.Lifting ACL2.ExecGen Lean Lean.Meta Lean.Elab
  Lean.Elab.Command Lean.Parser.Term

/-! ## The enc-normal-form rewrite kit

The script keeps encoded lists in `enc <list>` form throughout — that is
what lets a callee's `_enc` and the induction hypotheses match after one
exec step (expanding `enc` to raw `SExpr.cons` destroys exactly those
matches). Each lemma below reduces one `Logic` destructor/constructor
against an `enc`; the script disables the `Logic.*` simp-defs so these
control the normal form. -/

theorem enc_cdr (l : List SExpr) : Logic.cdr (enc l) = enc l.tail := by
  cases l <;> rfl

theorem enc_car (a : SExpr) (l : List SExpr) :
    Logic.car (enc (a :: l)) = a := rfl

theorem enc_car_nil : Logic.car (enc ([] : List SExpr)) = SExpr.nil := rfl

theorem enc_toBool_consp (l : List SExpr) :
    Logic.toBool (Logic.consp (enc l)) = !l.isEmpty := by cases l <;> rfl

theorem enc_consp_cons (a : SExpr) (l : List SExpr) :
    Logic.consp (enc (a :: l)) = SExpr.t := rfl

theorem enc_consp_nil :
    Logic.consp (enc ([] : List SExpr)) = SExpr.nil := rfl

theorem enc_cons (a : SExpr) (l : List SExpr) :
    Logic.cons a (enc l) = enc (a :: l) := rfl

theorem enc_cons_nil (a : SExpr) : Logic.cons a SExpr.nil = enc [a] := rfl

theorem enc_nil : enc ([] : List SExpr) = SExpr.nil := rfl

theorem toBool_cond_t_nil (b : Bool) :
    Logic.toBool (bif b then SExpr.t else SExpr.nil) = b := by cases b <;> rfl

/-! ## The closing ladder

FIXED for every invocation — this is the template whose failure is the
ruled gate. It alternates enc-normal-form simplification with case
splitting until neither applies, then discharges each residual leaf by
`rfl` / `omega` (the integer readings) / `grind` (the residual
equality-orientation goals: ACL2's `(EQUAL E (CAR X))` compares in the
opposite order from `List.count`/`List.erase`). Nothing here is
per-function: the only per-invocation input is the lemma list, which is
the callee `_enc`s from the registry plus the declared bridges. -/
open Lean.Parser.Tactic in
macro "sim_iso_close" "[" xs:simpLemma,* "]" : tactic =>
  `(tactic|
    ((repeat' (first
        | (simp_all [-Logic.toBool, -Logic.consp, -Logic.car, -Logic.cdr,
              -Logic.cons, -Logic.equal, enc_cdr, enc_car, enc_car_nil,
              enc_toBool_consp, enc_consp_cons, enc_consp_nil, enc_cons,
              enc_cons_nil, enc_nil, toBool_cond_t_nil, toBool_equal,
              boolEnc, $xs,*])
        | split)) <;> (first | rfl | omega | grind)))

/-! ## Callee resolution (through the exec-kit registry) -/

/-- The registered execs a compiled exec calls: the constants used by
    `execName`'s value, following its own satellites (`._unary`, the
    well-founded-recursion helpers) so a WF-compiled body's callees are
    found. Deterministic; `none` for an unknown constant is a hard error
    at the call site. -/
partial def execCallees (env : Environment) (execName : Name) : List Name :=
  go [execName] [] []
where
  go : List Name → List Name → List Name → List Name
  | [], _, out => out.eraseDups
  | c :: rest, seen, out =>
    if seen.contains c then go rest seen out
    else
      match env.find? c with
      | none => go rest (c :: seen) out
      | some ci =>
        let used := (ci.value?.getD ci.type).getUsedConstants.toList
        let (sat, other) := used.partition (execName.isPrefixOf ·)
        go (sat ++ rest) (c :: seen) (other ++ out)

/-! ## The command -/

/-- How one `vars` position of an iso statement is read. -/
inductive SimVarKind where
  /-- a bare `SExpr`, passed to both sides -/
  | raw
  /-- a `List SExpr` that enters the exec under `enc` -/
  | list
  /-- NOT a binder: the position is this fixed `SExpr` literal -/
  | lit (t : Term)

/-- One binder of the iso statement with its READING: `raw` = a bare
    `SExpr` passed to both sides; `list` = a `List SExpr` that enters the
    exec under `enc`; `lit <term>` = NOT a binder at all — the position is
    a fixed SExpr LITERAL (R4 wave 2a, the per-mode FILTER readings: the
    book passes `'LT`/`'GTE` as quoted symbols, and a reading with no
    runtime dispatch is only stateable at ONE such literal). -/
syntax simVarSpec := "(" ident " : " ident (term:max)? ")"

declare_syntax_cat simInductSpec
/-- Induct on the native's own recursion (`fun_induction <native args>`). -/
syntax "functional " term:max : simInductSpec
/-- Induct structurally on a list binder. -/
syntax "structural " ident (" generalizing " ident+)? : simInductSpec

syntax (name := deriveSimCmd)
  (docComment)? "derive_sim% " ident &" for " str
  &" vars " simVarSpec+
  &" exec " "[" ident,* "]"
  &" native " term:max
  &" simp " "[" Lean.Parser.Tactic.simpLemma,* "]"
  &" induct " simInductSpec : command

/-- Generate the stage-2 iso for the registered kit `<ACLNAME>`:

    ```
    derive_sim% <thmName> for "<ACLNAME>"
      vars (x : raw) (xs : list)     -- the binder telescope + readings
      exec [x, xs]                   -- the exec's argument order
      native (<reading term>)        -- parenthesized (term:max)
      simp [<bridges>]               -- native defs + bridge lemmas
      induct <structural|functional> -- last: its idents run to the end
    ```

    The user supplies ONLY the fidelity judgment (which native reads the
    program, and how each argument/result is read) plus the bridge lemmas
    the readings rest on; the statement's left-hand side comes from the
    registry and the proof is the fixed template. -/
@[command_elab deriveSimCmd] def elabDeriveSim : CommandElab := fun stx => do
  -- raw destructuring (mirrors ExecGen's idiom): [0] doc? [1] atom
  -- [2] thm [3] " for " [4] str [5] " vars " [6] varSpecs [7] " exec "
  -- [8] "[" [9] execArgs [10] "]" [11] " native " [12] term
  -- [13] " simp " [14] "[" [15] lemmas [16] "]" [17] " induct "
  -- [18] inductSpec
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs > 0 then some ⟨stx[0][0]⟩ else none
  let thmId : Ident := ⟨stx[2]⟩
  let some aclName := stx[4].isStrLit?
    | throwError "derive_sim%: the ACL2 name must be a string literal"
  let varSpecs := stx[6].getArgs
  let execArgIds : Array Ident := stx[9].getSepArgs.map (⟨·⟩)
  let nativeStx : Term := ⟨stx[12]⟩
  let simpArgs := stx[15].getSepArgs
  let inductStx := stx[18]
  -- the kit (fail-closed: no registry entry = no exec to state an iso for)
  let env ← getEnv
  let some kit := findKit env aclName
    | throwError "derive_sim%: no registered exec kit for {aclName} \
        (frontier — generate it with derive_exec%, or register the \
        hand-written exec with register_exec_kit% first)"
  -- readings
  let mut kinds : List (Name × SimVarKind) := []
  for spec in varSpecs do
    let v : Ident := ⟨spec[1]⟩
    let k : Ident := ⟨spec[3]⟩
    let kind := k.getId.toString
    let hasTerm := spec[4].getNumArgs > 0
    let b ←
      if kind == "raw" then pure .raw
      else if kind == "list" then pure .list
      else if kind == "lit" then
        if hasTerm then pure (.lit ⟨spec[4][0]⟩)
        else throwError "derive_sim%: reading `lit` for {v.getId} needs \
            the LITERAL term it stands for (`(fv : lit modeLT)`)"
      else throwError "derive_sim%: reading {kind} for {v.getId} is \
          outside the derived table (frontier — the argument readings are \
          `raw` (a bare SExpr), `list` (a List SExpr under `enc`) and \
          `lit <term>` (a fixed SExpr literal, not a binder))"
    match b with
    | .lit _ => pure ()
    | _ =>
      if hasTerm then
        throwError "derive_sim%: reading `{kind}` for {v.getId} takes no \
            term — only `lit` does"
    kinds := kinds ++ [(v.getId, b)]
  -- A LITERAL-SPECIALIZED iso is a VALIDATION artifact, not a callee
  -- entry: it states the exec at ONE fixed argument, so it can never be
  -- what a caller's iso rewrites with. It is therefore NOT registered on
  -- the kit — which is also why the "already has a registered iso"
  -- fail-close does not apply to it: the thing that check protects
  -- (callee resolution) is untouched, and the general iso stays the one
  -- and only registered one. (Two isos at the SAME literal cannot hide
  -- either: they would be two theorems of the same name.)
  let isLitIso : Bool := kinds.any fun (_, k) => match k with
    | .lit _ => true
    | _ => false
  unless isLitIso do
    unless kit.encName == .anonymous do
      throwError "derive_sim%: {aclName} already has a registered iso \
          ({kit.encName}) — a second one would silently redirect callee \
          resolution (fail-closed)"
  unless execArgIds.size == kit.arity do
    throwError "derive_sim%: {aclName} has arity {kit.arity} but \
        {execArgIds.size} exec arguments were given"
  -- the exec application (list-read arguments enter under `enc`; a
  -- `lit`-read argument enters as its literal)
  let execArgs : Array Term ← execArgIds.mapM fun (a : Ident) => do
    let some b := kinds.lookup a.getId
      | throwError "derive_sim%: exec argument {a.getId} is not one of \
          the declared vars"
    match b with
    | .list => `($(mkCIdent ``ACL2.Lifting.enc) $a:ident)
    | .raw => `($a:ident)
    | .lit t => pure t
  let lhs := Syntax.mkApp (mkCIdent kit.execName) execArgs
  -- binders, in `vars` order (a `lit` position binds nothing)
  let sexprTy : Term := mkCIdent ``ACL2.SExpr
  let listTy : Term ← `(List $sexprTy)
  let binders ← varSpecs.filterMapM fun spec => do
    let v : Ident := ⟨spec[1]⟩
    let some b := kinds.lookup v.getId
      | throwError "derive_sim%: internal — var {v.getId} lost"
    match b with
    | .lit _ => pure none
    | .list => do pure (some (← `(bracketedBinderF| ($v:ident : $listTy))))
    | .raw => do pure (some (← `(bracketedBinderF| ($v:ident : $sexprTy))))
  -- FRONTIER: mutual recursion (the template inducts on ONE function)
  if let some (.defnInfo di) := env.find? kit.execName then
    if di.all.length > 1 then
      throwError "derive_sim%: {kit.execName} is part of a MUTUAL \
          recursion block ({di.all}) — mutual recursion is a named \
          frontier of the iso template (hand-write nothing: extend the \
          template or route the bridging fact through a replayed ACL2 \
          theorem)"
  -- the induction tactic
  let inductKw : String := inductStx[0].getAtomVal
  let inductTac : TSyntax `tactic ←
    if inductKw == "functional" then
      let tgt : Term := ⟨inductStx[1]⟩
      `(tactic| fun_induction $tgt)
    else if inductKw == "structural" then
      let vi : Ident := ⟨inductStx[1]⟩
      let v ← `(Lean.Parser.Tactic.elimTarget| $vi:ident)
      if inductStx[2].getNumArgs == 0 then `(tactic| induction $v)
      else
        let gens : Array Term :=
          inductStx[2][1].getArgs.map (fun g => (⟨g⟩ : Term))
        `(tactic| induction $v generalizing $gens*)
    else
      throwError "derive_sim%: unknown induction spec {inductKw}"
  -- callee `_enc`s, through the registry
  let calleeEncs : List Name :=
    (execCallees env kit.execName).filterMap fun c =>
      match (execKitExt.getState env).find? (·.execName == c) with
      | some k => if k.encName == .anonymous then none else some k.encName
      | none => none
  let calleeLemmas ← calleeEncs.toArray.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let allLemmas := calleeLemmas ++ simpArgs.map
    (fun a => (⟨a⟩ : TSyntax ``Lean.Parser.Tactic.simpLemma))
  -- A NON-RECURSIVE exec's `eq_def` is a RESERVED name, realized on
  -- demand, and `mkCIdent` bypasses that realization (a recursive exec's
  -- already exists, so this is a no-op for every kit that predates the
  -- R4 wave-2a ODDS kit — the first non-recursive one to want an iso).
  let eqDefName := kit.execName ++ `eq_def
  unless env.contains eqDefName do
    let _ ← liftTermElabM <|
      realizeGlobalConstNoOverloadWithInfo (mkIdent eqDefName)
  let eqDefId : Term := mkCIdent eqDefName
  let proof ← `(by
      $inductTac:tactic <;> rw [$eqDefId:term] <;>
        sim_iso_close [$allLemmas,*])
  let thm ← `($[$doc?:docComment]? theorem $thmId $binders* :
      $lhs = $nativeStx := $proof)
  elabCommand thm
  -- TEMPLATE FAILURE = HARD ERROR (never a hand-proof fallback)
  let env' ← getEnv
  let thmName := (← getCurrNamespace) ++ thmId.getId
  let bad :=
    match env'.find? thmName with
    | none => true
    | some ci => ((ci.value?.getD ci.type).hasSorry)
  if bad then
    throwError "derive_sim%: the iso template did not close \
        {thmId.getId} — the chosen NATIVE READING DOES NOT ALIGN WITH \
        THE EXEC'S RECURSION, so a hand-written correspondence would \
        carry content ACL2 proves (thin-Lean ruling 2026-08-11). Either \
        align the native reading with the exec's recursion, or route the \
        bridging fact through a replayed ACL2 theorem. A hand `_enc` \
        proof is NOT the escape."
  -- FRONTIER: the result reading must be in the derived table
  let some ci := env'.find? thmName
    | throwError "derive_sim%: internal — {thmName} vanished"
  let rhsHead : Option Name := Id.run do
    let mut ty := ci.type
    while ty.isForall do
      ty := ty.bindingBody!
    match ty.eq? with
    | some (_, _, rhs) =>
      match rhs.getAppFn with
      | .const n _ => some n
      | _ => none
    | none => none
  -- FRONTIERS on the NATIVE side, read off the elaborated reading:
  -- a noncomputable subject, or a native in a mutual block (the
  -- template inducts on ONE function's recursion).
  let rhsExpr : Expr := Id.run do
    let mut ty := ci.type
    while ty.isForall do
      ty := ty.bindingBody!
    match ty.eq? with
    | some (_, _, rhs) => rhs
    | none => ty
  for c in rhsExpr.getUsedConstants do
    if Lean.isNoncomputable env' c then
      throwError "derive_sim%: the native reading of {thmId.getId} \
          mentions the NONCOMPUTABLE constant {c} — a named frontier of \
          the iso template (the iso relates a total computable exec to \
          its reading)"
    if let some (.defnInfo di) := env'.find? c then
      if di.all.length > 1 then
        throwError "derive_sim%: the native reading of {thmId.getId} \
            mentions {c}, part of a MUTUAL recursion block ({di.all}) — \
            mutual recursion is a named frontier of the iso template"
  let allowed : List Name :=
    [``ACL2.Lifting.enc, ``ACL2.Lifting.boolEnc, ``ACL2.SExpr.atom, ``cond]
  -- THE RAW (ELEMENT) READING — ruled 2026-08-11. A program whose value
  -- is an ELEMENT of the data rather than a structure over it (ACL2's
  -- `perm-counter-example`: an element of the list, or the `car` of the
  -- empty case) is read by a native that returns a bare `SExpr`, so the
  -- reading is the IDENTITY and there is no encoder to name in the
  -- table above. Admitted BY RESULT TYPE, not by head constant: the
  -- native's own type must END in `ACL2.SExpr` — a `List SExpr`-valued
  -- native still has to go under `enc`, a `Bool`-valued one under
  -- `boolEnc`, an `Int`-valued one under `intRep`. Nothing about the
  -- TEMPLATE changes; this is the table admitting a case the fixed
  -- script already proves (the threat-model note above still governs:
  -- the identity reading names no wrapper, so the frontier check's
  -- discriminating power over such a native is its result type alone —
  -- the template, not this check, is what rejects a misaligned
  -- reading).
  let rawReading : Bool :=
    match rhsHead with
    | some h =>
      match env'.find? h with
      | some ci => Id.run do
          let mut t := ci.type
          while t.isForall do
            t := t.bindingBody!
          return t.isConstOf ``ACL2.SExpr
      | none => false
    | none => false
  match rhsHead with
  | some h => unless allowed.contains h || rawReading do
      throwError "derive_sim%: the result reading of {thmId.getId} is \
          headed by {h}, outside the derived reading table (`enc` / \
          `boolEnc` / `intRep` (an SExpr integer atom) / the t-nil \
          `bif` / the RAW ELEMENT reading (an `SExpr`-valued native — \
          the identity, no encoder)) — a named frontier"
  | none =>
      throwError "derive_sim%: {thmId.getId} is not an equation between \
          a program value and a reading of it (frontier)"
  -- register the iso on the kit (first-match lookup: the updated copy
  -- supersedes; the prior entry stays inert). A LITERAL-SPECIALIZED iso
  -- is not registered — see the note at the fail-close above.
  unless isLitIso do
    registerKitEnc aclName thmName

/- DELIBERATELY ABSENT: a `register_sim_kit%` for hand-written isos.
   Registering a hand `_enc` so that callers could still resolve it would
   BE the hand-proof fallback the ruling forbids — the ruled escape from a
   template failure is an ACL2 book theorem routed through replay, never a
   hand correspondence. If a future frontier genuinely needs one, that is a
   ruling, not a convenience. -/

end ACL2.SimGen
