import ACL2Lean.MirrorProofs.IsoGen

/-!
# THE MIRROR-LEVEL TRANSPORT GENERATOR — `mirror_transport%`

Split out of `MirrorProofs/IsoGen.lean` at R4 wave 2c, when that file
crossed the 1500-line module-size norm (wave 2a flagged it at 1466 and
said the next growth splits it; O-2 and O-3 are that growth). The split
is along the seam the two generators already had: `mirror_iso%` — the
SQUARES, the closing ladder, the registry — stays there; the ASSEMBLY
that turns registered squares plus one waypoint theorem into a mirror
PRODUCT is here. Nothing moved but the text: both the transport closer
macro and `elabMirrorTransport` are byte-identical to their
pre-split form, and the consuming pages import this module instead of
(or as well as) `IsoGen`.

Read `IsoGen`'s header first: the data-refinement frame, the thin-Lean
ruling (template failure is a HARD ERROR, never a hand assembly), the
vocabulary rule, and the closing ladder's admission criterion all govern
this generator too.
-/

namespace ACL2Lean.MirrorProofs

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Parser.Term

open Lean.Parser.Tactic in
/-- The transport closer, two rungs — both plumbing (generated skeleton
    squares, `map_inj`, and `List.map_nil`), and NO content lemma in
    either direction:

    1. PULL THE MAP OUT OF THE CROSSING INSTANCE: rewrite the homomorphism
       squares right-to-left to pull `List.map` outwards, and the
       invariance squares left-to-right to delete it, then land the goal —
       directly for a scalar conclusion, through the embedding's
       injectivity for a list conclusion.
    2. PUSH THE MAP INTO THE GOAL (added by R1-A with its first consumer,
       `app_nil_int`): when the spec `Prop` carries a CLOSED LIST LITERAL
       (`app xs [] = xs`), rung 1 cannot fire — `[]` is not syntactically
       `List.map e.enc []`, so the homomorphism square's reversed pattern
       has nothing to match. Take the injectivity step first and rewrite
       the GOAL with the same squares forwards, plus `List.map_nil` (a
       `rfl`-lemma, already in the square closer's fixed kit and pinned in
       `LadderPins`), which turns the literal into the form the crossing
       instance has.

    Rung 2 is a fallback, so the three pre-R1 transports keep their rung-1
    proofs verbatim. -/
macro "mirror_transport_close" "[" xs:simpLemma,* "]"
    " fwd " "[" fs:simpLemma,* "]"
    " embed " e:term:max " in " h:ident : tactic =>
  `(tactic|
    (first
      | (simp only [$xs,*] at $h:ident
         first
           | exact $h
           | exact map_inj $e $h)
      | (refine map_inj $e ?_
         simp only [$fs,*, List.map_nil]
         exact $h)))
/-! ## `mirror_transport%`

The assembly measured off the three hand transports (`app_assoc_int`,
`len_app_int`, `len_revAcc_int`): encode → cross → pull back, with the
numeric variant differing only in the last step. Both artifacts are
generated from one declaration:

* the CROSSING `<name> : Basics.P SExpr` — the spec Prop at the ACL2 value
  type, proved by rewriting mirror vocabulary into waypoint vocabulary with
  the registered AGREEMENT squares and then citing the waypoint theorem
  exactly. This is the SOLE entry point of the theorem's content, and it is
  one `exact` of a replayed-backed theorem.
* the MIRROR `<name> : Basics.P <T>` — the crossing instantiated at encoded
  arguments, normalised by the registered HOMOMORPHISM squares, landed
  through the embedding's injectivity.

The user still WRITES the mirror statement (`Basics.app_assoc Int`): the
product's statement is never generated out of sight, and the `#guard_msgs`
receipt stays pinned per theorem in the consuming file. -/

syntax (name := mirrorTransportCmd)
  (docComment)? "mirror_transport% " ident " : " ident term:max
  &" embed " term:max
  &" crossing " ident &" from " ident : command

/-- Generate the CROSSING + the MIRROR theorem for one spec Prop:

    ```
    mirror_transport% app_assoc_int : ACL2Lean.Basics.app_assoc Int
      embed intEmbed
      crossing app_assoc_sexpr from Imported.Waypoints.app_assoc_native_driver
    ```

    The proof is fixed on both rungs; the only inputs are the fidelity
    judgments (which waypoint theorem IS this property, which embedding
    reads the element type). -/
@[command_elab mirrorTransportCmd] def elabMirrorTransport : CommandElab :=
  fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs > 0 then some ⟨stx[0][0]⟩ else none
  let thmId : Ident := ⟨stx[2]⟩
  let specId : Ident := ⟨stx[4]⟩
  let elemTy : Term := ⟨stx[5]⟩
  let embedStx : Term := ⟨stx[7]⟩
  let crossId : Ident := ⟨stx[9]⟩
  let wpId : Ident := ⟨stx[11]⟩
  let specName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo specId
  let wpName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo wpId
  let env ← getEnv
  let some (.defnInfo _) := env.find? specName
    | throwError "mirror_transport%: {specName} is not a definition — the \
        transported statement is a spec `Prop` of the mirror layer \
        (frontier)"
  -- the crossing's statement: the spec Prop at the ACL2 value type, in
  -- UNFOLDED form (so the generated crossing states what the hand one did)
  let sexprC : Term := mkCIdent ``ACL2.SExpr
  let crossTyStx : Term ← `($(mkCIdent specName) $sexprC)
  let (crossStmt, binderNames) ← liftTermElabM do
    let ty ← whnf (← Term.elabType crossTyStx)
    unless ty.isForall do
      throwError "mirror_transport%: {specName} at SExpr is not a \
          quantified statement (frontier — the transported spec is a \
          `∀`-statement over lists)"
    let names ← forallTelescopeReducing ty fun xs body => do
      for x in xs do
        let t ← whnf (← inferType x)
        unless t.isAppOf ``List && (t.appArg!).isConstOf ``ACL2.SExpr do
          throwError "mirror_transport%: {specName} binds a non-`List \
              SExpr` argument — outside the derived transport table (a \
              named frontier: every binder is encoded by `List.map`)"
      if body.isForall then
        throwError "mirror_transport%: {specName}'s body is not an \
            equation between list/scalar terms (frontier)"
      pure (← xs.mapM fun x => do pure (← x.fvarId!.getDecl).userName)
    pure (← PrettyPrinter.delab ty, names)
  let bs : Array Ident := binderNames.map mkIdent
  -- the crossing: mirror vocabulary → waypoint vocabulary, then the
  -- replayed-backed waypoint theorem EXACTLY
  let agreeLemmas ← (currentSquares env).flatMap (·.agree.map (·.thmName))
    |>.toArray.mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let crossProof ← `(by
      intro $bs*
      simp only [$agreeLemmas,*]
      exact $(mkCIdent wpName) $bs*)
  elabCommand (← `(theorem $crossId : $crossStmt := $crossProof))
  -- the crossing's docstring is GENERATED too: it says exactly what the
  -- crossing is (the content's sole entry point) and names the replayed
  -- theorem it cites, so the page stays readable without hand prose.
  addDocStringCore ((← getCurrNamespace) ++ crossId.getId)
    s!"THE CROSSING for `{specName}` (generated by `mirror_transport%`): \
       the spec `Prop` at the ACL2 value type `SExpr`. Proved by rewriting \
       mirror vocabulary into waypoint vocabulary with the REGISTERED \
       agreement squares and then citing `{wpName}` exactly — so this is \
       the SOLE entry point of the theorem's content, and that content is \
       the replay's."
  -- the mirror theorem: the crossing at encoded arguments, normalised
  let env2 ← getEnv
  let homLemmas ← (currentSquares env2).filterMapM fun s => do
    if s.homName == .anonymous then pure none
    else if s.homIsScalar then
      pure (some (← `(Lean.Parser.Tactic.simpLemma|
        $(mkCIdent s.homName):term)))
    else
      pure (some (← `(Lean.Parser.Tactic.simpLemma|
        ← $(mkCIdent s.homName):term)))
  -- the same squares FORWARDS, for the closer's second rung (which
  -- rewrites the GOAL rather than the crossing instance)
  let homLemmasFwd ← (currentSquares env2).filterMapM fun s => do
    if s.homName == .anonymous then pure none
    else pure (some (← `(Lean.Parser.Tactic.simpLemma|
      $(mkCIdent s.homName):term)))
  let hId : Ident := mkIdent `h
  let encArgs ← bs.mapM fun b => `(List.map ($embedStx).enc $b:ident)
  let crossApp := Syntax.mkApp crossId encArgs
  let mainProof ← `(by
      intro $bs*
      have $hId : _ := $crossApp
      mirror_transport_close [$(homLemmas.toArray),*]
        fwd [$(homLemmasFwd.toArray),*]
        embed $embedStx in $hId)
  let mainStmt : Term ← `($(mkCIdent specName) $elemTy)
  elabCommand (←
    `($[$doc?:docComment]? theorem $thmId : $mainStmt := $mainProof))
  -- TEMPLATE FAILURE = HARD ERROR, on either rung
  let env3 ← getEnv
  let ns ← getCurrNamespace
  for (nm, what) in [(ns ++ crossId.getId, "crossing"),
                     (ns ++ thmId.getId, "transport")] do
    -- FAILURE REPORTING (R0 item 10, 2026-08-13): as with `mirror_iso%`,
    -- this message used to ASSERT the cause per rung. State the OBSERVED
    -- residual and list candidates; the goals themselves are reported by
    -- Lean as separate elaboration errors on the declaration.
    let residual : String :=
      match env3.find? nm with
      | none => "no declaration was produced"
      | some ci =>
        if (ci.value?.getD ci.type).hasSorry then
          "the declaration was produced but carries `sorryAx` (the \
           assembly left goals open)"
        else ""
    if residual != "" then
      throwError "mirror_transport%: the fixed {what} assembly did not \
          close {nm}.\n\
          OBSERVED: {residual}. Spec `{specName}`; waypoint theorem \
          `{wpName}`; failing rung: {what}. The residual GOALS are \
          reported separately by Lean as elaboration errors on this \
          declaration — read those first; this message does not \
          diagnose them.\n\
          CANDIDATE CAUSES (none asserted, not ranked): (a) the \
          registered agreement squares do not carry {specName} into \
          {wpName}'s vocabulary (a MISSING or misaligned square); (b) \
          `{wpName}` is not this property (the crossing cites it \
          exactly, so a mismatched statement fails here); (c) a \
          missing registered HOMOMORPHISM square for one of the \
          definitions in {specName}; (d) a wrong square CLASS \
          (scalar vs list) for one of those definitions; (e) a \
          missing instance at the element type.\n\
          Remedy: generate the missing square with `mirror_iso%`, fix \
          the crossing's citation, or route the fact through a \
          replayed ACL2 book theorem — a hand assembly is NOT the \
          escape."

/- DELIBERATELY ABSENT, exactly as in `derive_sim%`: a `register_square%`
   for HAND-written squares. Registering one so a transport could resolve
   it would BE the hand-proof fallback the ruling forbids. If a future
   frontier genuinely needs one, that is a ruling, not a convenience. -/
end ACL2Lean.MirrorProofs
