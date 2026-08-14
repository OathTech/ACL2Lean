import ACL2Lean.Syntax

/-!
# THE MIRROR-LEVEL GENERATORS — `mirror_iso%` + `mirror_transport%`

The Basics-closeout arc's increments C+D (charter
`docs/plans/2026-08-13_basics-closeout-charter.md`), built in the image of
the proven layer below: `derive_exec%` (`Imported/ExecGen.lean`) and
`derive_sim%` (`Imported/SimGen.lean`).

Where `derive_sim%` generates the WAYPOINT-level iso (an exec on encoded
lists computes its native reading), this module generates the two
MIRROR-level artifacts that stood hand-written in `MirrorProofs/Basics.lean`:

* **`mirror_iso%`** — the SQUARES. Two classes, both measured off the hand
  file's six squares:
  - AGREEMENT (`app_agree_append`, `len_agree_length`,
    `revAcc_agree_revAccL`): the mirror definition at `List SExpr` IS the
    waypoint's spelling of the same recursion.
  - MAP-HOMOMORPHISM (`app_map_hom`, `revAcc_map_hom`) and its scalar form,
    MAP-INVARIANCE (`len_map_invariant`): mapping an element embedding
    commutes with the mirror definition.
* **`mirror_transport%`** — the ASSEMBLY: from a waypoint theorem, the
  crossing (`Basics.P SExpr`, in mirror vocabulary, via the agreement
  squares) and then the mirror theorem at the user's element type
  (`Basics.P Int`, via the homomorphism squares + injectivity).

## WHY THESE MUST BE GENERATED (the thin-Lean ruling, at the mirror level)

The squares are P3 content — statements about Lean objects that ACL2 cannot
state, so there is nothing to replay and no intrinsic bound on proof
difficulty. A hand square can therefore smuggle in exactly the content ACL2
proves while looking like plumbing: the standing example is the accumulator,
where `revAcc xs acc = xs.reverse ++ acc` (an ACL2 BOOK THEOREM) would sit in
the same syntactic slot as the alignment square `revAcc xs acc = revAccL xs
acc`. The gate is the same one `derive_sim%` carries: **TEMPLATE FAILURE IS A
HARD ERROR**. The user supplies only the correspondence judgment; the macro
proves it by ONE FIXED SCRIPT driven off the mirror definition's own
recursion. If that script does not close the goal, the declared
correspondence does not align with the definition's recursion, and the legal
escape is a replayed ACL2 book theorem — never a hand square.

## THE VOCABULARY RULE (Mike, 2026-08-13) — why this gate is CLAUSE-INDEPENDENT

Native readings and MIRROR DEFINITIONS are OWN-DEFINITIONS: their bodies are
built from constructors and our own functions, never from library functions.
`ACL2Lean/Mirrors/` carries the rule by construction (zero imports beyond the
prelude, `just check-mirrors-pure`), and `derive_sim%`'s threat-model note
carries it for waypoint readings. The consequence here is the one that makes
this generator's gate trustworthy: **no library lemma exists about our
names**, so no default-simp/`grind` set can close a misaligned square by
accident — the template fails closed regardless of the induction clause. This
is precisely the leak probe P1 found one level down (a LIBRARY-vocabulary
reading `xs.reverse ++ acc` closed by `reverse_cons`/`append_assoc`), and it
is unrepresentable for a mirror definition.

The closer is ALSO built so the leak cannot re-enter through the tactic
script (see "the closing ladder" below): every fixed rung is a `rfl`-lemma
(pinned as such in this file) except the ONE ruled addition, the
embedding's own injectivity as an iff (`enc_inj_iff`, ruling 2026-08-14 —
plumbing about our own definitions, see the ladder's criterion); and the
only per-invocation input is a list of DEFINITIONS to unfold (a
non-definition is a hard error). Definitional unfolding cannot introduce
content.

Threat model, per the two-standard rule: this gate is a SPEEDBUMP, reviewed
by "does it catch the honest mistake". DO NOT HARDEN it with semantic
classifiers; the per-book provenance audit is the backstop.

## THE ONE SQUARE TEMPLATE

    <theorem binders> : <lhs> = <rhs> := by
      fun_induction <mirror fn> <vars> <;> mirror_square_close [...]

`fun_induction` supplies exactly the induction hypotheses of the mirror
definition's OWN recursion, at the recursive call's actual arguments —
which is how THE LIST item 8's structural demand (the accumulator square's
IH lands at `a :: acc`, so the motive must quantify the non-measured
arguments) is met for free: functional induction's motive abstracts EVERY
argument, so accumulating arguments are generalized by construction, never
carried fixed.

## VALIDATION BY RETIREMENT

Every hand square and every hand transport in `MirrorProofs/Basics.lean` is
replaced by an invocation emitting the SAME NAME and the SAME STATEMENT
(`#check`-compared before/after), so the three mirror theorems' receipts
re-derive against the generated artifacts. The build is the gate.
-/

namespace ACL2Lean.MirrorProofs

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Parser.Term

/-! ## The transfer kit's core (THE LIST items 1 + 4)

Lifted out of `MirrorProofs/Basics.lean` unchanged (same namespace, same
names, same statements) because the generators must build statements that
mention them. -/

/-- An element embedding into the ACL2 value universe: an injection
    `α → SExpr`. The pathfinder needs nothing more (no order field —
    that dimension arrives with sorting). -/
structure Acl2Embed (α : Type u) where
  enc : α → ACL2.SExpr
  inj : ∀ {a b : α}, enc a = enc b → a = b

/-- `Int` embeds as integer atoms. -/
def intEmbed : Acl2Embed Int where
  enc n := .atom (.number (.int n))
  inj h := by injection h with h1; injection h1 with h2; injection h2

/-- The embedding's defining field IN ITS USEFUL FORM: `Acl2Embed.inj`
    is a one-way implication, and a rewrite needs the `iff` (the
    converse is `congrArg`). Admitted to the square closer's fixed kit
    by ruling 2026-08-14 — see "the closing ladder" for why that is
    plumbing and not content. -/
theorem enc_inj_iff (e : Acl2Embed α) (a b : α) :
    e.enc a = e.enc b ↔ a = b :=
  ⟨e.inj, fun h => h ▸ rfl⟩

/-- Injectivity lifts pointwise to lists (THE LIST item 4). -/
theorem map_inj (e : Acl2Embed α) :
    ∀ {xs ys : List α}, xs.map e.enc = ys.map e.enc → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, b :: ys, h => by
    simp only [List.map] at h
    injection h with h1 h2
    rw [e.inj h1, map_inj e h2]

/-! ## The closing ladder — and why each rung is safe

FIXED for every square invocation. The ladder is two rungs: `rfl` (pure
definitional unfolding — it can close a base case, never an inductive
content fact), then one `simp_all only` over a FIXED kit plus the
per-invocation definitions.

THE FIXED KIT'S ADMISSION CRITERION (as widened by ruling 2026-08-14):
**`rfl`-lemmas + the embedding's `inj` iff** — nothing else. Concretely:

* the `rfl`-lemmas are the constructor-case equations of a core
  operation, true by definitional unfolding. Nothing that RELATES two
  operations is admitted, because that is where content lives.
* `enc_inj_iff` is the ONE non-`rfl` rung. It is PLUMBING, per the
  ruling: a square is a statement of DEFINITIONAL CORRESPONDENCE about
  OUR OWN definitions, and `Acl2Embed.inj` is the embedding's own
  defining field — admitting it lets an element-position homomorphism
  square rewrite `e.enc a = e.enc b` to `a = b` (the list form,
  `map_inj`, was already plumbing in the transport closer). Content
  still arrives ONLY via replay: injectivity says nothing about any
  mirror definition, so it cannot close a misaligned square — it only
  removes the encoding from an element comparison.

Admitted, each `rfl` rung pinned by the examples directly below (so the
criterion cannot rot silently):

| rung                | is | deliberately NOT admitted    |
| ------------------- | -- | ---------------------------- |
| `List.map_nil/cons` | `List.map`'s own two cases     | `List.map_append` |
| `List.nil/cons_append` | `++`'s own two cases        | `List.append_assoc`, `List.append_nil` |
| `List.length_nil/cons` | `List.length`'s own two cases | `List.length_append` |
| `Bool.cond_true/false` | `cond`'s own two cases   | any `lexorderB`/order fact |
| `enc_inj_iff`       | `Acl2Embed.inj` as an iff   | any OTHER embedding property |

(`Acl2Embed` has exactly two fields, `enc` and `inj`; there is no order
field, so an element-position square that needs the embedding to RESPECT
an order still fails closed — as W1's `hom list` does.)

The excluded column is exactly the content column: `append_assoc` IS the
02-rev book's APP-ASSOC, `length_append` IS `simple.lisp`'s MY-LEN-MY-APP,
and `List.reverse_cons` + `append_assoc` are what closed probe P1's
misaligned reading one level down. None of them can be reached from here:
they are not in the kit, `simp_all only` admits nothing else, and the
per-invocation input is definitions-only.

HYPOTHESIS-DIRECTED CLOSING (ruling 2026-08-14, item 2). The closer is
`simp_all`-class, so the LOCAL CONTEXT of each case the template itself
created participates: the IHs (in a `fun_induction` case, exactly the
mirror definition's own induction hypotheses) AND the CASE HYPOTHESIS of
an `if`-split in the mirror definition's body. For that case hypothesis
to reach the goal it must speak the goal's vocabulary: where the split
is on a CLASS operation (`a ≤ b` under a `TotalOrder` instance) the
instance is a DEFINITION, so naming it in the invocation's
`unfold [...]` list normalises the hypothesis to the reading's own Bool
equation (`lexorderB a b = true`), which then rewrites the reading's
`bif` — closed by `cond`'s own two cases. Unfolding an instance cannot
introduce content for the same reason any other definitional unfolding
cannot; and the choice is VISIBLE in the invocation, not hidden in the
generator. (Measured on W1 `insertOrd_agree_insertL`,
`MirrorProofs/Sorting.lean`: without the instance in the unfold list the
two `bif`/`≤` residuals survive verbatim; with it, the square closes.) -/

section LadderPins

/-- The fixed kit's `rfl` rungs are DEFINITIONAL — pinned, so the
    admission criterion above cannot rot silently. (`enc_inj_iff` is the
    ruled exception and is NOT `rfl`; it is proved from the embedding's
    own `inj` field above.) -/
example (f : α → β) : List.map f ([] : List α) = [] := rfl
example (f : α → β) (a : α) (as : List α) :
    List.map f (a :: as) = f a :: List.map f as := rfl
example (as : List α) : [] ++ as = as := rfl
example (a : α) (as bs : List α) : (a :: as) ++ bs = a :: (as ++ bs) := rfl
example : ([] : List α).length = 0 := rfl
example (a : α) (as : List α) : (a :: as).length = as.length + 1 := rfl
example (x y : α) : (bif true then x else y) = x := rfl
example (x y : α) : (bif false then x else y) = y := rfl

end LadderPins

open Lean.Parser.Tactic in
/-- The square closer (see "the closing ladder"). The only per-invocation
    input is `xs`: the mirror definition's equations, the declared
    definitions to unfold, and the registered squares of its callees. -/
macro "mirror_square_close" "[" xs:simpLemma,* "]" : tactic =>
  `(tactic|
    (first
      | rfl
      | simp_all only [List.map_nil, List.map_cons, List.nil_append,
          List.cons_append, List.length_nil, List.length_cons,
          Bool.cond_true, Bool.cond_false, enc_inj_iff, $xs,*]))

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

/-! ## The square registry

Squares reference each other exactly as exec kits do: a mirror definition
that CALLS another (`rev` calls `app`) needs the callee's square in its own
closer, and the transport needs every registered square. The registry is the
lookup, and it is FAIL-CLOSED in the `derive_exec%` style: a second square of
the same class for the same function is refused rather than silently
redirecting a later closer's rewrite set. -/

/-- Which square class an entry records. -/
inductive SquareClass where
  /-- `<fn> xs … = <waypoint spelling>` at `List SExpr`. -/
  | agree
  /-- `(<fn> xs …).map e.enc = <fn> (xs.map e.enc) …` (list-valued). -/
  | homList
  /-- `<fn> (xs.map e.enc) … = <fn> xs …` (scalar-valued). -/
  | homScalar
  deriving BEq, Inhabited

/-- The squares registered for one mirror definition. -/
structure MirrorSquares where
  /-- the mirror definition -/
  fnName : Name
  /-- its agreement square (`.anonymous` = none registered) -/
  agreeName : Name := .anonymous
  /-- its homomorphism/invariance square (`.anonymous` = none) -/
  homName : Name := .anonymous
  /-- `true` when `homName` is the SCALAR (invariance) form -/
  homIsScalar : Bool := false
  deriving Inhabited

initialize mirrorSquareExt :
    SimplePersistentEnvExtension MirrorSquares (List MirrorSquares) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => e :: s
    -- NEWEST-FIRST, matching `addEntryFn`'s prepend (the `execKitExt`
    -- precedent, audit F1 there): a later `mirror_iso%` supersedes the
    -- entry it updates, and imported entries must present the same way or
    -- a downstream module would see the pre-update copy.
    addImportedFn := fun ess => ((ess.map (·.toList)).toList.flatten).reverse
  }

/-- The entry in force for `fn` (first match — newest wins). -/
def findSquares (env : Environment) (fn : Name) : Option MirrorSquares :=
  (mirrorSquareExt.getState env).find? (·.fnName == fn)

/-- Every mirror definition's IN-FORCE entry, superseded copies dropped. -/
def currentSquares (env : Environment) : List MirrorSquares :=
  (mirrorSquareExt.getState env).foldl (init := []) fun acc e =>
    if acc.any (·.fnName == e.fnName) then acc else acc ++ [e]

/-- Attach a square to its mirror definition, refusing a second square of
    the same class (fail-closed: with first-match lookup a re-registration
    would silently redirect every later closer). -/
def registerSquare (fn : Name) (cls : SquareClass) (thm : Name) :
    CommandElabM Unit := do
  let cur := (findSquares (← getEnv) fn).getD { fnName := fn }
  let next ←
    match cls with
    | .agree =>
      unless cur.agreeName == .anonymous do
        throwError "mirror_iso%: {fn} already has an agreement square \
            ({cur.agreeName}) — a second one would silently redirect the \
            crossing's rewrite set (fail-closed)"
      pure { cur with agreeName := thm }
    | .homList | .homScalar =>
      unless cur.homName == .anonymous do
        throwError "mirror_iso%: {fn} already has a homomorphism square \
            ({cur.homName}) — a second one would silently redirect the \
            transport's rewrite set (fail-closed)"
      pure { cur with homName := thm, homIsScalar := cls == .homScalar }
  modifyEnv fun env => mirrorSquareExt.addEntry env next

/-! ## `mirror_iso%` -/

declare_syntax_cat mirrorSquareSpec
/-- The agreement square, with the waypoint-vocabulary reading. -/
syntax "agree " term:max : mirrorSquareSpec
/-- The map-homomorphism square of a LIST-valued mirror definition. -/
syntax "hom " &"list" : mirrorSquareSpec
/-- The map-invariance square of a SCALAR-valued mirror definition. -/
syntax "hom " &"scalar" : mirrorSquareSpec

syntax (name := mirrorIsoCmd)
  (docComment)? "mirror_iso% " ident &" for " ident
  &" vars " "[" ident,* "]"
  &" square " mirrorSquareSpec
  (&" unfold " "[" ident,* "]")? : command

/-! ### The ARGUMENT READINGS (R1 item B, audit finding F1)

How each explicit binder of a mirror definition enters the HOMOMORPHISM
statement. This is the per-binder form of what `derive_sim%` carries one
level down (`Imported/SimGen.lean`'s `raw`/`list` reading table) — but
here it needs NO user syntax: at the mirror level the reading is a
FUNCTION OF THE SPEC'S OWN LEAN BINDER TYPE, so the generator infers it
and a declaration cannot disagree with the definition it is about.

Before R1 the shape walk collapsed the telescope to an `allList`
boolean and hard-errored on anything else, which rejected every mirror
definition with an ELEMENT argument (`insertOrd (a : α)`,
`howMany (a : α)`) — audit F1. -/

/-- How one explicit binder of a mirror definition is READ when the
    square's statement is built. -/
private inductive ArgReading where
  /-- `List α` — enters the homomorphism statement under
      `List.map e.enc`. -/
  | list
  /-- the embedded element type `α` itself — enters under `e.enc`. -/
  | elem
  deriving BEq, Inhabited

/-- The mirror definition's shape, as the generator must read it: the
    per-binder READING VECTOR of its explicit arguments (in order), and
    whether the RESULT is a `List`.

    The readings are inferred from the binder TYPES against the
    definition's own type variable `α` (the thing an `Acl2Embed`
    embeds); anything else is a hard error naming the observed type —
    the argument-reading frontier.

    Also returned: the definition's INSTANCE-IMPLICIT binders, as the
    class names they apply to `α` (`howMany` carries `[DecidableEq α]`,
    `insertOrd` carries `[TotalOrder α]`). A HOMOMORPHISM square's
    statement mentions the definition at the USER's element type `α`, so
    it must re-bind them: at `SExpr` (the `agree` class, and the encoded
    side of a homomorphism) the instance is synthesised from the
    ambient environment, but at a bound `α` there is nothing to
    synthesise and the statement would not elaborate at all. A class
    applied to anything OTHER than the element type is a hard error
    naming it (a frontier — the generator never guesses a binder it
    cannot state). -/
private def mirrorFnShape (fnName : Name) (ty : Expr) :
    MetaM (Array ArgReading × Bool × Array Name) :=
  forallTelescopeReducing ty fun xs body => do
    -- the definition's own type variable: the sole binder that is a type
    let mut elemTy? : Option Expr := none
    for x in xs do
      if (← whnf (← inferType x)).isSort then
        if elemTy?.isSome then
          throwError "mirror_iso%: {fnName} is polymorphic over MORE THAN \
              ONE type variable — outside the square table, which reads \
              each argument against the single element type an \
              `Acl2Embed` embeds (a named frontier)"
        elemTy? := some x
    let mut readings : Array ArgReading := #[]
    let mut instClasses : Array Name := #[]
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo.isInstImplicit then
        -- the RAW binder type (never `whnf`: `DecidableEq α` is itself a
        -- definition and would unfold to its `∀ a b, Decidable …` body)
        let t ← inferType x
        let some cls := t.getAppFn.constName?
          | throwError "mirror_iso%: {fnName}'s instance argument \
              `{t}` is not a CLASS APPLICATION — outside the table of \
              binders a homomorphism statement can re-bind at the user's \
              element type (a named frontier)"
        let some elemTy := elemTy?
          | throwError "mirror_iso%: {fnName} has an instance argument \
              but NO type variable (a named frontier)"
        unless t.getAppNumArgs == 1 && t.appArg! == elemTy do
          throwError "mirror_iso%: {fnName}'s instance argument `{t}` is \
              not a ONE-PARAMETER class over the element type \
              `{elemTy}` — the homomorphism statement re-binds the \
              definition's instances at the user's element type, and a \
              class over anything else is not something this generator \
              may guess (a named frontier)"
        instClasses := instClasses.push cls
      if (← x.fvarId!.getDecl).binderInfo.isExplicit then
        let t ← whnf (← inferType x)
        let some elemTy := elemTy?
          | throwError "mirror_iso%: {fnName} has explicit arguments but \
              NO type variable — outside the square table, whose \
              statements read every argument position against the element \
              type an `Acl2Embed` embeds (a named frontier)"
        if t == elemTy then
          readings := readings.push .elem
        else if t.isAppOf ``List && t.getAppNumArgs == 1
            && t.appArg! == elemTy then
          readings := readings.push .list
        else
          throwError "mirror_iso%: {fnName}'s explicit argument \
              `{(← x.fvarId!.getDecl).userName} : {t}` is outside the \
              ARGUMENT-READING table.\n\
              OBSERVED: binder type `{t}`; the definition's element type \
              is `{elemTy}`. The two derived readings are `List {elemTy}` \
              (the argument enters the homomorphism statement under \
              `List.map e.enc`) and `{elemTy}` itself (it enters under \
              `e.enc`).\n\
              CANDIDATE CAUSES (none asserted, not ranked): (a) a \
              FUNCTION-VALUED argument (e.g. `{elemTy} → Bool`) — an \
              `Acl2Embed` is an injection on ELEMENTS and has no action \
              on a function position, so reading one is a design \
              question, not something this generator may guess; (b) a \
              NON-EMBEDDED scalar (`Nat`, `Int`, …) — the embedding does \
              not act on it either, and whether the square should hold it \
              fixed is the same design question; (c) a list over some \
              OTHER type than `{elemTy}`.\n\
              What this failure is NOT: a statement that the declared \
              correspondence is wrong. The declaration never reached the \
              statement builder — this is the reading table's own bound, \
              and widening it is a design change to the square classes, \
              never a hand square (thin-Lean ruling 2026-08-11)."
    return (readings, (← whnf body).isAppOf ``List, instClasses)

/-- Generate one SQUARE for a mirror definition:

    ```
    mirror_iso% app_agree_append for ACL2Lean.Basics.app
      vars [xs, ys]
      square agree (xs ++ ys)

    mirror_iso% app_map_hom for ACL2Lean.Basics.app
      vars [xs, ys]
      square hom list
    ```

    The user supplies ONLY the correspondence judgment (which waypoint
    spelling this definition agrees with; which square class its result
    type carries) plus, for a reading that rests on a definition of ours,
    the `unfold [...]` list — DEFINITIONS ONLY, since a definitional
    unfolding cannot introduce content. Everything else — the statement's
    left-hand side, EACH ARGUMENT'S READING (inferred from the
    definition's own binder types, see `ArgReading`), the induction, the
    closer — is fixed. -/
@[command_elab mirrorIsoCmd] def elabMirrorIso : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs > 0 then some ⟨stx[0][0]⟩ else none
  let thmId : Ident := ⟨stx[2]⟩
  let fnId : Ident := ⟨stx[4]⟩
  let vars : Array Ident := stx[7].getSepArgs.map (⟨·⟩)
  let specStx := stx[10]
  let unfolds : Array Ident :=
    if stx[11].getNumArgs == 0 then #[] else stx[11][2].getSepArgs.map (⟨·⟩)
  -- the mirror definition
  let fnName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fnId
  let env ← getEnv
  let some (.defnInfo di) := env.find? fnName
    | throwError "mirror_iso%: {fnName} is not a definition — a square is \
        generated FOR a mirror definition (frontier)"
  if di.all.length > 1 then
    throwError "mirror_iso%: {fnName} is part of a MUTUAL recursion block \
        ({di.all}) — mutual recursion is a named frontier of the square \
        template (which inducts on ONE definition's recursion)"
  let (readings, resIsList, instClasses) ←
    liftTermElabM <| mirrorFnShape fnName di.type
  unless vars.size == readings.size do
    throwError "mirror_iso%: {fnName} takes {readings.size} explicit \
        arguments but {vars.size} vars were given"
  if vars.any (·.getId == `e) then
    throwError "mirror_iso%: `e` is the embedding binder's reserved name — \
        rename the var"
  -- the declared unfoldings: DEFINITIONS ONLY (a lemma here would be the
  -- content channel the template gate exists to close)
  let unfoldNames ← unfolds.mapM fun u => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo u
    match env.find? n with
    | some (.defnInfo _) => pure n
    | _ => throwError "mirror_iso%: `unfold [{n}]` is not a DEFINITION — \
        the square closer unfolds definitions only. A LEMMA here would be \
        exactly the content channel the template gate closes: route a \
        bridging fact through a replayed ACL2 book theorem instead."
  -- the square class + the drift check against the real result type
  let cls : SquareClass ←
    match specStx[0].getAtomVal, specStx[1].getAtomVal with
    | "agree", _ => pure .agree
    | "hom", "list" => pure .homList
    | "hom", "scalar" => pure .homScalar
    | k, k' => throwError "mirror_iso%: unknown square spec {k}{k'}"
  match cls with
  | .homList =>
    unless resIsList do
      throwError "mirror_iso%: {fnName}'s result is NOT a list, but `hom \
          list` was declared — declare `hom scalar` (the declared class is \
          checked against the definition's type so a drift fails closed)"
  | .homScalar =>
    if resIsList then
      throwError "mirror_iso%: {fnName}'s result IS a list, but `hom \
          scalar` was declared — declare `hom list` (the declared class is \
          checked against the definition's type so a drift fails closed)"
  | .agree => pure ()
  -- the statement (each var at its inferred READING: a `.list` binder is
  -- a list of the element type and enters under `List.map e.enc`; an
  -- `.elem` binder is one element and enters under `e.enc`)
  let sexprC : Term := mkCIdent ``ACL2.SExpr
  let sexprTy : Term ← `(List $sexprC)
  let alphaId : Ident := mkIdent `α
  let eId : Ident := mkIdent `e
  let fnC : Term := mkCIdent fnName
  let varsR : Array (Ident × ArgReading) := vars.zip readings
  let plainApp : Term := Syntax.mkApp fnC (vars.map (fun v => (v : Term)))
  let binders : Array (TSyntax ``bracketedBinderF) ← do
    match cls with
    | .agree => varsR.mapM fun (v, r) =>
        match r with
        | .list => `(bracketedBinderF| ($v:ident : $sexprTy))
        | .elem => `(bracketedBinderF| ($v:ident : $sexprC))
    | _ =>
      -- the definition's OWN instance binders, re-bound at the user's
      -- element type (see `mirrorFnShape`): at `α` there is nothing to
      -- synthesise, so without these the statement does not elaborate
      let iB ← instClasses.mapM fun c => do
        `(bracketedBinderF| [$(Syntax.mkApp (mkCIdent c) #[alphaId]):term])
      let eB ← `(bracketedBinderF| ($eId:ident : Acl2Embed $alphaId:ident))
      let vB ← varsR.mapM fun (v, r) =>
        match r with
        | .list => `(bracketedBinderF| ($v:ident : List $alphaId:ident))
        | .elem => `(bracketedBinderF| ($v:ident : $alphaId:ident))
      pure (iB ++ #[eB] ++ vB)
  let encoded : Array Term ← varsR.mapM fun (v, r) =>
    match r with
    | .list => `(List.map ($eId:ident).enc $v:ident)
    | .elem => `(($eId:ident).enc $v:ident)
  let reading : Term := ⟨specStx[1]⟩
  let stmt : Term ←
    match cls with
    | .agree => `($plainApp = $reading)
    | .homList =>
      let rhs := Syntax.mkApp fnC encoded
      `(List.map ($eId:ident).enc $plainApp = $rhs)
    | .homScalar =>
      let lhs := Syntax.mkApp fnC encoded
      `($lhs = $plainApp)
  -- the closer's lemmas: the definition's own equations, the declared
  -- unfoldings, and the registered squares of the definition's callees
  let calleeSquares : List Name :=
    di.value.getUsedConstants.toList.filterMap fun c =>
      match findSquares env c with
      | some s =>
        match cls with
        | .agree => if s.agreeName == .anonymous then none else some s.agreeName
        | _ => if s.homName == .anonymous then none else some s.homName
      | none => none
  let lemmaNames : Array Name :=
    #[fnName] ++ unfoldNames ++ calleeSquares.eraseDups.toArray
  let lemmas ← lemmaNames.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let proof ← `(by
      fun_induction $plainApp <;> mirror_square_close [$lemmas,*])
  let thm ← `($[$doc?:docComment]? theorem $thmId $binders* : $stmt := $proof)
  elabCommand thm
  -- TEMPLATE FAILURE = HARD ERROR (never a hand-proof fallback)
  let env' ← getEnv
  let thmName := (← getCurrNamespace) ++ thmId.getId
  -- FAILURE REPORTING (R0 item 10, 2026-08-13): this message used to
  -- ASSERT one cause ("the declared correspondence does not align with
  -- the recursion"), which is wrong in every other failure mode — a
  -- mis-chosen rung class, a missing instance, or an unregistered callee
  -- square all land here too. State only what is OBSERVED and list the
  -- candidates; the residual goals themselves are reported by Lean as
  -- separate elaboration errors on this declaration.
  let residual : String :=
    match env'.find? thmName with
    | none => "no declaration was produced"
    | some ci =>
      if (ci.value?.getD ci.type).hasSorry then
        "the declaration was produced but carries `sorryAx` (the closer \
         left goals open)"
      else ""
  if residual != "" then
    let clsName : String :=
      match cls with
      | .agree => "agree"
      | .homList => "homList"
      | .homScalar => "homScalar"
    throwError "mirror_iso%: the square template did not close \
        {thmId.getId}.\n\
        OBSERVED: {residual}. Rung class `{clsName}`; target \
        `{fnName}`; the closer was given the lemma set \
        {lemmaNames.toList} (the definition's own equations, the \
        declared unfoldings, and the registered squares of \
        {fnName}'s callees). The residual GOALS are reported \
        separately by Lean as elaboration errors on this \
        declaration — read those first; this message does not \
        diagnose them.\n\
        CANDIDATE CAUSES (none asserted, not ranked): (a) the declared \
        correspondence does not align with {fnName}'s own recursion; \
        (b) the wrong rung CLASS for this statement (`agree` vs \
        `homList` vs `homScalar`); (c) a missing instance needed to \
        elaborate the statement or fire a lemma; (d) a MISSING \
        REGISTERED SQUARE for a callee of {fnName} — generate that \
        callee's square with `mirror_iso%` first, since only \
        registered ones reach the closer.\n\
        What this failure is NOT: under the VOCABULARY RULE \
        (2026-08-13) a mirror definition is an OWN-DEFINITION, so no \
        library lemma about our names exists and no default simp set \
        could have closed it either. Whatever the cause, the remedy is \
        to fix the correspondence/class/registration, or to route the \
        bridging fact through a REPLAYED ACL2 BOOK THEOREM. A hand \
        square is NOT the escape (thin-Lean ruling 2026-08-11, at the \
        mirror level)."
  registerSquare fnName cls thmName

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
  let agreeLemmas ← (currentSquares env).filterMap
      (fun s => if s.agreeName == .anonymous then none else some s.agreeName)
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
