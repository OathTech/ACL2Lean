import ACL2Lean.MirrorProofs.IsoKit

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

## THE FRAME: DATA REFINEMENT (Mike, 2026-08-14)

What the square classes above ARE, named: per ACL2 datatype a Lean
datatype plus a MAPPING to the ACL2 values (`Acl2Embed` is the mapping
for an element type); the mirror definition runs the SAME ALGORITHM
MODULO THAT REFINEMENT — the same ACCESS PATTERN, not the same code.
A SQUARE is then exactly the statement that the algorithm commutes with
the refinement, and the ARGUMENT-READING table below (`ArgReading`) is
the refinement calculus: it says how each binder position is carried
across. The consequence that makes the generator trustworthy is a
consequence of the frame, not an extra gate: where the access patterns
DIVERGE there is no commuting square to state, so the template fails
CLOSED — which is the honest outcome, not a proof failure to work
around.

Ruled as the frame's next instance, and NOT BUILT AS RULED: for a CLOSED
ENUM in a `.fixed` position, a once-per-datatype constructor↦ACL2-value
table (the finite sibling of `Acl2Embed`), off which the square generator
would ENUMERATE the constructors and emit one square per constructor with
the mapped ACL2 literal on the WAYPOINT side. That form does not close,
and wave 0 measured why: the waypoint reading `filterL` dispatches on a
RUNTIME symbol comparison, so specialising the ARGUMENT VALUE leaves the
dispatch in place and the fixed ladder cannot evaluate it (W3 stage 3,
`MirrorProofs/Sorting.lean`).

WHAT WAS BUILT INSTEAD (R4 wave 2a, the standing `(b)` ruling): the same
per-constructor family, keyed off the MIRROR side rather than generated
from a value table — `vars` takes a CONSTRUCTOR LITERAL (below), the
registry is KEYED by it, and the WAYPOINT side is a reading that never
dispatches (`Imported/SortingModeReadings.lean`, four own-definitions,
each validated by `derive_sim%` against the real exec at its literal
mode). The frame is unchanged and the fail-closed properties are the
ruled ones — a constructor CARRYING DATA is a hard error, a duplicate key
is refused, and an unkeyed square cannot join a family — but the
declaration is per square rather than once per datatype, which is what
the measurement supports.

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

The closer is built so the leak does not re-enter through the tactic
script BY ACCIDENT (see "the closing ladder" below): every fixed rung is a
`rfl`-lemma (pinned as such in this file) except the TWO ruled PLUMBING
FAMILIES — the embedding's own injectivity as an iff (`enc_inj_iff`,
ruling 2026-08-14) and the Bool/decide coercions (`Bool.decide_eq_true`,
ruling 2026-08-14), both plumbing about our own definitions, see the
ladder's criterion; and the only per-invocation input is a list of
DEFINITIONS to unfold (a non-definition is a hard error).

**BOUND, HONESTLY (audit 2026-08-16, `docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md`
F1 — this paragraph previously claimed "definitional unfolding cannot
introduce content", and that claim is FALSIFIED by demonstration).** The
unfold-list check USED TO accept anything with `.defnInfo` — INCLUDING a
Prop-valued `def`. A deliberately-authored oriented definition could
therefore be handed to the closer and DID smuggle content into a square's
proof: the auditor closed the accumulator content square
(`rev xs = revAccL xs []` — literally the standing example named above)
with the fixed template plus one such `def`. What stopped the
demonstration at the last hop was the fail-close in the registry
(duplicate registration for an already-squared definition,
`IsoGen.lean:443-460`) — not the unfold gate. The consequence was bounded
to PROVENANCE: such a square is still kernel-true, so no false mirror is
reachable; what is lost is the evidence that the content came via replay.

**THE REJECTION NOW EXISTS (R-1a, ruled by Mike 2026-08-16 — synthesis
R-1 "both taken").** The unfold-list validation additionally rejects
Prop-typed entries (`Lean.Meta.isProp` on the constant's type, at the
`.defnInfo` check below), so the demonstrated route now fails AT THE GATE
with a named error; the attack is pinned as a negative test
(`Tests/IsoGenGateTests.lean`, the tamper-test convention) so the gate
cannot silently regress.

Threat model, per the two-standard rule: this gate remains a SPEEDBUMP,
reviewed by "does it catch the honest mistake" — which it does; the route
above was deliberate construction, not an honest mistake, and closing it
does NOT make the generator's provenance story a proof. **A determined
author still has other routes** — the same audit records one on the same
page (A1-F9: an `embed S via [fields]` richer embedding's extra fields are
unconstrained in content, so a field proved machinery-side can be carried
into a closer), and the general point stands that no syntactic check on
the invocation can classify content. The bound is A1-F1's bound and it is
unchanged by this fix: PROVENANCE only — a smuggled square is still
kernel-true, so no false mirror is reachable. DO NOT HARDEN this with
semantic classifiers; the per-book provenance audit is the backstop.

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

/-- One registered AGREEMENT square: the theorem, and the CONSTRUCTOR
    LITERAL its statement is specialized at (`.anonymous` = the general,
    unkeyed square). -/
structure SquareEntry where
  /-- the generated theorem -/
  thmName : Name
  /-- the `vars` constructor literal this square is stated at -/
  key : Name := .anonymous
  deriving Inhabited, BEq

/-- The squares registered for one mirror definition. -/
structure MirrorSquares where
  /-- the mirror definition -/
  fnName : Name
  /-- its agreement square(s): either ONE unkeyed entry, or a
      PER-CONSTRUCTOR FAMILY whose members are at DISTINCT literals
      (`[]` = none registered) -/
  agree : List SquareEntry := []
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

/-- Every AGREEMENT square registered for `fn`: the single general one,
    or the whole per-constructor family.

    Handing a closer the whole family cannot redirect a rewrite the way a
    second GENERAL square would, because each member's statement is at a
    DISTINCT constructor literal and so matches only its own occurrences —
    which is exactly why the keyed family is the only shape in which
    multiple agreement squares may exist (ruled 2026-08-16).

    "A lookup matches exactly one" is an INVARIANT OF THE REGISTRY, not a
    separate lookup function: `registerSquare` refuses a duplicate key, so
    at most one entry carries any given key, and there is deliberately no
    key-directed lookup here because no consumer wants one — a caller's
    closer wants the whole family (its own body carries the literals). -/
def agreeSquares (env : Environment) (fn : Name) : List Name :=
  match findSquares env fn with
  | none => []
  | some s => s.agree.map (·.thmName)

/-- Attach a square to its mirror definition, refusing a second square of
    the same class (fail-closed: with first-match lookup a re-registration
    would silently redirect every later closer).

    THE ONE EXCEPTION (ruled 2026-08-16): agreement squares may form a
    PER-CONSTRUCTOR FAMILY — several squares for one definition, each
    stated at a distinct `vars` constructor literal. That is still
    fail-closed in every direction: a duplicate key is refused, a keyed
    square cannot join an unkeyed one, and an unkeyed square cannot join a
    family. -/
def registerSquare (fn : Name) (cls : SquareClass) (thm : Name)
    (key : Name := .anonymous) : CommandElabM Unit := do
  let cur := (findSquares (← getEnv) fn).getD { fnName := fn }
  let next ←
    match cls with
    | .agree =>
      if key == .anonymous then
        unless cur.agree.isEmpty do
          throwError "mirror_iso%: {fn} already has an agreement square \
              ({cur.agree.map (·.thmName)}) — a second UNKEYED one would \
              silently redirect the crossing's rewrite set (fail-closed). \
              Several agreement squares for one definition exist ONLY as a \
              PER-CONSTRUCTOR FAMILY: state each at its own constructor \
              literal in `vars`."
        pure { cur with agree := [{ thmName := thm }] }
      else
        if cur.agree.any (·.key == .anonymous) then
          throwError "mirror_iso%: {fn} already has an UNKEYED agreement \
              square ({cur.agree.map (·.thmName)}), which speaks for EVERY \
              value of the position `{key}` specializes — a keyed family \
              cannot join it (fail-closed)"
        if cur.agree.any (·.key == key) then
          throwError "mirror_iso%: {fn} already has an agreement square at \
              `{key}` ({(cur.agree.filter (·.key == key)).map (·.thmName)}) \
              — a second one at the same literal would make the family's \
              lookup ambiguous, and a lookup must match EXACTLY ONE \
              (fail-closed)"
        pure { cur with agree := cur.agree ++ [{ thmName := thm, key := key }] }
    | .homList | .homScalar =>
      unless cur.homName == .anonymous do
        throwError "mirror_iso%: {fn} already has a homomorphism square \
            ({cur.homName}) — a second one would silently redirect the \
            transport's rewrite set (fail-closed)"
      pure { cur with homName := thm, homIsScalar := cls == .homScalar }
  modifyEnv fun env => mirrorSquareExt.addEntry env next

/-! ## CALLEE RESOLUTION THROUGH NOTATION (O-2, R4 wave 2c)

Callee resolution reads the squared definition's VALUE and looks up each
used constant in the registry. That misses a callee spelled as OPERATOR
NOTATION: `Mirrors/Sorting.lean`'s `qsort` writes its append as `++`
(permitted by the vocabulary practice as unambiguous operator notation),
and its value therefore carries `HAppend.hAppend` and `List.instAppend`
and NEVER `List.append` — so `qsort_map_hom`'s whole remaining distance
(wave 2b: `List.map_append` and nothing else) sat behind a SPELLING.

THE RULED ROUTE (O-2), and why it is this one rather than the other:
admitting `List.map_append` as a LADDER RUNG would put a
content-shaped library lemma — one that RELATES TWO OPERATIONS, the
criterion's own content test — permanently in every square's closer.
The append homomorphism square is not that: it is the SAME artifact
`mirror_iso%` generates for any other callee, `List.append`'s own
refinement square, and a library FUNCTION's square is legal machinery
(it is not a spec NAME, so the collision rule is not in play). So the
square is DECLARED and REGISTERED like any other, and resolution learns
the notation.

WHAT THE NORMALIZATION IS, exactly (`notationSpellings`): a fixed table
from the NOTATION'S INSTANCE CONSTANT to the underlying function whose
square is wanted, plus the projection constants that carry the
notation's spelling to that function's. It fires only when

* the instance constant is ACTUALLY PRESENT in this definition's own
  value — never a general unfolding, and never a guess about what the
  goal might contain; and
* a square is ACTUALLY REGISTERED for the underlying function —
  otherwise nothing at all is added, so a definition whose `++` callee
  has no square is treated exactly as it was (which is why every
  pre-existing square's proof term is unchanged by O-2).

WHY IT IS NOT A CONTENT CHANNEL. The projections it adds
(`HAppend.hAppend`, `Append.append`) are STRUCTURE PROJECTIONS of the
notation classes — definitional unfoldings of the same character as the
invocation's own `unfold [...]` list, and they relate no two operations;
they only rewrite `xs ++ ys` to `List.append xs ys`. The content, such
as it is, is in the SQUARE, which is generated and gated exactly like
every other square. -/

/-- The NOTATION table (O-2). Each row is
    `(instance constant, underlying function, projections to unfold)`;
    see "callee resolution through notation". Deliberately a fixed,
    tiny, EXPLICIT table rather than a general "unfold any instance"
    rule: the only entry is the one with a measured consumer
    (`qsort`'s `++`), and a new one is a visible edit here. -/
private def notationSpellings : List (Name × Name × List Name) :=
  [(``List.instAppend, ``List.append, [``HAppend.hAppend, ``Append.append])]

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
  &" vars " "[" term,* "]"
  &" square " mirrorSquareSpec
  (&" embed " ident &" via " "[" ident,* "]")?
  (&" unfold " "[" ident,* "]")?
  (&" instances " "[" ident,* "]")? : command

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
`howMany (a : α)`) — audit F1.

THE PASS-THROUGH READING (R1-E, 2026-08-14). The FILTER re-render
(Mike's ruling of the same day: a mirror is the closest idiomatic Lean
analog of the BOOK, so `filterRel` takes the book's MODE argument
`(fn : RelMode)` rather than a predicate closure) put a third kind of
binder in front of the table: an argument whose type is CLOSED — it
does not mention the element type at all. The embedding has no action
on such an argument and needs none: it is the SAME value on both sides
of every square (`.fixed`). The scope is deliberately tight — a closed
type, i.e. one with no free variables, so in particular no occurrence
of `α`. A FUNCTION over `α` (`α → Bool`) is still outside the table and
still hard-errors: an `Acl2Embed` is an injection on ELEMENTS and has
no derived action on a function position. -/

/-- How one explicit binder of a mirror definition is READ when the
    square's statement is built. -/
private inductive ArgReading where
  /-- `List α` — enters the homomorphism statement under
      `List.map e.enc`. -/
  | list
  /-- the embedded element type `α` itself — enters under `e.enc`. -/
  | elem
  /-- a CLOSED type the embedding does not act on (`RelMode`, `Bool`,
      `Nat`, …) — the argument passes through both sides of the square
      unchanged, at its own type. -/
  | fixed (ty : Term)

/-- One `vars` entry: a BINDER (an atomic identifier, quantified in the
    square's statement) or a fixed CONSTRUCTOR LITERAL (R4 wave 2a — it
    enters the statement as itself, binds nothing, and KEYS the square in
    the registry's per-constructor family). -/
private inductive VarEntry where
  /-- an atomic identifier: the statement quantifies over it -/
  | binder (id : Ident)
  /-- a nullary constructor literal at a `.fixed` position -/
  | lit (stx : Term) (ctor : Name)

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
        else if !t.hasFVar then
          -- a CLOSED type: no free variables at all, so in particular no
          -- occurrence of the element type — the embedding has no action
          -- on it and the argument passes through both sides unchanged
          readings := readings.push (.fixed (← PrettyPrinter.delab t))
        else
          throwError "mirror_iso%: {fnName}'s explicit argument \
              `{(← x.fvarId!.getDecl).userName} : {t}` is outside the \
              ARGUMENT-READING table.\n\
              OBSERVED: binder type `{t}`; the definition's element type \
              is `{elemTy}`, which OCCURS in that binder type. The three \
              derived readings are `List {elemTy}` (the argument enters \
              the homomorphism statement under `List.map e.enc`), \
              `{elemTy}` itself (it enters under `e.enc`), and any \
              CLOSED type (no free variables — the embedding does not \
              act on it, so the argument passes through both sides \
              unchanged).\n\
              CANDIDATE CAUSES (none asserted, not ranked): (a) a \
              FUNCTION-VALUED argument (e.g. `{elemTy} → Bool`) — an \
              `Acl2Embed` is an injection on ELEMENTS and has no action \
              on a function position, so reading one is a design \
              question, not something this generator may guess; (b) a \
              list over some OTHER type than `{elemTy}`; (c) any other \
              type mentioning `{elemTy}` (`Option {elemTy}`, a product, \
              …) — each such position needs its own derived action of \
              the embedding, which is a design change to the square \
              classes.\n\
              What this failure is NOT: a statement that the declared \
              correspondence is wrong. The declaration never reached the \
              statement builder — this is the reading table's own bound, \
              and widening it is a design change to the square classes, \
              never a hand square (thin-Lean ruling 2026-08-11)."
    return (readings, (← whnf body).isAppOf ``List, instClasses)

/-- THE INSTANCE-FACTS SHAPE CHECK (O-7, ruled 2026-08-18) — see "the
    instance-facts clause" in the header.

    `n` must be a THEOREM whose statement (under any binders) is an
    EQUATION between two terms whose type is proof-irrelevant by
    construction: the head is `Decidable`/`DecidableEq`, or the type
    carries a synthesizable `Subsingleton` instance. Everything else is
    a hard error naming the observed type — which is what makes a
    CONTENT lemma (`List.map_append`, whose equation is at `List β`)
    fail the check rather than reach a closer. -/
private def checkInstanceFact (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  unless ci matches .thmInfo _ do
    throwError "mirror_iso%: `instances [{n}]` is not a THEOREM — the \
        instance-facts clause names PROVED equalities of instances \
        (fail-closed: a definition here would be the unfold list's \
        content channel under another name)"
  forallTelescopeReducing ci.type fun _ body => do
    let some (ty, lhs, rhs) := body.eq?
      | throwError "mirror_iso%: `instances [{n}]`'s statement is not an \
          EQUATION (`{body}`). The clause admits an equality between two \
          INSTANCE terms and nothing else (fail-closed)."
    unless (← isDefEq (← inferType lhs) ty) && (← isDefEq (← inferType rhs) ty) do
      throwError "mirror_iso%: `instances [{n}]`'s two sides do not have \
          the equation's own type `{ty}` — the clause admits an equality \
          between two INSTANCE terms of ONE type (fail-closed)"
    let allowed : Bool :=
      match ty.getAppFn.constName? with
      | some c => c == ``Decidable || c == ``DecidableEq
      | none => false
    unless allowed do
      let sub ← trySynthInstance (← mkAppM ``Subsingleton #[ty])
      unless sub matches .some _ do
        throwError "mirror_iso%: `instances [{n}]` is an equation at \
            `{ty}`, which is neither in the instance-facts allowlist \
            (`Decidable`, `DecidableEq`) nor provably `Subsingleton`.\n\
            The clause exists for ONE thing: two spellings of one \
            INSTANCE ARGUMENT that a `local` spec instance and the \
            ambient one produce (O-7, 2026-08-18). Such an equality is \
            content-free BY CONSTRUCTION — proof-irrelevant, relating \
            no two operations. An equation at any OTHER type CAN carry \
            subject content, so it is refused here (fail-closed): route \
            a bridging fact through a replayed ACL2 book theorem."

/-- Generate one SQUARE for a mirror definition:

    ```
    mirror_iso% app_agree_append for ACL2Lean.Basics.app
      vars [xs, ys]
      square agree (xs ++ ys)

    mirror_iso% app_map_hom for ACL2Lean.Basics.app
      vars [xs, ys]
      square hom list

    mirror_iso% insertOrd_map_hom for ACL2Lean.Sorting.insertOrd
      vars [a, xs]
      square hom list
      embed OrderedEmbed via [ord]
    ```

    The user supplies ONLY the correspondence judgment (which waypoint
    spelling this definition agrees with; which square class its result
    type carries) plus, for a reading that rests on a definition of ours,
    the `unfold [...]` list — DEFINITIONS ONLY, since a definitional
    unfolding cannot introduce content — and, for a homomorphism square
    over an ORDER-USING definition, the `embed S via [fields]` clause
    (the square is only TRUE for an order-respecting embedding, so the
    hypothesis belongs in its statement; see "the order-respect route").
    Everything else — the statement's
    left-hand side, EACH ARGUMENT'S READING (inferred from the
    definition's own binder types, see `ArgReading`), the induction, the
    closer — is fixed. -/
@[command_elab mirrorIsoCmd] def elabMirrorIso : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs > 0 then some ⟨stx[0][0]⟩ else none
  let thmId : Ident := ⟨stx[2]⟩
  let fnId : Ident := ⟨stx[4]⟩
  let varStxs : Array Term := stx[7].getSepArgs.map (⟨·⟩)
  let specStx := stx[10]
  -- the ORDER-RESPECT route (R4 wave 1): an optional RICHER EMBEDDING for
  -- THIS square, plus the fields of it the closer may use. See "the
  -- order-respect route" above for why this is a per-square binder and
  -- not a ladder rung.
  let embedSpec? : Option (Ident × Array Ident) :=
    if stx[11].getNumArgs == 0 then none
    else some (⟨stx[11][1]⟩, stx[11][4].getSepArgs.map (⟨·⟩))
  let unfolds : Array Ident :=
    if stx[12].getNumArgs == 0 then #[] else stx[12][2].getSepArgs.map (⟨·⟩)
  -- THE INSTANCE-FACTS CLAUSE (O-7, ruled 2026-08-18): per-square, scoped
  -- exactly like `embed … via [fields]`, shape-checked below.
  let instanceStxs : Array Ident :=
    if stx[13].getNumArgs == 0 then #[] else stx[13][2].getSepArgs.map (⟨·⟩)
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
  unless varStxs.size == readings.size do
    throwError "mirror_iso%: {fnName} takes {readings.size} explicit \
        arguments but {varStxs.size} vars were given"
  -- THE `vars` ENTRIES (R4 wave 2a): an ATOMIC IDENTIFIER is a BINDER, as
  -- it always was; anything else is a CONSTRUCTOR LITERAL, admitted ONLY
  -- at a `.fixed` position (a closed type the embedding does not act on)
  -- and only as a NULLARY constructor of that type — it enters the
  -- statement as that literal and binds nothing. That literal is the
  -- registry KEY, which is what lets a definition carry a PER-CONSTRUCTOR
  -- FAMILY of agreement squares instead of one general one. The split
  -- is purely syntactic (an atomic ident is a binder, a dotted or applied
  -- term is a literal) so a declaration cannot mean one and read as the
  -- other; a NON-atomic identifier is a hard error naming the dot form.
  let mut vars : Array VarEntry := #[]
  let mut litKeys : Array Name := #[]
  for (v, r) in varStxs.zip readings do
    if v.raw.isIdent then
      unless v.raw.getId.isAtomic do
        throwError "mirror_iso%: the `vars` entry `{v.raw.getId}` is a \
            QUALIFIED identifier. A `vars` binder is an atomic identifier; \
            a CONSTRUCTOR LITERAL must be written in dot form (`.lt`), so \
            that a literal can never be read as a binder name \
            (fail-closed)."
      if v.raw.getId == `e then
        throwError "mirror_iso%: `e` is the embedding binder's reserved \
            name — rename the var"
      vars := vars.push (.binder ⟨v.raw⟩)
    else
      let .fixed tyStx := r
        | throwError "mirror_iso%: a `vars` CONSTRUCTOR LITERAL was given \
            at an argument position whose reading is not `.fixed` — a \
            literal specializes a CLOSED-TYPE (pass-through) position, \
            the one kind of argument the embedding does not act on. At a \
            `List α` or `α` position there is nothing for a literal to \
            specialize (fail-closed)."
      let ctor ← liftTermElabM do
        let tyE ← Term.elabType tyStx
        let e ← instantiateMVars (← Term.elabTerm v (some tyE))
        let .const c _ := e
          | throwError "mirror_iso%: the `vars` literal `{v}` does not \
              elaborate to a NULLARY CONSTRUCTOR of `{tyE}` (it is \
              `{e}`). The per-constructor family is a DATA REFINEMENT of a \
              closed enum position: each member is one constructor, and a \
              constructor CARRYING DATA — or any other term — is outside \
              it (fail-closed, and widening it is a ruling)."
        let .ctorInfo ci ← getConstInfo c
          | throwError "mirror_iso%: the `vars` literal `{v}` elaborates \
              to `{c}`, which is not a CONSTRUCTOR (fail-closed)"
        unless ci.numFields == 0 do
          throwError "mirror_iso%: the `vars` literal `{v}` is the \
              constructor `{c}`, which CARRIES DATA ({ci.numFields} \
              fields) — outside the per-constructor family, which \
              enumerates a closed enum (fail-closed; hard-fail by design \
              until a real witness demands more)"
        pure c
      vars := vars.push (.lit v ctor)
      litKeys := litKeys.push ctor
  if litKeys.size > 1 then
    throwError "mirror_iso%: {litKeys.size} `vars` CONSTRUCTOR LITERALS \
        were given ({litKeys.toList}). A square is keyed by AT MOST ONE \
        literal — the registry's family is per-constructor over ONE enum \
        position, and two keys would make the family's lookup ambiguous \
        (fail-closed)."
  let squareKey : Name := litKeys[0]?.getD .anonymous
  -- the declared unfoldings: DEFINITIONS ONLY (a lemma here would be the
  -- content channel the template gate exists to close)
  let unfoldNames ← unfolds.mapM fun u => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo u
    match env.find? n with
    | some (.defnInfo ui) =>
      -- R-1a (ruled 2026-08-16, off audit A1-F1): `.defnInfo` ALONE lets a
      -- PROP-VALUED `def` through, and the auditor closed the accumulator
      -- CONTENT square that way. Reject the Prop case by name. Speedbump,
      -- honest-mistake standard (two-standard rule): this shuts the
      -- demonstrated route, not every route (A1-F9's `embed … via
      -- [fields]` is the other one on record) — DO NOT HARDEN it with
      -- semantic classifiers. Negative test: `Tests/IsoGenGateTests.lean`.
      if ← liftTermElabM (Lean.Meta.isProp ui.type) then
        throwError "mirror_iso%: `unfold [{n}]` is a PROP-VALUED \
          definition — a Prop-valued def in the unfold list is the \
          content-smuggling channel the 2026-08-16 audit demonstrated \
          (A1-F1) — rejected; unfold accepts non-Prop DEFINITIONS only. \
          Route a bridging fact through a replayed ACL2 book theorem \
          instead."
      pure n
    | _ => throwError "mirror_iso%: `unfold [{n}]` is not a DEFINITION — \
        the square closer unfolds definitions only. A LEMMA here would be \
        exactly the content channel the template gate closes: route a \
        bridging fact through a replayed ACL2 book theorem instead."
  -- the declared INSTANCE FACTS: shape-checked before anything is
  -- generated, so a refusal costs no declaration (O-7)
  let instanceNames ← instanceStxs.mapM fun u => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo u
    liftTermElabM <| checkInstanceFact n
    pure n
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
  -- the EMBEDDING the statement binds, and the fields of it THIS square's
  -- closer may use (the order-respect route — see the header). Default:
  -- the plain `Acl2Embed`, no extra facts.
  let mut embedStruct : Name := ``Acl2Embed
  let mut embedFacts : Array Name := #[]
  if let some (sId, fs) := embedSpec? then
    if cls == .agree then
      throwError "mirror_iso%: an `embed` clause was given for an \
          AGREEMENT square, whose statement is at `SExpr` and binds NO \
          embedding at all — there is nothing for the richer embedding's \
          fields to be about (fail-closed). Declare the `embed` clause on \
          the `hom` square instead."
    let s ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo sId
    unless isStructure env s do
      throwError "mirror_iso%: `embed {s}` is not a STRUCTURE — the \
          richer embedding must be a structure EXTENDING `Acl2Embed`, so \
          that `e.enc` still means the embedding's own map and every \
          registered callee square (stated over `Acl2Embed`) still \
          resolves against it (fail-closed)"
    let parents ← liftCoreM <| getAllParentStructures s
    unless parents.contains ``Acl2Embed do
      throwError "mirror_iso%: `embed {s}` does not EXTEND `Acl2Embed` \
          (its parent structures are {parents.toList}). \
          A homomorphism square's statement is built from `e.enc`, and its \
          callees' registered squares are stated over `Acl2Embed`, so an \
          unrelated structure could neither state the square nor reuse \
          them (fail-closed)"
    embedStruct := s
    embedFacts ← fs.mapM fun f => do
      let n := s ++ f.getId
      unless env.contains n do
        throwError "mirror_iso%: `via [{f.getId}]` is not a field of \
            `{s}` (no constant `{n}`). Only `{s}`'s OWN fields may reach \
            this square's closer — a free-standing lemma here would be \
            the content channel the template gate closes (fail-closed)."
      pure n
  -- the statement (each var at its inferred READING: a `.list` binder is
  -- a list of the element type and enters under `List.map e.enc`; an
  -- `.elem` binder is one element and enters under `e.enc`; a `.fixed`
  -- binder has a CLOSED type and passes through both sides unchanged)
  let sexprC : Term := mkCIdent ``ACL2.SExpr
  let sexprTy : Term ← `(List $sexprC)
  let alphaId : Ident := mkIdent `α
  let eId : Ident := mkIdent `e
  let fnC : Term := mkCIdent fnName
  let varsR : Array (VarEntry × ArgReading) := vars.zip readings
  -- a LITERAL entry enters every position as itself (it is a `.fixed`
  -- argument: the same value on both sides of the square), and binds
  -- nothing
  let varTerms : Array Term := vars.map fun
    | .binder id => (id : Term)
    | .lit s _ => s
  let plainApp : Term := Syntax.mkApp fnC varTerms
  let binders : Array (TSyntax ``bracketedBinderF) ← do
    match cls with
    | .agree => varsR.filterMapM fun (v, r) =>
        match v with
        | .lit _ _ => pure none
        | .binder v =>
          match r with
          | .list => do pure (some (← `(bracketedBinderF| ($v:ident : $sexprTy))))
          | .elem => do pure (some (← `(bracketedBinderF| ($v:ident : $sexprC))))
          | .fixed ty => do pure (some (← `(bracketedBinderF| ($v:ident : $ty))))
    | _ =>
      -- the definition's OWN instance binders, re-bound at the user's
      -- element type (see `mirrorFnShape`): at `α` there is nothing to
      -- synthesise, so without these the statement does not elaborate
      let iB ← instClasses.mapM fun c => do
        `(bracketedBinderF| [$(Syntax.mkApp (mkCIdent c) #[alphaId]):term])
      let eB ← `(bracketedBinderF|
        ($eId:ident : $(Syntax.mkApp (mkCIdent embedStruct) #[alphaId])))
      let vB ← varsR.filterMapM fun (v, r) =>
        match v with
        | .lit _ _ => pure none
        | .binder v =>
          match r with
          | .list => do
            pure (some (← `(bracketedBinderF| ($v:ident : List $alphaId:ident))))
          | .elem => do
            pure (some (← `(bracketedBinderF| ($v:ident : $alphaId:ident))))
          | .fixed ty => do
            pure (some (← `(bracketedBinderF| ($v:ident : $ty))))
      pure (iB ++ #[eB] ++ vB)
  let encoded : Array Term ← varsR.mapM fun (v, r) =>
    match v with
    | .lit s _ => pure s
    | .binder v =>
      match r with
      | .list => `(List.map ($eId:ident).enc $v:ident)
      | .elem => `(($eId:ident).enc $v:ident)
      | .fixed _ => pure v
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
  -- (an agreement callee may carry a whole PER-CONSTRUCTOR FAMILY; each
  -- member is stated at a distinct literal, so the family cannot redirect
  -- a rewrite the way a second GENERAL square would — see `agreeSquares`)
  let usedConsts : List Name := di.value.getUsedConstants.toList
  let squaresOf (c : Name) : List Name :=
    match cls with
    | .agree => agreeSquares env c
    | _ =>
      match findSquares env c with
      | some s => if s.homName == .anonymous then [] else [s.homName]
      | none => []
  let calleeSquares : List Name := usedConsts.flatMap squaresOf
  -- THE NOTATION NORMALIZATION (O-2, R4 wave 2c) — see "callee
  -- resolution through NOTATION" in the header. A mirror definition that
  -- spells a callee as OPERATOR NOTATION (`xs ++ ys`) carries the
  -- notation's INSTANCE in its value, never the underlying function, so
  -- plain callee resolution cannot see the function's registered square.
  -- The table below is keyed on the INSTANCE CONSTANT ACTUALLY PRESENT IN
  -- THIS DEFINITION'S VALUE and does two things, both fail-closed:
  -- resolve the square of the underlying function, and add the notation's
  -- own PROJECTIONS to the closer's set so the goal's notation spelling
  -- meets the square's. Both are added ONLY when a square is actually
  -- registered for the underlying function, so a definition whose callee
  -- has no square is treated exactly as before (and every pre-existing
  -- square's proof term is unchanged).
  let mut notationUnfolds : Array Name := #[]
  let mut notationSquares : List Name := []
  for (instC, fnUnder, projs) in notationSpellings do
    if usedConsts.contains instC then
      let sqs := squaresOf fnUnder
      unless sqs.isEmpty do
        notationSquares := notationSquares ++ sqs
        notationUnfolds := notationUnfolds ++ projs.toArray
  -- THE FIXPOINT-GUARD CAPABILITY (R4 wave 2g — `IsoKit.lean`'s
  -- `fixpointGuardEqns?`). A guarded fixpoint recursion's own `eq_def`
  -- LOOPS the closer, so it is replaced by the definition's own two
  -- GUARDED equations. Applied to the squared definition and to every
  -- declared reading alike; a definition that is not one is handed its
  -- `eq_def` exactly as before.
  let mut kitNames : Array Name := #[]
  let mut isFixpoint := false
  for n in #[fnName] ++ unfoldNames do
    match ← fixpointGuardEqns? n with
    | some (p, q) => isFixpoint := true; kitNames := kitNames ++ #[p, q]
    | none => kitNames := kitNames.push n
  -- A FIXPOINT square's callee HOM squares enter REVERSED: what the
  -- guarded equations need from them is the guard NORMALISED OUT of the
  -- embedding's image (`bnext (map e.enc xs)` ↦ `map e.enc (bnext xs)`,
  -- which `map_inj_iff` then strips), and the forward direction was
  -- measured to leave the guard's side condition undischargeable. Only
  -- the new class is affected — an AGREE square's callee squares are
  -- forward as before, and so is every pre-existing square.
  let squareNames : Array Name :=
    (calleeSquares ++ notationSquares).eraseDups.toArray
  let reversed : Bool := isFixpoint && (match cls with
    | .agree => false | _ => true)
  -- the declared INSTANCE FACTS go LAST, so every square that declares
  -- none is handed exactly the set it was handed before O-7 (and its
  -- proof term is unchanged)
  let lemmaNames : Array Name :=
    kitNames ++ notationUnfolds
      ++ (if reversed then #[] else squareNames)
      ++ instanceNames
  let mut lemmas ← lemmaNames.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  if reversed then
    for n in squareNames do
      lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma|
        ← $(mkCIdent n):term))
  if isFixpoint then
    for n in fixpointExtraLemmas do
      lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma|
        $(mkCIdent n):term))
  -- the declared embedding's own fields, AT THIS SQUARE'S BINDER: scoped
  -- exactly like a registered callee square, never a ladder rung
  for f in embedFacts do
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma|
      $(Syntax.mkApp (mkCIdent f) #[eId]):term))
  -- THE INDUCTION (W9's fallback, ruled 2026-08-16): a recursive
  -- definition keeps `fun_induction`, byte-for-byte; a NON-RECURSIVE one
  -- has no functional induction principle at all, and takes the
  -- definition's own case analysis instead. Decided off the DEFINITION,
  -- not by swallowing a tactic failure.
  let inductTac : TSyntax `tactic ←
    if Lean.Tactic.FunInd.isFunInductName env (fnName ++ `induct) then
      `(tactic| fun_induction $plainApp)
    else
      `(tactic| fun_cases $plainApp)
  -- THE DEFINITION-DIRECTED CASE SPLIT (W7's capability, ruled
  -- 2026-08-16): emitted ONLY when the definition's own match leaves an
  -- argument undestructured, so every other square's script — and hence
  -- its proof term — is exactly what it was.
  let splitCtor? ← liftTermElabM <| undestructuredGuardCtor? fnName
  let proof ← match splitCtor? with
    | none => `(by
        $inductTac:tactic <;> mirror_square_close [$lemmas,*])
    | some c => `(by
        $inductTac:tactic <;>
          mirror_square_close_split $fnId guard $(mkCIdent c) [$lemmas,*])
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
        `{fnName}`; embedding `{embedStruct}` with fields \
        {embedFacts.toList}; declared instance facts \
        {instanceNames.toList}; the closer was given the lemma set \
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
  registerSquare fnName cls thmName squareKey

end ACL2Lean.MirrorProofs
