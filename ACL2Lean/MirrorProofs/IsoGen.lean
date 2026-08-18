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

THE FIXED KIT'S ADMISSION CRITERION (as widened by the two rulings of
2026-08-14): **`rfl`-lemmas + TWO NAMED PLUMBING FAMILIES — the
embedding's `inj` iff, and Bool/decide coercions** — nothing else.
Concretely:

* the `rfl`-lemmas are the constructor-case equations of a core
  operation, true by definitional unfolding. Nothing that RELATES two
  operations is admitted, because that is where content lives.
* `enc_inj_iff` is the FIRST plumbing family. It is PLUMBING, per the
  ruling: a square is a statement of DEFINITIONAL CORRESPONDENCE about
  OUR OWN definitions, and `Acl2Embed.inj` is the embedding's own
  defining field — admitting it lets an element-position homomorphism
  square rewrite `e.enc a = e.enc b` to `a = b` (the list form,
  `map_inj`, was already plumbing in the transport closer). Content
  still arrives ONLY via replay: injectivity says nothing about any
  mirror definition, so it cannot close a misaligned square — it only
  removes the encoding from an element comparison.
* `Bool.decide_eq_true` (`decide (b = true) = b`) is the SECOND
  plumbing family, admitted by ruling 2026-08-14. It is not a
  `rfl`-lemma (it is `cases b <;> rfl`), and it is admitted for the
  same reason: it is CONTENT-FREE. A mirror spec decides a `Bool`
  through a `Prop` (`decide (a ≤ b)` under a `TotalOrder` instance)
  where the waypoint reading has the plain `Bool` (`lexorderB a b`);
  the two are TWO SPELLINGS OF ONE BOOL, and this rung collapses them.
  It relates no two operations, mentions no mirror definition, and
  says nothing about any recursion — so it cannot rescue a misaligned
  square; it can only delete a `decide`/`= true` coercion.
  `Bool.false_eq_true` (`(false = true) = False`, R4 wave 2a) is the
  SAME family and joins it under the SAME clause — the `Bool` `false`
  and the `Prop` `False` are two spellings of one thing, it relates no
  operations and mentions no definition. It is a LEMMA rung, not a
  capability, so it is inside the criterion as already written rather
  than a new ruling; its consumer is W3's `filterRel_map_hom`, whose
  whole residual after the order field had done its work was
  `⊢ … = if false = true then … else …` (measured at R4 wave 1 stage 4
  and REPRODUCED VERBATIM at wave 2a before this rung was added).
  `Bool.and_eq_true` (`((a && b) = true) = (a = true ∧ b = true)`, R4
  wave 2c, DECISION O-3) is the THIRD member of the same family and
  joins it as a MEMBER ADDITION to an already-ruled family rather than
  as a new ruling. It says exactly that the `Bool` `&&` and the `Prop`
  `∧` are two spellings of one conjunction: it relates no two
  OPERATIONS (both sides are the same conjunction, once in each
  universe), mentions no mirror definition and no recursion, so it
  cannot rescue a misaligned square — it can only cross the
  `Bool`/`Prop` seam a mirror `Prop` and a `Bool`-valued reading sit on
  either side of. Its two MEASURED consumers (wave 2b recorded both
  residuals verbatim before the rung existed) are `ordered_agree_
  orderedpRec` — the mirror spells `Ordered`'s adjacent-pair chain as
  `∧`, the `chain2Rec` reading as `&&` — and `Permuted`'s agree square.
  HONESTLY, AND ON THE RECORD: the ladder's table below used to name
  this lemma BY NAME in the deliberately-NOT-admitted column (as an
  example of "any OTHER `Bool`/`Prop` fact"), which is why wave 2b
  escalated it (J-2b-3) instead of taking it; the table row is corrected
  in place below rather than silently, and `decide_eq_true_eq` — the
  other name that column carried — is NOT admitted and stays named
  there.

  **THE RUNG IS ADMITTED IN ONE DIRECTION (`←`), AND THE OTHER
  DIRECTION WAS MEASURED TO REGRESS TWO LIVE SQUARES** (R4 wave 2c,
  recorded because it is the kind of thing that looks like a typo
  later). Added FORWARDS (`(a && b) = true ↦ a = true ∧ b = true`) the
  rung also rewrites HYPOTHESES, and a `bif`-splitting square's own case
  hypothesis is exactly of that shape: `filterRel_lt_agree_filterLtL`
  and `filterRel_gt_agree_filterGtL` STOP CLOSING, because `simp_all`
  can no longer use the split conjunction on the goal's `bif (a && b)`
  condition (measured residuals: case 2 becomes
  `⊢ … = bif true && true then … else …` and case 3
  `h✝ : ¬(lexorderB ev head✝ = true ∧ (!decide (head✝ = ev)) = true)`
  with the `bif` untouched). Added BACKWARDS — merging a `Prop`
  conjunction of `Bool` equations INTO the single `Bool` equation — it
  closes `ordered_agree_orderedpRec` and leaves all 23 pre-existing
  squares closing. Same lemma, same seam, and the `←` is the direction
  that carries the mirror's `Prop` spelling to the reading's `Bool`
  spelling, which is the direction every consumer wants.

Admitted, each `rfl` rung pinned by the examples directly below (so the
criterion cannot rot silently):

| rung                | is | deliberately NOT admitted    |
| ------------------- | -- | ---------------------------- |
| `List.map_nil/cons` | `List.map`'s own two cases     | `List.map_append` |
| `List.nil/cons_append` | `++`'s own two cases        | `List.append_assoc`, `List.append_nil` |
| `List.length_nil/cons` | `List.length`'s own two cases | `List.length_append` |
| `Bool.cond_true/false` | `cond`'s own two cases   | any `lexorderB`/order fact |
| `ite_true`/`ite_false` | `ite`'s own two cases    | `if_pos`/`if_neg`, `List.map_eq_nil_iff`, any conditional-rewrite discharge |
| `decide_true`/`decide_false` | `decide`'s own two VALUES (R4 wave 2d-prep) | `eq_comm` and `decide (a = b) = decide (b = a)` — BOTH MEASURED TO REGRESS live squares, see `MirrorProofs/SortingPermSquares.lean` |
| `enc_inj_iff`       | `Acl2Embed.inj` as an iff   | any OTHER embedding property |
| `Bool.decide_eq_true` | the `decide`/`= true` coercion | any OTHER `Bool`/`Prop` fact (`decide_eq_true_eq`, …) |
| `Bool.false_eq_true` | the same family: `false`/`False` | as above — still nothing that relates two operations |
| `← Bool.and_eq_true` | the same family: `&&`/`∧`, BACKWARDS ONLY (O-3, wave 2c) | as above — `decide_eq_true_eq` in particular; and the FORWARD direction of this very lemma (measured: it regresses two live squares) |

`decide_true`/`decide_false` (R4 wave 2d-prep, 2026-08-18) are the
`decide` twin of the same pair and are admitted under the SAME clause:
they are `rfl` (pinned below by the same `example` device), they are
one operation's own two VALUES, and they relate nothing. Core states
both over an ARBITRARY `Decidable` instance
(`∀ (h : Decidable True), @decide True h = true`), which is what lets
them fire where a reading and a mirror reached the same `decide` by
different routes. Their consumer is `memb`'s agree square
(`MirrorProofs/SortingPermSquares.lean`), whose residual before them
was `⊢ true = match decide True with | true => true | false => …`,
verbatim. NOT admitted, and MEASURED-AND-REFUTED rather than merely
declined: `eq_comm` and `decide (a = b) = decide (b = a)`, the two
candidate rungs for the equality-test ORIENTATION gap the same page
records — each regresses live squares (five and four respectively; the
residuals are on that page).

`ite_true`/`ite_false` (R4 wave 1, 2026-08-14) are the `ite` twin of the
already-admitted `cond` pair and are admitted under the SAME clause of
the criterion — they are `rfl` (pinned below, by the same `example`
device as the other `rfl` rungs), they are one operation's own two
cases, and they relate nothing. Their consumer is the ORDER-RESPECT
route below: once the embedding's order field has rewritten a
homomorphism square's `if e.enc a ≤ e.enc b` condition to the SOURCE
condition, the split's own case hypothesis reduces it to `True`/`False`
and these two rungs finish the branch. Measured on
`insertOrd_map_hom`: without them the two cases survive as
`⊢ … = if True then … else …` and its `False` twin, verbatim.

THE LINE (R4 wave 1, AMENDED by ruling R-6/W7 of 2026-08-16): the kit
grows by LEMMA rungs that meet the criterion (`rfl`-lemmas, the two
plumbing families), and **the closer's ONE structural capability beyond
the lemma kit is the definition-directed case split (ruled 2026-08-16):
it case-splits ONLY arguments the squared definition's own match leaves
undestructured — it reads the definition, it never searches** (see "the
definition-directed case split" below for how the argument is read and
where it fails closed). Everything else stays outside the line: GROUND
EVALUATION (W3's stage-3 record) is still NOT taken and is still a
ruling if it is ever wanted.

(`Acl2Embed` has exactly two fields, `enc` and `inj`; there is no order
field, so an element-position square that needs the embedding to RESPECT
an order fails closed against `Acl2Embed` — which is why the ORDER
dimension arrives as a SEPARATE, RICHER EMBEDDING declared per square,
below, and not as another ladder rung.)

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
two `bif`/`≤` residuals survive verbatim; with it, the square closes.)

## THE ORDER-RESPECT ROUTE — a RICHER EMBEDDING, per square (R4 wave 1)

A homomorphism square over an ORDER-USING mirror definition
(`insertOrd`, `isort`, `merge2`, `msort`) is NOT TRUE for an arbitrary
`Acl2Embed`: `List.map e.enc (insertOrd a xs) = insertOrd (e.enc a)
(List.map e.enc xs)` says the encoded insertion takes the same branch as
the source insertion, which holds exactly when the embedding RESPECTS
the order. So the missing ingredient is not a lemma the closer may
reach for — it is a HYPOTHESIS the square's own statement must carry.

The route, therefore, is the SQUARE'S BINDER, declared per invocation:

    mirror_iso% insertOrd_map_hom for ACL2Lean.Sorting.insertOrd
      vars [a, xs]
      square hom list
      embed OrderedEmbed via [ord]

`embed S via [f₁, …]` replaces the statement's embedding binder
`(e : Acl2Embed α)` by `(e : S α)`, where `S` must be a structure
EXTENDING `Acl2Embed` (checked; anything else is a hard error), and
makes `S.fᵢ e` — and only those — available to THAT square's closer.
`e.enc` still means `Acl2Embed.enc e.toAcl2Embed`, so a square declared
over the richer embedding still resolves the REGISTERED squares of
callees stated over the plain one (`msort` calling `evens`).

WHY THIS IS NOT A LADDER RUNG, and why it is safe (the criterion-text
addition ruled on at merge):

* it is not GLOBAL. A ladder rung is available to every square forever;
  `S.fᵢ` reaches exactly the one invocation that declares it. That is
  the same scoping a REGISTERED CALLEE SQUARE has, and the same
  visibility: the fact is named in the source of the square that uses
  it, not hidden in the generator.
* it is PROVED PER INSTANCE, not assumed. `S` is a structure; every
  `S α` value in the tree is a definition whose fields are discharged
  where it is declared (`intOrderedEmbed`, `MirrorProofs/OrderBridge.lean`
  — its order field is `lexorderB_intEmbed`, itself proved from
  `LexorderOrder.lean`'s core-logic theorems). Nothing is trusted.
* it CANNOT rescue a misaligned square. `S`'s fields are facts about the
  EMBEDDING — exactly the character of `Acl2Embed.inj`, the first
  plumbing family. They mention no mirror definition and relate no two
  operations, so they cannot supply a definitional correspondence that
  is not there; they can only remove the encoding from a comparison.
  (Measured: `insertOrd_map_hom` still requires `insertOrd`'s own
  equations and `ite`'s two cases; the order field alone closes
  nothing.)
* it makes the square STRONGER-HYPOTHESISED, never weaker-concluded:
  the statement is the same equation, over a smaller class of
  embeddings — the class in which it is true.

The gate stays fail-closed in both directions: `embed` on an `agree`
square is a hard error (that statement has no embedding binder at all),
a non-structure or a structure that does not extend `Acl2Embed` is a
hard error, and a name that is not a field of `S` is a hard error.

AND, PLAINLY (the A1-F9 amendment, ruled 2026-08-16): those four checks
are STRUCTURAL — they check that `S` is a richer embedding and that the
named fields are its own. **The CONTENT of an extra field is not checked
by anything, and cannot be: a field is whatever its declaration says, so
a field proved machinery-side can be carried into a square's closer.**
`ord` is honest because it is a fact about the EMBEDDING alone (it
mentions no mirror definition and relates no two operations) and is a
HYPOTHESIS of the square's statement — but that judgement is made at
REVIEW TIME, by reading the field, not by this generator. Extra embed
fields are therefore REVIEW-TIME CONTENT-CHECKED. This is the audit's
recorded second route past the unfold gate (A1-F9,
`docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md`), and the bound is
A1-F1's: PROVENANCE only — such a square is still kernel-true, so no
false mirror is reachable. DO NOT HARDEN this with semantic classifiers;
the per-book provenance audit is the backstop.

## THE INSTANCE-FACTS CLAUSE — `instances [...]`, per square (O-7, 2026-08-18)

The third per-square channel, modelled EXACTLY on the `embed … via
[fields]` scope above; ruled by the orchestrator 2026-08-18 (O-7, R4
wave 2e) to resolve J-2b-4's PLACEMENT question.

THE PROBLEM. A mirror spec may declare an instance `local`
(`Mirrors/Sorting.lean`'s `decEqOfOrder`, deliberately `local`+low
priority so `qsort` carries no `[DecidableEq α]` binder). A definition
elaborated INSIDE that file then carries it, while a square elaborated
OUTSIDE picks up the ambient `instDecidableEqSExpr`; the two print
identically without `pp.explicit`, the residual is `X = X` differing in
ONE INSTANCE ARGUMENT, and a registered callee square is therefore TRUE
and CANNOT FIRE (measured: waves 2b/2c/2d, `SortingSquares.lean` W13 and
its Q4 postscript). Neither existing slot can carry the fact that
dissolves it: `unfold [...]` is DEFINITIONS ONLY and hard-errors on a
lemma, and a LADDER RUNG is impossible because such a fact names a
MIRROR SPEC constant while this module imports only `ACL2Lean.Syntax`.

WHAT IT IS: `instances [thm₁, …]` makes those theorems — and only those
— available to THAT square's closer, as `embed S via [f]` does `S.f e`.

THE SHAPE CHECK (mechanical, and the whole of it). Each named theorem's
statement must be an EQUATION whose two sides have the equation's own
type, and that type's head must be in the small named allowlist
`{Decidable, DecidableEq}` or carry a synthesizable `Subsingleton`
instance. Anything else is a hard error naming the observed type.

WHY THAT CRITERION (the `ord` field's argument, and why this is a
criterion and not a taste call): an equality between two INSTANCES of a
subsingleton class is CONTENT-FREE BY CONSTRUCTION — both sides were
provably equal before the fact existed, so it carries no subject matter,
relates no two operations, mentions no recursion, and cannot supply a
definitional correspondence that is not there; all it can do is make two
spellings of ONE instance argument meet. Proved PER INVOCATION
(`Subsingleton.elim`), never assumed, never global.

HONESTLY (the A1-F9 amendment's sibling): the check is STRUCTURAL — it
rejects a content lemma by its TYPE, which is what makes it mechanical,
and a determined author can still write a theorem that satisfies it. The
bound is A1-F1's, unchanged: PROVENANCE only — such a square is still
kernel-true, so no false mirror is reachable. Speedbump standard; DO NOT
HARDEN it with semantic classifiers. Negative test:
`Tests/IsoGenGateTests.lean` (the file's fourth).

## THE DEFINITION-DIRECTED CASE SPLIT (ruled 2026-08-16 — R4 wave 2a/W7)

The one structural capability the closer has. Its consumer is the
BOOK-FAITHFUL UNDESTRUCTURED ARM: the mirror `merge2` renders the book's
`(if (consp x) (if (consp y) … x) y)` exactly, so its second arm does not
destructure the first list (`| xs, [] => xs`), and Lean emits that
equation GUARDED —

    Sorting.merge2.eq_2 : ∀ {α} [TotalOrder α] (x : List α),
      (x = [] → False) → Sorting.merge2 x [] = x

— handing the template a case whose scrutinee is a bare variable plus a
guard. Neither square could get past it (the residuals are on the witness
page, `MirrorProofs/Sorting.lean` W7), and the measured distance was ONE
case split on that argument plus the EXISTING kit.

WHAT THE CAPABILITY IS, exactly:

* the ARGUMENT IS READ OFF THE DEFINITION, never off the goal and never
  by search. `undestructuredArgPos?` below walks the definition's OWN
  equations; an equation with a GUARD hypothesis (`v = <pat> → False`)
  names the variable the arm left undestructured, and that variable's
  POSITION IN THAT EQUATION'S OWN LEFT-HAND SIDE is the argument index.
  A definition with no guarded equation yields no index and the emitted
  script is EXACTLY the pre-ruling one (which is why every pre-existing
  square's proof term is unchanged).
* it fires ONLY where the kit alone failed: the emitted script is
  `first | (close; done) | (split <;> close)`, so a case the ladder
  closes is closed by the ladder, unsplit.
* it is ONE split of ONE argument by the argument's OWN constructors —
  not a `split` of whatever `match`/`ite` happens to be in the residual,
  and not a search for something to case on. Two DIFFERENT undestructured
  positions across the equations is a HARD ERROR, not two splits.
* it fails closed at the goal too: if the definition's application in the
  goal carries a non-variable at that position, the tactic hard-errors
  rather than guessing.

WHY IT IS NOT A CONTENT CHANNEL. A case split introduces no lemma and no
fact: it replaces one goal by the goal at each constructor of a type,
which is definitional case analysis on data the definition ITSELF
analyses in another arm. It cannot relate two operations, so it cannot
supply a definitional correspondence that is not there — the misaligned
reading still fails (probed: a `merge2` square declared against a
deliberately wrong reading still hard-errors, see the witness page).

## THE `fun_cases` FALLBACK (ruled 2026-08-16 — R4 wave 2a/W9)

`fun_induction` needs a functional INDUCTION principle, and Lean derives
none for a NON-RECURSIVE definition, so the template used to fail before
any goal existed ("No functional induction theorem for `Sorting.odds`").
That bound is general, not an `odds` quirk (`relMode` and `permWitness`
are non-recursive spec definitions too).

The fallback is mechanical and decided at ELABORATION time, off the
definition, exactly like the split: if a functional induction principle
EXISTS for the definition (`Lean.Tactic.FunInd.isFunInductName` on
`<fn>.induct` — true exactly for structurally/well-founded recursive
definitions), the template emits `fun_induction`, UNCHANGED; otherwise it
emits `fun_cases`, which supplies the definition's own case analysis with
NO induction hypotheses. It is NOT a `first | fun_induction | fun_cases`
combinator: a recursive definition can never take the fallback, so a
`fun_induction` failure for any OTHER reason still hard-errors instead of
being silently swallowed. And `fun_cases` adds no capability of its own —
it is the same "the definition's own case analysis" the induction
principle carries, minus the IHs. -/

section LadderPins

/-- The fixed kit's `rfl` rungs are DEFINITIONAL — pinned, so the
    admission criterion above cannot rot silently. (The two PLUMBING
    FAMILIES are the ruled exceptions and are NOT `rfl`: `enc_inj_iff`
    is proved from the embedding's own `inj` field above, and
    `Bool.decide_eq_true` is a `cases`-lemma of core, whose STATEMENT is
    pinned separately below.) -/
example (f : α → β) : List.map f ([] : List α) = [] := rfl
example (f : α → β) (a : α) (as : List α) :
    List.map f (a :: as) = f a :: List.map f as := rfl
example (as : List α) : [] ++ as = as := rfl
example (a : α) (as bs : List α) : (a :: as) ++ bs = a :: (as ++ bs) := rfl
example : ([] : List α).length = 0 := rfl
example (a : α) (as : List α) : (a :: as).length = as.length + 1 := rfl
example (x y : α) : (bif true then x else y) = x := rfl
example (x y : α) : (bif false then x else y) = y := rfl
example (x y : α) : (if True then x else y) = x := rfl
example (x y : α) : (if False then x else y) = y := rfl
example : decide True = true := rfl
example : decide False = false := rfl

/-- The SECOND plumbing family, pinned by its statement: the rung says
    exactly that `decide (b = true)` and `b` are two spellings of one
    `Bool`, and nothing more. -/
example (b : Bool) : decide (b = true) = b := Bool.decide_eq_true

/-- The same family's second member (R4 wave 2a), pinned the same way:
    it says exactly that the `Bool` `false` and the `Prop` `False` are
    two spellings of one thing. -/
example : (false = true) = False := Bool.false_eq_true

/-- The same family's THIRD member (R4 wave 2c, decision O-3), pinned
    the same way: it says exactly that the `Bool` `&&` and the `Prop`
    `∧` are two spellings of one conjunction, and nothing more. -/
example (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) :=
  Bool.and_eq_true a b

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
          Bool.cond_true, Bool.cond_false, ite_true, ite_false,
          decide_true, decide_false,
          enc_inj_iff, Bool.decide_eq_true, Bool.false_eq_true,
          ← Bool.and_eq_true, $xs,*]))

/-- The CONSTRUCTOR that the definition's OWN match leaves an argument
    UNDESTRUCTURED against, in a GUARDED equation — `none` when no
    equation of `fnName` carries a guard, which is the ordinary case and
    leaves the emitted script exactly as it was before the 2026-08-16
    ruling.

    Read off the DEFINITION, never off the goal (see "the
    definition-directed case split"): Lean emits an undestructured arm as
    an equation with a guard hypothesis `(v = <pat> → False)` — for
    `merge2.eq_2`, `(x = [] → False)` — and the pattern's head
    CONSTRUCTOR is what identifies that guard again in the case
    `fun_induction` builds from that very equation. (The equation's
    ARGUMENT POSITION is not usable for this: `fun_induction` UNFOLDS the
    definition in the goal, so by the time the closer runs there may be
    no application of it left to count arguments in.) Fail-closed: two
    DIFFERENT guard constructors across the equations is a hard error —
    the ruled capability is ONE split. -/
private def undestructuredGuardCtor? (fnName : Name) :
    MetaM (Option Name) := do
  let some eqns ← getEqnsFor? fnName | return none
  let mut found : Option Name := none
  for eqn in eqns do
    let ci ← getConstInfo eqn
    let ctor? ← forallTelescopeReducing ci.type fun xs body => do
      let some (_, lhs, _) := body.eq? | return (none : Option Name)
      unless lhs.getAppFn.isConstOf fnName do return none
      for x in xs do
        let .forallE _ dom bod _ ← inferType x | continue
        unless bod.isConstOf ``False do continue
        let some (_, gl, gr) := dom.eq? | continue
        unless gl.isFVar do continue
        let .const c _ := gr.getAppFn | continue
        unless (← getConstInfo c).isCtor do continue
        return some c
      return none
    if let some c := ctor? then
      match found with
      | none => found := some c
      | some d =>
        unless c == d do
          throwError "mirror_iso%: {fnName}'s own equations leave \
            arguments undestructured against TWO DIFFERENT constructors \
            (`{d}` and `{c}`). The ruled closer capability is ONE \
            definition-directed case split, so this definition is outside \
            it (fail-closed — a second split would be a new capability, \
            i.e. a ruling)."
  return found

open Lean Elab Tactic Meta in
/-- THE DEFINITION-DIRECTED CASE SPLIT (ruled 2026-08-16), as a tactic.
    `guard c` is the constructor `undestructuredGuardCtor?` read off the
    definition's own guarded equation; `fun_induction` puts THAT
    equation's guard into the case's context, so the tactic finds it by
    its shape (`v = c … → False`, `v` a variable) and case-splits `v`.

    It does not search: it matches ONE hypothesis shape, the one the
    definition's own equation contributes, and requires EXACTLY ONE
    match — zero or several is a hard error rather than a choice. -/
elab "mirror_definition_split " fnId:ident " guard " ctorId:ident :
    tactic => do
  let fnName ← realizeGlobalConstNoOverloadWithInfo fnId
  let ctor ← realizeGlobalConstNoOverloadWithInfo ctorId
  let goal ← getMainGoal
  let hits ← goal.withContext do
    let mut hits : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let .forallE _ dom bod _ ← instantiateMVars d.type | continue
      unless bod.isConstOf ``False do continue
      let some (_, gl, gr) := dom.eq? | continue
      unless gl.isFVar && gr.getAppFn.isConstOf ctor do continue
      hits := hits.push gl.fvarId!
    pure hits
  unless hits.size == 1 do
    throwError "mirror_definition_split: this case carries \
        {hits.size} guard hypotheses of the shape `<var> = {ctor} … → \
        False` — the shape `{fnName}`'s own undestructured equation \
        contributes, and the split needs EXACTLY ONE (fail-closed: it \
        never picks among candidates, and it never manufactures one)"
  let subs ← goal.cases hits[0]!
  replaceMainGoal (subs.map (·.mvarId)).toList

open Lean.Parser.Tactic in
/-- The square closer WITH the definition-directed case split available
    (emitted only for a definition whose own match leaves an argument
    undestructured — see `undestructuredGuardCtor?`).

    The ladder is unchanged and runs FIRST: the split fires only where
    the kit alone did not CLOSE the case (`; done` is what makes that
    true — a partial simplification must not count as success and hide
    the case). -/
macro "mirror_square_close_split " fnId:ident " guard " c:ident
    " [" xs:simpLemma,* "]" : tactic =>
  `(tactic|
    (first
      | (mirror_square_close [$xs,*]; done)
      | (mirror_definition_split $fnId guard $c <;>
          mirror_square_close [$xs,*])))

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
  -- the declared INSTANCE FACTS go LAST, so every square that declares
  -- none is handed exactly the set it was handed before O-7 (and its
  -- proof term is unchanged)
  let lemmaNames : Array Name :=
    #[fnName] ++ unfoldNames ++ notationUnfolds
      ++ (calleeSquares ++ notationSquares).eraseDups.toArray
      ++ instanceNames
  let mut lemmas ← lemmaNames.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
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
