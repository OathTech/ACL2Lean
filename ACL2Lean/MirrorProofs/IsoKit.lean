import ACL2Lean.Syntax

/-!
# THE MIRROR SQUARE KIT — the transfer kit's core, the closing ladder, and
the closer (split out of `MirrorProofs/IsoGen.lean`, R4 wave 2g)

A VERBATIM move. `IsoGen.lean` had reached the 1500-line module-size norm
and the FIXPOINT-GUARD capability (below) could not land in it; the seam
this file cuts on is the one the ratchet asks for — the KIT (the
embedding structures, the ladder's rungs and their pins, and the square
closer) on this side, `mirror_iso%`'s ELABORATOR on the other. Nothing
was restated: same namespace, same names, same statements, same proofs.

`IsoGen.lean`'s header still carries the template's criterion text and
the ladder's rationale, and it is where a reader should start; this file
is what that text is about.
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

/-! ### THE `Option` ROW of the data-refinement calculus (close-out arc
item 2, 2026-08-18)

ACL2's single most pervasive return shape is VALUE-OR-NIL: `MEMBER`,
`ASSOC`, `PERM-COUNTER-EXAMPLE` and every other search function return
the thing they found, or `nil` when there is nothing to return. Lean
renders that shape as `Option α`, and the row below is that rendering
as a REFINEMENT MAP, keyed by the TYPE SHAPE and by nothing else:

    none    ↦ SExpr.nil
    some a  ↦ e.enc a

i.e. an `Acl2Embed (Option α)` built from an `Acl2Embed α`. It is a row
of the same calculus `Acl2Embed` and the `ArgReading` table are rows of
(`IsoGen.lean`'s "the frame: data refinement"), and it carries NO
constant of any consuming spec — the only inputs are the underlying
embedding and the side condition below.

**THE FAIL-CLOSED SHAPE CHECK, and it is the row's whole content.** The
map above is injective ONLY IF the underlying encoding AVOIDS `nil`:
otherwise `none` and `some a₀` (for the `a₀` with `e.enc a₀ = nil`) have
the same image, and the refinement conflates "nothing was found" with
"`nil` was found" — which is exactly the conflation ACL2 itself lives
with and a Lean `Option` does not. So the side condition is a
HYPOTHESIS of the row's constructor, in the same style as
`OrderedEmbed`'s `ord` field: the row cannot be BUILT without it, and
the obligation is discharged where the instance is declared
(`optIntEmbed`, `MirrorProofs/OrderBridge.lean`, from `intEmbed`'s
integer-atom image). There is no unchecked variant to reach for.

The consequence is a real BOUND on the row, and it is stated here
because it is the reason the row is an ELEMENT-TYPE row and not a
RESULT-TYPE one: at the ACL2 value type itself (`α := SExpr`, the
identity encoding) the side condition is FALSE, so an `Option
SExpr`-valued mirror function has no refinement to the ACL2 values at
all — it distinguishes cases the ACL2 function conflates, and no book
theorem can supply the difference. A `mirror_transport%` crossing is
stated at `SExpr` by construction, so an Option-VALUED spec definition
fails closed there, while an Option-TYPED ELEMENT (this row) goes
through. -/

/-- **A VALUE-OR-NIL EMBEDDING** — a richer embedding whose element type
    has a `default`, and which sends that `default` to ACL2's `nil`.

    It is a RICHER EMBEDDING in the sense of `OrderedEmbed` (`IsoGen`'s
    "the order-respect route"), and for the same reason: an
    ELEMENT-RESULT homomorphism square over a mirror definition with a
    JUNK ARM — a total Lean rendering of an untyped ACL2 function has to
    invent a value where ACL2 has `(car nil)` — is NOT TRUE for an
    arbitrary `Acl2Embed`. It is true exactly when the type's invented
    value is ACL2's, so that is a HYPOTHESIS the square's statement must
    carry, declared per square as `embed ValueOrNilEmbed via
    [encDefault]`.

    The field is a fact about the EMBEDDING alone: it mentions no mirror
    definition and relates no two operations, so it cannot supply a
    definitional correspondence that is not there (the same review-time
    judgement `ord` carries — see `IsoGen`'s A1-F9 amendment). -/
structure ValueOrNilEmbed (α : Type u) [Inhabited α] extends Acl2Embed α where
  /-- the element type's junk value is ACL2's junk value — and `SExpr`'s
      DERIVED `default` IS `SExpr.nil`, the value ACL2's `(car nil)` has
      (pinned by the `example` below, so the reading cannot drift). -/
  encDefault : enc default = (default : ACL2.SExpr)

/-- The pin for `ValueOrNilEmbed.encDefault`'s reading: the right-hand
    side is `SExpr.nil`. -/
example : (default : ACL2.SExpr) = ACL2.SExpr.nil := rfl

/-- **The `Option` refinement row**: `Option α` embeds as ACL2's
    value-or-nil idiom — `none` as `nil`, `some a` as `a`'s encoding.

    `hne` is the row's fail-closed shape check (see above): without it
    the map is not injective and this is not an embedding.

    The row lands a `ValueOrNilEmbed` rather than a bare `Acl2Embed`
    because its `encDefault` field is DISCHARGED BY THE ROW ITSELF —
    `Option`'s own `default` IS `none`, which the row sends to `nil` —
    so the value-or-nil property is a consequence of the refinement and
    never a per-witness obligation. -/
def optEmbed {α : Type u} (e : Acl2Embed α)
    (hne : ∀ a : α, e.enc a ≠ ACL2.SExpr.nil) : ValueOrNilEmbed (Option α) where
  enc
    | none => ACL2.SExpr.nil
    | some a => e.enc a
  inj := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exact absurd hab.symm (hne _)
    · exact absurd hab (hne _)
    · exact congrArg some (e.inj hab)
  encDefault := rfl

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

/-- `IsoGen`'s `map_inj` IN ITS USEFUL FORM, exactly as `enc_inj_iff` is
    to `Acl2Embed.inj`: a transport whose spec `Prop` concludes in an
    `Iff` (`ordered_perm_unique`: `xs = ys ↔ Permuted xs ys`) cannot
    LAND through a one-way implication — the encoded equality sits on
    one side of an `Iff` and has to be replaced there. The converse is
    `congrArg`, so this adds nothing: it is the same injectivity
    plumbing, and like `map_inj` it says nothing about any mirror
    definition and cannot rescue a misaligned crossing. It lives HERE
    rather than in the transfer kit because the transport closers are
    its only consumers (and `IsoGen` is at the module-size cap). -/
theorem map_inj_iff {α : Type u} (e : Acl2Embed α) {xs ys : List α} :
    xs.map e.enc = ys.map e.enc ↔ xs = ys :=
  ⟨map_inj e, fun h => h ▸ rfl⟩

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
  -- `+instances` (v4.33 bump, 4.29 #12244): simp stopped processing
  -- typeclass-instance arguments by default, which severed the ladder's
  -- documented route of unfolding a declared ORDER INSTANCE
  -- (`unfold [instTotalOrderSExpr]`) so the split's case hypothesis meets
  -- the reading's `bif`. `+instances` is the release's own supported
  -- restore of exactly the old behavior, applied to the FIXED ladder once
  -- (the alternative — instance-bridge LEMMAS in the `unfold` list — is
  -- refused by the definitions-only gate below, by design).
  `(tactic|
    (first
      | rfl
      | simp_all +instances only [List.map_nil, List.map_cons, List.nil_append,
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
-- (no longer `private`: `mirror_iso%`'s elaborator moved to
-- `IsoGen.lean` in the R4 wave 2g split and is its only caller.)
def undestructuredGuardCtor? (fnName : Name) :
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

/-! ## THE FIXPOINT-GUARD CAPABILITY (R4 wave 2g)

A definition that recurses TO A FIXED POINT under an `if` — the mirror's
`bsort` and its reading `bsortL`, from ACL2's
`(if (equal (bnext x) x) x (bsort (bnext x)))` — cannot be handed to the
closer as its own equation. Its `eq_def` rewrites `f x` to a term
CONTAINING `f (step x)`, which simp rewrites again, forever; wave 2d-prep
recorded exactly that, verbatim (`Possibly looping simp theorem:
Sorting.bsort.eq_1`, then a `whnf` timeout), for both of `bsort`'s
squares.

The capability is a BOUNDED UNFOLD, read off the definition and nothing
else: from `f`'s own `eq_def` this derives the definition's TWO GUARDED
equations — `f x = <then>` under the `if`'s condition and `f x = <else>`
under its negation — and hands THOSE to the closer instead. They say
exactly what the definition says (each is `eq_def` composed with
`if_pos`/`if_neg`, and nothing else is available to the proof), and they
terminate: the recursive occurrence's own guard is not derivable, so simp
stops after one step. `fun_induction` on the squared definition supplies
the guard in each case, which is why the two forms are enough.

FAIL-CLOSED, and it is the shape that decides: the two equations are
derived only when the definition's `eq_def` right-hand side is an `ite`
whose branches mention the definition ITSELF. Every other definition —
in particular every definition squared before this wave, all of which are
pattern-matching — takes the unchanged route and is handed its own
`eq_def` exactly as before. -/

/-- The generated equations live OUTSIDE `ACL2Lean.MirrorProofs` on
    purpose. The mirror seam gate enumerates PRODUCTS mechanically as
    "a theorem under `ACL2Lean.MirrorProofs` whose statement mentions a
    `Mirrors/` spec constant and no other constant of this package", and
    a spec definition's OWN GUARDED EQUATION matches that description
    exactly while being the opposite of a product. Classifying it out of
    the product namespace is the honest fix; hardening the gate's
    criterion would not be (the two-standard rule). -/
private def fixpointEqnName (fnName : Name) (suffix : String) : Name :=
  `ACL2Lean.FixpointEqns ++
    Name.mkSimple ((fnName.toString.replace "." "_") ++ suffix)

/-- The DEFINITION'S OWN two guarded equations, derived and declared on
    demand; `none` when `fnName` is not a guarded fixpoint recursion (the
    ordinary case), which leaves the emitted script exactly as it was. -/
def fixpointGuardEqns? (fnName : Name) :
    CommandElabM (Option (Name × Name)) := do
  let posName := fixpointEqnName fnName "_fix"
  let negName := fixpointEqnName fnName "_step"
  if (← getEnv).contains posName && (← getEnv).contains negName then
    return some (posName, negName)
  let some eqDefName ← liftTermElabM (Lean.Meta.getUnfoldEqnFor? fnName)
    | return none
  let ci ← getConstInfo eqDefName
  let types? ← liftTermElabM <|
    Lean.Meta.forallTelescope ci.type fun xs body => do
      let some (_, lhs, rhs) := body.eq? | return (none : Option (Expr × Expr))
      unless lhs.getAppFn.isConstOf fnName do return none
      unless rhs.getAppFn.isConstOf ``ite do return none
      let args := rhs.getAppArgs
      unless args.size == 5 do return none
      let c := args[1]!
      let t := args[3]!
      let e := args[4]!
      -- the LOOPING shape: the definition calls ITSELF under the `if`
      unless (t.find? (·.isConstOf fnName)).isSome
          || (e.find? (·.isConstOf fnName)).isSome do return none
      let guarded (g : Expr) (rhs' : Expr) : MetaM Expr := do
        let concl ← Lean.Meta.mkEq lhs rhs'
        Lean.Meta.mkForallFVars xs
          (Expr.forallE `h g (concl.liftLooseBVars 0 1) .default)
      let posTy ← guarded c t
      let negTy ← guarded (mkApp (mkConst ``Not) c) e
      return some (posTy, negTy)
  let some (posTy, negTy) := types? | return none
  let eqDefI : Term := mkCIdent eqDefName
  let declare (nm : Name) (ty : Expr) (positive : Bool) :
      CommandElabM Unit := do
    let stx ←
      if positive then
        `(by intros; rename_i h; rw [$eqDefI:term, if_pos h])
      else
        `(by intros; rename_i h; rw [$eqDefI:term, if_neg h])
    let val ← liftTermElabM do
      let v ← Lean.Elab.Term.elabTerm stx (some ty)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars v
    liftCoreM <| addDecl (.thmDecl
      { name := nm, levelParams := ci.levelParams, type := ty, value := val })
  declare posName posTy true
  declare negName negTy false
  return some (posName, negName)

/-- The closer's FIXPOINT EXTENSION — appended ONLY for a square whose
    definition (or declared reading) is a guarded fixpoint recursion, so
    every square declared before this wave is handed the identical set
    and its proof term is unchanged (net-verified).

    Both members are plumbing of families already admitted, and both are
    load-bearing exactly at the GUARD: `map_inj_iff` is `enc_inj_iff`'s
    list twin (the first plumbing family) and turns the guard's
    `map e.enc a = map e.enc b` back into `a = b`; `not_false_eq_true`
    closes the negated guard's side condition once the case hypothesis
    has rewritten it to `¬False`. Neither says anything about any mirror
    definition. -/
def fixpointExtraLemmas : List Name := [``map_inj_iff, ``not_false_eq_true]


end ACL2Lean.MirrorProofs
