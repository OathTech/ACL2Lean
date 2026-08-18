# NEW-BOOK MIRROR EVALUATION — the rulings record (2026-08-18)

The R4 evaluation wave asked three questions at its checkpoint. Mike ruled
on all three the same day. This file records the ruling VERBATIM, what
each item was, and what was done under it — so a later reader does not
have to reconstruct the decision from the diff.

Base: `c8b9e1e` (the `mdd/r4-wave2` tip at the time this worktree
detached). Branch: `mdd/r4-eval`. The evaluation's own findings (F1–F7),
the corpus survey and the broadening shortlist live in the wave's
checkpoint report; this file is the DECISION record only.

## THE RULING, VERBATIM

> ruling 1a/b - great, do as you recommend. 2 - great, do it. 3 - agree,
> let's do the cheap safe thing first.

## THE THREE ITEMS

### 1a — the `Filler` class (BLESSED as drafted)

**The question.** `p7-cong-collapse`'s `DUB` rebuilds its argument with
the literal `0` in every position. ACL2 is untyped, so `0` needs no
interface there; a Lean mirror at an arbitrary element type does — an
element type with no designated value has nothing to write. The draft
introduced an own one-field class `ACL2Lean.CongCollapse.Filler` rather
than reusing core `Inhabited`.

**Ruled.** Blessed as drafted. `Mirrors/CongCollapse.lean` keeps the
class, and its docstring carries the rationale in one line: the book's
literal `0` becomes the element type's DESIGNATED FILLER, and
`Inhabited` is rejected because its `default` at a given type is chosen
by whatever instance is already in scope and is therefore not the book's
`0`.

**Consequence, machinery-side.** The homomorphism square over a
definition that WRITES a designated constant is FALSE for an embedding
that sends that constant elsewhere, so the filler-respect fact is a
HYPOTHESIS OF THE SQUARE'S STATEMENT and lands as a RICHER EMBEDDING
(`MirrorProofs.FillerEmbed extends Acl2Embed`, field `fill`), consumed
through the pre-existing `embed S via [...]` clause. That is the
`OrderedEmbed` shape exactly; no generator change was needed.

### 1b — `dupp_prepend`'s binder-pattern rendering (BLESSED as drafted)

**The question.** `p5-or-shape-flipped`'s `DUPP-REP-MID` is

    (implies (and (consp x) (equal (car x) e) (dupp x))
             (or (equal x 'junk) (dupp (cons e x))))

The draft renders the two hypotheses `(consp x)` and `(equal (car x) e)`
as the BINDER PATTERN `e :: tl` rather than carrying them as Lean
hypotheses over a general `x`. The alternative considered and NOT taken
was `∀ (e : α) (x : List α), x ≠ [] → x.head? = some e → …` — closer to
the book's literal shape, equivalent in content, less idiomatic.

**Ruled.** Blessed as drafted. `Mirrors/OrShapeFlipped.lean`'s
`dupp_prepend` docstring records the correspondence explicitly: the
binder pattern `e :: tl` IS the conjunction `(consp x) ∧ (equal (car x)
e)`, said without a hypothesis; and the `(equal x 'junk)` disjunct is
unreachable for a `List α`, so the disjunction collapses to its second
disjunct. Both deltas are discharged one layer DOWN, at the waypoint
`Imported.Waypoints.p5_dupp_prepend_native_driver`, whose own docstring
records them against the real log.

### 2 — the F3 element-binder transport widening (APPROVED)

**The question.** `mirror_transport%`'s derived binder table was
DATA(`List SExpr`)-THEN-HYPOTHESES, so a spec `Prop` binding an ELEMENT
failed closed:

    mirror_transport%: ACL2Lean.OrShapeFlipped.dupp_prepend binds `e`,
    which is neither a `List SExpr` argument nor a HYPOTHESIS (`SExpr`)
    — outside the derived transport table (a named frontier: every data
    binder is encoded by `List.map`, and every hypothesis is carried by
    the registered INVARIANCE squares)

The evaluation prototyped the widening and measured it rather than only
naming it.

**Ruled.** Approved. The widening is the transport table's counterpart
of `mirror_iso%`'s existing `ArgReading.elem`: an element binder is
encoded by `e.enc` where a list binder is encoded by `List.map e.enc`.
Three parts, all in `MirrorProofs/TransportGen.lean`:

* the binder walk accepts an `SExpr` binder as an element data binder,
  under the SAME DATA-THEN-HYPOTHESES hard error;
* `encArgs` encodes it by `e.enc`;
* a SEPARATE closer macro `mirror_transport_close_hyps_elem`, whose only
  extra rung is `← List.map_cons` — a `rfl`-lemma already pinned in
  `IsoGen`'s `LadderPins`, relating no two operations (it IS the
  `List.map` equation). It is needed because an element binder makes the
  crossing instance read `f (e.enc a :: List.map e.enc as)` while the
  registered INVARIANCE squares are stated about `List.map e.enc`
  applied to ONE list.

The change is strictly ADDITIVE: with no element binders every
pre-existing path emits byte-identical syntax, which is why the two
ruled closers were left literally untouched and a third was added
instead (the same "keep the old path byte-identical" discipline R4 wave
2d used when it added the hypothesis-carrying closer).

**COLLECTION-TIME RECONCILIATION (ruled, not optional).** This
worktree's base PREDATES R4 wave 2f, which adds a SCALAR-binder row to
the same table. The two rows are to be reconciled into ONE table row AT
ARC COLLECTION — not here. See "residuals" below for the exact overlap,
recorded so the collector does not have to re-derive this analysis.

### 3 — the `BEq`/`DecidableEq` seam (BEqEmbed is the ruled route)

**The question.** A `Bool`-valued RECOGNIZER that tests element equality
splits its two squares across the `BEq`/`DecidableEq` divide. Measured
both arms on the real declaration:

* with `[DecidableEq α]` the AGREEMENT square fails, residual
  `⊢ (decide (a = b) && chain2Rec (fun x1 x2 => x1 == x2) (b :: t))
     = (a == b && chain2Rec …)`
  (re-measured with the `&&` body, so the finding is about the CLASS and
  not about an `if`-vs-`&&` shape);
* with `[BEq α]` the agreement square closes and the INVARIANCE square
  fails, residual
  `⊢ (e.enc a == e.enc b && dupp (b :: t)) = (a == b && dupp (b :: t))`.

The cause is that the waypoint reading is `BEq`-spelled (`duppRec =
chain2Rec (· == ·)`, inherited from the generic `chain2Rec` schematic)
while `Acl2Embed`'s injectivity and the closer's `enc_inj_iff` rung are
`Prop`-spelled. Two candidate resolutions were put up: a RICHER
EMBEDDING carrying the `BEq` form of injectivity, or admitting
`beq_iff_eq`/`LawfulBEq` as a LADDER RUNG.

**Ruled — "the cheap safe thing first".** The richer embedding is the
route: `MirrorProofs.BEqEmbed extends Acl2Embed` with field
`beq : ∀ a b, (enc a == enc b) = (a == b)`, declared per square via
`embed BEqEmbed via [beq]`. It needs NO generator change and it keeps
the fact where it belongs — the square is genuinely false for an
embedding that does not reflect the test, so the fact is a hypothesis of
the statement, not plumbing the closer may reach for.

**THE REVISIT CONDITION (the ruling's own terms).** A `LawfulBEq` ladder
rung is NOT taken now and becomes a candidate ONLY IF the `BEq` pattern
RECURS ACROSS SEVERAL BOOKS — and the RECURRENCE ITSELF IS THE DEMAND
WITNESS. Until then there is exactly one consumer (`dupp`), and one
consumer does not justify a permanent rung in every square's closer.
Anyone reopening this must bring the several books, not an argument.

## WHAT LANDED UNDER THE RULINGS

Two mirror PRODUCTS, both trio-clean, taking the layer from 11 to 13:

* `ln_dub_int : ACL2Lean.CongCollapse.ln_dub Int` — the p7-cong-collapse
  book's `P7-TARGET`, and the FIRST pattern-test book to reach the
  product layer. Ruled machinery only (no widening).
* `dupp_prepend_int : ACL2Lean.OrShapeFlipped.dupp_prepend Int` — the
  p5-or-shape-flipped book's `DUPP-REP-MID`, riding item 2's widening
  and item 3's `BEqEmbed`.

Both are enumerated MECHANICALLY by the mirror seam gate with no edit to
its criterion, each tracing to a `driver_replayed%` seam
(`ln_dub_int → p7TargetReplayedCond`,
`dupp_prepend_int → duppRepReplayed`).

## RESIDUALS

**For the collection-time F3 / 2f-scalar reconciliation.** The exact
overlap, so the collector can merge without re-deriving it:

* BOTH rows widen the SAME code — `elabMirrorTransport`'s binder walk in
  `MirrorProofs/TransportGen.lean`, the `if t.isAppOf ``List && … then`
  chain, plus `encArgs` immediately below it.
* This row's key is `t.isConstOf ``ACL2.SExpr` — the ELEMENT of the value
  universe, encoded by `e.enc`, which is `mirror_iso%`'s
  `ArgReading.elem` at the transport level. 2f's scalar row is a
  DIFFERENT key (a binder the embedding does not act on) answering to
  `ArgReading.fixed`. They are the two REMAINING `ArgReading`
  constructors, so the merged table should be stated as "the transport
  binder table IS `ArgReading` plus hypotheses", with one branch per
  constructor, rather than as two ad-hoc `if`s.
* Both preserve the DATA-THEN-HYPOTHESES invariant and each raised its
  own copy of that hard error; the merged row wants ONE copy.
* This row also adds a closer macro
  (`mirror_transport_close_hyps_elem`, `← List.map_cons`). Check whether
  2f's row needs a closer rung at all — a `.fixed` binder is the same
  value on both sides and plausibly needs none, in which case the merged
  generator selects the elem closer only when an ELEMENT binder is
  present, exactly as it does today.
* Byte-identity of pre-existing transports is a property BOTH rows
  currently hold by keeping the old closers untouched. The merged
  version must re-establish it, and the 11 pre-existing product receipts
  plus the seam gate are the check.

**Not addressed here (carried to the wave's finding list):** the
`derive_exec%` swap frontier's terse message
(`derive_exec%: M2 site formals mismatch`, which does not follow the
project's frontier-message convention — compare the rich message on the
adjacent line), and the EQUAL-only decode combinator family
(`native_of_replayed_equal` is the only one), which is what actually
bounds the rest of the non-sorting corpus.

---

# THE YANK (2026-08-18, afternoon) — SUPERSEDES THE MORNING BLESSES

## THE RULING, VERBATIM

> yes, let's yank the eval things - they don't really fit with this
> philosophy. The aim is for the top level mirrors here to be truly
> worthwhile Lean theorems (even if small).

Mike articulated a PRODUCT BAR the same afternoon and chose to apply it
RETROACTIVELY rather than let the morning's blesses stand. Both are
recorded here because the blessed-then-yanked sequence is the honest
record: the morning's rulings above are NOT deleted, and the yank is a
NEW commit on top of the commit that landed them, never a rewrite.

## THE PRODUCT BAR

**`Mirrors/` admission requires the top-level theorem to be a TRULY
WORTHWHILE LEAN THEOREM — even if small.** Two consequences, both
binding:

1. **"Is the book worth admitting" is a PRIOR question to the
   bijection.** The bijection discipline (each `Prop` ↔ one named book
   `defthm`, tightest idiomatic correspondent, verbatim semantics) says
   HOW to render a book once admitted. It says nothing about WHETHER to
   admit it, and it must not be read as an admission criterion — an
   impeccably bijective rendering of a theorem no Lean reader would stop
   for is still not a product.
2. **Books greened FOR CAPABILITY stay at the waypoint/catalog layer.**
   Proving that the machinery can reach a book is a METRIC achievement
   and the metric already has a home. Promoting a capability
   demonstration to the product layer inflates the product count with
   things that are not results.

Under that bar `ln_dub` (rebuilding a list with a constant leaves its
length alone) and `dupp_prepend` (prepending a copy of the head of an
adjacent-equal chain keeps it one) do NOT qualify. Both were chosen for
what they EXERCISED — a new value class, a new statement shape, a new
binder kind — which is exactly the capability criterion the bar
excludes. The p7/p5 waypoints (`p7TargetReplayedCond`,
`duppRepReplayed`) are pre-existing on the base and are UNTOUCHED: the
metric layer keeps its rows and its credit.

## WHAT THE YANK REMOVES, AND WHAT SURVIVES

REMOVED (the entire code delta of the morning commit):

* `ACL2Lean/Mirrors/CongCollapse.lean`, `ACL2Lean/Mirrors/OrShapeFlipped.lean`
* `ACL2Lean/MirrorProofs/CongCollapse.lean`, `ACL2Lean/MirrorProofs/OrShapeFlipped.lean`
  (`FillerEmbed`/`intFillerEmbed` and `BEqEmbed`/`intBEqEmbed` go with
  their spec files — they exist only to serve those squares)
* the `ACL2Lean.lean`, `MirrorProofs/SeamGate.lean` and
  `Tests/MirrorNameCheck.lean` wiring edits
* **the F3 element-binder widening in `MirrorProofs/TransportGen.lean`**,
  reverted BYTE-IDENTICAL to base

**Why the F3 row goes too, even though ruling 2 approved it.** Its only
consumer was `dupp_prepend_int`. A transport-table row with no consumer
is precisely the project's banned anti-pattern — "build the
infrastructure now, wire it into the real proof later" — under which
there is no later where it gets validated. The row re-lands WITH its
first product that passes the bar, not before.

SURVIVES:

* **Rulings 2 and 3's DESIGN DECISIONS STAND.** The element-binder row
  is ruled-approved AS A DESIGN (an `SExpr` binder is data, encoded by
  `e.enc`; the transport binder table is `ArgReading` plus hypotheses),
  and `BEqEmbed` is THE RULED ROUTE for the `BEq`/`DecidableEq` seam
  (not a `LawfulBEq` ladder rung, whose revisit condition — recurrence
  across several books as the demand witness — is unchanged). What is
  shelved is the IMPLEMENTATION, pending a consumer that passes the
  product bar. **Re-landing is a paste**, not a re-derivation: the
  material is preserved verbatim in the appendix below.
* The F3 / wave-2f reconciliation analysis in RESIDUALS above **remains
  binding** whenever the row re-lands. It is not invalidated by the
  yank; it is deferred with the row.
* The corpus survey, the A/B/C classification, the F1–F7 findings and
  the broadening shortlist are unaffected — they are observations about
  the machinery and the corpus, not product claims. Note that the survey
  now has a SECOND filter stacked on top of its capability filter: a
  candidate must clear the product bar before its A/B/C class matters.

## APPENDIX — PASTE-BACK MATERIAL (complete)

Everything below is verbatim as it stood at commit `4f75867`. Re-landing
the shelved work means pasting these files back, re-applying the
`TransportGen.lean` hunk, and re-adding the four wiring lines — after
the consumer that motivates them clears the product bar.

### A1. `ACL2Lean/Mirrors/CongCollapse.lean`

```lean
/-! # MIRRORS — the `p7-cong-collapse` book

The mirror spec for `acl2_samples/pattern-tests/p7-cong-collapse.lisp`,
the first PATTERN-TEST book to reach the product layer. Same rules as
`Mirrors/Basics.lean` and `Mirrors/Sorting.lean`: pure idiomatic Lean,
ZERO imports (core prelude only), self-contained vocabulary, properties
as named `Prop`s until their proofs arrive via replay, no `sorry` ever.

THE BOOK, verbatim (`p7-cong-collapse.lisp`):

    (defun ln (x)   (if (endp x) 0 (+ 1 (ln (cdr x)))))
    (defun same-ln (x y) (equal (ln x) (ln y)))
    (defthm same-ln-is-an-equivalence … :rule-classes :equivalence)
    (defcong same-ln equal (ln x) 1)
    (defun dub (x)  (if (endp x) nil (cons 0 (dub (cdr x)))))
    (defthm same-ln-dub (same-ln (dub x) x))
    (defthm p7-target (equal (ln (dub x)) (ln x)))

THE LINE (the reshape ruling's result tier). ONE result-tier theorem:
`P7-TARGET`. `SAME-LN-IS-AN-EQUIVALENCE` is an equivalence REGISTRATION
(`:rule-classes :equivalence` — it licenses the congruence, it is not a
property of the book's subject), the `defcong` is a rule, and
`SAME-LN-DUB` is the book's helper feeding that congruence (its content
is `P7-TARGET`'s, one abbreviation away: `same-ln x y` IS
`(equal (ln x) (ln y))`). Helpers and registrations stay in the waypoint
catalog; only `P7-TARGET` gets a mirror `Prop`, one for one.

THE FILLER (a design point this book is the first to raise). `DUB`
rebuilds its argument with `0` in every position. ACL2 is untyped, so
`0` needs no interface there; a Lean rendering at an arbitrary element
type does — an element type with no designated value has nothing to
write. `Filler` below is that interface: OUR OWN minimal class (not
`Inhabited`, whose `default` at a given type is chosen by whatever
instance is already in scope and is therefore not the book's `0`), with
exactly one field, and its instance at a user type is one line. `ln`'s
insensitivity to WHICH value is written is the book's business, not the
mirror's: the theorem is stated exactly as the book states it.

Waypoint status: the row is green — `P7-TARGET → REPLAYED ✓`
(unconditional; its `tp:LN` hypothesis discharged by the driver's TP
prover), lifted at the waypoint layer by
`Imported.Waypoints.p7_dub_len_native_driver`. -/

namespace ACL2Lean.CongCollapse

universe u

/-- The DESIGNATED FILLER of an element type: **the book's literal `0`
    becomes the designated filler value**, which is what `DUB` writes
    into every position.

    Our own minimal interface class, deliberately NOT `Inhabited`:
    `Inhabited`'s `default` at a given type is chosen by whatever
    instance is already in scope, so it is not the book's `0` — a mirror
    must name the book's constant explicitly, not inherit an unrelated
    one. (Blessed as drafted, ruling 1a of 2026-08-18 —
    `docs/notes/2026-08-18_eval-rulings.md`.)

    The machinery-side consequence is recorded with the square that needs
    it: a homomorphism square over a definition that WRITES this constant
    is FALSE for an embedding sending it elsewhere, so `enc filler =
    filler` is a hypothesis of that square's statement
    (`MirrorProofs.FillerEmbed`), never a closer rung. -/
class Filler (α : Type u) where
  /-- the value written into every position -/
  filler : α

variable {α : Type u}

/-! ## The objects of study (the book's functions, idiomatically) -/

/-- Length (the book's `LN`). -/
def ln : List α → Nat
  | [] => 0
  | _ :: t => ln t + 1

/-- Rebuild the list with the filler in every position (the book's
    `DUB` — `(if (endp x) nil (cons 0 (dub (cdr x))))`). -/
def dub [Filler α] : List α → List α
  | [] => []
  | _ :: t => Filler.filler :: dub t

/-! ## The target property -/

/-- **P7-TARGET** (the book's sole result-tier theorem):
    `(equal (ln (dub x)) (ln x))` — rebuilding a list with the filler
    leaves its length alone. -/
def ln_dub (α : Type u) [Filler α] : Prop :=
  ∀ (xs : List α), ln (dub xs) = ln xs

end ACL2Lean.CongCollapse
```

### A2. `ACL2Lean/MirrorProofs/CongCollapse.lean`

```lean
import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.Imported.Waypoints.Validation
import ACL2Lean.Mirrors.CongCollapse

/-! # MIRROR PROOFS — the `p7-cong-collapse` book

The proof of `ACL2Lean/Mirrors/CongCollapse.lean`'s single target Prop,
VIA REPLAY. Same placement rule as `MirrorProofs/Basics.lean`: the spec
file stays zero-import; this layer imports the machinery and proves the
Prop.

The route is the standard one — two agreement squares, two homomorphism
squares, one transport, all generated. What this book ADDS to the
machinery's exercised surface is the FILLER: `DUB` writes a CONSTANT of
the element type into every position, and a homomorphism square over
such a definition is FALSE for an embedding that does not send that
constant to the ACL2 value the book writes. So the filler-respect fact
is a HYPOTHESIS OF THE SQUARE'S STATEMENT and lands as a RICHER
EMBEDDING (`FillerEmbed`), exactly as the order dimension did for
sorting (`MirrorProofs/OrderBridge.lean`'s `OrderedEmbed`) — not as a
ladder rung.

The spec-side half (the `Filler` class, and why it is an own class
rather than `Inhabited`) was blessed as drafted, ruling 1a of
2026-08-18 — `docs/notes/2026-08-18_eval-rulings.md`. -/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

universe u

/-! ## The element-type interfaces at the two ends -/

/-- The filler at `SExpr`: the book's `0`, as the integer atom the
    proof log carries (`(CONS '0 (DUB (CDR X)))`). -/
instance instFillerSExpr : ACL2Lean.CongCollapse.Filler SExpr :=
  ⟨.atom (.number (.int 0))⟩

/-- The filler at `Int` — the book's `0`, at the element type the
    mirror is transported to. -/
instance instFillerInt : ACL2Lean.CongCollapse.Filler Int := ⟨0⟩

/-! ## The FILLER-RESPECTING embedding

`Acl2Embed` has exactly two fields and knows nothing about designated
constants. A homomorphism square over a definition that WRITES such a
constant needs one more fact — `enc filler = filler` — and that fact is
not plumbing the closer may reach for: the square is simply FALSE for an
embedding that sends the mirror's filler somewhere other than the ACL2
value `DUB` writes. So it is a hypothesis of the square's statement, and
the generator's existing `embed S via [...]` clause binds it per square.
-/

/-- An embedding that RESPECTS THE FILLER: `enc` is an injection (the
    inherited `Acl2Embed` fields) which additionally carries the element
    type's designated filler to `SExpr`'s. -/
structure FillerEmbed (α : Type u) [ACL2Lean.CongCollapse.Filler α]
    extends Acl2Embed α where
  /-- the embedding carries the filler to the filler -/
  fill : enc ACL2Lean.CongCollapse.Filler.filler
    = (ACL2Lean.CongCollapse.Filler.filler : SExpr)

/-- **The filler-respect witness**: `intEmbed` sends `(0 : Int)` to the
    integer atom `0`, which is exactly the value `DUB` writes. Proved
    (by computation on the two instances), not assumed. -/
def intFillerEmbed : FillerEmbed Int where
  toAcl2Embed := intEmbed
  fill := rfl

/-! ## The squares — `ln` (the book's `LN`) -/

/-- SQUARE (vocabulary alignment): our spec-layer `ln` agrees with core
    `length` — needed only because the waypoint theorem is stated with
    `length`. Definitional agreement, not content. -/
mirror_iso% ln_agree_length for ACL2Lean.CongCollapse.ln
  vars [xs]
  square agree (xs.length)

/-- The map-invariance square for `ln`: mapping the embedding leaves the
    length alone (the SCALAR class — `ln`'s result carries no
    reading). -/
mirror_iso% ln_map_invariant for ACL2Lean.CongCollapse.ln
  vars [xs]
  square hom scalar

/-! ## The squares — `dub` (the book's `DUB`) -/

/-- SQUARE (vocabulary alignment): our spec-layer `dub` at `List SExpr`
    IS the waypoint's constant-map spelling. Definitional agreement, not
    content. -/
mirror_iso% dub_agree_mapFiller for ACL2Lean.CongCollapse.dub
  vars [xs]
  square agree (xs.map (fun _ => (SExpr.atom (.number (.int 0)))))
  unfold [instFillerSExpr]

/-- The homomorphism square for `dub`, over the FILLER-RESPECTING
    embedding: mapping commutes with our `dub`. About OUR function's
    skeleton plus the one fact that makes it true at all — that the
    embedding carries the filler to the filler. -/
mirror_iso% dub_map_hom for ACL2Lean.CongCollapse.dub
  vars [xs]
  square hom list
  embed FillerEmbed via [fill]

/-! ## THE MIRROR — `ln_dub` (the book's `P7-TARGET`) -/

/-- **`ln_dub` at `Int`, via ACL2 replay** — the first PATTERN-TEST
    book's mirror. Content enters via the waypoint
    `p7_dub_len_native_driver` (the p7 book's `P7-TARGET`) through the
    generated crossing `ln_dub_sexpr` and nowhere else. -/
mirror_transport% ln_dub_int : ACL2Lean.CongCollapse.ln_dub Int
  embed intFillerEmbed
  crossing ln_dub_sexpr from Imported.Waypoints.p7_dub_len_native_driver

/-- info: 'ACL2Lean.MirrorProofs.ln_dub_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ln_dub_int

end ACL2Lean.MirrorProofs
```

### A3. `ACL2Lean/Mirrors/OrShapeFlipped.lean`

```lean
/-! # MIRRORS — the `p5-or-shape-flipped` book

The mirror spec for `acl2_samples/pattern-tests/p5-or-shape-flipped.lisp`.
Same rules as `Mirrors/Basics.lean`: pure idiomatic Lean, ZERO imports
(core prelude only), self-contained vocabulary, the property as a named
`Prop` until its proof arrives via replay, no `sorry` ever.

THE BOOK, verbatim (`p5-or-shape-flipped.lisp`):

    (defun rep (n e)  (if (zp n) nil (cons e (rep (1- n) e))))
    (defun dupp (x)
      (cond ((endp x) t)
            ((endp (cdr x)) t)
            ((equal (car x) (car (cdr x))) (dupp (cdr x)))
            (t nil)))
    (defthm dupp-rep-mid
      (implies (and (consp x) (equal (car x) e) (dupp x))
               (or (equal x 'junk) (dupp (cons e x))))
      :rule-classes nil)

THE LINE (the reshape ruling's result tier). ONE result-tier theorem:
`DUPP-REP-MID`. `REP` is defined but the theorem does not mention it, so
no mirror definition renders it.

THE SHAPE, AND THE HONEST DELTAS. The book's statement is an ACL2
`(implies (and …) (or …))` over an UNTYPED `x`; the Lean correspondent
below is the same fact at a typed list, and two of the book's clauses
disappear for reasons that are facts about Lean's types rather than
weakenings:

* `(consp x)` together with `(equal (car x) e)` says exactly that `x` is
  a cons whose head is `e` — which the Lean binder pattern `e :: tl`
  says, and says without a hypothesis;
* `(equal x 'junk)` is the disjunct that ACL2 needs because an untyped
  `x` might be the symbol `JUNK`; a `List α` never is, so the disjunction
  collapses to its second disjunct.

Both deltas are discharged one layer DOWN, at the waypoint
(`Imported.Waypoints.p5_dupp_prepend_native_driver`, whose docstring
records them against the real log): the antecedent is instantiated at
`hd := e` and the junk disjunct dies because an encoded list is never
that symbol. What is left — prepending a copy of the head keeps the
adjacent-equal chain — is the book's content.

THE EQUALITY CLASS. `DUPP` tests its elements with ACL2's `EQUAL`, so
the spec needs an equality interface on `α`. This file takes `BEq`
(`==`) where `Mirrors/Sorting.lean` takes `DecidableEq`, and the choice
is NOT free: `dupp` is `Bool`-valued, and a `Bool`-valued recognizer's
correspondence squares straddle the `BEq`/`Decidable` divide (measured
2026-08-18 — with `DecidableEq` the AGREEMENT square does not close,
with `BEq` it does). That is a machinery observation about the seam and
not a claim about which spelling is more idiomatic; it is recorded here
because a reader comparing the two spec files will notice. -/

namespace ACL2Lean.OrShapeFlipped

universe u

variable {α : Type u}

/-! ## The object of study (the book's function, idiomatically) -/

/-- Every adjacent pair is equal (the book's `DUPP`: two base arms, then
    a test on the first two elements). The book's third `cond` arm is
    `((equal (car x) (car (cdr x))) (dupp (cdr x)))` with a `t → nil`
    fallthrough — i.e. the conjunction of the test and the recursive
    call, which is what `&&` spells here. -/
def dupp [BEq α] : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => (a == b) && dupp (b :: t)

/-! ## The target property -/

/-- **DUPP-REP-MID** (the book's sole result-tier theorem): prepending a
    copy of the head of an adjacent-equal chain keeps it one.

    THE BINDER PATTERN IS THE BOOK'S TWO HYPOTHESES. The book states

        (implies (and (consp x) (equal (car x) e) (dupp x))
                 (or (equal x 'junk) (dupp (cons e x))))

    and this `Prop` binds `e :: tl` where the book binds `x`. That is a
    correspondence, not a weakening: `(consp x)` says `x` is a cons and
    `(equal (car x) e)` says its head is `e`, which together are exactly
    what the pattern `e :: tl` says — and the pattern says it WITHOUT a
    hypothesis, because a Lean binder can destructure where an ACL2
    formula must test. The remaining book clauses map across unchanged:
    `(dupp x)` is the antecedent `dupp (e :: tl) = true`,
    `(dupp (cons e x))` is the conclusion `dupp (e :: e :: tl) = true`,
    and `(equal x 'junk)` — the disjunct ACL2 needs because an untyped
    `x` might be that symbol — is unreachable for a `List α`, so the
    disjunction collapses to its second disjunct.

    The rejected alternative was the book's literal shape over a general
    list (`∀ e x, x ≠ [] → x.head? = some e → …`): equivalent in content,
    further from idiomatic Lean. (Blessed as drafted, ruling 1b of
    2026-08-18 — `docs/notes/2026-08-18_eval-rulings.md`.)

    Both collapses are discharged one layer DOWN, at the waypoint
    `Imported.Waypoints.p5_dupp_prepend_native_driver`, whose docstring
    records them against the real log — not assumed away here. -/
def dupp_prepend (α : Type u) [BEq α] : Prop :=
  ∀ (e : α) (tl : List α), dupp (e :: tl) = true → dupp (e :: e :: tl) = true

end ACL2Lean.OrShapeFlipped
```

### A4. `ACL2Lean/MirrorProofs/OrShapeFlipped.lean`

```lean
import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.Imported.Waypoints.Validation
import ACL2Lean.Mirrors.OrShapeFlipped

/-! # MIRROR PROOFS — the `p5-or-shape-flipped` book

The proof of `ACL2Lean/Mirrors/OrShapeFlipped.lean`'s single target
Prop, VIA REPLAY (waypoint: `p5_dupp_prepend_native_driver`).

WHAT THIS BOOK PROBES that the earlier mirrors did not: a `Bool`-valued
RECOGNIZER (so a map-INVARIANCE square whose truth rests on the
embedding's injectivity rather than on a homomorphism), and a spec
`Prop` whose binders are an ELEMENT plus a list, with an IMPLICATION as
the body. -/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

universe u

/-! ## The BEq-RESPECTING embedding

`Acl2Embed`'s injectivity field is stated at the `Prop` level
(`enc a = enc b → a = b`), and the square closer's rung `enc_inj_iff` is
its `Iff` form. A `Bool`-valued RECOGNIZER that tests element equality
puts the same fact on the OTHER side of the `BEq`/`DecidableEq` divide:
its map-invariance square needs `(enc a == enc b) = (a == b)`, which no
`Prop`-level rung can reach. Like the order dimension and the filler,
that is a fact about the EMBEDDING, and the square is FALSE without it
(an unlawful `BEq` on either side breaks it), so it lands as a richer
embedding rather than as a ladder rung.

RULED 2026-08-18 (item 3, `docs/notes/2026-08-18_eval-rulings.md`) —
"the cheap safe thing first": this richer embedding, which needs NO
generator change, and NOT a `LawfulBEq`/`beq_iff_eq` ladder rung. That
rung becomes a candidate ONLY IF the `BEq` pattern RECURS ACROSS SEVERAL
BOOKS, and the recurrence itself is the demand witness — today there is
exactly ONE consumer (`dupp`), and one consumer does not justify a
permanent rung in every square's closer. -/

/-- An embedding whose `enc` REFLECTS AND PRESERVES the boolean equality
    test — the `BEq` form of the inherited injectivity. -/
structure BEqEmbed (α : Type u) [BEq α] extends Acl2Embed α where
  /-- the embedding reflects and preserves the `BEq` test -/
  beq : ∀ a b : α, (enc a == enc b) = (a == b)

/-- **The BEq-respect witness at `Int`**: `intEmbed` sends distinct
    integers to distinct integer atoms, and `SExpr`'s derived `BEq` is
    lawful, so the two tests agree. Proved, not assumed. -/
def intBEqEmbed : BEqEmbed Int where
  toAcl2Embed := intEmbed
  beq a b := by
    by_cases h : a = b
    · simp [h]
    · have : intEmbed.enc a ≠ intEmbed.enc b := fun he => h (intEmbed.inj he)
      simp [this, h]

/-! ## The squares — `dupp` (the book's `DUPP`) -/

/-- SQUARE (vocabulary alignment): our spec-layer `dupp` at `List SExpr`
    IS the waypoint's `duppRec` — the same recursion spelled in the two
    layers' vocabularies (`duppRec` is the EQUAL instance of the
    machinery's `chain2Rec` fold). Definitional agreement, not
    content. -/
mirror_iso% dupp_agree_duppRec for ACL2Lean.OrShapeFlipped.dupp
  vars [xs]
  square agree (Imported.Waypoints.duppRec xs)
  unfold [Imported.Waypoints.duppRec, Lifting.chain2Rec]

/-- The map-INVARIANCE square for `dupp` (the SCALAR class — `dupp`'s
    result is a `Bool` and carries no list reading): mapping the
    embedding leaves the verdict alone. Its one non-skeletal step is the
    declared embedding's `beq` field (see above); the closer's
    `enc_inj_iff` rung is the same fact one type universe over and cannot
    fire on a `Bool` test. -/
mirror_iso% dupp_map_invariant for ACL2Lean.OrShapeFlipped.dupp
  vars [xs]
  square hom scalar
  embed BEqEmbed via [beq]

/-! ## THE MIRROR — `dupp_prepend` (the book's `DUPP-REP-MID`) -/

/-- **`dupp_prepend` at `Int`, via ACL2 replay.** Content enters via the
    waypoint `p5_dupp_prepend_native_driver` through the generated
    crossing and nowhere else.

    This is the FIRST transport with an ELEMENT binder
    (`∀ (e : α) (tl : List α), …`), and it is the demand witness for the
    binder-table row RULED 2026-08-18 (item 2,
    `docs/notes/2026-08-18_eval-rulings.md`; `TransportGen.lean`'s
    `mirror_transport_close_hyps_elem`). -/
mirror_transport% dupp_prepend_int : ACL2Lean.OrShapeFlipped.dupp_prepend Int
  embed intBEqEmbed
  crossing dupp_prepend_sexpr
    from Imported.Waypoints.p5_dupp_prepend_native_driver

/-- info: 'ACL2Lean.MirrorProofs.dupp_prepend_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dupp_prepend_int

end ACL2Lean.MirrorProofs
```

### A5. The F3 element-binder hunk for `ACL2Lean/MirrorProofs/TransportGen.lean`

Apply against the base file (`c8b9e1e`'s copy). Reconciliation with wave
2f's scalar row is still owed at collection — see RESIDUALS above.

```diff
@@ -92,6 +92,29 @@ macro "mirror_transport_close_hyps" "[" xs:simpLemma,* "]"
        | exact map_inj $e ($h $hs*)
        | exact map_inj ($e).toAcl2Embed ($h $hs*)))
 
+open Lean.Parser.Tactic in
+/-- The hypothesis-carrying closer for a spec whose binders include an
+    ELEMENT (`e.enc a`, not `List.map e.enc as`) — R4 evaluation wave,
+    RULED 2026-08-18 (item 2, `docs/notes/2026-08-18_eval-rulings.md`).
+    It is a SEPARATE macro so the two closers above keep byte-identical
+    proof terms.
+
+    The one extra rung is `← List.map_cons`, a `rfl`-lemma already pinned
+    in `IsoGen`'s `LadderPins`: an element binder makes the crossing
+    instance read `f (e.enc a :: List.map e.enc as)`, and the registered
+    INVARIANCE squares are stated about `List.map e.enc` applied to ONE
+    list, so the cons has to be pulled back under the map before any
+    square can fire. It relates no two operations — it is the `List.map`
+    equation itself. -/
+macro "mirror_transport_close_hyps_elem" "[" xs:simpLemma,* "]"
+    " embed " e:term:max " in " h:ident &" hyps " "[" hs:ident,* "]" : tactic =>
+  `(tactic|
+    (simp only [← List.map_cons, $xs,*] at $h:ident
+     first
+       | exact $h $hs*
+       | exact map_inj $e ($h $hs*)
+       | exact map_inj ($e).toAcl2Embed ($h $hs*)))
+
 /-! ## `mirror_transport%`
 
 The assembly measured off the three hand transports (`app_assoc_int`,
@@ -157,20 +180,45 @@ syntax (name := mirrorTransportCmd)
   -- binder that is neither a `List SExpr` nor a `Prop` is a hard error,
   -- and so is a data binder AFTER a hypothesis (which would need the
   -- hypothesis's own binder to be encoded — outside the table).
-  let (crossStmt, binderNames, hypNames) ← liftTermElabM do
+  let (crossStmt, binderNames, hypNames, elemNames) ← liftTermElabM do
     let ty ← whnf (← Term.elabType crossTyStx)
     unless ty.isForall do
       throwError "mirror_transport%: {specName} at SExpr is not a \
           quantified statement (frontier — the transported spec is a \
           `∀`-statement over lists)"
-    let (names, hyps) ← forallTelescopeReducing ty fun xs body => do
+    let (names, hyps, elems) ← forallTelescopeReducing ty fun xs body => do
       let mut names : Array Name := #[]
       let mut hyps : Array Name := #[]
+      -- THE ELEMENT BINDERS (R4 evaluation wave, RULED 2026-08-18 —
+      -- item 2, `docs/notes/2026-08-18_eval-rulings.md`): the data
+      -- binders whose type is `SExpr` itself rather than `List SExpr`.
+      -- They are the transport table's counterpart of `mirror_iso%`'s
+      -- `ArgReading.elem`, and they are encoded by `e.enc` where a list
+      -- binder is encoded by `List.map e.enc`. Everything else — the
+      -- DATA-THEN-HYPOTHESES shape and both hard errors — is unchanged.
+      --
+      -- COLLECTION-TIME RECONCILIATION (ruled with the row): R4 wave 2f
+      -- adds a SCALAR-binder row to this same chain, answering to
+      -- `ArgReading.fixed` where this one answers to `.elem`. The two
+      -- are to be merged into ONE table row at arc collection — stated
+      -- as "this table IS `ArgReading` plus hypotheses", one branch per
+      -- constructor, with a single copy of the data-after-hypothesis
+      -- hard error. The overlap is written out in the rulings note.
+      let mut elems : Array Name := #[]
       for x in xs do
         let nm := (← x.fvarId!.getDecl).userName
         let raw ← inferType x
         let t ← whnf raw
-        if t.isAppOf ``List && (t.appArg!).isConstOf ``ACL2.SExpr then
+        if t.isConstOf ``ACL2.SExpr then
+          unless hyps.isEmpty do
+            throwError "mirror_transport%: {specName} binds the `SExpr` \
+                argument `{nm}` AFTER {hyps.size} hypothesis binder(s) — \
+                the derived transport table is DATA-THEN-HYPOTHESES (the \
+                data binders are what get encoded), and anything else is \
+                a named frontier"
+          names := names.push nm
+          elems := elems.push nm
+        else if t.isAppOf ``List && (t.appArg!).isConstOf ``ACL2.SExpr then
           unless hyps.isEmpty do
             -- the hypothesis binders are ANONYMOUS, so the count (not
             -- their hygienic names) is what this message can honestly say
@@ -192,8 +240,8 @@ syntax (name := mirrorTransportCmd)
       if body.isForall then
         throwError "mirror_transport%: {specName}'s body is not an \
             equation between list/scalar terms (frontier)"
-      pure (names, hyps)
-    pure (← PrettyPrinter.delab ty, names, hyps)
+      pure (names, hyps, elems)
+    pure (← PrettyPrinter.delab ty, names, hyps, elems)
   let bs : Array Ident := binderNames.map mkIdent
   -- The hypotheses are ANONYMOUS binders in the spec (`Ordered xs → …`),
   -- so their `userName`s are all the same inaccessible `a✝` and using
@@ -252,7 +300,12 @@ syntax (name := mirrorTransportCmd)
     else pure (some (← `(Lean.Parser.Tactic.simpLemma|
       $(mkCIdent s.homName):term)))
   let hId : Ident := mkIdent `h
-  let encArgs ← bs.mapM fun b => `(List.map ($embedStx).enc $b:ident)
+  -- an ELEMENT binder is encoded by `e.enc`, a LIST binder by
+  -- `List.map e.enc` (the ruled row above; with no element binders this
+  -- is the pre-existing `bs.mapM` verbatim)
+  let encArgs ← (binderNames.zip bs).mapM fun (nm, b) =>
+    if elemNames.contains nm then `(($embedStx).enc $b:ident)
+    else `(List.map ($embedStx).enc $b:ident)
   let crossApp := Syntax.mkApp crossId encArgs
   let mainProof ←
     if hs.isEmpty then
@@ -267,11 +320,18 @@ syntax (name := mirrorTransportCmd)
       -- introduced first, the crossing instance is normalised by the
       -- registered INVARIANCE squares (which carry `Ordered (map e.enc
       -- xs)` back to `Ordered xs`), and the result is APPLIED to them.
-      `(by
-        intro $bs* $hs*
-        have $hId : _ := $crossApp
-        mirror_transport_close_hyps [$(homLemmas.toArray),*]
-          embed $embedStx in $hId hyps [$hs,*])
+      if elemNames.isEmpty then
+        `(by
+          intro $bs* $hs*
+          have $hId : _ := $crossApp
+          mirror_transport_close_hyps [$(homLemmas.toArray),*]
+            embed $embedStx in $hId hyps [$hs,*])
+      else
+        `(by
+          intro $bs* $hs*
+          have $hId : _ := $crossApp
+          mirror_transport_close_hyps_elem [$(homLemmas.toArray),*]
+            embed $embedStx in $hId hyps [$hs,*])
   let mainStmt : Term ← `($(mkCIdent specName) $elemTy)
   elabCommand (←
     `($[$doc?:docComment]? theorem $thmId : $mainStmt := $mainProof))
```

### A6. The wiring lines

`ACL2Lean.lean` — after `import ACL2Lean.Mirrors.Sorting`:

```lean
import ACL2Lean.Mirrors.CongCollapse
import ACL2Lean.Mirrors.OrShapeFlipped
```

and after `import ACL2Lean.MirrorProofs.Basics`:

```lean
import ACL2Lean.MirrorProofs.CongCollapse
import ACL2Lean.MirrorProofs.OrShapeFlipped
```

`ACL2Lean/MirrorProofs/SeamGate.lean` — after
`import ACL2Lean.MirrorProofs.Sorting`:

```lean
import ACL2Lean.MirrorProofs.CongCollapse
import ACL2Lean.MirrorProofs.OrShapeFlipped
```

`Tests/MirrorNameCheck.lean` — after `import ACL2Lean.Mirrors.Sorting`
(the coverage arm FAILS if a `Mirrors/` file is missing here):

```lean
import ACL2Lean.Mirrors.CongCollapse
import ACL2Lean.Mirrors.OrShapeFlipped
```

### A7. Verification that stood at `4f75867` (for comparison on re-land)

```
'ACL2Lean.MirrorProofs.ln_dub_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'ACL2Lean.MirrorProofs.dupp_prepend_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'ACL2Lean.MirrorProofs.ln_dub_sexpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ACL2Lean.MirrorProofs.dupp_prepend_sexpr' depends on axioms: [propext, Classical.choice, Quot.sound]

mirror seam gate: 13 mirror product theorems (was 11):
  ACL2Lean.MirrorProofs.ln_dub_int       → ACL2.Imported.Waypoints.p7TargetReplayedCond
  ACL2Lean.MirrorProofs.dupp_prepend_int → ACL2.Imported.Waypoints.duppRepReplayed

mirror name check: 59 spec names (was 57), no collision
lake build: 6465 jobs, 0 errors, 0 warnings; just test 3240 jobs
sweep REPLAYED 116/116; golden-diff: byte-identical
```

Non-degeneracy checks that passed (`#guard`): `ln [1,2,3] = 3`,
`dub [1,2,3] = [0,0,0]`, `dupp [1,1,1] = true`, `dupp [1,2] = false`,
`dupp ([] : List Int) = true`.
