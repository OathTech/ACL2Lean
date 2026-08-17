import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.Imported.Waypoints.Basics
import ACL2Lean.Mirrors.Basics

/-! # MIRROR PROOFS — the basics books

The proofs of `ACL2Lean/Mirrors/Basics.lean`'s target Props, VIA
REPLAY. Placement per Mike's ruling (2026-08-12): spec files stay
zero-import; this layer imports the machinery and proves the Props.

PROVED HERE: ALL SIX Basics Props (6/6 since R1 item A, 2026-08-14).
`app_assoc_int` (02-rev's APP-ASSOC), `len_app_int` (simple.lisp's
MY-LEN-MY-APP) and `len_revAcc_int` (the 14-accumulator book's
LEN-REV-ACC — the accumulator class) landed with the Basics-closeout
arc; `app_nil_int`, `rev_app_int` and `rev_rev_int` (the 02-rev book's
APP-NIL / REV-APP / REV-REV) landed with R1, once their decode-layer
blockers were built: the APP/REV exec+iso kit (`Imported/Rev.lean`) and
the true-listp hypothesis absorption. The absorption is NOT a weakening
— ACL2 proved `(implies (true-listp x) …)` and the decode discharges
that antecedent at the ENCODED instance via `Lifting.trueListp_enc`
(every `enc` image is a true list, kernel-checked machinery-side).

EVERY PROOF ON THIS PAGE IS NOW GENERATED (Basics-closeout increments
C+D): the six squares by `mirror_iso%` and the three
crossing+transport assemblies by `mirror_transport%`
(`MirrorProofs/IsoGen.lean`). What the user writes is the
CORRESPONDENCE JUDGMENT and nothing else — which waypoint spelling a
mirror definition agrees with, which square class its result type
carries, which waypoint theorem IS the property, which embedding reads
the element type. The proofs themselves are two fixed templates whose
FAILURE IS A HARD ERROR, so a misaligned declaration cannot be rescued
by hand (see IsoGen's header: the thin-Lean ruling at the mirror level,
and why THE VOCABULARY RULE makes that gate clause-independent).

EXPECTATIONS (deliberately not a gate — these are small demos, kept
straight by convention):
- Each theorem's STATEMENT mentions only `ACL2Lean.Basics` constants
  and core instance types — a reader of the spec file can read these
  statements with no further vocabulary.
- Mirror CONTENT enters via the waypoint theorems (replayed-backed)
  and nowhere else. The inductions on this page are SQUARES —
  definitional agreement and homomorphism — never the property
  itself. For `app_assoc`, core Lean's `List.append_assoc` could
  close the theorem in one line; using it would make this file
  worthless (the route IS the product). Since C, the squares' closer
  cannot even reach such a lemma: its fixed rungs are `rfl`-lemmas
  plus the embedding's own injectivity (ruling 2026-08-14) — nothing
  that relates two operations (IsoGen's ladder table pins them).
- `#guard_msgs` receipts pin each theorem's axiom set on the page.

THE LIST (the pathfinder's second deliverable — everything that was
hand-written here, and what increments C+D turned each item into).
TEN items: 1–8 are the original inventory (the three pre-R1 mirrors);
9–10 were ADDED by R1 item A and were never hand-written at all — they
are what the fourth, fifth and sixth mirrors cost under the generators:
1. `Acl2Embed` + the `Int` instance → **EXTRACTED** to the transfer
   kit (`MirrorProofs/IsoGen.lean`), unchanged in name and statement:
   the generators must build statements that mention them.
2. `app_map_hom` (the homomorphism square) → **GENERATED** by
   `mirror_iso% … square hom list`.
3. `app_agree_append` (vocabulary alignment at `List SExpr`) →
   **GENERATED** by `mirror_iso% … square agree …`. Still dissolves
   entirely if/when waypoint statements are generated in mirror
   vocabulary (the standing B5/C3 design point) — generation lowered
   its cost, it did not remove the reason it exists.
4. `encList_inj`/`map_inj` (injectivity plumbing) → **EXTRACTED** to
   the kit with item 1 (`map_inj`; `encList_inj` had already gone).
   REMAINS HAND-WRITTEN, deliberately: it is a fact about `List.map`
   and an injection, not about any ACL2 program, and the transport
   closer's only non-generated rung.
5. The transport assembly in `app_assoc_int` (rewrite-lift-pullback)
   → **GENERATED** by `mirror_transport%` (the list-conclusion path:
   the crossing at encoded arguments, normalised by the homomorphism
   squares, landed through `map_inj`).
6. `len_agree_length` + `len_map_invariant` (the len squares) →
   **GENERATED** (`square agree` / `square hom scalar`); the
   Nat-result transport pattern in `len_app_int` → **GENERATED** by
   the same `mirror_transport%` (its scalar path — the `exact h` rung
   instead of the `map_inj` one; one template, two rungs).
7. `app_assoc_sexpr`/`len_app_sexpr` (the waypoint crossings) →
   **GENERATED** by `mirror_transport%`, statement-identical: the
   crossing is the spec Prop at `SExpr`, proved by rewriting with the
   REGISTERED agreement squares and then citing the waypoint theorem
   exactly. Same dissolve condition as item 3.
8. THE ACCUMULATOR FAMILY (`len_revAcc`, the third mirror) — the
   measured shape C's generator had to reproduce, and did:
   - `revAcc_map_hom` — the item-2 square over TWO ACCUMULATING
     ARGUMENTS (its IH is taken at `a :: acc`, not at `acc`) →
     **GENERATED**, and the structural demand it made of `mirror_iso%`
     is met BY CONSTRUCTION rather than by a special case: the
     template inducts with `fun_induction` off the mirror definition's
     own recursion, whose motive abstracts EVERY argument, so
     accumulating arguments are generalized and never carried fixed.
   - `revAcc_agree_revAccL` — item 3's sharper form (the alignment is
     against a waypoint-layer native rather than a core operator) →
     **GENERATED**, with `unfold [revAccL]` as its only extra input
     (definitions only — a lemma there is a hard error).
   - `len_revAcc_sexpr` — the item-7 crossing → **GENERATED**. The
     length-SUM content still enters here and nowhere else.
   - the `len_revAcc_int` transport → **GENERATED** by the scalar path
     of item 5/6's assembly.
9. THE REV SQUARES (`rev_agree_revL`, `rev_map_hom`) — R1 item A, and
   the first mirror definition whose recursion CALLS another one
   (`rev` calls `app`): both squares close only because the closer
   resolves `app`'s REGISTERED squares out of the registry, so a
   missing callee square fails closed rather than silently. Never
   hand-written; **GENERATED** at 4 + 3 user lines.
10. THE 02-REV TRANSPORTS (`app_nil_int`, `rev_app_int`,
   `rev_rev_int`) — **GENERATED** by `mirror_transport%` at 3 lines
   each, the list-conclusion path throughout. Two are the first
   CONDITIONAL replayed rows to become mirrors (`(implies (true-listp
   x) …)`), and their antecedent is discharged one layer DOWN, at the
   waypoint decode's encoded instance (`Lifting.trueListp_enc`) — so
   `mirror_transport%` needed no notion of hypotheses. What it did
   need was a SECOND CLOSER RUNG: `app_nil`'s spec `Prop` carries a
   closed list literal (`app xs [] = xs`), which rung 1 cannot pull a
   `List.map` out of, so the closer now falls back to taking the
   injectivity step first and pushing the map INTO the goal with the
   same squares forwards plus `List.map_nil` (a `rfl`-lemma already in
   the square closer's fixed kit). Rungs stay plumbing-only; the three
   pre-R1 transports still close on rung 1, unchanged.

USER LINES PER MIRROR (increment D's go/no-go measurement). The count
is the SOURCE LINES A USER WRITES in this file for one mirror
theorem: non-blank, non-comment lines of the declarations that mirror
needs (its squares, its crossing, its transport), attributing a shared
square to the mirror that first needs it. The `hand` column is counted
off this file at 090a5f5 (`git show 090a5f5:ACL2Lean/MirrorProofs/Basics.lean`),
the `generated` column off the invocations below:

| mirror       | hand (090a5f5)   | generated | what it became      |
| ------------ | ---------------- | --------- | ------------------- |
| `app_assoc`  | 23 = 5+7+6+5     | 9 = 3+3+3 | 2 squares + 1 xport |
| `len_app`    | 20 = 4+4+5+7     | 9 = 3+3+3 | 2 squares + 1 xport |
| `len_revAcc` | 26 = 7+7+5+7     | 10= 4+3+3 | 2 squares + 1 xport |
| ALL THREE    | 69               | 28        | **2.5×**            |

(the summands are, in order: the agreement square, the homomorphism
square, the crossing, the transport — the crossing and the transport
merge into ONE declaration under `mirror_transport%`.) A FOURTH mirror
over functions that already carry squares costs THREE lines: the
transport declaration alone.

R1's three mirrors MEASURE that prediction, counted the same way (no
`hand` column: they were never hand-written):

| mirror     | generated  | what it is                          |
| ---------- | ---------- | ----------------------------------- |
| `app_nil`  | 3          | transport only (reuses `app`'s two) |
| `rev_app`  | 10 = 4+3+3 | 2 new squares + 1 xport             |
| `rev_rev`  | 3          | transport only (reuses `rev`'s two) |
| ALL THREE  | 16         |                                     |

— i.e. the predicted THREE lines, twice over, and one function's worth
of squares for the one new mirror definition (`rev`).

Per-mirror receipts (3 lines) and the spec `Prop` (2 lines in
`Mirrors/Basics.lean`) are unchanged by C+D and excluded from both
columns; the shared kit (`Acl2Embed`/`intEmbed`/`map_inj`, 15 lines)
moved to IsoGen unchanged and is excluded from both. -/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

/-! ## The squares — `app`

THE LIST items 2 + 3, generated. The `agree` reading is the FIDELITY
JUDGMENT (this waypoint spells our `app` as core `++`); the `hom list`
class is checked against `app`'s real result type, so a drift fails
closed. -/

/-- SQUARE A (vocabulary alignment, THE LIST item 3): our spec-layer
    `app` agrees with core `++` — needed only because the waypoint
    theorem is stated with `++`. Definitional agreement, not
    content. -/
mirror_iso% app_agree_append for ACL2Lean.Basics.app
  vars [xs, ys]
  square agree (xs ++ ys)

/-- The homomorphism square (THE LIST item 2): mapping commutes with
    our `app` — about OUR function's skeleton, not about
    associativity. -/
mirror_iso% app_map_hom for ACL2Lean.Basics.app
  vars [xs, ys]
  square hom list

/-! ## THE FIRST MIRROR — `app_assoc`

The crossing (`app_assoc_sexpr`) is associativity's SOLE entry point:
the agreement squares carry the mirror statement into `++` vocabulary
and the waypoint theorem — `app_assoc_native_driver` →
`appAssocReplayed_uncond` → the driver's replay of the 02-rev book's
APP-ASSOC — closes it exactly. The mirror theorem is that crossing at
encoded arguments, pulled back along the embedding's injectivity. -/

/-- **`app_assoc` at `Int`, via ACL2 replay** (THE LIST item 5 — the
    transport assembly): encode along the embedding, apply the
    SExpr-level fact (whose content is the replayed APP-ASSOC), pull
    back by injectivity. -/
mirror_transport% app_assoc_int : ACL2Lean.Basics.app_assoc Int
  embed intEmbed
  crossing app_assoc_sexpr from Imported.Waypoints.app_assoc_native_driver

/-- info: 'ACL2Lean.MirrorProofs.app_assoc_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms app_assoc_int

/-! ## The squares — `len` (THE LIST item 6)

The scalar pair: `len` agrees with core `length`, and mapping the
embedding leaves `len` alone. Both are reused verbatim by the third
mirror. -/

/-- Square: our spec-layer `len` agrees with core `length`
    (vocabulary alignment — the waypoint speaks `length`). -/
mirror_iso% len_agree_length for ACL2Lean.Basics.len
  vars [xs]
  square agree (xs.length)

/-- Square: mapping the embedding preserves our `len` (homomorphism
    over OUR function's skeleton; the SCALAR class, since `len`'s
    result carries no reading). -/
mirror_iso% len_map_invariant for ACL2Lean.Basics.len
  vars [xs]
  square hom scalar

/-! ## The stretch: `len_app` — the first honest debt inheritance -/

/-- **`len_app` at `Int`, via ACL2 replay** — the first mirror whose
    inherited DEBT RETIRED: the MY-LEN-MY-APP waypoint carried
    `sorryAx` via `drv_tp_mylen` (a TP fact ACL2 discharged, replayed
    Lean-side as registered debt) until the TP prover's return-path arm
    landed (TP-replay arc increment 1, 2026-08-12) — `tp:MY-LEN` now
    arrives from ACL2's emitted `:TYPE-PRESCRIPTION` corollary +
    `:LEAVES`, the waypoint is `.native`, and this receipt is the clean
    trio. Content enters via the waypoint (through the generated
    crossing `len_app_sexpr`) and nowhere else. -/
mirror_transport% len_app_int : ACL2Lean.Basics.len_app Int
  embed intEmbed
  crossing len_app_sexpr from Imported.Waypoints.my_len_my_app_native_driver

/-- info: 'ACL2Lean.MirrorProofs.len_app_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms len_app_int

/-! ## THE THIRD MIRROR: `len_revAcc` — the accumulator (THE LIST item 8)

The 14-accumulator book's `REV-ACC`. Two squares are new here, and only
one of them is new in KIND: the homomorphism square has to generalize
over the accumulator (the IH lands at `a :: acc`) — which the square
template gets from `fun_induction` off `revAcc`'s own recursion — while
the alignment square is item 3's vocabulary rewrite against a
waypoint-layer native instead of a core operator.
`len_agree_length`/`len_map_invariant` are REUSED verbatim from
`len_app`. -/

/-- SQUARE (vocabulary alignment, THE LIST item 3/8): our spec-layer
    `revAcc` at `List SExpr` IS the waypoint's `revAccL` — the same
    recursion spelled in the two layers' vocabularies. Definitional
    agreement, not content. -/
mirror_iso% revAcc_agree_revAccL for ACL2Lean.Basics.revAcc
  vars [xs, acc]
  square agree (Worlds.RevAcc.revAccL xs acc)
  unfold [Worlds.RevAcc.revAccL]

/-- The homomorphism square for the ACCUMULATOR (THE LIST item 8):
    mapping commutes with our `revAcc`. Note the generalization — the
    recursive appeal is at the EXTENDED accumulator `a :: acc`, so the
    square is about our function's skeleton with BOTH arguments moving,
    and says nothing about reversal. -/
mirror_iso% revAcc_map_hom for ACL2Lean.Basics.revAcc
  vars [xs, acc]
  square hom list

/-- **`len_revAcc` at `Int`, via ACL2 replay** — the third mirror, and
    the accumulator class's first. Same transport assembly as
    `len_app_int` (numeric conclusion, so no injectivity pullback);
    content enters via the waypoint — through the generated crossing
    `len_revAcc_sexpr`, whose one alignment rewrite plus three
    `len_agree_length` rewrites land exactly on
    `len_rev_acc_native_driver` — and nowhere else. The waypoint's own
    simulation step is the ALIGNED reading of `REV-ACC` (the
    `derive_sim%` template gate's decisive case) — the reassociating
    reading, which would have smuggled ACL2's own `(equal (rev-acc x
    acc) (append (rev x) acc))` into the iso, is rejected by that gate
    when its induction is driven off the reading itself. The SAME
    reading is rejected one level up by `mirror_iso%`'s square template
    (the arc's mirror-level gate probe). -/
mirror_transport% len_revAcc_int : ACL2Lean.Basics.len_revAcc Int
  embed intEmbed
  crossing len_revAcc_sexpr from Imported.Waypoints.len_rev_acc_native_driver

/-- info: 'ACL2Lean.MirrorProofs.len_revAcc_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms len_revAcc_int

/-! ## The squares — `rev` (THE LIST item 9)

The 02-rev book's `REV`, the last mirror definition of the Basics slice
and the first whose recursion CALLS another mirror definition (`app`):
both squares resolve `app`'s registered squares out of the registry and
would fail closed without them. -/

/-- SQUARE (vocabulary alignment, THE LIST item 3/9): our spec-layer
    `rev` at `List SExpr` IS the waypoint's `revL` — the same recursion
    spelled in the two layers' vocabularies (`app` ↦ `++` on the waypoint
    side, which is why `app_agree_append` is the rung that closes the
    step case). Definitional agreement, not content. -/
mirror_iso% rev_agree_revL for ACL2Lean.Basics.rev
  vars [xs]
  square agree (Worlds.Rev.revL xs)
  unfold [Worlds.Rev.revL]

/-- The homomorphism square for `rev`: mapping commutes with our `rev`.
    About OUR function's skeleton — it says nothing about reversal, and
    its step case is `app`'s homomorphism square applied under the
    recursion. -/
mirror_iso% rev_map_hom for ACL2Lean.Basics.rev
  vars [xs]
  square hom list

/-! ## THE FOURTH MIRROR — `app_nil` (THE LIST item 10)

The first CONDITIONAL replayed row to land as a mirror: ACL2 proved
`(implies (true-listp x) (equal (app x nil) x))`, and the waypoint
`app_nil_native_driver` is unconditional because the decode instantiates
`X` at an ENCODED list, where `Lifting.trueListp_enc` discharges the
antecedent (the machinery-side enc-image fact — the same one `listRep`'s
`mem` field carries). The hypothesis is DISCHARGED at the seam, not
dropped from the statement.

It is also the first transport whose crossing instance carries a CLOSED
list literal (`[]`), which is what the transport closer's second rung
exists for (see `IsoGen`'s "the closing ladder"). -/

/-- **`app_nil` at `Int`, via ACL2 replay** — the fourth mirror. Content
    enters via the waypoint (through the generated crossing
    `app_nil_sexpr`) and nowhere else. -/
mirror_transport% app_nil_int : ACL2Lean.Basics.app_nil Int
  embed intEmbed
  crossing app_nil_sexpr from Imported.Waypoints.app_nil_native_driver

/-- info: 'ACL2Lean.MirrorProofs.app_nil_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms app_nil_int

/-! ## THE FIFTH MIRROR — `rev_app` (THE LIST item 10) -/

/-- **`rev_app` at `Int`, via ACL2 replay** — the fifth mirror, and the
    first whose statement mentions TWO mirror definitions on each side.
    Content enters via the waypoint `rev_app_native_driver` (the 02-rev
    book's REV-APP) through the generated crossing `rev_app_sexpr`. -/
mirror_transport% rev_app_int : ACL2Lean.Basics.rev_app Int
  embed intEmbed
  crossing rev_app_sexpr from Imported.Waypoints.rev_app_native_driver

/-- info: 'ACL2Lean.MirrorProofs.rev_app_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rev_app_int

/-! ## THE SIXTH MIRROR — `rev_rev` (THE LIST item 10)

The book's capstone: ACL2 only gets REV-REV once APP-ASSOC, APP-NIL and
REV-APP are available as rewrite rules, so this mirror sits on top of the
whole chain — and, like `app_nil`, on a conditional row whose true-listp
antecedent the decode discharges at the encoded instance. -/

/-- **`rev_rev` at `Int`, via ACL2 replay** — the sixth mirror, closing
    the Basics slice at 6/6. Content enters via the waypoint
    `rev_rev_native_driver` through the generated crossing
    `rev_rev_sexpr`. -/
mirror_transport% rev_rev_int : ACL2Lean.Basics.rev_rev Int
  embed intEmbed
  crossing rev_rev_sexpr from Imported.Waypoints.rev_rev_native_driver

/-- info: 'ACL2Lean.MirrorProofs.rev_rev_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rev_rev_int

end ACL2Lean.MirrorProofs
