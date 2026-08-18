/-
  Replay/MeasureTable — THE unified MEASURE/ARITY table (R3; T1+2 sprint
  phase 2, 2026-08-14).

  Remedy for the overspecialization audit's F6/F7/F8 (+F13's cross-layer
  note, docs/audits/2026-08-13_overspecialization-audit.md): the shapes of
  an emitted `:MEASURE` term used to be classified INDEPENDENTLY at four
  sites —

    1. `proveTotality`'s admission gate   (Driver/Provers.lean)
    2. `proveTp`'s   `measuredOf` gate    (Driver/Provers.lean)
    3. the μ-registry `buildMeasureFn`    (Driver/Waterfall.lean)
       (+ `replayInduction`'s `registryCovered` route discriminator)
    4. `dischargeDecrease`'s walk dispatch (Driver/Totality.lean)
    5. `derive_exec%`'s `MeasureSpec`      (Imported/ExecGen.lean)

  — with DIFFERENT row sets, so a shape one fragment handled was invisible
  to the next (F6: 100% of the main-row `total:` debt was blocked by gate 1
  rejecting shapes gates 3 and 4 already understood).

  This module is the ONE classifier. Every consumer now dispatches on
  `MeasureShape`, so a new row is added HERE and each consumer either
  handles it or names its own honest frontier for it — the rows can no
  longer silently diverge.

  SCOPE OF THE F13 REMEDY, honestly (2026-08-16): the shared TYPE landed
  (`MeasurePos`, read by both ExecGen and the waterfall) but the shared
  DERIVATION did not — `MeasureShape.positionsIn` shipped unused and was
  deleted at the stale-material audit, so ExecGen still builds its
  positions inline from its own transcribed `measured` clause. The two
  layers therefore agree on a TYPE, not on a CONSTRUCTION; the shared
  derivation for ExecGen's M2 remains OPEN (audit A4 #6).

  TRUST NOTE (design I1, unchanged): the measure appears in NO statement —
  μ is proof bookkeeping. A wrong or missing row can only FAIL a proof; it
  can never weaken one. This table is therefore not a trust-bearing
  artifact, and the emitted termination CLAUSES (never this table) remain
  the sole license for any decrease (CLAUDE.md's carve-out extension).
-/
import ACL2Lean.ProofLogTypes

namespace ACL2.Replay

/-- ONE ROW of the measure table: the classified shape of an emitted
    `:MEASURE` term.

    Rows and their corpus witnesses (`acl2_samples/`):

    | row        | measure term                                    | witnesses               |
    |------------|-------------------------------------------------|-------------------------|
    | `count`    | `(ACL2-COUNT v)`                                | the default — most fns  |
    | `len`      | `(LEN v)`                                       | bsort's `BNEXT`         |
    | `nfix`     | `(NFIX v)`                                      | `CD2`/`COUNT-DOWN`/`MY-EVENP` |
    | `sumCount` | `(BINARY-+ (ACL2-COUNT v1) (ACL2-COUNT v2))`    | `MERGE2`, `INTERLEAVE`  |
    | `userFn`   | `(<user fn> v)`                                 | bsort's `BNEXT-SIZE`    |

    `userFn` is the catch-all UNARY row: a measure headed by a function
    with no trusted-core `Nat` interpretation. It carries no μ, so only
    the RECORDED-TERMINATION route (which interprets the measure fn
    through the replayed admission waterfall, `interpCount`) can consume
    it; every μ-based consumer names it as a frontier.

    The per-row μ INTERPRETATION lives in `Replay/Lemmas/MeasureMu.lean`
    (`MeasureShape.muHeads`) — it names trusted-core constants and so
    cannot live in this dependency-light data module. -/
inductive MeasureShape where
  /-- `(ACL2-COUNT v)` -/
  | count (v : Symbol)
  /-- `(LEN v)` -/
  | len (v : Symbol)
  /-- `(NFIX v)` -/
  | nfix (v : Symbol)
  /-- `(BINARY-+ (ACL2-COUNT v1) (ACL2-COUNT v2))` -/
  | sumCount (v1 v2 : Symbol)
  /-- `(fn v)` for a `fn` with no trusted-core Nat interpretation. -/
  | userFn (fn : Symbol) (v : Symbol)
  deriving Repr, BEq, Inhabited

namespace MeasureShape

/-- The measured VARIABLES this row is stated over, in the row's own
    order. (`Justification.measuredSubset` must agree with this set —
    `ofJustification?` enforces it.) -/
def vars : MeasureShape → List Symbol
  | .count v | .len v | .nfix v => [v]
  | .userFn _ v => [v]
  | .sumCount v1 v2 => [v1, v2]

/-- The row's head symbol name — for frontier messages only. -/
def headName : MeasureShape → String
  | .count _ => "ACL2-COUNT"
  | .len _ => "LEN"
  | .nfix _ => "NFIX"
  | .sumCount _ _ => "BINARY-+"
  | .userFn f _ => f.name

end MeasureShape

/-- View `(H u)` → `(H, u)`. -/
private def unaryApp? (t : SExpr) : Option (Symbol × SExpr) :=
  match t with
  | .cons (.atom (.symbol h)) (.cons u .nil) => some (h, u)
  | _ => none

/-- View `(ACL2-COUNT v)` → `v` for a BARE VARIABLE `v`. -/
private def countVar? (t : SExpr) : Option Symbol :=
  match unaryApp? t with
  | some (h, .atom (.symbol v)) => if h.name == "ACL2-COUNT" then some v else none
  | _ => none

/-- THE CLASSIFIER: an emitted `:MEASURE` term → its table row, or `none`
    when no row matches (every consumer then names its own frontier).

    Fail-closed by construction: the measured argument must be a BARE
    VARIABLE in every row (a compound measured argument is exactly what
    `substTerm`-based decrease matching cannot state, and ACL2's own
    sound-induction condition makes measured actuals distinct variables). -/
def measureShape? (measure : SExpr) : Option MeasureShape :=
  match measure with
  | .cons (.atom (.symbol h)) (.cons a (.cons b .nil)) =>
    if h.name == "BINARY-+" then
      match countVar? a, countVar? b with
      | some v1, some v2 => some (.sumCount v1 v2)
      | _, _ => none
    else none
  | _ =>
    match unaryApp? measure with
    | some (h, .atom (.symbol v)) =>
      if h.name == "ACL2-COUNT" then some (.count v)
      else if h.name == "LEN" then some (.len v)
      else if h.name == "NFIX" then some (.nfix v)
      else some (.userFn h v)
    | _ => none

/-- The row of an emitted justification, with the emitted `:MEASURED`
    subset CHECKED against it (same variables, any order — ACL2 emits
    `MERGE2`'s as `(Y X)` against the measure's `(X … Y)`). A disagreement
    is `none`: the consumer keeps its honest frontier rather than proving
    an induction the emitted data does not describe. -/
def MeasureShape.ofJustification? (just : Justification) :
    Option MeasureShape := do
  let sh ← measureShape? just.measure
  let vs := sh.vars
  guard (vs.length == just.measuredSubset.length)
  guard (vs.all just.measuredSubset.contains)
  guard (just.measuredSubset.all vs.contains)
  pure sh

/-- The `(O-P <measure>)` admission obligation, as ACL2 emits it (a
    one-literal clause). D9: it is absorbed by the `Nat`-typed μ, and its
    PRESENCE is shape-checked so an emission change cannot pass silently. -/
def opObligationClause (measure : SExpr) : SExpr :=
  .cons (.cons (.atom (.symbol { name := "O-P" })) (.cons measure .nil)) .nil

/-- ExecGen's POSITIONAL view of a row: the measured formal INDICES.
    `derive_exec%` transcribes the emitted `:MEASURE` as a `measured i (j)?`
    clause rather than parsing it, so this is the shared datatype the two
    layers now agree on (audit F13's cross-layer asymmetry). -/
inductive MeasurePos where
  /-- one measured position, measured by a TRUSTED-CORE measure — the
      `count`/`len`/`nfix` rows. -/
  | m1 (idx : Nat)
  /-- two measured positions — the `sumCount` row. -/
  | m2 (idx1 idx2 : Nat)
  /-- one measured position, measured by a WORLD FUNCTION — the `userFn`
      row (R4 wave 2g; corpus witness `BSORT`, measured by `BNEXT-SIZE`).

      The position alone does not describe this row: the measure is a
      defun, so the consumer additionally needs THE MEASURE FUNCTION and
      a DECREASE for it. `derive_exec%` carries both in its own clause
      (`measured i via "<FN>" decreasing <thm>`) — the measure's
      registered exec kit supplies the function and the named theorem is
      the REPLAYED decrease (`Imported/ExecGen.lean`, "the userFn measure
      row"). Splitting it out of `m1` is what makes a consumer that only
      understands trusted-core measures fail closed on this shape instead
      of silently reading it as a `consCount` decrease. -/
  | mUser (idx : Nat)
  deriving Repr, BEq, Inhabited

-- (`MeasureShape.positionsIn` — the derivation of a row's `MeasurePos`
-- from a formal list — DELETED 2026-08-16: it shipped with R3 and was
-- never called. `ExecGen.lean` builds its `MeasurePos` values inline
-- from its own transcribed `measured` clause. See the header note on
-- what that means for the F13 remedy.)

end ACL2.Replay
