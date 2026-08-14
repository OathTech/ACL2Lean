# R4 wave 0 — the refinement registry + the W3 close (2026-08-14)

Branch `mdd/r4-wave0-refinement` off main @ 15b016d. Opens the
roadmap's R4 (sorting mirrors); this wave implements the three
rulings Mike issued at the R1 exit and lands the first filterRel
squares. R2/R3 ordering intentionally left open — this wave blocks on
neither.

## The rulings being implemented (Mike, 2026-08-14)

1. **`Bool.decide_eq_true` admitted to the ladder** ("agreed") —
   criterion becomes rfl-lemmas + two named plumbing families
   (embedding inj; Bool/decide coercions). Content-free: collapses
   two spellings of one Bool; cannot rescue a misaligned square.
2. **The ENUM-REFINEMENT registry** (Mike's data-refinement framing,
   confirmed): for a closed enum in a `.fixed` position, a
   once-per-datatype constructor↦ACL2-value table (the finite sibling
   of `Acl2Embed`; injectivity checked by `decide`); the square
   generator ENUMERATES constructors — per-constructor squares
   produced from the one declaration, each literal on the waypoint
   side. Fail-closed: unregistered enum in `.fixed` → hard error;
   duplicate targets → rejected; constructor CARRYING DATA →
   hard-fail with a named message until a real witness demands it.
   The frame (record in IsoGen's header + LEXICON): DATA REFINEMENT —
   per ACL2 datatype a Lean datatype + mapping; same algorithm modulo
   the refinement (same access pattern, not same code); a square =
   the algorithm commutes with the refinement; the reading table is
   the refinement calculus; access-pattern divergence = template
   fails closed (honest).
3. **`decEqOfOrder` blessed** ("agreed") — no change needed; drop the
   review flag from TODO.

## Acceptance witness

The four `filterRel` per-constructor agree squares, LIVE and pinned
(R1-E measured them closing under mode-specialization + the rung —
the registry route must reproduce that from the single `RelMode`
declaration). The witness page's W3 section updated to its final
state; regression net (statements + proof terms) over all
pre-existing artifacts byte-identical.

## Escape hatch

Stop and report if: the per-constructor squares do NOT close via the
registry route (contradicts the R1-E measurement — diagnose, don't
force); the registry design grows beyond closed enums or needs any
search; or a new product-layer declaration becomes necessary.

## Exit

Rulings 1–3 landed; the witness live; fast-gate per increment; this
wave folds into R4's arc-level claim gate (no separate full gate
unless it becomes a merge candidate on its own).

## ARC LOG

### Wave 0 (2026-08-14) — rulings 1 + 3 landed, ruling 2 ESCAPE-HATCHED

- **Ruling 1 — LANDED.** `Bool.decide_eq_true` added to
  `mirror_square_close`'s fixed kit (`MirrorProofs/IsoGen.lean`); the
  pinned criterion now reads "`rfl`-lemmas + TWO named plumbing
  families: the embedding's `inj` iff, and Bool/decide coercions", with
  the content-free rationale (two spellings of ONE Bool; relates no
  operations, mentions no mirror definition, so it cannot rescue a
  misaligned square) plus a table row and a statement pin in
  `LadderPins`. Regression net BYTE-IDENTICAL — 598 lines, statements
  AND proof terms, over the 23 generated Basics artifacts, the 13
  sorting Props, the other spec declarations, the three live sorting
  squares and the order bridge: no pre-existing declaration changed
  route.
- **Ruling 3 — LANDED** (`decEqOfOrder` blessed; TODO flag retired).
- **Ruling 2 — NOT BUILT; the escape hatch's FIRST trigger fired.** The
  per-constructor squares do NOT close via the registry route. Measured
  (`.tmp`, four modes each, the registry's own statement shape
  `filterRel <ctor> ev xs = filterL <mapped literal> ev xs`):
  * the RULED ladder (fixed kit incl. the new rung): FAILS, all four;
  * ladder + ground evaluation (`simp_all (config := { decide := true })`)
    + `ite_true`/`ite_false`: CLOSES, all four;
  * R1-E's own measurement REPRODUCES unchanged (dispatch-free
    mode-specialized reading closes with the rung, re-opens without it).
  CAUSE: R1-E's "mode specialization" was at the READING level — a
  reading with no symbol dispatch, which is also what the real waypoint
  drivers speak (`Imported/Waypoints/Qsort.lean`). The registry as ruled
  specializes the ARGUMENT VALUE and hands the literal to `filterL`,
  whose `relL` still dispatches (`fv == symV "LT"`); the fixed closer
  cannot evaluate a ground `SExpr` comparison, and
  `Worlds.Sorting.symV` is PRIVATE — neither nameable in `unfold [...]`
  nor matchable by `relL_LT`/`_LTE`/`_GTE` (simp matches up to REDUCIBLE
  defeq). The registry was therefore not landed at all: with no live
  consumer it would be the banned "infrastructure now, wire it later".
  The ruled FRAME (data refinement) is recorded — `IsoGen.lean`'s header
  + `docs/LEXICON.md` — with the blocker named in both.
- The `hom list` square was re-probed for the record: residual
  byte-identical to R1-E's; the order-field frontier is unchanged.
- Gate: fast-gate (build `ACL2Lean`+`Tests` 3225 green, sorries 6,
  statics + name linter + mirror purity + golden as reported at exit).
