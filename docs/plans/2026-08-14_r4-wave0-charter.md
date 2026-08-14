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

### Wave 1 (2026-08-14) — THE SQUARE WAVE (isort + msort chains)

Executed in an isolated worktree; nothing committed there. Scope per
the roadmap's "R4 wave 1: squares en masse". `filterRel`/`relMode`
squares were out of scope (wave 0's blocker).

**The design piece — ORDEREDEMBED (flagged for Mike's review).**
`MirrorProofs/OrderBridge.lean`: `OrderedEmbed α` extends `Acl2Embed α`
with one field, `ord : ∀ a b, (enc a ≤ enc b) ↔ (a ≤ b)`; the witness
`intOrderedEmbed` discharges it from `lexorderB_intEmbed` (which needed
a `TotalOrder Int` instance, also landed there — four core `Int`
facts). `MirrorProofs/IsoGen.lean` gained the clause
`embed S via [f₁,…]`: the hom statement's embedding binder becomes
`(e : S α)` and `S.fᵢ e` reaches THAT square's closer only.

The justification, as it went into the criterion text: the field is
NOT a ladder rung and could not honestly be one. A ladder rung is
global and forever; this is scoped to the one invocation that declares
it — the same scope and the same visibility a REGISTERED CALLEE SQUARE
has. It is proved per instance, never assumed. And it cannot rescue a
misaligned square, because it is a fact about the EMBEDDING (the exact
character of `Acl2Embed.inj`, the first plumbing family): it mentions
no mirror definition and relates no two operations. The decisive point
is that the square is only TRUE over an order-respecting embedding —
so this is a hypothesis of the STATEMENT, not a convenience of the
proof. Tamper-probed: dropping the clause makes `insertOrd`'s hom
square FAIL. Fail-closed in four directions (non-structure, structure
not extending `Acl2Embed`, non-field name, `embed` on an `agree`
square) — all four probed.

FORM CHOICE, measured: the `Prop`-level IFF, not the charter's
suggested `lexorderB (enc a) (enc b) = decide (a ≤ b)`. The Bool form
would additionally need `decide_eq_true_eq`, which the ladder's
criterion explicitly lists as NOT admitted; the iff form rewrites the
`ite` condition directly and needs only `ite`'s own two cases.

**The ladder.** `ite_true`/`ite_false` added (`rfl`-lemmas, `ite`'s own
two cases, the twin of the admitted `cond` pair; pinned in
`LadderPins`, table row added). THE LINE HELD, and it is now written
into the ladder section: the kit grows by LEMMA rungs that meet the
criterion; the closer never grows a CAPABILITY. Two capabilities were
measured this wave and NOT taken — W7's case split and (wave 0's)
ground evaluation — both recorded instead.

**Squares — 5 LIVE (3 → 8 on the page), each `#guard_msgs`-pinned:**

| square | class | receipt |
| ------ | ----- | ------- |
| `insertOrd_map_hom` | hom list, `embed OrderedEmbed via [ord]` | trio |
| `isort_agree_isortL` | agree | trio |
| `isort_map_hom` | hom list, `embed OrderedEmbed via [ord]` | trio |
| `evens_agree_evensL` | agree (`unfold […, List.tail]`) | trio |
| `evens_map_hom` | hom list (PLAIN `Acl2Embed`) | `[propext]` |

**Frontiers — 3 new, recorded verbatim on the witness page (W7/W8/W9),
nothing declared:**

- **W7 `merge2`** (agree + hom). 3 of 4 cases close in both. Case 2 is
  the book-faithful UNDESTRUCTURED second arm (`| xs, [] => xs`,
  mirroring `(if (consp y) … x)`), whose Lean equation is GUARDED
  (`(x = [] → False) → merge2 x [] = x`) and whose scrutinee stays a
  bare variable. Agree: the reading `merge2L` DOES destructure, so
  neither of its equations applies. Hom: the guard would have to be
  transported through `List.map`. Measured: ONE case split on that
  argument + the existing kit closes both squares completely;
  `List.map_eq_nil_iff` does not; `merge2L.eq_def` LOOPS; a `split`
  rung has nothing to split. So the distance is one CLOSER CAPABILITY
  — a ruling, not an executor call.
- **W8 `msort`** (agree + hom). Cases 1–2 close; case 3 reduces, under
  the wave-1 kit + the registered `evens` squares +
  `unfold [ACL2Lean.Sorting.odds]`, to EXACTLY `merge2`'s corresponding
  square and nothing else. W7's ruling unblocks it at two four-line
  declarations. (`odds` needs no square on this route — unfolding it
  lands where `msortL`'s own recursion goes.)
- **W9 `odds`** (agree + hom). `odds` is NON-RECURSIVE, so Lean
  generates no functional induction theorem and the template fails
  before any goal exists ("No functional induction theorem for
  `Sorting.odds`"). This is the general bound W3 stage 2 already named
  (`relMode`, `permWitness` are in the same family); fix shape = a
  template fallback from `fun_induction` to `fun_cases`, a capability,
  so a ruling. SEPARATE second gap for the AGREE class only: there is
  no `oddsL` waypoint reading, and none can be validated because there
  is NO ODDS EXEC KIT (`oddsBody` exists; no `oddsExec`, no
  `register_exec_kit% "ODDS"` — `msort_exec_corr` walks the ODDS body
  inline as `evensExec (Logic.cdr xv)`).

**Out-of-scope measurement worth a ruling.** W3 `filterRel`'s `hom
list` frontier — recorded at wave 0 as "the order dimension
`Acl2Embed` has no field for" — is DISSOLVED by `OrderedEmbed`: the
`≤` test discharges, and the whole residual is one Bool coercion
(`if false = true then …`). With `Bool.false_eq_true` (the ALREADY
ADMITTED Bool/decide family) the square closes, all cases. Recorded on
the witness page as W3 stage 4; not declared (out of scope).

**Findings.** (1) `evensL`'s body is spelled with `List.tail` — a
seventh library-vocabulary reading the compliance census does not list;
re-spelling it would move `evensExec_enc`'s proof term, so it is
recorded, not fixed. (2) The `evens` agree square therefore carries
`List.tail` in its `unfold` list (a DEFINITION, so admissible on the
existing terms).

**Evidence.** Build `ACL2Lean`+`Tests` 3225 jobs green (exit 0);
sorries 6 (unchanged, all `Imported/Sorting.lean` FORBIDDEN-DEBT);
regression net 1455 lines BYTE-IDENTICAL before/after — statements AND
proof terms — over the transfer kit, the 20 generated Basics
artifacts, the order bridge, the 3 pre-existing sorting squares, the
13 Props + every spec definition, the 6 sorting waypoint readings +
their `derive_sim%` isos, and 6 waypoint-driver axiom receipts; golden
byte-identical to the live assembly (`cmp` on the assembled `.actual`);
14 `#guard_msgs` receipts green (9 pre-existing + 5 new); 7 tamper
probes all hard-error. Statics PASS: `lint-sh`, `check-bugs`,
`check-no-shadow`, `check-gz-agreement`, `check-mirrors-pure`,
`check-dark-files`, `check-file-weight`, `check-proof-logs`,
`check-no-getd-done`, `check-pattern-map`. NOT RUNNABLE in the
worktree (environmental, not diff-related): `check-acl2-tags` and
`check-log-provenance` — a git worktree does not populate submodules,
so `acl2/` is empty there; both must be re-run in the main tree.
