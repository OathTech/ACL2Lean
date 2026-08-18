# R4 wave 2 charter — the sorting mirror climb (2026-08-17)

Branch: from main post-merge (the audited sprint line). The four
wave-2a decisions were ENDORSED by Mike 2026-08-16 (synthesis RULINGS
RECORD, R-6): W7's undestructured-arm case split, W9's fun_cases
fallback, the filterRel per-mode assembly (implementing the standing
(b) ruling), and OrderedEmbed (blessed with the A1-F9 review-time
honesty amendment). Confirmed invariant: none of the four touches the
strength of any final mirror statement — machinery only; the 13 Props
stay byte-identical; trio-clean receipts are the only acceptance.

## Waves (A5's sequence, endorsed)

- **2a — the unblocking batch (~0.5 lane):** implement W7 + W9 in the
  template (structure-following capabilities: the split reads the
  squared definition's own match; fun_cases fires only for
  non-recursive defs — each with its criterion-text addition and a
  negative probe); the ODDS exec kit + oddsL reading (the one missing
  kit); the four dispatch-free per-mode filterRel readings + keyed
  per-mode square declarations (vars-term support + the keyed
  fail-closed registry); the OrderedEmbed criterion amendment (extra
  embed fields are review-time content-checked — say so). EXIT: merge2,
  msort, odds, filterRel squares LIVE (W8 measured to reduce to W7);
  the witness page fully green except hom squares awaiting
  order-respect where applicable.
- **2b — squares en masse (1-2 lanes):** the qsort chain (qsort,
  rel/all-rel positions) and the bsort chain (bnext, bnextSize, bsort
  — needs the bsort exec kit and the bnext-size measure row, the M3
  widening). Squares are replay-independent: fast-gate per increment,
  no sweeps in the loop.
- **2c — THE FIRST SORTING TRANSPORTS (~1 lane):** isort_ordered +
  isort_perm at Int — transport instance threading (deferred F3) built
  against these, its first real consumers; intOrderedEmbed's proved
  ord field means the Int mirrors carry no extra hypothesis. EXIT: the
  first two sorting Props are trio-clean THEOREMS — the route-proof.
- **2d — the long tail + the meta-theorems (1-2 lanes + ONE ruling):**
  msort/qsort/bsort ordered+perm; then ordered_perm_unique,
  sorts_agree, perm_iff_howMany, permWitness_complete over the
  unconditional waypoint layer; sorter_unique via the
  parametric/encapsulate lane — the wave's one NEW ruling (the
  constrained-order synthetic book through real ACL2) goes to Mike
  when reached, not before.

## Law

The four-line canon (CLAUDE.md) governs; check-mirrors-pure + the
collision linter + the NEW mirror seam gate (SeamGate.lean) + the
isProp unfold rejection bind every increment; golden untouched
(mirror-side arc — any movement is a STOP); receipts pinned; specs'
definitions/Props untouched (docstrings only); J/O-numbered logging
per the adopted convention; the five ask-first classes bind.

## Escape hatch

Stop and report when work gates on the 2d ruling, a fork round-trip,
or any square failing for a reason that smells like SPEC misalignment
(reader-facing = Mike's).

## ARC LOG

### Wave 2a (2026-08-17) — all four decisions LANDED; the page 8 → 19 squares

Executed in an isolated worktree; nothing committed there. The exit
condition is met: `merge2`, `msort`, `odds` and `filterRel` squares are
LIVE and pinned, and NO frontier is left undeclared on the witness page.

**1. W7 — the definition-directed case split.** The closer's one
structural capability, ruled 2026-08-16. Criterion text amended in
`MirrorProofs/IsoGen.lean` (the capability line, verbatim as ruled, plus
a section "THE DEFINITION-DIRECTED CASE SPLIT" giving the four
fail-closed properties). ONE DESIGN CORRECTION, found on contact and
reported here because it changes nothing about the ruling but everything
about the implementation: the guarded equation's ARGUMENT POSITION is not
usable at closing time, because `fun_induction` UNFOLDS the definition in
the goal (wave 1's own recorded residual `⊢ xs✝ = merge2L xs✝ []` shows
this — there is no `merge2` application left to index into). What
identifies the case is the GUARD HYPOTHESIS the same equation
contributes (`<var> = List.nil … → False`), and its CONSTRUCTOR is read
off the definition exactly as the position would have been. The tactic
matches that one shape and requires EXACTLY ONE hit; zero or several is a
hard error.

**2. W9 — the `fun_cases` fallback.** Decided at ELABORATION time off the
definition (`Lean.Tactic.FunInd.isFunInductName` on `<fn>.induct`), not
by swallowing a tactic failure: a recursive definition can never take the
fallback, so a `fun_induction` failure for any other reason still
hard-errors. Criterion note added.

**3. The ODDS kit + `oddsL` + the odds squares.** `Imported/
SortingOdds.lean`: `derive_exec% oddsExec corr odds_exec_corr` (ODDS is
non-recursive, so no `measured` clause) + the own-definition reading
`oddsL` (`| [] => [] | _ :: t => evensL t` — its own match, NOT
`evensL xs.tail`; `evensL`'s `List.tail` spelling stays the logged
compliance item and is not copied) + `derive_sim% oddsExec_enc`.
`msort`'s own kit is untouched. Two incidental findings: (a) a
NON-RECURSIVE exec's `eq_def` is a RESERVED name that `mkCIdent`
bypasses, so `derive_sim%` now realizes it when absent (a no-op for every
pre-existing kit — proof terms unchanged); (b) the ODDS iso needs one
bridge, `evensExec_nil`, because the template's enc-normal form
normalises `enc []` to `SExpr.nil` and the registered `evensExec_enc`
then no longer matches — it is `evensExec_enc` read at one point, not new
content.

**4. The filterRel per-mode assembly.** Four dispatch-free
own-definitions (`filterLtL`/`filterLteL`/`filterGtL`/`filterGteL`,
`Imported/SortingModeReadings.lean`), each VALIDATED by `derive_sim%`
against the real `FILTER` exec at its literal mode — which required a
`lit` reading in `derive_sim%` (a literal exec argument, not a binder). A
literal-specialized iso is a VALIDATION artifact and is deliberately NOT
registered on the kit, so callee resolution is untouched and the
"already has a registered iso" fail-close keeps its exact meaning.
`mirror_iso%`'s `vars` now takes a CONSTRUCTOR LITERAL (atomic ident =
binder; anything else = literal, admitted at a `.fixed` position only and
only as a NULLARY constructor), and the square registry is KEYED by it.
Wave 0's `symV`-is-private blocker stands and is routed around, not
fixed: the mode literals are re-spelled as values in the new module (same
values), so three of the four dispatch bridges cite the existing
`relL_LT`/`relL_LTE`/`relL_GTE` rows directly.

**The one ladder change.** `Bool.false_eq_true`, a LEMMA rung of the
ALREADY-ADMITTED Bool/decide plumbing family (pinned in `LadderPins`,
table row added, criterion paragraph extended). Its consumer is
`filterRel_map_hom`, and wave 1's stage-4 residual
(`⊢ … = if false = true then … else …`) was REPRODUCED VERBATIM before
the rung was added. Flagged plainly because the charter's summary said
the hom square closes "with the existing kit + OrderedEmbed": wave 1's
own record named this rung, and it is a rung, not a capability.

**The OrderedEmbed amendment (A1-F9).** One paragraph at the embed-via
criterion, saying plainly that the four `embed` checks are STRUCTURAL and
that the CONTENT of an extra field is REVIEW-TIME checked, not
structurally checked.

**Squares — 11 new, LIVE, each `#guard_msgs`-pinned** (`merge2` agree +
hom, `msort` agree + hom, `odds` agree + hom, the four
`filterRel_<mode>` agree, `filterRel` hom). Receipts: trio for all but
`odds_map_hom`, which is `[propext]`.

**Regression net.** Statements AND proof terms over 541 pre-existing
declarations (`MirrorProofs`, `Mirrors` specs, the sorting/perm/revAcc
waypoint layer). The ONLY changed declarations are the machinery
deliberately changed: the `MirrorSquares` structure and its
auto-generated companions, `elabMirrorIso`, `elabMirrorTransport`,
`mirrorIsoCmd`, `registerSquare`. Every square, reading, iso, spec
definition, `Prop` and driver receipt is BYTE-IDENTICAL.

**Tamper probes — six, all hard-error:** a swapped-argument `merge2`
reading (the split cannot rescue it, and correctly refuses to fire in a
case with no guard); an `odds`-as-`evens` reading (the fallback cannot
rescue it); a DUPLICATE registry key; a `vars` literal at a non-`.fixed`
position (also pinned as a build-time negative test in
`Tests/IsoGenGateTests.lean`); a misaligned per-mode agree square; a
misaligned literal-mode `derive_sim%`. NOT PROBED, and said plainly: the
registry's third arm ("an unkeyed square cannot join a family") is
unreachable in the present tree, because registration happens only after
the template CLOSES and no unkeyed `filterRel` agree square closes — it
is the four-line mirror image of the duplicate-key arm next to it.

**"Lookups must match exactly one" is implemented as a REGISTRY
INVARIANT, not a lookup function**: registration refuses a duplicate key,
so at most one entry carries any key. No key-directed lookup was written,
because no consumer wants one — a caller's closer wants the whole family
(its own body carries the literals), and an unwired lookup would be the
banned "infrastructure now, wire it later".

**Ordering note for wave 2b.** The two `msort` declarations stand BEFORE
the `odds` squares on the witness page on purpose: that is the route wave
1 measured (`unfold [ACL2Lean.Sorting.odds]`, no `odds` square
registered). And `IsoGen.lean` is at 1466 lines against the 1500 norm —
the next growth splits it.

### Wave 2b (2026-08-17) — the COMPLETE definition inventory on the page; 19 → 23 live squares; ZERO machinery changed

Executed in the same isolated worktree; nothing committed there. ONE file
touched: `ACL2Lean/MirrorProofs/Sorting.lean` (declarations + prose). No
generator, template, ladder, registry or reading was changed — every new
square closes with the machinery wave 2a left, and every frontier below is
recorded rather than forced.

**Scope reached, and it is not the scope the charter predicted.** The
charter's wave-2b line was "the qsort chain and the bsort chain (bnext,
bnextSize, bsort — needs the bsort exec kit and the bnext-size measure
row, the M3 widening)". Measured against the real spec, three of those
premises are wrong and are corrected here: `Mirrors/Sorting.lean` has NO
`bnextSize` and NO `iterate` definition (its `bsort` is
`(List.range xs.length).foldl (fun acc _ => bnext acc) xs`); the M3
widening is not what blocks `bsort`; and `qsort`'s two squares fail for
two DIFFERENT reasons, neither of which is the keyed-family call-site
wiring the brief anticipated. What wave 2b delivers instead is the
COMPLETE inventory: all fifteen spec definitions × both square classes
now appear on the witness page, LIVE or with a verbatim frontier.

**LANDED — four squares, 19 → 23, all `#guard_msgs`-pinned:**
`bnext` agree + hom (W10), `Ordered` hom scalar (W11), `relMode` hom
scalar (W12). Receipts: trio (`[propext, Classical.choice, Quot.sound]`)
for all four. `ordered_map_invariant` is the one wave 2c will consume
directly — it is the map-invariance square `isort_ordered`'s transport
needs.

**Tamper-probed, four, all hard-error:** a `bnext` agree square against
`evensL` (a misaligned reading); and each of the three new hom squares
declared over the PLAIN `Acl2Embed` — the order-respect hypothesis is
load-bearing in all three, `Ordered` and `relMode` included. No new
build-time negative test was added, and the reason is stated rather than
assumed: wave 2b introduced no new mechanism, so there is nothing new for
a negative test to pin (the gate-cruft doctrine — do not grow gates that
guard nothing).

**Regression net.** Statements AND proof terms (pretty-printed hashes)
over `ACL2Lean.MirrorProofs`, `ACL2Lean.Sorting`, `ACL2Lean.Basics`,
`ACL2.Worlds.Sorting`, `ACL2.Worlds.Perm` — 702 declarations before, 721
after, and the diff is 19 lines, ALL ADDITIONS: the four squares plus the
equation/`fun_cases` lemmas Lean realizes on demand for the three newly
squared definitions. ZERO pre-existing declarations changed.

**THE FRONTIERS, and what each is actually blocked on** (full residuals
verbatim on the witness page):

* `qsort` hom — ONE lemma rung, `List.map_append`, and nothing else (the
  two IHs are exactly the two halves of the goal). It is in the ladder's
  deliberately-NOT-admitted column BY NAME, so it is a ruling.
* `qsort` agree — TWO independent blockers: the reading `qsortL`
  destructures at depth 2 where the mirror destructures at depth 1 (W6's
  mismatch in the direction `unfold [List.tail]` cannot repair, with no
  guarded equation for W7's split); and a dispatch-free depth-1 reading
  cannot be VALIDATED, because `qsortExec` passes `symV "LT"`/`symV
  "GTE"` and `symV` is `private` — wave 2a's route-around runs out here.
* `bsort` both — the SPEC renders BSORT as `length`-many passes while the
  book recurses to the FIXPOINT; different access patterns, so there is no
  commuting square to state. Reader-facing, so Mike's.
* `Ordered` agree — ONE rung, `Bool.and_eq_true` (the mirror spells the
  adjacent-pair chain as `∧`, the reading as `&&`). Same Bool/`Prop`
  family as the two admitted rungs, but named in the NOT-admitted column.
* `relMode` agree family — a TEMPLATE finding: where the definition's own
  match IS on the keyed position, `fun_cases` GENERALIZES the constructor
  literal and emits the other three modes' (false) goals. Fail-closed and
  correct; refining at the key would be a capability, i.e. a ruling.
* `Permuted` both — the `∈`/`erase`/`isPerm` refinement squares, i.e. the
  library-spelled readings that are three of the four logged
  vocabulary-compliance items.
* `permWitness` both — the mirror is a `List.find?` multiplicity scan and
  the book's PCE is an erase-walk: a DIFFERENT ALGORITHM (the agree square
  in `some (pceL …)` shape is FALSE at `xs = ys = []`). The hom square
  does not elaborate at all: an `Option α` result needs a RESULT READING,
  a third result class the square table does not have.

**A FINDING ABOUT WAVE 2A, recorded on the page (W3's postscript).** The
four per-mode `filterRel` agree squares are true and trio-clean, but they
CANNOT FIRE AT THEIR ONLY CALL SITE: `qsort`'s body builds `filterRel` at
the spec's `decEqOfOrder` (declared `local`/low-priority on purpose so
`qsort` carries no `[DecidableEq α]` binder), while the squares are
elaborated here and pick up `ACL2.instDecidableEqSExpr`. The two print
identically without `pp.explicit`. Measured both ways: `simp only` with
the square on the caller's spelling reports "made no progress", and
restating the squares at `decEqOfOrder` breaks the two EQUALITY-testing
modes (`.lt`, `.gt`) because the reading's `==` is at the other instance.
Nothing on the page regresses (W13 is blocked independently), and the
resolution is a spec-side ruling, not an edit.

**J-CALLS (five, all of the form "measured, did not take, recorded").**

* **J-2b-1 — the bsort exec kit / M3 widening: NOT BUILT.** Measured: a
  Lean `bsortExec` recursing on `bnextExec x` needs
  `bnextSizeExec (bnextExec x) < bnextSizeExec x`, which IS the book's
  `HOW-MANY-BAD-PAIRS-BNEXT`; its only Lean form here
  (`how_many_bad_pairs_bnext_native_of_replayed`) carries world and
  `hreplayed` hypotheses a definition's termination proof cannot
  discharge, so the kit is a HAND kit under the P2
  Lean-termination-necessity exception. Decisive point: completing it
  would leave BOTH `bsort` squares exactly where they are, because the
  blocker is the spec's `foldl` rendering. Building it now is the banned
  "infrastructure now, wire it later".
* **J-2b-2 — `List.map_append` NOT admitted to the fixed kit.** The
  alternative was measured too and is worse: `mirror_iso% … for
  List.append` DOES elaborate and close by the template (receipt
  `[propext]`), but `qsort`'s value carries `HAppend.hAppend` /
  `List.instAppend` and never `List.append`, so callee resolution cannot
  find it — and the generated `xs.append ys` spelling does not match the
  `xs ++ ys` goal (`simp only` "made no progress"). Both routes are
  rulings; escalated, not taken.
* **J-2b-3 — `Bool.and_eq_true` NOT admitted.** It is the same Bool/`Prop`
  coercion family as `Bool.decide_eq_true`/`Bool.false_eq_true`, which is
  the argument FOR it; the table names it in the NOT-admitted column,
  which is the argument against. Two consumers measured (`Ordered` agree,
  `Permuted` agree). Escalated, not taken.
* **J-2b-4 — the four wave-2a `filterRel` agree squares NOT re-stated at
  `decEqOfOrder`.** Measured: the restatement breaks `.lt` and `.gt`. The
  choice is between a square that FIRES at the call site and one that
  CLOSES against the `==`-spelled reading, and it turns on a
  reader-facing spec declaration. Recorded for ruling.
* **J-2b-5 — `symV` NOT de-privatised.** It would rename the constant and
  move every proof term mentioning it — a regression-net-wide decision,
  not an executor edit. It is the ONLY route to a validated dispatch-free
  `qsort` reading found so far.

**No IsoGen split.** The charter flagged `IsoGen.lean` at 1466/1500 and
said the next growth splits it. Wave 2b added ZERO lines to it (it is at
1458 by `wc -l`), so the split is not performed and the flag stands for
whichever wave next grows the file.

**Gate (fast-gate, in-worktree) [wave 2b].** Full `lake build` green, 6439 jobs,
zero warnings; `just test` green (3228 jobs); the witness page elaborates
clean; 12 of 14 statics PASS — `check-acl2-tags` and
`check-log-provenance` fail ONLY because the `acl2/` submodule is not
checked out in this worktree (same as wave 2a: submodule statics owed at
collection); `just driver-coverage` 116/116 replayed, aggregate OK, and
`just check-golden-current` "golden matches the live assembly" (the
golden is byte-untouched — `git status` shows one modified file). The
sweep was CACHE-VALID rather than re-run from cold: the only edited file
is a leaf of the mirror layer that no coverage target imports. CPU was
shared with the perf lane in the main tree throughout, so no timing here
is a clean measurement.

### Wave 2c (2026-08-17) — THE FIRST SORTING PRODUCTS: two of the thirteen `Prop`s are THEOREMS

Executed in the same isolated worktree; nothing committed there. The
wave's point is met and the exit condition is met in substance but NOT
as the charter named it: the charter's pair was `isort_ordered` +
`isort_perm`, and **`isort_perm` is unreachable for a reason that is not
a machinery gap** (below, O-4). The two products are `isort_ordered` and
`msort_ordered`, both at `Int`, both trio-clean.

**THE HEADLINE.** `MirrorProofs/Sorting.lean` is now a PRODUCT page:

* `isort_ordered_int : ACL2Lean.Sorting.isort_ordered Int` —
  `[propext, Classical.choice, Quot.sound]`, content via the generated
  crossing `isort_ordered_sexpr` citing `orderedp_isort_native_driver`
  (the catalogued ORDEREDP-ISORT native, `sorting/isort`).
* `msort_ordered_int : ACL2Lean.Sorting.msort_ordered Int` — same
  receipt, via `msort_ordered_sexpr` citing
  `orderedp_msort_native_driver` (ORDEREDP-MSORT, `sorting/msort`).

The MIRROR SEAM GATE prints `6 → 8` products and pairs both correctly:
`isort_ordered_int → orderedpIsortReplayedCond`,
`msort_ordered_int → orderedpMsortReplayedCond`.

**THE MACHINERY GAP THE CHARTER PREDICTED DID NOT EXIST — reported, not
assumed.** Wave 2c was to build `mirror_transport%`'s deferred F3
INSTANCE THREADING against its first real consumers, and to widen the
`List SExpr`-only binder check. Measured: `isort_ordered`'s only binder
IS a `List`, and its `[TotalOrder α]` binder needs no threading —
the generator states the crossing at `SExpr` and the mirror at the
user's type, and ORDINARY INSTANCE SYNTHESIS supplies
`instTotalOrderSExpr` / `instTotalOrderInt` at each end. So NO THREADING
WAS BUILT: building it here would have been the banned "infrastructure
now, wire it later". The binder check stands as a real frontier for a
`Prop` with an ELEMENT binder (`perm_iff_howMany`'s `∀ a` is the first
that will hit it); nothing in this wave does.

**O-2 — the append callee-resolution normalization (IMPLEMENTED).** The
append hom square is DECLARED and REGISTERED (`listAppend_map_hom` for
`List.append`, receipt `[propext]`), and callee resolution learned the
notation: a fixed table (`notationSpellings`, `IsoGen.lean`) keyed on the
NOTATION'S INSTANCE CONSTANT as it appears in the squared definition's
own value (`List.instAppend`) resolves the underlying function's square
and adds the notation's own projections (`HAppend.hAppend`,
`Append.append` — structure projections) so the goal's `++` spelling
meets the square's. Fires only when the instance is in THIS definition's
value AND a square is actually registered, so every pre-existing square
is untouched. `List.map_append` was NOT admitted as a rung, on the
recorded rationale.

ONE THING O-2 DID NOT ANTICIPATE, found on contact: with the notation
gap closed, `qsort_map_hom`'s residual became `X = X` — identical under
`pp.implicit`, differing in ONE INSTANCE ARGUMENT. It is W3's postscript
(J-2b-4) again, now for the HOM square: the rewritten IHs speak
`instDecidableEqSExpr` (ambient where `filterRel_map_hom`'s statement
was elaborated) and `qsort`'s unfolded body speaks the spec's
`decEqOfOrder`. Repaired AT THE SQUARE: `filterRel_map_hom` is now
stated at the caller's instance (`attribute [local instance 5000]
ACL2Lean.Sorting.decEqOfOrder`, scoped to that one declaration, with the
reasoning at the declaration). **J-2b-4 IS NOT REOPENED**: the four
AGREE squares are untouched and their fire-vs-close tradeoff is still
Mike's — the HOM square has no reading on either side, so it closes at
either instance (measured both ways) and has no tradeoff.
`qsort_map_hom` is LIVE, trio-clean.

**O-3 — `Bool.and_eq_true` joins the Bool/decide family (IMPLEMENTED,
with a measured DIRECTION correction).** Added FORWARDS the rung
REGRESSES two live squares — `filterRel_lt/gt_agree_*`, whose own case
hypothesis is a `(a && b) = true` the forward rung splits apart
(residuals recorded in `IsoGen`'s ladder section). It is therefore
admitted BACKWARDS (`← Bool.and_eq_true`): merging a `Prop` conjunction
of `Bool` equations into the single `Bool` equation, which is the
direction every consumer wants. With it, `ordered_agree_orderedpRec` is
LIVE and trio-clean (its unfold list also gains the reading
`Worlds.Sorting.orderedpRec`, an `abbrev`). The ladder table's
NOT-admitted column is corrected in place (it named this lemma) and
`decide_eq_true_eq` stays named there.

**SQUARES: 23 → 26**, all `#guard_msgs`-pinned — `ordered_agree_
orderedpRec` (O-3), `listAppend_map_hom` (O-2), `qsort_map_hom` (O-2 +
the instance restatement).

**J-CALLS.**

* **J-2c-1 — THE PERMUTED READING CONVERSION: NOT BUILT** (charter item
  2). Measured first, and the measurement inverts the premise: the
  `Permuted` agree square fails at the SAME TWO PLACES against the
  library reading and against OWN-DEFINITION TWINS (`membL`/`rmL`/
  `permL`, written to the book's MEMB/RM/PERM body shapes in `.tmp`
  purely to locate the blocker). Both blockers are on the MIRROR side:
  the spec's `ys = []` against any `Bool` reading's base arm
  (`Permuted`'s own match never destructures `ys` and emits no guarded
  equation, so the W7 split cannot fire), and the spec's `a ∈ ys` — a
  `Prop` membership — against any `Bool` membership test. The HOM square
  is likewise blocked on `List.map_eq_nil_iff` / `List.mem_map` /
  `List.erase`-under-`map`, all library facts about library operations
  the SPEC BODY itself uses. So the conversion would leave both squares
  exactly where they are (the J-2b-1 pattern), and what the measurement
  actually finds is a SPEC question — the mirror `Permuted` renders the
  book's PERM through library `∈`/`List.erase` where the vocabulary
  practice would have a book function be an own-definition. Reader-
  facing, so Mike's. The compliance census is unchanged and still open.
* **J-2c-2 — `isort_perm` NOT LANDED, and it is not a gap we can close.**
  There is no PERM-ISORT theorem: the isort book's catalogued natives are
  ORDEREDP-ISORT, HOW-MANY-ISORT, TRUE-LISTP-ISORT, and no
  `(isortL xs).isPerm xs = true` exists anywhere in the tree. The book's
  route is the COMPOSITION of CONVERT-PERM-TO-HOW-MANY with
  HOW-MANY-ISORT — two theorems, i.e. a wave-2d meta-theorem, not a
  `mirror_transport%` declaration (which cites ONE waypoint exactly). The
  nearest perm mirror is `qsort_perm` (PERM-QSORT exists), and it needs
  BOTH the `qsort` agree square (held for Mike) and the `Permuted` agree
  square (J-2c-1).
* **J-2c-3 — `msort_ordered` TAKEN FROM WAVE 2d.** With 2c's second
  target unreachable, the second product is the cheapest 2d item: three
  transport lines, no new machinery, all four squares already live.
  Flagged rather than folded in silently.
* **J-2c-4 — the SEAM GATE's product criterion had a FALSE NEGATIVE, and
  it is fixed.** `isort_ordered Int` mentions `instTotalOrderInt`, which
  is declared in `MirrorProofs/OrderBridge.lean` — so the mechanical
  criterion ("mentions a `Mirrors/` spec constant and NO other constant
  of this package") classified the first sorting product as an ACL2
  notion and DROPPED it from the gate: the gate would have silently
  stopped checking exactly the mirrors this wave adds. One-level
  exemption added (a package constant is admitted in a product's
  statement when its OWN TYPE is in product vocabulary), which admits
  `instTotalOrderInt : TotalOrder Int` and still excludes anything typed
  in `SExpr` vocabulary — the two CROSSINGS are still correctly
  excluded, which is the negative evidence. Speedbump standard; the
  comment says do not harden it.

**TWO MODULE SPLITS (the ratchet, behaviour-preserving).** `IsoGen.lean`
crossed the 1500-line norm (wave 2a flagged it at 1466 and said the next
growth splits it): `mirror_transport%` and its closer moved VERBATIM to
`MirrorProofs/TransportGen.lean` (228 lines; `IsoGen` 1375).
`MirrorProofs/Sorting.lean` crossed it too and split along the METRIC /
PRODUCT seam: the squares are `MirrorProofs/SortingSquares.lean` (1440),
the transports keep `Sorting.lean` (188). No declaration text changed in
either split.

**TAMPER PROBES — five, all hard-error:** a MISALIGNED square for the
library callee `List.append` (arguments swapped — a library function's
square is gated exactly like any other); `qsort`'s hom square over the
PLAIN `Acl2Embed` (the order field is load-bearing, and the notation
normalization does not rescue it); a misaligned square for `isort`,
whose reported lemma set contains NO `HAppend`/`Append` projection and
no append square (the table fires only on the instance actually in the
definition's value); a misaligned `Ordered` agree square against the
chain of a REVERSED comparison (O-3's rung cannot rescue it); and a
transport citing the WRONG waypoint (`isort_ordered` from the MSORT
native), which fails at the crossing with a type mismatch.

**REGRESSION NET.** Statements AND proof-term hashes over the same
namespaces wave 2b used (`ACL2Lean.MirrorProofs`, `ACL2Lean.Sorting`,
`ACL2Lean.Basics`, `ACL2.Worlds.Sorting`, `ACL2.Worlds.Perm`), taken
before and after by restoring the pristine files and re-running the
dump: **604 pre-existing declarations, ZERO statement changes, ZERO
deletions, 8 additions** (the three new squares, the two crossings, the
two products, and one Lean-generated `qsort.induct_unfolding`). 39
declarations' PROOF TERMS moved, and each is deliberate machinery or its
consequence: the 25 pre-existing squares (the closer macro gained O-3's
rung), `elabMirrorIso` (O-2) and `elabMirrorTransport` (the file move),
and 12 Lean-generated `eq_def`/`induct_unfolding`/`fun_cases_unfolding`
auxiliaries, whose STATEMENTS are byte-identical and which are realized
on demand.

ONE CAVEAT, stated because the net cannot see it: `filterRel_map_hom`'s
statement is UNCHANGED as pretty-printed but its `DecidableEq SExpr`
INSTANCE ARGUMENT did change (`instDecidableEqSExpr` →
`decEqOfOrder`), which is the O-2 repair above. The two instances are
propositionally equal (`Subsingleton`) and print identically without
`pp.explicit`; the change is deliberate, is the only such change, and is
documented at the declaration.

**Gate (fast-gate, in-worktree).** Full `lake build` green, 6443 jobs,
zero warnings; `just test` green (3229 jobs); `just driver-coverage`
116/116 replayed, aggregate OK, 29 books; `just check-golden-current`
"golden matches the live assembly" (`git status` shows the golden and
all of `Tests/` and `acl2_samples/` byte-untouched); no
`sorry`/`admit`/`native_decide` anywhere in the diff or the new files;
11 of 13 statics PASS — `check-acl2-tags`, `check-log-provenance` and
`test-provenance-gates` fail ONLY because the `acl2/` submodule is not
checked out in this worktree (`ls acl2` is empty), the same environmental
owe waves 2a and 2b recorded. The five tamper probes above were run
against the built tree.

### Wave 2d-prep (2026-08-18) — Mike's rulings Q1/Q2 LANDED as spec re-renders, Q4 MEASURED-AND-REFUTED, Q3 drafted only; 26 → 34 live squares, products unchanged at 8

Executed in the same isolated worktree; nothing committed there. The
wave implements the four rulings of 2026-08-18 in dependency order. The
headline is honest and is not a product: **the two SPEC re-renders
landed and moved five frontiers, but no new mirror PRODUCT is
reachable** — Q4's route is refuted and `qsort`'s agree square is
unchanged, so the product count stands at 8 (two sorting).

**Q1 — `Permuted` re-rendered through own-definition `memb`/`rm`
(LANDED).** `Mirrors/Sorting.lean` gains `memb` (MEMB) and `rm` (RM),
both read off the emitted `:DEFUN` bodies in
`acl2_samples/sorting/perm.proof-log`, and `Permuted` now renders
`PERM`'s body at the book's own access pattern (the base arm
destructures `ys`, exactly as `(if (consp y) nil t)` does). MEANING
PRESERVED AND CHECKED, not asserted: the two bodies were proved
equivalent in `.tmp` (`PermutedNew xs ys ↔ PermutedOld xs ys`, via
`memb a ys = true ↔ a ∈ ys` and `rm a ys = ys.erase a`). All 13 target
`Prop` STATEMENTS are byte-identical (the regression net below).

**Q2 — `bsort` re-rendered as the book's fixpoint recursion (LANDED).**
The spec gains `howManySmaller` (HOW-MANY-SMALLER) and
`howManyBadPairs` (the book's `BNEXT-SIZE` — named for its own lemma
`HOW-MANY-BAD-PAIRS-BNEXT`, since there is no `HOW-MANY-BAD-PAIRS`
defun; the discrepancy is recorded rather than smoothed over), and
`bsort` is `if bnext xs = xs then xs else bsort (bnext xs)`
`termination_by howManyBadPairs xs`. The decrease is proved in the spec
in ~45 lines (three lemmas: the count is bubble-pass invariant, the
measure never increases, and a pass that CHANGES the list strictly
decreases it) — the P2 Lean-termination-necessity exception, and the
same obligation ACL2 discharges at `BSORT`'s admission. `bsort_ordered`
and the other `Prop`s that name `bsort` are untouched.

**Q4 — MEASURED, and the route is REFUTED (not "not taken").** Verbatim
in W13's postscript (`MirrorProofs/SortingSquares.lean`): the mismatch
is NOT at a `decide` — it is at `filterRel`'s own `DecidableEq`
INSTANCE ARGUMENT (`fun a b => decEqOfOrder a b` against
`instDecidableEqSExpr`, shown with `pp.explicit`), one level above any
`decide`; Q4's fact as stated is not a rewrite rule (unassignable RHS
variable, "made no progress" on a real two-instance goal); the
canonicalizing variant is inert because simp solves that binder by
SYNTHESIS; and the DEPTH blocker is independent and untouched
(`qsortL (head :: t)` has no equation at a variable tail). So NO new
product landed and nothing was forced.

**Q3 — DRAFTED AND MEASURED, NOT LANDED (as ruled).** The full draft
(defs, the new `Prop`, and the affected-square analysis) is in the
wave report and in `.tmp/w2d/Q3Scratch.lean`; it elaborates clean. It
DOES drop the `Option` wrapper and change `permWitness_complete`'s
statement — to the book's own equivalence, plus an `[Inhabited α]`
binder for `(CAR Y)` on an exhausted list. Measured with the draft
temporarily in the tree, then reverted: the agree square against `pceL`
now ELABORATES (the old `some`-wrapped shape was FALSE at `[] []`) and
its ONLY residual is the same `rm` square below; the hom square fails
with a TYPE MISMATCH that names the missing square class (an
ELEMENT-RESULT homomorphism).

**SQUARES: 26 → 34, all `#guard_msgs`-pinned** (new page
`MirrorProofs/SortingPermSquares.lean`, split off because the algorithm
page was at 1445 of the 1500-line norm): `memb` agree + hom, `rm` hom,
`Permuted` hom, `howManySmaller` agree + hom, `howManyBadPairs` agree +
hom. Receipts: `[propext]` for the first three, `[propext, Quot.sound]`
for `Permuted`'s, trio for the four measure squares.

**THE ONE LADDER CHANGE, and the two REFUTED candidates.**
`decide_true`/`decide_false` joined the fixed kit as the `decide` twin
of the admitted `cond`/`ite` pairs (`rfl`-lemmas, pinned by `example`,
one operation's own two values); their consumer is `memb`'s agree
square. The equality-test ORIENTATION gap that blocks `rm`'s agree
square has TWO candidate rungs and BOTH WERE MEASURED TO REGRESS LIVE
SQUARES — `eq_comm` flips the square's own top-level equation (five
squares stop closing) and `decide (a = b) = decide (b = a)` collides
with `Bool.decide_eq_true` at `α := Bool` (the four `filterRel` agree
squares stop closing). Neither was taken; the residuals are on the new
page.

**THE ONE REMAINING SQUARE, and it is a READING question.** `rm`'s
agree square is one residual wide: the book's `RM` tests
`(EQUAL E (CAR X))` (target-first, which the mirror renders
faithfully) and the library `List.erase` tests head-first. `List.erase`
is one of the four logged vocabulary-compliance items and this is the
first square where the gap is load-bearing: `Permuted`'s agree square,
and Q3's, are each EXACTLY this one square away. The fix is an
own-definition `rmL` reading — a waypoint-layer change that moves
`permExec_enc` and every PERM-* native's vocabulary, so out of scope
here and recorded.

**`bsort`'s squares: the blocker MOVED but neither landed.** The
access-pattern objection wave 2b recorded is gone (that was the point of
Q2), and two new ones are recorded verbatim: the hom square's closer
LOOPS on the fixpoint equation (`Possibly looping simp theorem:
Sorting.bsort.eq_1`, then a whnf timeout — controlling it is a template
capability, i.e. a ruling), and the agree square still has no `bsortL`
reading in the tree.

**J-CALLS.**

* **J-2d-1 — the two orientation rungs: MEASURED AND REFUTED, not
  escalated.** Both regress live squares, so there is nothing for a
  ruling to weigh: the rung route is closed, and the open decision is
  the READING conversion (already a standing compliance item).
* **J-2d-2 — `decide_true`/`decide_false` TAKEN as member additions to
  the ruled `rfl`-rung class** (delegation boundary class 2: "adding a
  member to a ruled class stays delegated"), with the criterion text,
  the table row and the `example … := rfl` pins added at the ladder.
  Disclosed because the ladder is the trust-relevant surface: they are
  two lines and revert cleanly.
* **J-2d-3 — `bsort`'s termination lemmas are SPEC-side hand proofs.**
  ~45 lines in a reader-facing file, admitted under the P2
  Lean-termination-necessity exception and under the spec header's own
  "the only proofs here are the termination measures Lean's kernel
  demands". They knowingly re-prove in Lean what the book proves as
  `HOW-MANY-BAD-PAIRS-BNEXT` — that is what P2 names, and the ruled
  re-render cannot exist without them. Flagged, not hidden.
* **J-2d-4 — no `permWitness`/`bsort`/`qsort` square was forced.** Each
  frontier above is recorded with its verbatim residual and nothing was
  declared that does not close.

**REGRESSION NET.** Statements AND proof-term hashes over
`ACL2Lean.MirrorProofs`, `ACL2Lean.Sorting`, `ACL2Lean.Basics`,
`ACL2.Worlds.Sorting`, `ACL2.Worlds.Perm`, taken before and after by
stashing the work and re-running the dump: **612 pre-existing
declarations, ZERO statement changes, ZERO deletions, 34 additions.**
FIVE pre-existing proof TERMS moved, each entailed by a ruling:
`ACL2Lean.Sorting.Permuted` and `ACL2Lean.Sorting.bsort` (the two ruled
bodies themselves), `Sorting.bnext.induct_unfolding` (a Lean-generated
auxiliary, realized on demand by the new termination lemmas' 
`fun_induction`; STATEMENT byte-identical), and `isort_ordered_int` /
`msort_ordered_int` — the two PRODUCTS, whose statements and receipts
are unchanged but whose generated proofs now carry the newly registered
squares in their fixed simp sets (the transport collects every
registered square). Disclosed rather than hidden: it is the price of
registering squares before the transports, and the seam gate still pairs
both correctly.

**TAMPER PROBES — six, all hard-error with "the square template did not
close":** `memb` against the NEGATED membership test; `rm` against the
IDENTITY; `Permuted` against `isPerm` with the arguments SWAPPED;
`howManySmaller`'s hom square over the PLAIN `Acl2Embed` (the
order-respect hypothesis is load-bearing); `howManyBadPairs` against an
OFF-BY-ONE reading; `howManySmaller` against the OTHER count reading
(`howManyL`). The two new `decide` rungs rescue none of them.

**Gate (fast-gate, in-worktree).** Full `lake build` green, 6453 jobs,
ZERO warnings; `just test` green (3236 jobs); `just driver-coverage`
116/116 replayed, aggregate OK, 29 books; `just check-golden-current`
passes and `git status` shows `acl2_samples/` and `Tests/` byte-
untouched; no `sorry`/`admit`/`native_decide` anywhere in the diff;
11 of 14 statics PASS — `check-acl2-tags`, `check-log-provenance` and
`test-provenance-gates` fail ONLY because the `acl2/` submodule is not
checked out in this worktree (`ls acl2` is empty), the same
environmental owe waves 2a–2c recorded, owed at collection.

### Wave 2d (2026-08-18) — the perm chain OPENS: 34 → 37 squares, the FIRST hypothesis-carrying transport, PRODUCT #9; item 1's RED BUILD found and repaired

Executed in the same isolated worktree, resuming after the Mathlib
incident (`docs/notes/2026-08-18_mathlib-incident.md`, RESOLVED — the
shared checkout is restored at the manifest pin with its cache
unpacked). This entry covers STEP 0 (item 1's owed re-verification and
O-6) and the original items 2–8.

**STEP 0's HEADLINE IS A RED BUILD, and it is item 1's.** The full
worktree build of `d9bdc96` FAILS. That commit's own message said "a
full-tree build showed no error lines through a grep filter but the
success line was NOT seen"; it was not seen because the build was
broken. Verbatim:

```
error: ACL2Lean/Imported/SortingConvertPerm.lean:170:0: derive_sim%: the iso
template did not close pceExec_enc — the chosen NATIVE READING DOES NOT ALIGN
WITH THE EXEC'S RECURSION …
h_1 : ¬pceExec (enc xs) (enc (rmL x ys)) = pceL xs (ys.erase x)
```

CAUSE: item 1 converted `RM`'s reading to the own-definition `rmL`, and
`pceL` — a CONSUMER of that reading, since `pceExec` calls the `RM` exec
— still spelled its removal step `ys.erase x`, so `pceExec_enc`'s
induction met `rmL` on one side and `List.erase` on the other. FIX: the
one-line conversion of `pceL`'s recursive step to `rmL`, which is the
same compliance move one level down and is what the `permWitness` agree
square needed anyway. The reading is re-VALIDATED by its own
`derive_sim%` (template failure = hard error). **The gap this exposes is
a process one and is stated plainly: a grep filter over a build log is
not a build result — only the exit code and the success line are.**

**O-6 (orchestrator, 2026-08-18) — IMPLEMENTED, both halves.**

* THE GUARD at the two decode bridges (`Imported/SortingReadings.lean`):
  a paragraph at the bridge section and a one-line docstring on each of
  `rmL_eq_erase` / `permL_eq_isPerm` saying they must NEVER join the
  mirror square closer's kit or a square's `unfold` list. The reasoning
  is recorded, not just the rule: the closer's PURITY is why the
  acceptance is sound — a bridge in the kit would rewrite the
  own-definition reading straight back to the library one and re-open the
  channel the vocabulary rule exists to shut, making the conversion
  cosmetic. Checkable by `grep -rn "rmL_eq_erase\|permL_eq_isPerm"
  ACL2Lean/MirrorProofs` returning nothing.
* THE PERM-SIDE NATIVES re-stated in `permL` vocabulary, through the
  bridges at the seam and nowhere else — the three O-6 named, and no
  others. Statement changes enumerated in the regression-net disclosure
  below.

**Q3 LANDED (the wave's ONE authorized spec change), verbatim from the
ruled draft.** `Mirrors/Sorting.lean`'s `permWitness` is now the book's
ERASE-WALK returning a VALUE (`| [], ys => List.headD ys default |
a :: xs, ys => if memb a ys then permWitness xs (rm a ys) else a`), with
the `[Inhabited α]` binder for `(CAR Y)` on an exhausted list, and
`permWitness_complete` is the book's SINGLE EQUIVALENCE. The header
carries the re-render note next to Q1's and Q2's. Nothing else in
`Mirrors/` changed (net-verified).

**SQUARES: 34 → 37, all `#guard_msgs`-pinned** — `rm` AGREE (against the
own-definition `rmL`; receipt `[propext]`), `Permuted` AGREE (against
`permL`; `[propext, Quot.sound]`), `permWitness` AGREE (against `pceL`;
`[propext]`). Each closes with its reading as its ONLY unfold, on the
registered `memb`/`rm` squares plus the fixed kit — the ladder is
UNCHANGED this wave (zero new rungs). The chain that unblocked them is
the one wave 2d-prep predicted exactly: the `rm` agree square was the
whole residual of `Permuted`'s, and `Permuted`'s the whole residual of
the perm-side crossings.

**PRODUCT #9 — `ordered_perm_unique_int`, trio-clean.** The book's
ORDERED-PERMS at `Int`, and the FIRST product whose spec `Prop` carries
HYPOTHESES. The seam gate prints `8 → 9` products and pairs it correctly
(`ordered_perm_unique_int → orderedPermsCapReplayedCond`). Two things
had to arrive and both are real:

* the `Permuted` agree square above (which carries the third hypothesis
  into the reading's vocabulary);
* **item 5 — `mirror_transport%`'s HYPOTHESIS-CARRYING rung.** The
  binder walk now classifies each binder as DATA (`List SExpr`) or
  HYPOTHESIS (`Prop`) and admits DATA-THEN-HYPOTHESES, fail-closed in
  both directions (a binder that is neither is a hard error; so is a
  data binder after a hypothesis). The crossing rewrites the hypotheses
  as well as the goal with the SAME fixed agreement-square set
  (`simp_all only` instead of `simp only`), and the mirror rung applies
  the normalised crossing instance to the mirror's own hypotheses. The
  hypothesis-FREE path is a separate branch and a separate closer macro,
  so every pre-existing transport's proof term is byte-identical.
  The waypoint cited is `ordered_perms_eq_driver`, a DECODE-SHAPE
  corollary of the catalogued ORDERED-PERMS native — the same class as
  that native's existing `List.Perm` corollary.

**ITEM 3 (the qsort pair) — TWO of its three blockers fall, and the
third is a RECORDED STOP.** Full measurement verbatim on the product
page; the summary:

* J-2b-5 is **REFUTED**. `qsortExec_eq_modes` — the exec's own equation
  re-spelled at `modeLT`/`modeGTE` — states and proves from OUTSIDE
  `Imported/Sorting.lean` by `rw [qsortExec.eq_def]; rfl`. `symV` never
  has to be NAMED, so de-privatising it is not on the critical path.
* the DEPTH blocker is **solved**: a depth-2 dispatch-free reading
  (`qsortOwnL`, through `filterLtL`/`filterGteL`) is a Lean definition,
  and against it `qsort`'s agree square's case 1 closes and case 2's
  equation SHAPES match.
* what is left is **exactly J-2b-4** — `filterRel`'s `DecidableEq`
  instance argument. The fact that dissolves it is PROVED
  (`decEqOfOrder_eq_instSExpr`, by `Subsingleton.elim`; Q4's general
  form was not a rewrite rule, this concrete one is, and it was measured
  to close the two-instance goal) — but it CANNOT BE PLACED: `unfold`
  is definitions-only and hard-errors on a lemma (verified), and a
  ladder rung is impossible because the fact names a MIRROR SPEC
  constant while `IsoGen.lean` imports only `ACL2Lean.Syntax`.
* NOT TAKEN. J-2b-4 is a recorded stop (delegation-boundary class 5), so
  it returns to the orchestrator with the measurement above rather than
  being re-decided here. A third item rides on whichever route wins:
  `qsortOwnL` cannot be `derive_sim%`-VALIDATED where it stands (a
  second general iso for "QSORT" is fail-closed), and converting
  `qsortL` itself needs `filterLtL` visible from `Imported/Sorting.lean`
  — i.e. a split of that grandfathered module.

**ITEM 4 (the element-result class) — BUILT, MEASURED, and NOT LANDED.**
The class works: `hom elem` infers the result reading from the
definition's own result type, drift-checks like the other two, and
`permWitness`'s square elaborates with every case closing but one —
`(List.map e.enc ys).headD default = e.enc (ys.headD default)`. That
residual is FALSE and no machinery can repair it: it is the JUNK ARM
(the book returns `(CAR NIL)` = `nil`; `intEmbed.enc` is an integer atom
and never `nil`). The `Prop` is unharmed; the POINTWISE square is what
cannot be stated. With its only consumer refuted the class would be
unwired machinery, so it was reverted — `IsoGen.lean` and the square
half of `TransportGen.lean` are byte-identical to their pre-wave form.
The open question is a SPEC one (how a mirror declares a junk arm) and
is reader-facing, so Mike's. `permWitness_complete`'s CROSSING does
close, which is the other half of the record.

**ITEMS 6, 7, 8 — NO WAYPOINT THEOREM EXISTS TO TRANSPORT.** Checked
concretely in the tree rather than inferred from the catalogue: there is
no `convert_perm_to_how_many_*`, no `*_is_isort_*`, no
`orderedp_bsort_*`/`how_many_bsort_*`, and no `bsortExec`/`bsortL` at
all. So the element-binder widening (item 6), the composition
meta-theorems (item 7) and the bsort exec kit (item 8) each have NO
consumer that could be wired now, and building any of them would be the
banned "infrastructure now, wire it later" — the J-2b-1 finding,
unchanged. Recorded, not built.

**J-CALLS.**

* **J-2d-5 — `pceL`'s reading converted to `rmL` (TAKEN).** It is the
  repair of item 1's red build AND the compliance move one level down;
  the reading is re-validated by its own `derive_sim%`. Disclosed
  because it changes a waypoint reading's definition.
* **J-2d-6 — the element-result square class REVERTED after measurement
  (TAKEN).** The alternative was to keep validated machinery with no
  closing consumer, which the working discipline names as the banned
  anti-pattern. The measurement is preserved verbatim on the pages.
* **J-2d-7 — `ordered_perms_eq_driver` ADDED as a decode corollary, not
  a statement change (TAKEN).** The catalogued native keeps its
  statement; the corollary is additive and in the class the layer
  already writes (`ordered_perms_native_perm_driver`,
  `perm_qsort_perm_driver`, `orderedp_qsort_isChain_driver`).
* **J-2d-8 — item 3's route NOT taken, returned to the orchestrator**
  (delegation-boundary class 5: re-opening a recorded stop). See above.

**REGRESSION NET.** Statements AND proof-term hashes over
`ACL2Lean.MirrorProofs`, `ACL2Lean.Sorting`, `ACL2Lean.Basics`,
`ACL2.Worlds.Sorting`, `ACL2.Worlds.Perm`. BASELINE PROVENANCE, stated
because it is not the usual one: the baseline is the dump wave 2d-prep
recorded as its AFTER state (646 declarations — the tree at `054fcb2`),
because `d9bdc96`'s own state CANNOT be dumped: it does not build. So
this net covers item 1 as well as items 2–8.

MEASURED: **646 declarations before, 663 after; ZERO REMOVALS, 17
additions, 7 changed statements and 7 moved proof terms** — and every
one of the fourteen is entailed by a ruling, an O-call or a logged
J-call. The complete list:

CHANGED STATEMENTS (7):

* `ACL2Lean.Sorting.permWitness`,
  `ACL2Lean.Sorting.permWitness_complete` — Mike's ruling Q3, the one
  authorized spec change. Every OTHER `Prop` in `Mirrors/` is
  byte-identical.
* `ACL2.Worlds.Perm.rmExec_enc`, `ACL2.Worlds.Perm.permExec_enc` — the
  two converted readings (item 1).
* `ACL2.Worlds.Sorting.pce_is_counterexample_native_of_replayed` —
  re-stated in `permL` vocabulary (O-6).
* `ACL2.Worlds.Sorting.pceL.eq_def`,
  `ACL2.Worlds.Sorting.pceL.induct_unfolding` — Lean-generated
  auxiliaries, following `pceL`'s body (J-2d-5).

MOVED PROOF TERMS, statements byte-identical (7):

* `ACL2.Worlds.Perm.corr_rm_enc`, `ACL2.Worlds.Perm.corr_perm_enc` — the
  decode bridges item 1 inserted so these keep their library statements.
* `ACL2.Worlds.Sorting.pceL` and its two `match_1.congr_eq_*`
  companions, and `ACL2.Worlds.Sorting.pceExec_enc` — J-2d-5.
* `ACL2Lean.MirrorProofs.elabMirrorTransport` — item 5's generator
  change, the only machinery term that moved.

NOTE what did NOT move, because it is the load-bearing negative: the two
pre-existing sorting PRODUCTS (`isort_ordered_int`, `msort_ordered_int`)
and their crossings are byte-identical, statement AND proof term, even
though three new agreement squares were registered — unlike wave
2d-prep, which had to disclose the opposite. So are all 25+ pre-existing
squares and every `Mirrors/Basics` declaration.

NET COVERAGE, stated because it is a real bound: the net's namespaces
are `ACL2Lean.MirrorProofs`, `ACL2Lean.Sorting`, `ACL2Lean.Basics`,
`ACL2.Worlds.Sorting`, `ACL2.Worlds.Perm` — `ACL2.Imported.Waypoints`
is NOT among them, so the two O-6 driver re-statements
(`perm_qsort_native_driver`, `ordered_perms_native_driver`), the third
(`pce_is_counterexample_native_driver`) and the added
`ordered_perms_eq_driver` are enumerated HERE rather than caught there.
Those four, plus the seven above, are the complete statement-change set
for this wave.

**TAMPER PROBES — three for the new mechanism, all hard-error:** a
transport whose cited waypoint has its sortedness and permutation
hypotheses SWAPPED (application type mismatch at the crossing); a spec
`Prop` with a FUNCTION binder (`sorter_unique`'s `f` — "neither a `List
SExpr` argument nor a HYPOTHESIS"); and a spec `Prop` with a DATA binder
AFTER a hypothesis. The third is also pinned as a BUILD-TIME negative
test (`Tests/IsoGenGateTests.lean`, the file's third), because this wave
introduced a new mechanism and that is what such a pin is for.

**RECEIPTS (verbatim).** New squares: `rm_agree_rmL` `[propext]`,
`permuted_agree_permL` `[propext, Quot.sound]`,
`permWitness_agree_pceL` `[propext]`. New product and its crossing:
`ordered_perm_unique_int` and `ordered_perm_unique_sexpr`, both
`[propext, Classical.choice, Quot.sound]`. The re-stated / added
waypoint entries, all trio: `perm_qsort_native_driver`,
`perm_qsort_perm_driver`, `ordered_perms_native_driver`,
`ordered_perms_eq_driver`, `pce_is_counterexample_native_driver`. The
two pre-existing products keep theirs: `isort_ordered_int`,
`msort_ordered_int`, both trio. No `sorryAx`, no `native_decide`
anywhere.

**Gate (fast-gate, in-worktree) [wave 2d].** Full `lake build` GREEN —
`BUILD_EXIT=0`, 6453 jobs, ZERO errors and ZERO warnings — and RE-RUN
after the last edit so the green covers the final tree state (the first
run had been started before a docstring edit; that is disclosed rather
than glossed, and the second run is the claim). `just test` green (3236
jobs). `just driver-coverage` 116/116 replayed, aggregate OK, 29 books;
`just check-golden-current` "golden matches the live assembly", and
`git status` shows `acl2_samples/` and all of `Tests/` except the
deliberately-edited `Tests/IsoGenGateTests.lean` byte-untouched. THE
MIRROR SEAM GATE prints **9** products, pairing the new one correctly
(`ordered_perm_unique_int → orderedPermsCapReplayedCond`). 10 of 13
statics PASS; `check-acl2-tags`, `check-log-provenance` and
`test-provenance-gates` fail ONLY because the `acl2/` submodule is not
checked out in this worktree (`ls acl2` is empty) — the same
environmental owe waves 2a–2d-prep recorded, owed at collection. No
`sorry`/`admit`/`native_decide` in the diff.

**WHAT THE SORTING CLOSE-OUT NEEDS FROM HERE, and its honest shape.**
Thirteen target `Prop`s; THREE are theorems (`isort_ordered`,
`msort_ordered`, `ordered_perm_unique`, all at `Int`). Of the ten left:

* **TWO are one ORCHESTRATOR DECISION away** — `qsort_ordered` and
  `qsort_perm`. Everything else for them exists or is measured; the
  decision is J-2b-4 plus where an instance-canonicalisation fact may
  live, and a module split of `Imported/Sorting.lean` rides on it.
* **ONE is one SPEC DECISION away** — `permWitness_complete`. Its
  crossing closes today; the junk-arm question is Mike's.
* **SEVEN need a WAYPOINT NATIVE THAT DOES NOT EXIST** —
  `isort_perm`, `msort_perm`, `bsort_ordered`, `bsort_perm`,
  `sorts_agree`, `perm_iff_howMany`, `sorter_unique`. That is the
  arc's real remaining shape and it is NOT mirror-side work: it is the
  `CONVERT-PERM-TO-HOW-MANY` native, the bsort exec kit + its two
  natives, the three `*-IS-ISORT` capstones, and (for `sorter_unique`)
  the encapsulate/parametric lane and its still-unraised ruling. The
  mirror machinery is ahead of the waypoint layer for the first time in
  the arc.

### Wave 2e (2026-08-18) — O-7 IMPLEMENTED; the QSORT PAIR LANDS (products 10 + 11); the CONVERT-PERM capstone native LANDS; three frontiers re-measured and one brief premise corrected

Executed in the same isolated worktree; nothing committed there. The
wave's headline is the one O-7 predicted: **`qsort_ordered` and
`qsort_perm` are THEOREMS at `Int`**, the product count goes 9 → 11, and
the square that had been recorded as blocked through waves 2b, 2c, 2d-prep
and 2d closed on the FIRST attempt once the instance fact had a legal
home. No ladder rung was added this wave and no closer capability was
added; the ladder is byte-identical.

**O-7 — THE INSTANCE-FACTS CLAUSE, implemented as ruled.**
`mirror_iso%` takes an optional `instances [thm₁, …]` clause
(`MirrorProofs/IsoGen.lean`: the syntax, `checkInstanceFact`, the
criterion section "THE INSTANCE-FACTS CLAUSE"). The named theorems reach
THAT square's closer and nothing else — scoped exactly like
`embed S via [fields]`, appended LAST to the lemma set so a square that
declares none is handed the identical set it was handed before (and its
proof term is unchanged). The SHAPE CHECK is the ruled one: the
statement must be an equation whose two sides carry the equation's own
type, and that type's head must be in the allowlist
`{Decidable, DecidableEq}` or carry a synthesizable `Subsingleton`
instance; anything else is a hard error naming the observed type. The
criterion paragraph states the rationale (an equality of subsingleton
instances is content-free BY CONSTRUCTION — proof-irrelevant, relating
no operations, proved per invocation by `Subsingleton.elim`, never
global) AND its honest bound in the A1-F9 form (the check is
STRUCTURAL; the bound is PROVENANCE only; do not harden).

**THE FACT, AND WHERE IT LIVES.** `decEqOfOrder_eq_instSExpr`
(`MirrorProofs/SortingQsortSquares.lean`, a NEW module — `SortingSquares`
was at 1499 of the 1500-line norm and could not take it), proved by
`funext; exact Subsingleton.elim _ _`, stated with an explicit
`: DecidableEq SExpr` ascription so the equation's own type is the
allowlisted one rather than the eta-expanded Pi it would otherwise
elaborate to.

**THE READING — and its validation bound, stated plainly.**
`Imported/SortingQsortReading.lean` (NEW): `qsortOwnL`, the depth-1
dispatch-free reading (`| [] => [] | a :: t => qsortOwnL (filterLtL a t)
++ a :: qsortOwnL (filterGteL a t)`), a Lean definition on the per-mode
filters' own length bounds. `derive_sim%` admits ONE general iso per exec
kit and a second `"QSORT"` registration is fail-closed, so this reading
CANNOT be handed to the template; it is validated by COMPOSITION instead,
and both halves are kernel-checked: `qsortOwnL_eq_qsortL` (a HAND proof
by the reading's own recursion) and `qsortExec_enc_own` (the template's
own conclusion, restated for it). The bound is on the record in the
module header and here: that one equation is a HAND correspondence where
the generated one is unavailable — the same class as the decode-kit
bridges of `Imported/SortingReadings.lean`, and in the SAFER direction,
since both sides are own-definitions and no library lemma speaks about
either. The O-6 guard is carried verbatim: the bridge and the two
`*_eq_filter` lemmas must never enter the mirror closer's kit or any
square's `unfold` list.

`qsortL`'s own equations are RE-SPELLED at the mode VALUES
(`qsortL_cons_cons`, proved `rw [qsortL.eq_def]; rfl`) — wave 2d's
`qsortExec_eq_modes` finding used one level up, and the reason J-2b-5
stays refuted: `symV` is never NAMED, only re-spelled past.

**PRODUCTS 10 AND 11 — `qsort_ordered_int`, `qsort_perm_int`, both
trio-clean.** The seam gate prints **11** products and pairs both
correctly (`qsort_ordered_int → orderedpQsortReplayedCond`,
`qsort_perm_int → permQsortReplayedCond`). `qsort_perm_int` is the
FIRST perm-shaped sorting product. The waypoints cited are two DECODE
corollaries added next to their natives (`orderedp_qsort_own_driver`,
`perm_qsort_own_driver` — the J-2d-7 class: additive, no statement
change to any catalogued native, no content of their own).

**THE CONVERT-PERM-TO-HOW-MANY NATIVE — BUILT, and the catalogue row is
PROMOTED `.pending` → `.native`** (`Imported/SortingConvertPerm.lean`'s
`convert_perm_to_how_many_native_of_replayed` +
`Imported/Waypoints/ConvertPerm.lean`'s
`convertPermToHowManyReplayedCond` /
`convert_perm_to_how_many_native_driver`, trio-clean, stated in the
own-definition `permL`/`pceL` vocabulary per O-6).

ONE CORRECTION TO THAT ROW'S OWN RECORD, recorded rather than smoothed
over: its `.pending` text said "no replay blocker … the replay side is
done". A bare `driver_replayed% convertPermDev convertPermWorldD
"convert-perm-to-how-many"` HARD-FAILS —
`replayCongCollapse: own-position rewrite under PERM at arg 0: 0
step-cited equivfull hypotheses (need exactly 1; cited equivalence runes
[PERM-IS-AN-EQUIVALENCE])`. It replays with `deps [permDev]`, which
offers the PERM book's own equivalence tree. The claim was true of the
CONDITIONS and false of the invocation; the fix is one clause, and the
catalogue comment now says so.

**THE THREE FRONTIERS, RE-MEASURED THIS WAVE (verbatim residuals on
`MirrorProofs/Sorting.lean` under "R4 WAVE 2e").**

* `permWitness_complete` — the CROSSING was BUILT and CLOSES with no
  residual against a real cited waypoint (the PCE row as an iff), and
  the MIRROR rung's entire residual is the ELEMENT-RESULT homomorphism
  for `permWitness`. **Mike's junk-arm RULING of 2026-08-18 arrived
  mid-wave, was implemented, and its ROUTE is REFUTED — see J-2e-6.**
* `perm_iff_howMany` — the transport was declared against the NEW
  CONVERT-PERM native and the crossing's residual proves two things: the
  registered agree squares DO carry the mirror `Prop` all the way into
  reading vocabulary, and the gap is the THEOREM. The book proves the
  WITNESS form; the mirror `Prop` is the `∀`-form, and no
  `PERM-IMPLIES-EQUAL-HOW-MANY`-shaped row exists in the complete
  `(:DEFTHM …)` inventory of either `convert-perm-to-how-many` or
  `sorts-equivalent` (checked, not inferred). A SECOND independent
  blocker is recorded: the `Iff` needs the crossing's `∀ a : SExpr` FROM
  the mirror's `∀ a : α`, which the encoded-only quantifier cannot give.
* `sorts_agree` + the two `bsort` `Prop`s — see the two J-calls below.

**J-CALLS.**

* **J-2e-1 — `qsortOwnL_eq_qsortL` is a HAND correspondence (TAKEN,
  disclosed).** The alternative routes were measured and are worse:
  converting `qsortL` itself to depth-1 breaks its `derive_sim%`
  (the exec tests `(consp x)` then `(consp (cdr x))`, so a depth-1
  reading cannot align with its recursion — the very failure mode item
  1 of wave 2d hit), and a second general `derive_sim%` for `"QSORT"`
  is fail-closed by design. Both sides are own-definitions, so unlike
  the O-6 bridges this one cannot re-open a library-lemma channel.
* **J-2e-2 — the three `*-IS-ISORT` capstone natives NOT BUILT, and the
  brief's premise is CORRECTED.** The catalogue's `.pending`s say "the
  native is the only gap", and that is right about the replay
  CONDITIONS and wrong about the work: `sorting/sorts-equivalent` has NO
  waypoint module at all — no `derive_world`, no `driver_replayed%`
  row — so the three natives are a new waypoint module for the corpus's
  largest book (eight dependency books on its coverage row). MEASURED,
  not assumed: a probe module (`derive_world` + `driver_replayed% …
  "msort-is-isort" with_termination deps [permDev, convertPermDev,
  orderedPermsDev, isortDev, msortDev, qsortDev, bsortDev,
  equisortDev]`) ran to `(deterministic) timeout at isDefEq/whnf,
  maximum number of heartbeats (8000000)` — i.e. the row does not
  elaborate at eight million heartbeats — and reported
  `[cross-book equisortDev: world NOT included in seWorldD — transfer
  refused]`. `BSORT-IS-ISORT` additionally needs `bsortL`, so at most
  two of the three were ever reachable this wave, and `sorts_agree`
  names all three in ONE `Prop` and is additionally a COMPOSITION
  (`mirror_transport%` cites one waypoint exactly). No product was
  reachable down this route; not built.
* **J-2e-3 — the bsort chain NOT BUILT, and ONE PIECE OF J-2b-1's
  ANALYSIS IS CORRECTED.** J-2b-1 said the kit's Lean termination fact
  exists only as `how_many_bad_pairs_bnext_native_of_replayed`, carrying
  world/`hreplayed` hypotheses "a definition's termination proof cannot
  discharge". The DRIVER form has them discharged:
  `how_many_bad_pairs_bnext_native_driver (xs) (h : xs ≠ bnextL xs) :
  bnextSizeL (bnextL xs) < bnextSizeL xs` is an unconditional theorem
  today, so a `bsortL` READING is an ordinary Lean definition on the
  REPLAYED measure decrease — no P2 hand proof at all. What is NOT
  discharged is the EXEC's termination: `bsortExec` recurses on
  `bnextExec x` for an ARBITRARY `SExpr`, where the replayed decrease
  (an `enc`-image statement, per the type-absorbed doctrine) does not
  reach; that plus BSORT's stage-1 `bsort_exec_corr` is the kit's honest
  remaining shape. Without the kit the reading is unvalidated and the
  natives cannot be stated, so building `bsortL` alone would be the
  banned "infrastructure now, wire it later". Not built; the looping-
  closer capability was therefore not built either (it has no consumer
  until a `bsortL` exists).
* **J-2e-4 — `sorter_unique` SCOUTED, and the scout found a SECOND
  route the brief did not name.** ROUTE A (the encapsulate/parametric
  lane) has three obstacles in increasing depth: the transport's
  FUNCTION-binder frontier (already a pinned tamper probe); the book's
  capstone relates TWO CONSTRAINED SORTERS rather than one sorter and
  `ISORT`, so the mirror's shape needs the constrained-order variant
  through real ACL2 (the wave's still-unraised ruling); and — the deep
  one — the mirror `Prop` quantifies over an ARBITRARY Lean
  `f : List α → List α` while a parametric constant is instantiable only
  at the `evalOpt` image of a `World` defun, so route A cannot reach the
  `Prop` AS STATED however much machinery is built. ROUTE B is
  COMPOSITION FROM LANDED PRODUCTS: `ordered_perm_unique` (product 9)
  and `isort_ordered` (product 1) are theorems, and with `isort_perm`
  plus the replayed PERM equivalence (`perm_transitive_native_driver`,
  `isPerm_equivalence_driver`) `sorter_unique` follows for ANY `f` from
  its own two hypotheses. Route B needs no encapsulate lane at all; its
  cost is exactly `isort_perm` plus a COMPOSITION mechanism — which is
  also what `sorts_agree` and the whole `*_perm` family need, making the
  composition mechanism the single highest-leverage unbuilt thing in the
  arc. Whether route B's logical glue is "thin generic lifting" (canon
  line 1's exception) or a Lean-side theorem specific to this example is
  a RULING; recorded for it, DESIGN ONLY, nothing built.
* **J-2e-6 — MIKE'S JUNK-ARM RULING (2026-08-18): the SPEC CHANGE IS
  LANDED VERBATIM; the ROUTE IT ENABLES IS REFUTED, kernel-checked.**
  The ruling authorised `permWitness_complete`'s precondition
  `(xs ≠ [] ∨ ys ≠ []) →`, the function unchanged with its junk arm
  named in a comment, on the premise that "the hom square becomes
  CONDITIONAL (true away from the junk arm)" and that the
  hypothesis-carrying transport would then land
  `permWitness_complete_int` as product 12.
  BOTH HALVES OF THE SPEC CHANGE ARE LANDED EXACTLY AS RULED
  (`Mirrors/Sorting.lean`: the precondition in the ruled shape, the
  `THE JUNK ARM` comment on the function, the honest-delta note in the
  `Prop`'s docstring including "do NOT add the unconditional
  corollary"). THE PREMISE IS FALSE, and the measurement is on the
  product page verbatim: **the precondition does not quarantine the
  junk arm, because the junk arm is reached BY RECURSION from inputs
  the precondition admits.** `fun_induction` on the conditional square
  leaves case 2 with an IH whose own precondition
  (`xs✝ ≠ [] ∨ rm a✝ ys✝ ≠ []`) the case cannot supply; the square is
  DISPROVED at `xs = ys = [1]`
  (`conditional_elem_square_false`, by `decide` — the two sides are
  `NIL` and `0`); and the characterisation is structural rather than a
  boundary case: `permWitness xs ys` IS the junk value on the ENTIRE
  `Permuted` half (measured: `permWitness [1,2] [2,1] = 0 = default`,
  against `[1,2] [2,1,5] = 5` and `[9] [2] = 9`, which are real
  witnesses). The square is true exactly where `¬ Permuted xs ys` —
  precisely the content-free half of the `Iff`. So NO precondition
  leaving the theorem's content intact makes the pointwise square true,
  the element-result class was NOT landed (its only consumer is
  disproved — J-2d-6's situation with a stronger disproof), and
  `permWitness_complete_int` DID NOT LAND. Two routes remain, neither an
  executor call and both recorded on the product page: an embedding with
  `e.enc default = default` (a spec/type question — no `Acl2Embed Int`
  can satisfy it), or COMPOSITION, which is blocked behind
  `perm_iff_howMany`'s missing `→` direction and is REASONING besides.
  RETURNED TO THE ORCHESTRATOR/MIKE: the precondition now buys clarity
  rather than the route, so whether to KEEP it is a follow-up spec call
  — it was not reverted here, because reverting a ruled spec change is
  itself a spec change.
* **J-2e-5 — a NEAR-CLONE accepted for one step (disclosed).**
  `convert_perm_to_how_many_native_of_replayed`'s decode is a near-clone
  of `pce_is_counterexample_native_of_replayed`'s (same `corr_*` chain;
  the only difference is that this row has no antecedent, so its ender
  is `Logic.eq_of_equal_ne_nil` directly). Two copies IS the extraction
  threshold and the extraction is flagged in the module; it was not
  taken in the same step that lands the native, per the
  one-verifiable-step-at-a-time rule.

**TAMPER PROBES — three for the new mechanism, all hard-error, plus a
BUILD-TIME negative test.**

* the SAME `qsort` agree square WITHOUT the `instances` clause →
  "the square template did not close", with the residual verbatim
  identical to wave 2d's recorded one (the two per-mode filters
  un-rewritten). This is the probe that proves the clause is
  LOAD-BEARING rather than decorative.
* the `qsort` agree square against a MISALIGNED reading (`isortL`) WITH
  the clause → hard-errors; the clause cannot rescue a misaligned
  square.
* a NON-THEOREM in the clause → "is not a THEOREM …".
* BUILD-TIME NEGATIVE TEST (`Tests/IsoGenGateTests.lean`, the file's
  fourth): the file's own first attack re-aimed — the accumulator
  CONTENT law handed to `instances [...]` instead of `unfold [...]` —
  refused at the shape check because its equation is at `List SExpr`.
  This wave introduced a new mechanism, which is exactly what such a pin
  is for.

**REGRESSION NET — the load-bearing negative, MEASURED not asserted.**
Registering a new AGREEMENT square before the transports is exactly the
mechanism that moved five proof terms in wave 2d-prep, so it was
measured directly rather than reasoned about: the three PRE-EXISTING
sorting transports and their crossings (`isort_ordered`,
`msort_ordered`, `ordered_perm_unique` — six declarations) were
re-generated by `mirror_transport%` twice, once with the new square
registered and once without, and their `pp.all` proof terms are
BYTE-IDENTICAL (28373 bytes each, `diff` clean modulo the probe's name
prefix). The mechanism that makes that true is deliberate: the
`instances` list is appended LAST to the closer's lemma set, so a square
declaring none is handed the identical set. ONE CHANGED SPEC STATEMENT, ruled and entailed:
**`ACL2Lean.Sorting.permWitness_complete`** gains the precondition
`(xs ≠ [] ∨ ys ≠ []) →` (Mike's ruling of 2026-08-18, the second and
final authorized `Mirrors/` change this wave — see J-2e-6).
`ACL2Lean.Sorting.permWitness` itself is BYTE-IDENTICAL (comment only,
as ruled), and the other TWELVE target `Prop`s and every other spec
definition are byte-identical. No other statement anywhere changed. The
additions are enumerated: `checkInstanceFact`
(machinery); `decEqOfOrder_eq_instSExpr`, `qsort_agree_qsortOwnL`,
`qsort_ordered_sexpr`, `qsort_ordered_int`, `qsort_perm_sexpr`,
`qsort_perm_int` (`MirrorProofs`); `qsortL_nil`, `qsortL_single`,
`qsortL_cons_cons`, `filterLtL_eq_filter`, `filterGteL_eq_filter`,
`filterLtL_length_le`, `filterGteL_length_le`, `qsortOwnL`,
`qsortOwnL_eq_qsortL`, `qsortExec_enc_own`,
`convert_perm_to_how_manyFormula`,
`convert_perm_to_how_many_native_of_replayed` (`ACL2.Worlds.Sorting`);
`convertPermToHowManyReplayedCond`,
`convertPermToHowManyReplayed_uncond`,
`convert_perm_to_how_many_native_driver`, `perm_qsort_own_driver`,
`orderedp_qsort_own_driver` (`ACL2.Imported.Waypoints`);
`smuggledInstanceFact` (Tests). ONE MOVED PROOF TERM, and it is the
generator this wave changed: `elabMirrorIso`. The catalogue's
CONVERT-PERM row changed CONSTRUCTOR (`.pending` → `.native`), which is
the promotion itself. TWO IMPORTS were added (`Waypoints/Qsort.lean`
gains the reading module; `Waypoints/ConvertPerm.lean` gains
`PermBook`, which is what `deps [permDev]` needs).

**RECEIPTS (verbatim, all ELEVEN new declarations trio-clean —
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
`native_decide`):** `qsort_agree_qsortOwnL`,
`decEqOfOrder_eq_instSExpr`, `qsort_ordered_sexpr`, `qsort_ordered_int`,
`qsort_perm_sexpr`, `qsort_perm_int`,
`convert_perm_to_how_many_native_driver`, `perm_qsort_own_driver`,
`orderedp_qsort_own_driver`, `qsortOwnL_eq_qsortL`,
`qsortExec_enc_own`. The pre-existing products keep theirs.

**Gate (fast-gate, in-worktree) [wave 2e].** Full `lake build` GREEN —
`BUILD_EXIT=0`, 6457 jobs, ZERO errors and ZERO warnings — RE-RUN after
the last source edit so the green covers the final tree state.
`just test` green (3238 jobs). `just driver-coverage`: **116/116
replayed, aggregate OK, 29 books**; `just check-golden-current`
"golden matches the live assembly", and `git status` shows
`acl2_samples/` and all of `Tests/` except the deliberately-edited
`Tests/IsoGenGateTests.lean` byte-untouched. THE MIRROR SEAM GATE prints
**11** products, pairing both new ones correctly. 10 of 13 statics PASS;
`check-acl2-tags`, `check-log-provenance` and `test-provenance-gates`
fail ONLY because the `acl2/` submodule is not checked out in this
worktree (`ls acl2` is empty — verbatim: "FAIL: no acl2/*.lisp files
found — submodule missing/not initialized?"), the same environmental owe
waves 2a–2d recorded, owed at collection. No `sorry`/`admit`/
`native_decide` in the diff or the new files.

**MODULE SIZE.** Two new modules rather than growth:
`MirrorProofs/SortingQsortSquares.lean` (90) and
`Imported/SortingQsortReading.lean` (145) — `SortingSquares.lean` was at
1499 of 1500 and may not grow. `IsoGen.lean` crossed the norm on first
draft (1506) and was brought back to 1500 by tightening THIS WAVE'S OWN
prose, not by deleting anyone else's.

**THE CLOSE-OUT SHAPE AFTER 2e — thirteen `Prop`s, FIVE are theorems
(`isort_ordered`, `msort_ordered`, `ordered_perm_unique`,
`qsort_ordered`, `qsort_perm`, all at `Int`). Of the eight left, the
shape has CHANGED CHARACTER and that is the finding this wave hands the
arc-exit decision:**

* **ONE IS NOT A SPEC DECISION AWAY ANY MORE, and that is this wave's
  hardest finding** — `permWitness_complete`. Its crossing demonstrably
  CLOSES; the residual is the element-result square; and that square is
  now KERNEL-DISPROVED under the ruled precondition, with the junk value
  characterised as the witness on the ENTIRE `Permuted` half (J-2e-6).
  The pointwise-square route is structurally dead at a junk-carrying
  element type. What is left is an embedding/type question or a
  composition that is blocked behind `perm_iff_howMany`. Mike's, with
  the premise corrected.
* **ONE is a MISSING BOOK THEOREM** — `perm_iff_howMany`. The corpus
  does not prove the `∀`-form (checked against the complete `:DEFTHM`
  inventory of both books), and the `Iff`'s quantifier direction is a
  second, independent blocker. This is NOT machinery and no amount of
  it helps.
* **SIX need a COMPOSITION MECHANISM and/or the bsort exec kit** —
  `isort_perm`, `msort_perm`, `bsort_ordered`, `bsort_perm`,
  `sorts_agree`, `sorter_unique`. The single highest-leverage unbuilt
  thing is the COMPOSITION mechanism (`mirror_transport%` cites ONE
  waypoint exactly, and every one of these six is a composition of two
  or more replayed facts); the second is the BSORT exec kit, whose cost
  J-2e-3 revises DOWNWARD for the reading and pins to the exec's
  arbitrary-`SExpr` termination. Note what is NO LONGER on this list:
  "the mirror machinery is ahead of the waypoint layer" was wave 2d's
  reading, and it still holds — but three of the six now turn on ONE
  mechanism rather than on six separate natives.
* NOT ON THE LIST ANY MORE: the qsort pair (landed) and
  CONVERT-PERM-TO-HOW-MANY (native built, catalogue promoted).

### Wave 2f (2026-08-18) — THE BIJECTION LANDS: the spec's 13 `Prop`s become 16, five of the moved rows land as products (11 → 15), and three of the arc's recorded "machinery frontiers" turn out to have been SPEC defects

Executed in the same isolated worktree; nothing committed there. Mike
approved the reshape checkpoint ("Agree on all", 2026-08-18) and the
checkpoint's landing list is what this wave executed. The permanent
record of the reshape itself is
`docs/notes/2026-08-18_sorting-spec-reshape.md`; this entry is the
execution log.

**THE HEADLINE.** `Mirrors/Sorting.lean`'s target-property section now
stands in a BIJECTION with the sorting corpus's RESULT-TIER theorems —
16 `Prop`s, 16 book theorems, one docstring citation each. Products go
**11 → 15**: `isort_howMany_int`, `msort_howMany_int`,
`qsort_howMany_int`, `permuted_equivalence_int` are new, and
`ordered_perm_unique_int` RE-LANDED as the `Iff`. The seam gate prints
15 and pairs every one correctly.

**WHAT THE RESHAPE COST, AND WHAT IT REVEALED.** Five of the ten moved
rows landed as products in the same wave, on ONE transport-table row
and ONE plumbing lemma. Three items this arc had recorded on
`MirrorProofs/Sorting.lean` as MACHINERY frontiers — `isort_perm`
(wave 2c: "the book does not prove it"), `perm_iff_howMany` (2e: "the
book does not prove the `∀`-form"), `sorts_agree` (2e: "additionally a
COMPOSITION") — were each a SPEC defect wearing a machinery costume:
`Prop`s no single book theorem backed. The composition mechanism that
wave 2e called "the single highest-leverage unbuilt thing in the arc"
is not needed by ANY of the sixteen `Prop`s as now stated; it was an
artifact of the old shapes. Correspondingly, two book theorems with
NATIVES ALREADY BUILT (`HOW-MANY-QSORT`, `PERM-IS-AN-EQUIVALENCE`) had
no `Prop` at all, and both landed the moment they were named.

**THE MACHINERY ADDED, IN FULL (three items, all measured before
built).**
1. THE SCALAR ROW of `mirror_transport%`'s binder table
   (`TransportGen`): an `SExpr` (element) binder encoded by `e.enc`
   where a list binder is encoded by `List.map e.enc`. This is the
   ELEMENT-BINDER frontier the charter predicted and wave 2c pinned;
   its first consumers are the three multiplicity mirrors. Fail-closed
   on the hypothesis-carrying path (a scalar binder plus hypotheses is
   a hard error — carrying an encoded element through a hypothesis
   needs an element-position invariance square, a class that does not
   exist), pinned as the file's FOURTH negative test in
   `Tests/IsoGenGateTests.lean`.
2. `map_inj_iff` (`TransportGen`) — `map_inj`'s `Iff` form, exactly as
   `enc_inj_iff` is to `Acl2Embed.inj`, plus two closer alternatives in
   `mirror_transport_close_hyps` that use it. Needed because
   `ordered_perm_unique`'s conclusion is now an `Iff` whose left side is
   the encoded list equation, and a one-way implication cannot replace a
   subterm inside an `Iff`. Appended LAST, so every pre-existing
   transport's proof term is unchanged — net-verified below.
3. THREE waypoint DECODE corollaries, all in the established class
   (additive, no statement change to any catalogued native, no content
   of their own): `ordered_perms_iff_driver` (ORDERED-PERMS as the
   `Iff` it literally is), `how_many_qsort_own_driver` (HOW-MANY-QSORT
   at the depth-1 reading), `perm_equivalence_permL_driver`
   (PERM-IS-AN-EQUIVALENCE in `permL` vocabulary).

**MEASURED, NOT ASSUMED — `permWitness_complete` re-measured against
the UNCONDITIONAL `Prop`.** Wave 2e's residual was taken against the
preconditioned one, so it was re-run rather than carried: the CROSSING
CLOSES with no residual (against a probe-local two-line decode
corollary of the CONVERT-PERM native, deliberately NOT landed — a
decode corollary whose only consumer cannot close is unwired
machinery), and the MIRROR rung's residual is verbatim identical to
wave 2e's, with `howMany_map_invariant` reported UNUSED. So J-2e-6's
structural verdict stands for the book-form `Prop` a fortiori: the
`Prop` is correct, the `Int` product is structurally unavailable, and
that is an honest scoreboard entry rather than a to-do.

**THE REGRESSION NET (built from a real reverted-source build, not
argued).** 685 declarations before, 697 after, over
`ACL2Lean.MirrorProofs`, `ACL2Lean.Sorting`, `ACL2Lean.Basics`,
`ACL2.Worlds.Sorting`, `ACL2.Worlds.Perm`.

* 17 ADDED — 7 new spec `Prop`s, 4 products + 4 crossings, `map_inj_iff`.
* 5 REMOVED — `isort_perm`, `msort_perm`, `bsort_perm`, `sorts_agree`,
  `perm_iff_howMany` (each replaced per the approved adjudication).
* 1 STATEMENT CHANGED — `ordered_perm_unique_sexpr` (the crossing),
  implication → `Iff`, entailed by the ruled spec change.
* 5 VALUE-ONLY CHANGED — the three reshaped-in-place spec `Prop`
  BODIES (`ordered_perm_unique`, `permWitness_complete`,
  `sorter_unique`; their signatures are unchanged so the change shows
  in the value), `elabMirrorTransport` (the generator), and
  `ordered_perm_unique_int` (the re-landed product).
* EVERYTHING ELSE BYTE-IDENTICAL — 674 pre-existing declarations,
  including all five KEEP `Prop`s (`isort_ordered`, `msort_ordered`,
  `qsort_ordered`, `qsort_perm`, `bsort_ordered`) and every
  pre-existing PRODUCT except the one that was ruled to change. That
  is the check that the closer's two new alternatives and the binder
  table's new row are non-intrusive.

**THE PAGE PRUNING, stated rather than done quietly.**
`MirrorProofs/Sorting.lean` lost its wave-2c and wave-2d frontier
sections and wave-2e's `perm_iff_howMany` subsection (653 → 473 lines).
Every one of those subjects is now either LANDED (the qsort pair, the
`Permuted` Q1 re-render) or describes a `Prop` THAT NO LONGER EXISTS
(`isort_perm`, `perm_iff_howMany`, `sorts_agree`), so keeping them
would point a reader at spec constants they cannot find. The text is
preserved verbatim in this charter's wave-2c/2d/2e entries above, which
is where the historical record belongs; the load-bearing measurements
(J-2e-6's kernel refutation and characterisation, J-2e-3's corrected
bsort-kit shape, the `sorts-equivalent` module absence) were carried
forward into the wave-2f section rather than dropped.

**J-2f-1 — THE COMPOSITION MECHANISM IS NOT NEEDED BY THE SPEC AS NOW
STATED.** Recorded because wave 2e ranked it the arc's highest-leverage
unbuilt item. Every one of the sixteen `Prop`s is a single book
theorem, so `mirror_transport%`'s "cite ONE waypoint exactly" is no
longer a constraint any target `Prop` violates. It remains relevant to
route B for `sorter_unique` (which is a REASONING route and a ruling,
not an executor call) and to nothing else in the sorting spec.

**J-2f-2 — `sorter_unique`'s ROUTE B SIMPLIFIED BY THE RESHAPE.** With
the `Prop` in the equisort capstone's own two-constrained-sorters shape
and `ordered_perm_unique` landed AS AN IFF, route B's remaining input
is exactly `permWitness_complete`'s `←` direction plus a composition
step — it no longer needs `isort_perm` (which no longer exists) or the
PERM equivalence separately. Its first input is the
structurally-unavailable product, so the route is blocked there; route
A's DEEP blocker (an arbitrary Lean `f` is not the `evalOpt` image of
any `World` defun) is unchanged and is the recorded reachability
question.

**THE REMAINING SEVEN, by real cause (no euphemism).**
* `bsort_ordered`, `bsort_howMany` — the waypoint natives do not exist
  and `bsortL` needs the BSORT exec kit (J-2e-3's corrected shape:
  the READING is free, the EXEC's arbitrary-`SExpr` termination is not).
* `msort_is_isort`, `qsort_is_isort`, `bsort_is_isort` —
  `sorting/sorts-equivalent` has NO waypoint module at all (J-2e-2);
  the third also needs the bsort kit. The reshape removed the OTHER
  blocker: three separate `Prop`s need no composition mechanism.
* `permWitness_complete` — `Prop` correct, product structurally
  unavailable (J-2e-6).
* `sorter_unique` — `Prop` correct, reachability open (the recorded
  ruling).

**VERIFICATION (fast-gate tier in-worktree).** Full `lake build`
EXIT=0, 6457 jobs, ZERO warnings, re-run after the last edit; seam gate
15/15 with correct pairings; mirror name check 56 spec names, no
collisions; the four `#guard_msgs` receipts on the new products are
trio-clean `[propext, Classical.choice, Quot.sound]`; the new negative
test's message is pinned; regression net as above from a real
reverted-source build.
