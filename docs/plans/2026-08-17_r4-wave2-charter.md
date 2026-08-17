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

**Gate (fast-gate, in-worktree).** Full `lake build` green, 6439 jobs,
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
