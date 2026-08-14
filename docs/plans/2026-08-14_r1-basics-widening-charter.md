# R1 charter — Basics 6/6 + generator widening (2026-08-14)

Branch `mdd/r1-basics-widening` off main @ 631c282. Second arc of the
R-sequence (`docs/plans/2026-08-13_r-arcs-roadmap.md`); executes the
master plan's A4 prep. Governing findings: over-spec audit F1/F3
(persisted 2026-08-13); the fork audit's verdict that the three
remaining Basics rows are GREEN + UNCONDITIONAL (no emission work —
mirror-side decode only).

## Goal

1. **A — Basics 6/6.** The three remaining mirrors of
   `Mirrors/Basics.lean` — `app_nil`, `rev_app`, `rev_rev` — proved at
   `Int` via `mirror_iso%`/`mirror_transport%`, trio-clean receipts
   (`#print axioms` = {propext, Classical.choice, Quot.sound}; no
   sorryAx, no native_decide), THE LIST in `MirrorProofs/Basics.lean`
   updated. Blockers are decode-layer only: the REV exec/iso kit
   (the revAcc slice from the Basics close-out is the template) and
   APP-NIL's TRUE-LISTP hypothesis absorption (every `List Int` enc
   image is a true list — a machinery-side kernel-checked fact, the
   sanctioned route per the trust story).
2. **B — F1: `mirror_iso%` per-argument readings.** Port SimGen's
   raw/list reading table up one level (the audit's noted irony: the
   layer below already has it); the hom builder applies `e.enc` at
   element positions and `List.map e.enc` at list positions.
   **Demand anchor (anti-"infrastructure now, wire later"):** each
   widening lands in the same increment as a REAL square declaration
   read off `Mirrors/Sorting.lean` — the acceptance witnesses are the
   audit F1 rejects: `insertOrd` (element arg), `howMany` (element
   arg + Nat result), `filterRel` (function arg — may adjudicate to a
   named frontier if the reading table doesn't extend honestly; a
   frontier message stating the real bound is a legal outcome).
   These squares are R4's consumers; declaring them now IS the wiring.
3. **C (stretch) — F3: transport instance threading + the order
   bridge.** `mirror_transport%` threads typeclass instances through
   the crossing (today: none — sorting's `TotalOrder` transport is
   unreachable); plus the restriction lemma
   (`lexorderB` on int-atom encodings ↔ `Int.≤` — a concrete
   kernel-checked machinery-side lemma, R4's named bridge). Stretch:
   drop without ceremony if A+B consume the arc.

### B design scout (2026-08-14, read-only, pre-execution)

Verified shapes: `derive_sim%`'s reading table is USER-DECLARED syntax
(`(x : raw) (xs : list)`, SimGen.lean:176-247) — necessary there
because the waypoint layer is untyped SExpr. At the mirror level the
reading is INFERABLE from the spec's Lean binder types:
`mirrorFnShape` (IsoGen.lean:285-293) already walks the telescope and
collapses to an `allList` boolean; F1 = return a per-binder reading
vector instead (`.list` for `List α`, `.elem` for the embedded `α`,
hard-error with the observed binder type for anything else), and the
hom builder wraps `.elem` vars in `e.enc`, `.list` vars in
`List.map e.enc`. No new user syntax. `filterRel`'s `keep : α → Bool`
is outside this table by construction — expected outcome is a named
frontier stating the real bound (function-valued arguments), unless
the book side turns out to use fixed-predicate filters that adjudicate
it differently. `howMany`'s `Nat` RESULT is a result-class question
(hom-scalar already exists) — check whether the scalar class's codec
covers `Nat` or only `Int` before claiming the witness.

### C design scout (2026-08-14, read-only, pre-execution)

The restriction lemma is concrete and small:
`Worlds… lexorderB` is `lexorder · · == SExpr.t` over the trusted-core
`lexorder` (Lexorder.lean:91; two-valuedness already proved,
Imported/Sorting.lean:26); on `intEmbed.enc` images (integer atoms,
IsoGen.lean:106) `lexorder` reduces to the number-comparison arm, so
the statement is `∀ m n : Int, lexorderB (intEmbed.enc m)
(intEmbed.enc n) = decide (m ≤ n)` — machinery-side, kernel-checked,
no new definitions. Instance threading in `mirror_transport%` remains
the substantive part of C.

## Discipline

- Real-artifact first: read the replayed statements off the live rows
  (`dump-proof-tree` / the coverage modules), never off memory; the
  revAcc slice is the template for the REV kit.
- One increment = one mirror or one widening + its witness; fast-gate
  each (build of touched targets + focused checks + the statics the
  diff touches); full `just claim-gate` once at exit.
- Vocabulary practice binds (own-definition readings; the collision
  linter); golden must stay byte-identical (this arc is mirror-side —
  any row movement means something went wrong: STOP and diagnose).
- F1 is a generator change: the 15 retired hand-square byte-identity
  checks from the Basics close-out must keep passing (the regression
  net for exactly this edit).

## Escape hatch (mandatory early-exit)

Stop and report immediately if remaining work gates on: a user ruling
(e.g. an unforeseen reading-table design fork with product-layer
consequences), a fork round-trip, or a ratified design boundary; or if
an A-item turns out NOT to be decode-only (i.e. the fork audit's
green+unconditional verdict fails on contact — that contradicts a
persisted audit and must be reported, not worked around).

## Exit

A complete (6/6 trio-clean) + B landed with witnesses (or honestly
frontiered per-witness) + C explicitly landed-or-dropped; claim-gate
TRUE_EXIT=0; ARC LOG appended here; merge candidate presented for
sign-off.

## ARC LOG (2026-08-14)

- **A — DONE** (commit 9cea7ce). Basics 6/6: `app_nil_int`,
  `rev_app_int`, `rev_rev_int` trio-clean, receipts
  `#guard_msgs`-pinned. New `Imported/Rev.lean` (APP/REV kit; 4
  generated exec/sim pairs; TRUE-LISTP absorbed at the encoded
  instance by the existing `Lifting.trueListp_enc` — the decoded
  statements are the full conditionals ACL2 proved).
  `mirror_transport%` gained one general closed-literal fallback rung;
  the three pre-R1 transports verified unchanged on rung 1. Fork-audit
  green+unconditional verdict CONFIRMED at the source. THE LIST 8→10;
  16 user lines for the three mirrors. `revL` spelled with `++`
  (forced by the registered `app_agree_append` square; inherits the
  logged compliance-pass item).
- **B — DONE** (commit bd14831). The reading vector landed (inferred
  from spec binder types, no user syntax; hard errors F5-style). W1
  `insertOrd`: past the shape gate to the honest instance frontier.
  W2 `howMany`: the positive witness (agree square elaborates; the
  hom-scalar codec question adjudicated CLEAN — the class asserts
  invariance, `Nat` needs nothing). W3 `filterRel`: the expected
  function-argument frontier, LIVE `#guard_msgs`-pinned
  (tamper-probed). Regression net reconstructed and passed: 23/23
  generated artifacts byte-identical.
- **C — concrete half DONE, threading half DEFERRED.**
  `MirrorProofs/OrderBridge.lean`: `TotalOrder SExpr` by LEXORDER's
  Bool reading (laws = `LexorderOrder.lean`'s CORE-LOGIC theorems)
  + the restriction lemma `lexorderB (enc m) (enc n) = decide (m ≤ n)`
  — both trio-clean, no sorryAx despite importing the debt-carrying
  `Imported/Sorting.lean`. W1 re-probed with the instance: statement
  ELABORATES; the closer leaves the two `bif lexorderB`/`if ≤`
  residuals (recorded verbatim on the witness page). Instance-THREADING
  machinery deferred: no elaborating witness exists before R4's exec
  kits, and W1's residual shows the next blocker is ladder design, not
  threading plumbing — building it now would be the banned
  wire-later pattern.
- **EXIT TRIGGER (escape hatch, declared):** remaining scope gates
  entirely on design rulings — the RULING BATCH: (1) ladder admission
  of `Acl2Embed.inj` (element-position hom squares; it is the
  embedding's defining field, list form `map_inj` already plumbing);
  (2) a hypothesis-directed Bool-reading rung (W1's `bif`/`if`
  residual; the ladder is currently hypothesis-blind by pinned
  criterion); (3) `filterRel`: widen the reading table to function
  arguments vs re-render the spec closer to the book's
  `(filter fn x e)` (mode symbol + pivot element) — product-layer,
  reader-facing; (4) the HOW-MANY waypoint reading's library
  vocabulary (`List.count` — one of the five logged compliance items)
  now surfaces in W2's residual. All four are widening questions
  ruling-1-sanctioned in principle; their concrete shapes are Mike's.
- **EXIT:** full claim-gate TRUE_EXIT=0 on 636c2ed (artifact:
  `.gate-runs/636c2ed-20260814T060311Z.log`) — 113/116 (84
  unconditional), golden matches live. Merge candidate presented.

## R1-D — the ruling batch (items 1, 2, 4; ruled 2026-08-14)

Item 3 (`filterRel` re-render) was NOT in scope and is untouched.

- **Item 1 — `Acl2Embed.inj` ADMITTED to the ladder.** `enc_inj_iff`
  (`IsoGen.lean`, the iff form, proved from the `inj` field) joins the
  square closer's fixed kit; the pinned criterion is now "`rfl`-lemmas +
  the embedding's `inj` iff", with the ruling's plumbing rationale and
  the `Acl2Embed`-has-no-order-field note. Acceptance (W2's hom-scalar
  residual): the residual CLOSES — but only after a gap the ruling did
  not anticipate. The STATEMENT BUILDER dropped the mirror definition's
  own instance binders, so `howMany`'s `hom scalar` statement did not
  elaborate at all (`failed to synthesize instance of type class
  DecidableEq α`). Reported as a deviation and fixed minimally
  (`mirrorFnShape` now returns the instance-implicit binders and the hom
  builder re-binds them at `α`, hard-erroring on any class that is not
  one-parameter-over-the-element-type). `howMany_map_invariant` is LIVE,
  `#print axioms` = [propext].
- **Item 2 — HYPOTHESIS-DIRECTED CLOSING.** Finding first: the closer
  was ALREADY `simp_all`-class, so case hypotheses always participated;
  W1's real blocker was VOCABULARY — `h : a ≤ head` and the goal's
  `bif lexorderB a head` never meet unless the order INSTANCE is
  unfolded. Minimal extension: the instance goes in the invocation's
  `unfold [...]` list (definitions only — already gated; an instance is
  a definition), and the fixed kit gained `Bool.cond_true/false`
  (`cond`'s own two cases, `rfl`, pinned in `LadderPins`). Deviation
  from the ruled acceptance text: the invocation therefore reads
  `unfold [Worlds.Sorting.insertL, instTotalOrderSExpr]`, not
  `unfold [Worlds.Sorting.insertL]` — measured both ways (without the
  instance the two residuals survive verbatim). W1's agree square
  `insertOrd_agree_insertL` is LIVE, trio-clean.
- **Item 4 — the HOW-MANY reading is an OWN-DEFINITION.**
  `Worlds.Sorting.howManyL` (new module `Imported/SortingReadings.lean`
  — `Imported/Sorting.lean` is at its ratchet cap), replacing
  `xs.count e` at the `derive_sim%` invocation and at all 24 consumer
  sites across 8 files. Every downstream statement changed ONLY in the
  reading's spelling and NO downstream proof needed adjusting (nothing
  was leaning on a `List.count` lemma). W2's agree square
  `howMany_agree_howManyL` is LIVE, [propext]. Compliance pass 5 → 4
  (`SimGen.lean` note + `TODO.md` updated).
- **Regression net:** the 23 generated artifacts are byte-identical
  before/after in BOTH statements and PROOF TERMS (the R1-B `#check`
  baseline plus a `#print` extension of it) — no pre-existing
  declaration changed route. Six mirror receipts green; sorries stay 6;
  golden matches live; tamper-probed (two misaligned readings still
  hard-error).

### R1-E (2026-08-14) — the filterRel re-render (ruled item 3)

- The spec re-rendered to the book's shape (`RelMode` four-mode enum +
  `relMode` dispatch + `filterRel fn e`, qsort at `.lt`/`.gte` with the
  book's argument correspondence verified at the source); 13 Prop
  statements byte-unchanged (regression net, 598 lines, statements AND
  proof terms). The `.fixed` pass-through reading landed tightly-scoped
  (`!hasFVar` types only), tamper-probed both directions, positive
  control closes live `[propext]`.
- DEVIATION: `decEqOfOrder` (a `local` low-priority `DecidableEq`
  derived from the order via antisymmetry) added to the spec so
  `qsort`'s Props keep binding `[TotalOrder α]` only — flagged for
  Mike's eyeball as a new product-layer declaration.
- W3 outcome: the old function-argument frontier pin is GONE
  (dissolved — nothing hard-errors pre-declaration any more); both
  filterRel squares BUILD but neither CLOSES; nothing declared.
  Measured closing condition for the agree square: (i) one ladder rung
  `Bool.decide_eq_true` (a `cases`-lemma — outside the pinned
  `rfl`-only criterion; removing it alone re-opens the squares) +
  (ii) per-mode square declaration (the registry is fail-closed at one
  `agree` square per definition; `relMode` is non-recursive so no
  functional induction exists — a general bound shared with `odds`,
  `permWitness`). Both are RULINGS, presented at exit. The hom square
  waits on the order-field question (W1's, unchanged).
- New compliance finding: `Worlds.Sorting.filterL` is spelled
  `xs.filter (…)` — a SIXTH library-vocabulary reading the five-item
  census missed; logged in TODO.
- LEXICON gained the closest-idiomatic-Lean paragraph (the two-step
  use pattern, Mike 2026-08-14).
