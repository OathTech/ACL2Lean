# Sorting-absolute arc (branch `mdd/sorting-absolute`)

Ratified by MDD 2026-08-01 ("Great, let's do it" on the three-phase
proposal). Opened at main 557c37b, immediately after the
sorting-completion-2 merge.

## Goal

The sorting book to ABSOLUTE completion, generalization prioritized:
every book of the 11-book sorting family in the sweep, every row green,
every reasonable green row mirrored natively, pins toward one per book —
with the industrialization done FIRST so the marginal cost of each new
mirror collapses before the new rows arrive.

## Ground truth at arc open (sweep 71/79, golden of 557c37b)

- In-sweep sorting books (6): perm, isort, ordered-perms, msort, qsort,
  sorts-equivalent. Red rows (5 of the sweep's 8):
  - ACL2-COUNT-EVENS-STRONG — branch-substitution literal
    `(not (equal (ACL2-COUNT (CDR X)) '0))` neither in clause nor
    segment fact at Subgoal *1/2.3' (msort).
  - ACL2-COUNT-EVENS-WEAK — spine ran out of items with no closer at
    Subgoal *1/2.2' (msort).
  - MSORT-IS-ISORT / QSORT-IS-ISORT — the R7
    functional-instantiation/:use frontier (constraint chain already
    discharged; the instantiated hyps await :use soundness).
  - BSORT-IS-ISORT — replayPreprocessChain lhs mismatch, downstream of
    the clausify-region RECON wall.
  (Non-sorting reds, NOT arc-gating: CLASSIFY-POS, CD2-BOUND,
  LEN2-APP-VIA-USE — though LEN2-APP-VIA-USE shares the R7 class and
  should fall with it.)
- Off-sweep sorting books (5): bsort (recon wall), equisort
  (encapsulate, R6), how-many / orderedp / convert-perm-to-how-many
  (logs on disk, consumed only as includes — never replayed
  first-class).
- Non-row debt carried in: ORDERED-PERMS mirror pending on dp-fact
  emission; hand `rule:` dischargers proving included-book content
  value-level in Lean (the industrialization note's flagged
  non-opportunity); statement pins 4/25 sorting rows; BUG-027
  ratify-or-narrow open (MDD decision).

## Phase 1 — INDUSTRIALIZATION

(Source: docs/notes/2026-07-31_mirror-industrialization.md.)

- **1a. Unify `driver_replayed%` with the runner's replay entry.** One
  shared replay-configuration builder (dev → cfg + fcRules + the
  termination pre-pass + equivRefls + every future channel) consumed by
  both. Removes the missing-channel bug class (three hard-failures
  accreted one at a time during the mirror program). First because it
  is a bug-class fix and everything later touches the macro.
- **1b. The exec-kit generator (`derive_exec%`).** A MetaM elaborator
  emitting `<fn>Exec` + `<fn>_exec_corr` from the emitted `:DEFUN`
  `:BODY` (IF→ite on toBool, builtin→Logic twin, defn call→callee exec,
  formal→argument) with termination from the emitted `:MEASURE`
  justifications (consCount, pair sums; per-instance kernel-checked —
  the certifying-walker lane of the generality plan). VALIDATION IS THE
  POINT: regenerate the existing ~20 hand kits in Sorting.lean; the
  generated defs/statements must match the hand ones; retire hand
  copies incrementally, each step behavior-preserving. The env-binding
  helper (#3) folds in here. `<fn>Exec_enc` (the native reading) STAYS
  HUMAN — that choice is the mirror criterion's fidelity judgment.
- **1c. The discharger registry.** `dis_<fn>_total` = exec_corr + one
  witness wrapper; `dis_<fn>_tp` = arg-strictness + val_unique + one
  value-shape lemma per emitted corollary shape (the observed closed
  set: boolean t-or-nil, consp, non-negative integer, true-listp,
  args-valued consp-or-second-arg). Built on 1b.
- **1d. Decode-kit v2.** Promote the accreted combinators (conv_if3,
  bool_of_iff_truthy, toBool_equal, conv_if_false', the implies/equal
  ender cadences) into Imported/Lifting.lean — 3+ consumers each;
  behavior-preserving extraction, each its own verifiable step.
- The ACL2 quotation macro (#5) is a COMPANION of 1b, built only where
  it pays into the generator — not its own project.

Banned failure mode (CLAUDE.md): building the generator "to wire in
later". 1b's unit of progress is a hand kit RETIRED with the build
green, never a generator feature in isolation.

## Phase 2 — FEATURES THE WHOLE BOOK NEEDS (value order)

- **2a. Cross-world replay wiring.** how-many / orderedp /
  convert-perm-to-how-many become first-class sweep books; `rule:`
  hypotheses discharge from the DEPENDENCY book's replayed statement
  (cross-world transfer). Retires the hand rule dischargers
  (dis_convert_perm, dis_rule_orderedp_append, the FOLD-CONSTS /
  NOT-MEMB class) and is the biggest conditional-row reducer.
- **2b. The two msort admission frontiers** (branch-substitution
  literal channel; spine closer).
- **2c. ORDERED-PERMS dp-fact emission.** Fork-side: emit the
  value-defining links the DP-value abstraction drops so the four
  ASSUMED:dp-fact hypotheses are provable as emitted (the documented
  replayDischargeNode threading TODO); then the last pending mirror
  falls.
- **2d. R7 — :use / functional-instantiation soundness.** DESIGN-HEAVY.
  An MDD design note for ratification BEFORE building (the arc's one
  planned mid-arc user checkpoint). Targets MSORT-IS-ISORT,
  QSORT-IS-ISORT, LEN2-APP-VIA-USE, and (post-2a) the
  CONVERT-PERM-TO-HOW-MANY replay that retires dis_convert_perm.
  **AMENDMENT (Mike, 2026-08-01): DEFERRED TO LAST in the arc — Mike is
  AFK and the ratification checkpoint must not block the other work.
  Draft the note en route; present on their return; build nothing on it
  before ratification. All other phase-2/3 items are R7-independent and
  proceed first.**
- **2e. The bsort recon wall.** clausify-input's second
  expand-abbreviations interleaving into the clausify event stream
  (ProofTree crash sites); flips BSORT-IS-ISORT's blocker and the
  p4-iff-or-shape tripwire.
- **2f. BUG-027 ratify-or-narrow** — MDD decision, one diff either way
  (the closure sits in one place by design).

## Phase 3 — THE REST OF THE BOOK

- bsort into the sweep (after 2e).
- equisort: encapsulate support (R6) — :CONSTRAINT-list emission (the
  deferred BUG-019-adjacent surface) + functional-instance consumption,
  pairing with R7.
- Mirrors for every new reasonable green row via the 1b generator —
  the arc's own test that industrialization worked.
- Statement pins toward one per book.

## Discipline

Unchanged and binding: emitted facts only, hard-fail at frontiers —
where an increment needs data ACL2 didn't emit, the fix is fork
emission, not Lean inference. Mirror criterion (MDD-ratified, see
NativeMirrors header + memory) governs every new mirror. Sub-arcs may
merge into this branch only after a comprehensive audit; the arc merge
itself gates on local `just ci` + explicit sign-off at the moment of
merge. Defects found en route are fixed in-arc, not deferred.

## Risk note

R7 and R6 are the two genuinely design-heavy items and both sit on the
critical path to the capstones (sorts-equivalent, equisort); everything
else is named-frontier work. If either design stalls, the arc still
lands phases 1 + 2a-c + bsort as standalone value.
