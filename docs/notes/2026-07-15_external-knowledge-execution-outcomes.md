# External-knowledge arc — execution outcomes (2026-07-15)

Companion to the ratified design (`docs/plans/2026-07-10_external-knowledge-design.md`)
and the execution brief (`docs/notes/2026-07-12_wp-execution-brief.md`). Records what
the execution found that the plan did not predict, the pre-merge audit, and the
frontier backlog the arc surfaced. The WP-by-WP execution record is in `TODO.md`.

## Queue outcome

WP0–WP4 and WP5(a) landed as specified, each gate-verified at its commit
(`ca039fc`, `e3a12b5`, `6e6942e`, `af33381`, `51b4580`, `5f658ce`).
Scoreboard: REPLAYED 26/50 throughout (the arc's target rows all ADVANCED to
later, different-class walls — see "frontier backlog"); differential
389 match / 8 known-bug / 0 FAIL throughout.

## Divergences from the plan (all surfaced at the time, recorded here)

- **WP2 / audit F1's FIX interim keep** (ratified 2026-07-15, retired same
  day): full builtin exclusion briefly regressed MY-LEN-MY-APP (its step case
  replays `(:DEFINITION FIX)`); a one-entry interim keep preserved the status
  quo until FIX's D4 definition fact landed and made the exclusion total.
- **WP3 / audit F2's anticipated `dischargeRuleHyp` builtin-boolean branch
  was NOT needed**: ground-zero rules discharge via prelude constants, which
  bypass `dischargeRuleHyp` entirely; the two-valuedness reasoning lives
  inside the constants' proofs (`lexorder_boolean`), and the `if1/boolean`
  LEXORDER branch predated the arc.
- **WP3 surfaced the FC-RELIEF frontier**: ORDEREDP-ISORT's next wall after
  the stored-rule offer is hypothesis relief recorded only as FC/type-set
  rune sets (`marker-relieved hyp … no (not …)-falsity fact in scope`) — the
  relief *derivations* are not in the log. Design territory (emit more, or a
  ratified carve-out extension); not in the WP queue.
- **WP4 / the ≈557M-node figure was historical** (pre-letBindFVar-era). The
  measured WP4 baseline: PERM-IS-AN-EQUIVALENCE inline = 13,506,883 nodes /
  5.9 s build / 2.0 s check; registry = 777,719 / 1.2 s / 0.4 s (17.4× size,
  ~5× time, identical conditions). The two scale axes of design §4 (audit F8)
  are thus both landed and separately measured.
- **WP5(b) D7 assembly DEFERRED — the queue's one scope stop**: the current
  corpus contains NO applied cross-book rule. Verified on the raw logs: every
  rewrite rune applied in every isort SIMPLIFY-CLAUSE step is ground-zero
  (CAR-CONS ×30, CDR-CONS ×36, DEFAULT-CAR ×1, LEXORDER-REFLEXIVE ×15,
  LEXORDER-TRANSITIVE ×15); cross-book names occur only in `(:RULES)` storage
  re-emission. The REAL D7 consumer is `sorts-equivalent.proof-log` (applies
  HOW-MANY-ISORT / ORDEREDP-ISORT / TRUE-LISTP-ISORT ×3 each plus the
  msort/qsort/bsort variants) — blocked behind (i) the dotted-rune
  `(:REWRITE F . 1)` parse frontier and (ii) the induction-generality wall
  (msort/qsort books), both outside the ratified queue. `evalOpt_world_mono`
  (D2) is proved and waiting; building the D7 wiring with no exercisable
  consumer would have violated the validate-against-the-real-artifact
  discipline. D7-enabling order: dotted-rune parse → induction generality →
  assembly against sorts-equivalent.

## Pre-merge audit (2026-07-15)

Five adversarial Opus reviewers (trusted-core, D4, D5, D1-registry,
fork-emission/world), decorrelated, primary-sources-only, each finding
re-derived by an independent skeptical verifier (default: refute).
**Zero critical, zero major. Five minor findings, all verifier-CONFIRMED,
four fixed in the audit-fixes commit, one accepted-documented:**

1. `check-no-shadow.sh` arm scrape required exactly one space after `|`
   (latent evasion) — FIXED (whitespace-flexible pattern).
2. WP2 elaboration-time body pins covered 3/7 D4 fns while the docstring
   claimed blanket coverage — FIXED (ENDP/ATOM/BOOLEANP pinned from the
   embedded isort snapshot; docstring now states NFIX is replay-time-checked
   only, exercised by CD2-BOUND).
3. `dischargeGzRuleHyp` (D5) is never exercised end-to-end by a completing
   theorem — only by the isolation pin (its consumers wall earlier, at
   FC-relief). ACCEPTED-DOCUMENTED: fail-closed by construction (a mis-wire
   fails the kernel); the pin discloses this; end-to-end validation arrives
   with the FC-relief work.
4. `CoverageMirrors` name sanitization is non-injective; a collision
   surfaced as a bare FAIL on a green replay — FIXED (explicit collision
   guard with a named diagnostic).
5. `check-acl2-tags` was not in `just ci` (pre-existing on main; more
   load-bearing after WP0's 92 emit tags) — FIXED (added to the ci recipe).

Notable reviewer could-not-verify items (recorded, not defects): `hnew`
dischargeability for concrete book pairs is untestable until D7 wires a
transfer call site; differential FIX coverage lacks rational/char inputs
(the refactor is structurally identical to the retired arm); ACL2.lexorder
vs the emitted LEXORDER body is a differential/masquerade concern, not a
D5 one.

## Frontier backlog surfaced by the arc (for the next design session)

- **Builtin TYPE facts** (LEN-REV-ACC): first registry species with NO
  emitted anchor — MDD decision needed between (i) fork-emitting ground-zero
  TP snapshots (faithful; corpus recapture) and (ii) an anchor-free species
  ratified D5-style.
- **Recognizer composition** (TRUE-LISTP-ISORT): reducing a recognizer
  through a CONS step to a TP'd subterm — needs the recorded node checked
  against the real tree before extending `replayRecognizer`.
- **FC-relief** (ORDEREDP-ISORT) — see above.
- **compound-recognizer runes** (CD2-BOUND): no recipe; inspect what ACL2
  stores for them.
- **Unrecorded iff-normalization** `(EQUAL X 'NIL) ⇒ (IF X 'NIL 'T)`
  (APP-NIL ×2, TRUE-LISTP-REV, REV-REV, TLP-APP-NIL): emission gap — the
  rewriter's final iff-normalization is not recorded as a child node.
- **Dotted-rune parse** (qsort, sorts-equivalent): parser extension.
- **Induction generality** (5 recon rows + msort/qsort/bsort/ordered-perms
  books + the D7 consumer): the highest-leverage single item.
