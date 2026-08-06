# Sorting close-out arc — CLOSE REPORT (2026-08-05)

The arc's mechanical close under the MDD arc-exit amendment (2026-08-04,
recorded verbatim in the plan): the abstract-world buildout (equisort's 14
rows + the 3 sorts-equivalent capstones) is deferred to the follow-on arc;
P2/P3/P4 are read excluding those rows; the close DECLARES the missing
pieces with numbers.

Headline: **REPLAYED 86/116 (31 unconditional + 55 conditional);
DP-discharge leaves ✓60 ◌11 ✗0 of 71** — every count from the committed
golden at HEAD, gate TRUE_EXIT=0. (Post-close continuation e5eeab9: the
complement-tautology close flipped TRUE-LISTP-BNEXT green — the
add-literal complement class, previously a loud frontier.)

## The six predicates

- **P1 — HOLDS.** All 9 row-bearing family books in the sweep: perm,
  convert-perm-to-how-many, isort, bsort, ordered-perms, equisort, msort,
  qsort, sorts-equivalent. how-many/orderedp contribute defuns to their
  dependents' worlds and bear no rows of their own.
- **P2 — OPEN (declared; amended post-close).** Sorting FAIL rows under
  the amendment: **9** (bsort 6, convert-perm 3; the excluded equisort 14
  and capstones 3 are the deferred piece; TRUE-LISTP-BNEXT flipped green
  via the complement-tautology close). Every row carries a named class:
  - *(Sub-counts corrected + refreshed 2026-08-06, pre-merge audit N2 —
    the original bullet said "(8)" while naming 6 rows, and described
    termination:BSORT as `ASSUMED ◌`, stale after the second kill
    round.)*
  - Fork-blocked (6): the 3 μ-registry bsort rows (ORDEREDP-BSORT,
    TRUE-LISTP-BSORT, HOW-MANY-BSORT — the local `:LINEAR` snapshot gap
    behind termination:BSORT's now-LOUD parked frontier),
    HOW-MANY-SMALLER-BNEXT (the :TA-DERIVATIONS/marker-relief emission),
    HOW-MANY-BAD-PAIRS-BNEXT (rewrite-equal CAR phase — no recorded
    decision), ORDEREDP-WHEN-BNEXT-CONSTANT (equal-cars frames); the
    IF-FINISH window class rides the recognizer-tuple emission.
  - PERM-TLFIX: sharpened post-close — its node is the R-VALUED payload
    class the ratified equiv-lane design explicitly deferred to rung 3;
    its red is design-consistent (TODO records the rung-3 outline).
  - HOW-MANY-RM-GENERAL: now reds at the restored ambiguous-position
    hard-fail (Lean-side completion first: pin preSwap?/branchAnchor
    across survivors or prove uniqueness — the parked item-15 work);
    behind that, the solidify equation's type-alist DERIVED entry is
    fork-blocked on the provenance emission (batch item 3).
  - PCE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS: now reds at the recognizer TP
    frontier (the killed tpthm consumer's row); both its frontiers are
    fork-blocked (batch items 2 and 5).
  (6 + 1 + 1 + 1 = 9 ✓.)
- **P3 — DECIDED with 1 declared gap (amended post-close, commits
  75d8e39/e745263).** The **51** sorting catalog entries: **50** decided
  (.native or .replayedOnly-with-rationale), 1 `.pending` — the declared
  gap below. *(Numbers corrected 2026-08-06, pre-merge audit N1: the
  original text said "50 entries: 49 decided, 0 undecided", which both
  miscounted and contradicted the declared gap.)* This arc built
  FOUR native mirrors — the three planned convert-perm ones
  (NOT-MEMB-IMPLIES-HOW-MANY-IS-0, `List.count_eq_zero` class;
  NOT-MEMB-IMPLIES-RM-IS-NO-OP, `List.erase_of_not_mem` class;
  HOW-MANY-RM, count-of-erase) plus HOW-MANY-BNEXT (the full
  bnextExec/bnextL hand simulation — the msortExec-precedent route) —
  all `.native`, seam-gated, axiom-clean. The ONE declared gap:
  CONVERT-PERM-TO-HOW-MANY, whose honest blocker is NOT simulation work
  (the PCE exec kit exists; a decode was drafted, built green, and
  reverted per the unwired-infrastructure ban) but its conds
  rule:PERM-TLFIX and use:PCE-IS-COUNTEREXAMPLE — both from RED rows
  whose replayed statements are the only criterion-clean dischargers.
  It wires the moment those two P2 rows green.
- **P4 — HOLDS as of 2026-08-06 (was an overreach as originally
  declared — pre-merge audit M2).** The original text claimed
  "convert-perm existing"; in fact NO statement pin for any
  convert-perm-to-how-many theorem existed (its log was offered only as
  a cross-book dependency source), so the honest state at close was
  **6 of 7**. Fixed 2026-08-06: HOW-MANY-RM pinned
  (`Tests/SortingPins.lean`, the book's own `derive_world` + status-line
  + statement pin, transcribed from convert-perm-to-how-many.lisp:30).
  The other six books' pins were audit-verified against their `.lisp`
  sources (inside lane, term-for-term). sorts-equivalent/equisort
  excluded (no green row exists by the amendment's own deferral).
- **P5 — RUN, recorded.** The drift-test review ran mid-arc as the
  consumer-queue audit's outside lane and returned FAILS; the remediation
  REVERTED the offending walkers (conforming to ratified §3(c)) and
  queued the targeted emission. Post-remediation state: one type-set
  walker (the ratified `typeSetWalk`), recognizer-keyed arm count back at
  the sub-arc base level. Named residuals, recorded in TODO with queued
  dispositions: builtinRecogFacts (1 entry + 2 lemmas; subsumed by the
  queued recognizer-tuple emission), the compound-recognizer rune→head
  whitelist (same subsumption), the μ-route discrimination heuristic, the
  chainOk near-clones.
- **P6 — HOLDS.** `just ci` pipefail-honest TRUE_EXIT=0 recorded in every
  increment commit (6+ full gate runs on close day, each re-elaborating
  the coverage table against the same committed golden — the byte-stable
  double-elaboration evidence); audit records committed:
  2026-08-05_consumer-queue-audit.md (NOT-READY → remediated →
  fresh-verified READY, addendum in place) and this close report.
  *(Amended 2026-08-06, pre-merge audit M1: the branch drift audit
  itself had NO committed record — its item numbers were cited from six
  code sites and the golden with nothing to read. Now committed:
  2026-08-05_branch-drift-audit.md, the reviewer's report verbatim,
  recovered from the session transcript.)*

## Machinery debt — SWEPT where buildable (amended post-close)

Done in-arc after all (commits 04120bb, a6f5f77): **dp-premises F6** — a
proved DP leaf can no longer silently downgrade to ASSUMED (only genuine
prover failure or a runtime bound falls back; post-prove machinery
failures surface); **allBookRules v1 gap** — the direct rule-events walk
(last-theorem rules and theorem-less dep books now offered; golden
byte-identical). Not buildable in-arc, with reasons: **include-book
provenance gate** — the include EDGES are not emitted (only per-theorem
:SOURCE marks), so it joins the fork batch (item 5 below);
**leaf-class gating plumb** — the open ratification sub-question (MDD);
**generator-reads-the-log** — simulation-scale (12 hand exec defs),
declared. Also carried: S6 (position-canonical preSwap? pinning), N2
(the ASSUMED:dp-fact literal), chainOk dedupe, and the dpFactStmt
root-cause fix (assumed obligations at actual applications).

## Branch drift audit + second kill round (2026-08-05, post-close)

The commissioned Opus branch-wide drift review (user-directed) returned:
**"the branch's direction is right; its tail accreted."** 28-feature
inventory; 9 per-case mechanisms, 6 with zero dependent green rows
(verified per-commit — every new mechanism replaced a throwError, so the
golden delta is an exact dependency read-off). The full fix list was
executed the same day (zero scoreboard cost; all golden diffs are
error-text-only on red rows):

- **KILLED**: the tpthm consumer stack (Harness offers, replayRecognizer
  tpthm arm, tpthm demand emitter); Core's chain-end deep-walker
  fallback and last-position nil-drop completion (throws restored); the
  L-orientation call-stack fold and the boolean-TP fold; the
  single-summand and term-vs-sum disjointness cells (the NESTED-SUM cell
  and its match-capture fix kept); the type-set-equality orientation
  normalization; the world-fn compound-recognizer route (item 9); the
  ambiguous-position preference (hard-fail restored, item 15); 12
  orphaned EvalLemmas.
- **HELD UNDER EXPIRY** (in-code drift markers): R1 the
  equation-closure disequality rung — expires at fork item 3; R2
  `builtinRecogFacts` — expires at fork item 2; R3 the μ-route
  discrimination heuristic — revisit at the fork-batch review.
- **EXPLICIT KEEP**: the unwired emission surfaces (:TA-DERIVATIONS,
  :FC-DERIVATIONS, Development.scopes, encapsulate events) — the queued
  fork batch's consumers.
- **OPEN MDD QUESTION (R4)**: does GROUND-HYP discharge sit inside the
  DP-leaf carve-out, or does it need its own ratification?
- **Verified**: `bnextBody` mechanically equal to the log's `:DEFUN
  BODY` (parse-and-compare); the complement-tautology close re-commented
  as inferred-from-absence.

## The accumulated fork batch (ONE round-trip, pending review)

1. **Local `:LINEAR` rule snapshot** — extend the gz-linear cited-closure
   collectors (ld.lisp ~5474, `infra/gz-linear-rules`) beyond PREDEFINED
   syms to cited LOCAL `:LINEAR` rules (same entry shape, same event).
   Unblocks: termination:BSORT's assumed leaf → the 3 μ-registry bsort
   rows.
2. **`:FALSETS` + recognizer-tuple snapshot** — emit `:FALSETS` alongside
   the existing `:TYPESET`/`:TRUETS` at the two recognizer sites
   (rewrite.lisp ~5556/5618, already in scope there), and snapshot the
   cited `'recognizer-alist` tuples (fn, true-ts, false-ts, strongp).
   Makes recognizer verdicts data-driven off emitted content (the shape
   of ACL2's own `type-set-recognizer`), replacing the reverted walkers
   per ratified §3(c) and subsuming builtinRecogFacts + the rune→head
   whitelist. Unblocks: the 3 nfix termination rows' route; feeds the
   IF-FINISH window class (whose composition consumer is Lean-side work
   after this lands).
3. **fc-derivations at the expunge call sites** (simplify.lisp
   ~1713-1731; the ITEM-4 diagnosis) — the `:TA-DERIVATIONS` all-NIL fix.
   Unblocks: the LEXORDER-TRANSITIVE marker-relief class
   (HOW-MANY-SMALLER-BNEXT + the parked ORDEREDP-APPEND/MEMB backlog).
4. **emit/defthm tag text refresh** (comment-only: the tag omits
   `:TFORMULA`) — rides along.
5. **Literal-boundary normalization steps** (rewrite-atm's iff-context
   collapses — the IMPLIES-antecedent drop, the boolean-IF wrappers):
   the silent normalizations the killed tower bridge re-implemented; with
   them recorded, the PCE literal composes from recorded steps like every
   other chain (the drift tidy-up's replacement route, 2026-08-05).
6. **include-book EDGE emission** (one event per include-book with the
   included book's name) — the include graph the provenance gate on
   cross offers needs (currently only per-theorem `:SOURCE
   :INCLUDE-BOOK` marks are emitted); also the prerequisite for the
   queued sweep parallelization.
7. **add-literal complement-close emission** (added 2026-08-06, pre-merge
   audit B1): record the clause close when `add-literal` recognizes the
   rewritten result's complement among the earlier assumed-false literals
   — today the replay INFERS this close from the ABSENCE of a recorded
   continuation (`Core.lean`, the complement-tautology arm;
   TRUE-LISTP-BNEXT depends on it). Emitting it converts the one
   inferred-from-absence step into a recorded one. (The DISPOSITION of
   the existing arm meanwhile — hold under expiry vs restore the throw
   vs ratify — is an open user decision; see the pre-merge audit
   section.)

Every item is information ACL2 already stores; per the batching rule the
round is ONE rebuild + one full recapture + row-by-row golden review, and
the list requires review before rebuilding.

## Proposed pre-merge audit (requires sign-off before launch)

Same shape as the arc's sub-arc audits (the proven pattern): ground truth
first (build + gate re-run by the auditors), then two decorrelated
adversarial Opus reviewers — inside: the arc's commits vs the plan +
amendment (are the declared gaps honest and complete? did any predicate
claim overreach?); outside: the mirror criterion + drift test across the
arc's whole surface (seam pairings, the new pins' transcription fidelity,
the three new mirrors) — then a fresh verifier on the findings.
Estimated cost: on the order of the consumer-queue audit (~500k tokens
total). The merge into main additionally requires explicit sign-off at
the moment of merge, per the standing rules.

## Pre-merge audit — RUN (2026-08-06, two decorrelated Opus lanes)

User-approved two-lane version. Both lanes independently established
ground truth (build exit 0, `just ci` TRUE_EXIT=0, golden header
arithmetic reproduced, `#print axioms` clean on 5+ mirrors each, zero
sorry/axiom/native_decide in the branch diff). Findings, each
independently re-verified against the source before acting:

- **M1 (both lanes)** — the branch drift audit had no committed record
  while six code sites + the golden cite its item numbers. FIXED:
  `2026-08-05_branch-drift-audit.md` committed verbatim from the session
  transcript; P6 amended.
- **M2 (inside)** — P4 overreach: no convert-perm-to-how-many statement
  pin existed ("convert-perm existing" was false; 6/7). FIXED:
  HOW-MANY-RM pinned; P4 amended.
- **B1 (outside)** — the complement-tautology close is INFERRED FROM
  ABSENCE of a recorded continuation (the one such step on the branch;
  TRUE-LISTP-BNEXT depends on it; no expiry, no ratification). PARTIAL:
  emission queued as fork batch item 7; the arm's disposition
  (expiry-hold vs restore-throw vs ratify) is an OPEN USER DECISION.
- **B2 (outside)** — the complement arm could close a clause while
  silently dropping pushed children. FIXED: explicit
  `children.isEmpty` guard (throw).
- **S1/S3-inside/R4 (both lanes)** — the GROUND-hyp closed-form relief
  sits in rewrite-chain territory while the carve-out text is
  clause-leaf-scoped; merging must not settle it silently. FIXED
  (marking): explicit UNDER-OPEN-MDD-QUESTION-R4 marker at the arm;
  the R4 decision itself remains open.
- **S3-inside (both lanes)** — `bsortDpFact_false` cited in code, TODO,
  and the consumer-queue audit but never committed. FIXED: citations
  reworded (the structural fix it justified is real and stands);
  correction addendum added to the consumer-queue audit.
- **S2-outside** — the fork now emits `:GENEQV` (the honest net-step
  relation; R-lane prerequisite) and nothing parses it; the R-gate still
  keys on the under-reporting `:EQUIV`. RECORDED in TODO as the rung-3
  arc's designated consumer (deliberate queued surface, same class as
  :TA-DERIVATIONS).
- **N1/N2 (inside)** — P3's entry counts wrong (50/49/0 vs actual
  51/50/1) and P2's sub-count "(8)" naming 6 rows, with a stale
  `ASSUMED ◌` description. FIXED: both amended with dated corrections.
- **N3 (inside)** — TODO.md's top-of-file governing-arc pointer was
  stale. FIXED.
- **N5 (outside)** — the load-bearing witness-defun world exclusion was
  a `| _ => w` catch-all. FIXED: explicit `.witnessDefun` arm.
- **N8 (outside)** — the `:use` topological guard admitted everything
  when the citing theorem was absent from its book list. FIXED:
  fail-closed.
- **N4/N6/N7 (both lanes)** — scoreboard-reading hazard (green capstone
  with conds from red rows), the hand-maintained mirror axiom-gate list,
  the nested-`:use` cyclic-let robustness note, and the EVENS/ODDS
  destructor-whitelist watch item: RECORDED in TODO as queued hardening.

Both lanes credited (verified, not prose): the plain-`:use` composition,
the ASSUMED-vacuity fix, the four P4 pins' term-for-term transcription
fidelity, the tamper tests, and the end-to-end statement-fidelity traces
(HOW-MANY-BNEXT et al., .lisp → log → replayed statement → native
mirror, exact at every hop).

OPEN USER DECISIONS AT MERGE: (1) B1's disposition; (2) R4's answer —
neither is settled by merging; both are marked in-code and queued.
