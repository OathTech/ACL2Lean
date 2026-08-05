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
  - Fork-blocked (8): the 3 μ-registry bsort rows (ORDEREDP-BSORT,
    TRUE-LISTP-BSORT, HOW-MANY-BSORT — the local `:LINEAR` snapshot gap
    behind termination:BSORT's honest `ASSUMED ◌`), HOW-MANY-SMALLER-BNEXT
    (the :TA-DERIVATIONS/marker-relief emission), HOW-MANY-BAD-PAIRS-BNEXT
    (rewrite-equal CAR phase — no recorded decision),
    ORDEREDP-WHEN-BNEXT-CONSTANT (equal-cars frames), and the IF-FINISH
    window class rides the recognizer-tuple emission.
  - PERM-TLFIX: sharpened post-close — its node is the R-VALUED payload
    class the ratified equiv-lane design explicitly deferred to rung 3;
    its red is design-consistent (TODO records the rung-3 outline).
  - HOW-MANY-RM-GENERAL: the solidify equation comes from a type-alist
    DERIVED entry — fork-blocked on the provenance emission (batch
    item 3).
  - PCE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS: the spine literal-chain
    mismatch class (Lean-side, undiagnosed depth — the one remaining
    possibly-buildable row).
- **P3 — DECIDED with 1 declared gap (amended post-close, commits
  75d8e39/e745263).** The 50 sorting catalog entries: 49 decided
  (.native or .replayedOnly-with-rationale), 0 undecided. This arc built
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
- **P4 — HOLDS (amendment scope).** Statement pins ≥1 per book for all 7
  amendment-scoped books (isort, qsort, convert-perm existing; perm,
  ordered-perms, msort, bsort added this close — each transcribed by hand
  from the `.lisp` source, hypothesis sets source-checked, golden-prefix
  cross-checked). sorts-equivalent/equisort excluded (no green row exists
  by the amendment's own deferral).
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
5. **include-book EDGE emission** (one event per include-book with the
   included book's name) — the include graph the provenance gate on
   cross offers needs (currently only per-theorem `:SOURCE
   :INCLUDE-BOOK` marks are emitted); also the prerequisite for the
   queued sweep parallelization.

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
