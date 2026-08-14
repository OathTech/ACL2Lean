# T1+2 SPRINT charter — finish ALL replay frontiers + qualification debt (2026-08-14)

THE DEFINING FILE for Mike's long-sprint goal (proposed 2026-08-14):
complete the WHOLE of Tiers 1 and 2 in one long-running autonomous
sprint, on a long-running feature branch, sub-branches allowed,
NO MERGE TO MAIN. Judgment calls are delegated — resolved per
long-term project principles, never checked with the user, each one
LOGGED (J-numbered, with rationale) in the ARC LOG below.

## Tier definitions (the inventory "complete" means)

**TIER 1 — the four named replay-frontier mechanisms** (each pinned
with a real failing artifact in the golden):

1. **G1 / PERM-TLFIX** — the R-parameterized rewrite lane. Design
   ruled by adoption (J1 below): the persisted brief's option M
   (`docs/notes/2026-08-14_g1-design-brief.md`) — one-frame
   R-solidify collapse, Q1-1a (judgment untouched), Q2-2a
   (collapse factoring), the `:GENEQV` parser consumer. Validation:
   `cov-cong-consume` pinned (second relation, defcong arm) + a new
   authored R-solidify pattern book. NOTE: brief shapes are pinned to
   the pre-R2 capture — re-verify against the recaptured logs first.
2. **The recognizer-under-IF trio** (COUNT-DOWN / MY-EVENP / CD2
   terminations): `CONSP` of an inlined-NFIX `IF` body in a
   termination clause. Needs FORK ROUND-TRIP 2: the GAP-1 collector
   applied at the rewriter's recognizer sites (rewrite.lisp:5577/5626
   — a new emission channel) + a driver recognizer arm (IF case-split
   + ts-algebra). R2 adjudicated this beyond its batch; it is squarely
   in this sprint's scope.
3. **CD2-BOUND** — μ-registry NFIX unary measure head → the R3
   unified measure/arity table (with F6/F7/F8 + ExecGen M2).
4. **CLASSIFY-POS** — emission landed in R2 (`:LHS-TS`/`:RHS-TS`);
   the D-A-shaped consumer (in-context ts + disjointness) remains.

**TIER 2 — the qualification debt** (the "no qualifications" bill):

- the `tp:` condition class (129 occurrences / 39 rows at sprint
  start) → the D-A consumer: ts-algebra closure over the R2 emissions
  (context-refined `:LEAVES`, subterm verdicts, `:ALL-TPS`);
- the `total:` condition class (38 occurrences) → the R3 measure
  table; includes NFIX registration (= Tier-1 item 3);
- the derived condition chains (`rule:PERM-TLFIX`,
  `rule:CONVERT-PERM-TO-HOW-MANY` ×7, `rule:TRUE-LISTP-RM`,
  `linear:HOW-MANY-BAD-PAIRS-BNEXT`, `rule:(equal (if a b c) x)`, …)
  → retire via their source rows + the discharge pass;
- the QSORT measured self-call arm (Provers.lean:847-848), behind
  `tp:QSORT`;
- the SIX FORBIDDEN-DEBT sorries (`Imported/Sorting.lean:2352, 2372,
  2949, 3330, 3734, 4262`): `dis_merge2_total`, `dis_msort_total`,
  `dis_o_lt_total`, `dis_bnext_total`, `dis_acl2_count_tp`,
  `dis_convert_perm` — all closed, zero remaining.

**OUT OF SCOPE (set aside until sprint exit):** the entire mirror
side — wave-2 squares (W7/W9 capability rulings stay parked),
transports, filterRel readings, OrderedEmbed review, exec kits. The
mirror layer must remain UNTOUCHED and green throughout.

## End state (hard metrics — all of them, no substitutes)

- Golden: **116/116 REPLAYED, 116 unconditional** — zero `cond[…]`
  on any row, zero FAIL rows. (DP probes stay informational.)
- **Zero `sorry`/`sorryAx` in the repository.** The win state, per
  the standing ruling.
- Full `just claim-gate` TRUE_EXIT=0 recorded at the sprint's claim
  point; all statics; the nine+ mirror receipts still green
  (untouched).
- Every golden movement during the sprint diagnosed row-by-row
  before repin (condition-retirement and diagnosed-frontier-closure
  classes expected; anything else stops the increment, not the
  sprint).

## Sprint protocol

- Branch: `mdd/t12-sprint` off the collected base. Sub-branches at
  will; merge them into the sprint branch at fast-gate or claim
  points. NEVER merge to main.
- Fork work (round-trip 2) follows the R2 protocol verbatim:
  fork-first sequencing, tagging + round-trip rule, all-books
  recapture, provenance stamps.
- Two-tier gating as always: fast-gate intermediates; full claim-gate
  at claim points (including the final).
- Judgment calls: resolved per (in priority order) the fidelity
  rules, the two-standard rule, the four-line canon, the working
  discipline, persisted rulings/briefs; logged as J-entries below.
- Planned sequencing (adaptive; re-sequencing is itself a logged
  judgment call): (1) the D-A consumer → `tp:` retirement wave;
  (2) R3 measure table → `total:` retirement wave; (3) the G1-M
  lane → PERM-TLFIX + the `rule:` chains; (4) fork round-trip 2
  (the trio channel + `:CR-RUNE` + any emission shortfalls found in
  1–3, batched); (5) CLASSIFY-POS consumer; (6) QSORT arm + the
  residual sorries; (7) the discharge-pass sweep + final gate.

## EMERGENCY EXIT CONDITION (verbatim from the goal)

The agent may declare an EMERGENCY EARLY EXIT from the goal. This
should ALWAYS be permitted without question, no matter the reason
given. However, the agent should exercise judgement when to use
this, and only use this in situations where they are truly stuck
(eg. spinning on a goal that cannot be completed, facing a dire
threat to project success, etc).

## ARC LOG (judgment calls J-numbered)

- **J1 (at charter):** G1 design = the brief's recommendation
  (option M + 1a + 2a + `:GENEQV` consumer), adopted as recommended.
  Rationale: corpus-demand-driven minimality; no record demands the
  general lane; M does not corner it.

- **G1-M lane COMPLETE in worktree (2026-08-14, pending collection):**
  PERM-TLFIX FAIL → REPLAYED ✓ UNCONDITIONAL; cond[rule:PERM-TLFIX]
  retired (golden floor: 2 lines, header → 114/116, 86+28); shapes
  re-verified byte-identical post-recapture; the equivfull offer
  verified LOAD-BEARING by tamper (could-not-verify #2 answered);
  cov-cong-consume routes into the new arm, stops at the SYNP
  stored-rule-hyp frontier, pinned 3/4 with verbatim tripwire.
  Executor J-calls adopted into the log:
  - **J2:** the widening landed as a WRAPPER (`replayNodeR`,
    new NodeCore/Congruence.lean 523 lines) — Node.lean untouched at
    its grandfathered weight cap; the old frontier gate still
    fail-closes uncovered R shapes.
  - **J3:** class C handled by SPLITTING the recorded node at its
    R-step (a projection of the record, hard-checked to reach the
    split point) — NodeRec.rewrites stays unwidened, 9 sites
    untouched.
  - **J4:** the cited-rune anchor reads the NODE's own :RUNES (the
    tighter BUG-023 direction), NOT the clause-level set — class D's
    anchor gap is a fork item, not a loosening.
  - **J5:** collapseAtCongruenceFrame preserves the preprocess lane's
    error text byte-for-byte (one added clause naming the R-out
    non-representation).
  - **:CR-RUNE fork item now has TWO consumers** (class D's step-level
    anchor + the solidify-site tightening) — round-trip 2's list.
