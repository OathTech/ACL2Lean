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

- **PHASE 1 COMPLETE (b71e1be) — report verified ACCURATE at
  collection** (golden 85+28 with the 8 diagnosed retirements,
  committed; sorries 5). Phase-1 J-calls adopted: **J6**(=J-a)
  DISCHARGE-bracket tp: (119) is probe-structural, informational per
  charter, separate feasible item; **J7**(=J-b) demand-driven
  ts-algebra inventory; **J8**(=J-c) the <-against-zero mask is a
  Lean-side closure lemma about our model — the VERDICT stays ACL2's;
  **J9**(=J-d) addressed-leaf admissibility is GAP-1's payoff;
  **J10**(=J-e,f) shared extractions + module splits per ratchet.
- **G1-M COLLECTED into the sprint branch** (9-file patch 3-way +
  Congruence.lean copied — worktree `git diff` omits untracked new
  files). Combined golden: phase-1 base + PERM-TLFIX ✓ + convert-perm
  cond retired, header 114/116 (87+27), submitted to the verifying
  sweep (downstream rule:CONVERT-PERM-TO-HOW-MANY retirements may
  surface — the sweep arbitrates; retirement-class diffs extend the
  candidate, anything else stops).
- **ORCHESTRATION DEVIATION (logged for honesty): a `cd` into the
  G1-M worktree persisted across shell calls** — several commands
  (incl. a full verification sweep and a charter append) silently ran
  in the worktree; one interim conclusion (an accusation that
  phase-1's golden repin "did not survive") was drawn from the wrong
  tree and was WRONG — phase-1's report was accurate. Corrected here;
  the worktree copy of that text is discarded with the worktree.
  Countermeasure recorded in memory: absolute paths whenever any
  worktree exists.
- **RT2 shortfall list (current):** per-:ALL-TPS-entry :LEAVES
  (tp:QSORT); the recognizer-site channel (the trio); :CR-RUNE (two
  consumers). Driver queue: hypothetical-TP mode; the FILTER-opaque
  measured arg; SYNP hyp relief (class D).

- **FORK ROUND-TRIP 2 SHIPPED (acl2 @ e8d78e513d, 2026-08-15).** Three
  of the four asks landed; the fourth was scouted and skipped. Image
  rebuilt POST-commit, `just recapture-all` 91/91 stamped at
  e8d78e513d, golden movement ZERO (114/116, 98+16 — byte-identical
  `.actual`; no world-header shift, no row status change), build green,
  all 13 statics PASS, sorries unchanged (2), 15 `#guard_msgs` mirror
  receipts green.
  - **Ask 1 — per-`:ALL-TPS`-entry `:LEAVES`.** Entries are now
    `(rune hyps basic-ts corollary term leaves)`. Prototyped in-image
    BEFORE editing (the R2 discipline): `TRUE-LISTP-APPEND`'s leaves go
    `(3072, *ts-unknown*)` → `(1024, 1152)` under `((TRUE-LISTP B))`,
    both inside its basic-ts — the datum the admissibility gate needs.
    Corpus cross-check: for all **1554** events whose definitional
    stored rule has NIL hyps, the per-entry leaves reproduce the
    existing top-level `:LEAVES` byte-for-byte.
  - **Ask 2 — the recognizer-site channel** (`:ARG-LEAVES`, both
    `rewrite-recognizer` records). Non-NIL on **12** records
    corpus-wide, including all three trio books (06-measure,
    07-mutual-recursion, 11-custom-measure). The trio's argument
    `(IF (INTEGERP N) (IF (< N '0) '0 N) '0)` now carries leaves
    `('0 1)`, `(N 7)`, `('0 1)` — union 7 = the emitted `:TYPESET`,
    disjoint from CONSP's true-ts 3072.
  - **Ask 3 — `:CR-RUNE`** on `solidify/rewriting-equiv`: 361 records,
    all populated; the PERM-TLFIX step reads
    `(:EQUIVALENCE PERM-IS-AN-EQUIVALENCE)` exactly as the G1 brief §2
    predicted (the other 360 are EQUAL's fake anonymous rune).
  - **Ask 4 — ground-zero admission clauses: SKIPPED, PREMISE
    CONTRADICTED.** `emit-ground-zero-defuns` (ld.lisp) has emitted
    `:MEASURE`/`:WFREL`/`:MEASURED` + `:TERMINATION-CLAUSES`
    (recomputed fail-closed by `gz-termination-clauses`) since
    006bebce9f. Corpus: 103 distinct ground-zero defun events, **zero**
    recursive ones lacking clauses; O< and O-P carry full clause sets.
    `total:O<` / `total:O-P` and `dis_o_lt_total` are therefore a
    CONSUMPTION item, not an emission gap — the escape hatch was taken
    and no fork edit was made.
  - **J-RT2a:** the `infra/tp-leaves` collector family MOVED
    `defuns.lisp` → `type-set-b.lisp`, bodies unchanged. rewrite.lisp
    loads before defuns.lisp and ACL2 loads each source before
    compiling it, so the recognizer channel's call would have been a
    forward reference riding suppressed style warnings; a second copy
    in rewrite.lisp is the near-clone the working discipline forbids.
    type-set-b.lisp is also the collector's natural home — it mirrors
    `type-set-rec`'s `'if` case, which lives there.
  - **J-RT2b:** `:ALL-TPS` entries carry the rule's own `:term`. A
    stored rule's hyps/corollary speak the RULE's variables
    (`(BINARY-APPEND A B)`) not the fn's formals (`(X Y)`), so the body
    is instantiated formals→term-args and all four fields share one
    variable space. Fail-closed `er hard` if a `:term` is ever not a
    call of matching arity.
  - **J-RT2c:** `:ARG-LEAVES` is SCOPED to IF-valued arguments and
    computed only inside the structured-log guard. For any other
    argument the collector would merely repeat `:TYPESET` while
    dragging the ambient type-alist into every recognizer record — the
    item-I recapture incident's payload lesson.
  - **J-RT2d:** the parser REFUSES the 4-field R2 `:ALL-TPS` shape
    rather than half-reading it (`parse fully or hard-fail`); likewise
    a present-but-non-rune `:CR-RUNE`. Honest caveat carried in both
    the emitter tag and the Lean docstring: a stored rule proved by a
    real theorem need not have its leaves inside its basic-ts, so a
    consumer must fail closed rather than assume.
  - **J-RT2e:** the two new field readers live in `ProofLogTypes.lean`
    (`parseCrRuneField` / `parseArgLeavesField`), matching the existing
    `parseSymbolListField` idiom, which keeps `ProofLog.lean` at its
    1240-line ratchet cap instead of forcing a baseline loosening.
    `TpLeaf` + its reader moved above `RewriteStep` in the same file so
    `argLeaves : List TpLeaf` can be declared.

- **P3a COLLECTED (2026-08-15):** item 1 DONE (TotFacts carries
  value+convergence through the opaque-test arm; total:BSORT retired
  ×3 — the 4th occurrence is :INCLUDE-BOOK-sourced, correctly
  unmoved); item 4 ADVANCED (the .nfix decrease walk + DecreaseKit
  factOf? + the proved arithmetic family; CD2-BOUND's new frontier =
  the ZP compound-recognizer arm, cited-rune threading); items 3/5/6
  STOPPED with one shared root cause diagnosed verbatim — **the
  cross-book D1 transfer (WP5)**: the registry is per-book, cross-book
  rule: deps re-replay in the consumer telescope and frontier
  (measured: retiring rule:CONVERT-PERM swaps 1-for-1 to
  rule:TRUE-LISTP-RM; exploratory chain REVERTED per the movement
  rule). Item 2 dissolved (the offer already flows; the payoff is
  dischargeLinearHyp — new machinery). Three latent defects recorded
  for the transfer lane: no equivrefl: arm in depReplayedProofAt;
  containsFVar on un-instantiated exprs; first-name-match dependency
  selection (the two TRUE-LISTP-RMs).

## THE REMAINING BILL (post-P3a inventory — all driver-side)

- **P3b (consumption):** ordinal totality (total:O< ×12, O-P ×6,
  dis_o_lt_total — ground-zero clauses EXIST, RT2-verified);
  hypothetical-TP mode over per-entry :LEAVES (tp:QSORT ×2); the
  trio's recognizer arm over :ARG-LEAVES; CLASSIFY-POS consumer over
  :LHS-TS/:RHS-TS; CD2-BOUND's ZP arm.
- **P3c (the transfer lane):** cross-book D1 transfer (WP5) — unlocks
  the rule: chains (×10-class), total:QSORT/BSORT at sorts-equivalent
  (:INCLUDE-BOOK sources), dis_convert_perm; + the three latent
  defects; + dischargeLinearHyp (linear: ×4).

- **P3b (consumption) — 2026-08-15.** Two items DONE, two ADVANCED to a
  named deeper frontier, one NOT ATTEMPTED.
  - **Item 1 — ORDINAL TOTALITY: DONE.** `total:O<` (×12) and
    `total:O-P` (×6) RETIRED corpus-wide; `dis_o_lt_total` DELETED
    (deletion+rewiring precedent, `dis_pce_total`), sorries 2 → 1
    (`dis_convert_perm`, P3c's). Three pieces, all consuming the emitted
    ground-zero `:TERMINATION-CLAUSES` RT2 verified exist:
    (a) the ORDINAL S4 REGISTRY ROW in `chainLt` — `(O-RST u)` IS
    `(CDR u)` and, under the branch these obligations are emitted for,
    `(O-FIRST-EXPT u)` IS `(CAR (CAR u))`, both proved as CALL-LEVEL sim
    lemmas against the world's OWN byte-checked bodies (new
    `ACL2Lean/Replay/OrdinalSim.lean`); (b) the `O-FINP` RECOGNIZER
    DUALITY — a REFUTED `(O-FINP b)` IS the `(consp b)` evidence both
    decreases need, read off ACL2's emitted `(IF (CONSP X) 'NIL 'T)`;
    (c) the 2-ARY OPAQUE MEASURED-ARGUMENT arm (`O<`'s own self-calls
    are ground-zero DEFUN applications at both positions).
  - **Item 5 — CLASSIFY-POS: DONE.** FAIL → REPLAYED ✓ UNCONDITIONAL.
    The `:LHS-TS`/`:RHS-TS` DISJOINTNESS cell (`tseTsDisjointCell`) plus,
    behind it, the chain-end IF-COLLAPSE at NODE level: the literal's
    emitted `:IF-TEST-FALSE` marker is now threaded into `ReplayCtx` as
    an ANCHOR and the falsity itself PROVED by the same ts algebra.
  - **Items 3 + 4 — the trio's `:ARG-LEAVES` arm and CD2-BOUND's ZP arm:
    BUILT, rows NOT flipped.** Both mechanisms fire and are verified by
    the frontier MOVING: `(CONSP (IF …))`, `(NATP (IF …))`,
    `(INTEGERP N)`, `(INTEGERP (BINARY-+ '-1 N))` and `(ZP N) ⇒ 'NIL`
    all replay now. The rows stop at a NEWLY EXPOSED frontier that is an
    EMISSION GAP, not a consumption item — see J-P3b-g.
  - **Item 2 — HYPOTHETICAL-TP MODE: NOT ATTEMPTED** (budget). `tp:QSORT`
    ×3 unmoved.
  - **J-P3b-a:** the ordinal decreases were resolved as an S4 REGISTRY
    ROW (the EVENS/ODDS precedent), NOT a new measure-table row: the
    MEASURE is already the `.count` row: what is new is the DECREASE
    ARGUMENT. World-parametric (L3); every world shape byte-checked at
    the use site, so a differing ground zero keeps the honest frontier.
  - **J-P3b-b (EQUAL-ALIAS NORMALIZATION):** ACL2 emits a defun's
    `:BODY` NORMALIZED but recomputes the ground-zero
    `:TERMINATION-CLAUSES` from the UNNORMALIZED body
    (`gz-termination-clauses` reads `get-unnormalized-bodies`), so `O<`'s
    ruler is `(NOT (= …))` and `O-P`'s is `(EQL '0 …)` where the branch
    facts say `EQUAL`. Resolved by reading the WORLD's OWN definitional
    aliases of `EQUAL` and normalizing ONLY the coverage comparison
    (`wanted`/`matching` stay verbatim). Not a hard-coded name list; the
    alias source is `worldVal.defs.entries ++ cfg.gzDefs`, because a
    builtin-named snapshot (`EQL`) is excluded from the world by the
    no-shadow rule and `gzDefs` is the only place its emitted body lives.
  - **J-P3b-c:** the DP-probe totality sweep (`Runner.lean`) built its
    `ReplayConfig` WITHOUT `gzDefs`, so the SAME prover answered
    differently in the two paths (`O-P` proved in the harness, failed in
    the probe). Fixed at the source rather than worked around.
  - **J-P3b-d:** `tsFactOf` MOVED from `Driver/TsConsumer` to a new leaf
    module `Driver/TsFacts`, so the admission-side `tsFromFacts` and the
    new clause-side `inTsFromCtx` read ONE table of masks and proved
    lemmas — the near-clone the working discipline forbids. `TsFacts`
    also carries the generating side (`tsCtxProbes`), the `.isNil`
    direction (`tsTestNilOf`), the recognizer-verdict registries and the
    arithmetic-primitive cell; every probe result is interpreted BACK
    through the same table, so the directions cannot drift.
  - **J-P3b-e:** the literal's `:IF-TEST-TRUE/FALSE` markers are
    threaded into `ReplayCtx` so a NODE recipe's chain-end
    reconciliation can anchor an unrecorded IF collapse on the same
    records the literal-level bridge uses. The markers stay an ANCHOR
    ONLY — `valIsNil` still PROVES the falsity (from the in-scope facts
    or the ts algebra); a marker alone never licenses a collapse.
  - **J-P3b-f (RATCHET):** the additions pushed `ProofLog`, `NodeCore/Ctx`
    and `NodeCore/Node` over their caps. Resolved by MOVES, never
    baseline loosening: the integer-field reader to `ProofLogTypes` (the
    J-RT2e precedent), and `compoundRecogTsCell`, `tseTsDisjointCell`
    and the ZP compound-recognizer recipe to `NodeCore/TypeSetWalk`.
    Baselines TIGHTENED: `Node.lean` 1668 → 1650, `Sorting.lean`
    4278 → 4265.
  - **J-P3b-g (items 3/4 STOP — verbatim frontiers).** After the
    `:ARG-LEAVES` arm the trio's terminations stop at
    `definition: children chain reached (IF (< (BINARY-+ '-1 N) '0) '0
    (BINARY-+ '-1 N)), node rhs is (BINARY-+ '-1 N)` (CD2:
    `(IF (< N '0) '0 N)` vs `N`) — the `NFIX` body's inner
    must-be-arm collapse, for which the corpus logs carry NO if-test
    record at all (no `IF-FINISH/IF-TEST` marker for that test in
    `06-measure` / `07-mutual-recursion` / `11-custom-measure`). That is
    an EMISSION GAP (a fork item), not P3b consumption, so the item was
    stopped rather than closed by Lean-side inference. CD2-BOUND
    likewise advanced past its ZP arm to
    `replayClauseSpine: ran out of items with no closer at Subgoal *1/2`
    — a structural spine frontier, diagnosed but not pursued.
