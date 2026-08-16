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

- **P3c COMPLETE in worktree (2026-08-15, pending collection):** the
  EMERGENCY CHECK passed — worlds NEST (zero conflicting defun bodies
  corpus-wide, verified pre-edit; equisort's encapsulate witnesses
  correctly refused by the gate). The transfer = the dep's recorded
  tree replayed ONCE at the consumer's world, addDecl'd, registered
  (J-P3c-a: the evalOpt_world_mono transport route REJECTED —
  callBuiltin's 55-arm match cannot produce equation lemmas at the
  fixed whnf budget; re-replay is deterministic and sanctioned);
  world-inclusion as a meta-level fail-closed gate (J-P3c-b: buys
  principle, not soundness — the proof is a genuine replay);
  cross-book misses are frontiers, same-book stay defects (J-P3c-c);
  demand-only rune collector (J-P3c-d); diagnostics never in
  res.lines (J-P3c-e). Three latent defects FIXED (equivrefl: arm;
  usesFVar instantiates first; recompute-based candidate selection —
  the two TRUE-LISTP-RMs verified genuinely distinct). Sweep to
  quiescence (strict progress, cap 4). dischargeLinearHyp landed.
  dis_convert_perm RETIRED → combined with P3b, SORRIES = 0.
  Movement: rule:CONVERT-PERM ×7→0, rule:TRUE-LISTP-RM ×5→0,
  linear: ×5→1, the :INCLUDE-BOOK totals retired, +6 more rule:
  chains; ONE flagged addition (QSORT-IS-ISORT inherits
  rule:(+ (+ x y) z) from its retired dep's own honest conds — net
  −4/+1, reported not repinned, the arithmetic-rune family owns it).
  COST: sorts-equivalent ~50→65 min elaboration (weigh at gate).
  Known repin-time fixes: pins need crossDevs; two capstone pin
  telescopes drop retired hypotheses (documented case).

## POST-P3c REMAINING (pre-P4a-collection estimate)

Rows conditional after merging P3b+P3c: the ARITHMETIC-RUNE FAMILY
(rule:(+ y x), rule:(+ y (+ x z)), rule:(+ (+ x y) z),
rule:(+ x (if a b c)), rule:(equal (if a b c) x)) — ground-zero
theorem class, likely the gz-discharger (D5) route; rule:ORDEREDP-APPEND
+ rule:TRUE-LISTP-BNEXT + linear:@sorts-equivalent (may cascade in the
COMBINED quiescence sweep — P3c ran without P3b's retirements);
tp:QSORT + the trio + CD2-BOUND (P4a, in flight).

- **P4a (RT3 + CD2-BOUND) — 2026-08-15.** The trio's three termination
  rows RETIRED (FAIL → REPLAYED ✓) with **ZERO fork changes**; CD2-BOUND
  advanced through two frontiers to a third, diagnosed one. Item 2
  (hypothetical-TP) NOT attempted — scouted and stopped on a ratified
  design boundary (below). Golden: 3 status flips + 1 message churn,
  header UNCHANGED (115/116, 99+16); verifying sweep green (29 books,
  sections tile, `check-golden-current` PASS); 14 statics PASS; sorries
  still 1 (`dis_convert_perm`, the other lane's).
  - **J-P4a-a (RT3 PREMISE CONTRADICTED — no fork round-trip was made).**
    P3b's J-P3b-g recorded "the corpus logs carry NO if-test record at
    all" for the `NFIX` must-be-arm collapse. That is FALSE: all three
    books emit
    `(:IF-TEST-FALSE :ORIGIN IF-FINISH/IF-TEST :TEST (< … '0)
     :JUSTIFICATION (:RUNES ((:FAKE-RUNE-FOR-TYPE-SET NIL)
     (:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)) :PARENTS NIL))`.
    `11-custom-measure`'s copy is LINE-WRAPPED by ACL2's `fms` printer,
    which is what a single-line grep misses. The gap was pure
    CONSUMPTION, so the fork stayed at `e8d78e513d` and RT3 shipped as a
    driver change. (Method note: scout the ARTIFACT with a
    whitespace-normalized reader, never a raw line grep.)
  - **J-P4a-b:** `ifMarkerCitedCr` (Driver/TsFacts) reads the MARKER'S OWN
    `:JUSTIFICATION` ttree for its `(:COMPOUND-RECOGNIZER …)` runes — the
    BUG-023 direction the recognizer step site already takes. Three
    justification shapes are attested across all 5040 corpus IF-test
    markers (`NIL`, `:REWRITTEN-TO-CONSTANT`, the `(:RUNES … :PARENTS …)`
    ttree); a fourth HARD-FAILS rather than being swallowed.
    `bridgeIfCollapseNorm`'s `valIsNil` had been passing `[]`, so the
    compound-recognizer probe was never licensed and the collapse failed
    closed even though ACL2 had recorded its reason.
  - **J-P4a-c (the SHARP CONSTANT CELL).** `(BINARY-+ '-1 N)` under
    `¬(ZP N)` needed mask 7, which `tsBinaryOf`'s integer cell (23+23⊆23)
    loses. Added `tsPlusConstOf` + `inTs_plus_neg_one` (`InTs 6 a →
    InTs 7 (plus '-1 a)`, proved), keyed on the CONSTANT as well as the
    mask — ACL2's partition carries `*ts-one*` for exactly this. ONE cell,
    the `tsBinaryOf` precedent; the emission itself shows there is no
    `-2` cell to add (`CD2` emits the coarse `:TYPESET 23` for
    `(BINARY-+ '-2 N)` where `COUNT-DOWN` emits 7 for `'-1`).
  - **J-P4a-d:** `citedCr` threaded through `inTsFromArgLeaves` (it was
    dropped at the recursion and at the leaf's `inTsFromCtx`), which is
    what `termination:CD2` needed after its `(CONSP (IF …))` step.
  - **J-P4a-e (the μ-ROUTE DISCRIMINATOR WAS ROW-BLIND — a latent defect
    EXPOSED by the flip).** `replayInduction` chose between the registry μ
    and the recorded replay's `interpCount` μ by applying
    `destructorChainOk` to EVERY measure row. The moment `termination:CD2`
    became REPLAYED, `CD2-BOUND` took the `recReplayed?` branch, the
    row-blind test rejected `(BINARY-+ '-2 N)`, and the arithmetic
    decrease `dischargeDecrease` now produces stopped matching μ.
    Fixed at the source in the R3 shape: `decreaseArgInReach`
    (Driver/Decrease) dispatches on `MeasureShape` — chains for
    count/len/sum, `chainLtNfix`'s arm for `nfix`, nothing for `userFn`.
    Behavior change is confined to the `nfix` row (the other rows'
    conjunctions were already decided by `registryCovered`).
  - **J-P4a-f (the spine terminus' FOURTH closer).** `groundConstClose`
    (NodeCore/Compose) + `conv_if_either` (Lemmas/Derived): a clause whose
    recorded `branch-substitution` + `scons-term/exec` folds end in a `'T`
    literal IS the true clause. The `'T` closes (`conv_if_true`) and every
    PRECEDING literal is peeled by `conv_if_either` — both branches of
    `(IF l 'T rest)` converge to `'t`, so the peel needs only that `l`
    CONVERGES. Fail-closed on children / a non-empty residual / no `'T`,
    and the peeled reconstruction is checked to BE the clause's own
    disjunction. Closed `CD2-BOUND`'s `Subgoal *1/2` AND `*1/1`.
  - **J-P4a-g (CD2-BOUND STOPS — third frontier, diagnosed, OUT OF
    CLASS).** Verbatim:
    `compound-recognizer: no in-scope falsity fact for (INTEGERP N)
    (frontier)`. Site: `Subgoal 1` (`((NOT (< N '0)) (NOT (< '0 (CD2 N))))`),
    whose `(ZP N) ⇒ 'T` step is NOT the registered "refuted INTEGERP"
    recipe but a TYPE-SET verdict (`:TYPESET 112`, `:TRUETS -7`). The ts
    cell would need a `tsRecogTrue` entry for `ZP`, and it would then be
    REFUSED by `recogVerdictFromTs`'s `acl2Ok` guard
    (`tsSubsumedM stepTs m`): from `(< N '0)` true our model derives mask
    48 while ACL2 emits 112 = 48 ∪ *ts-complex-rational*, because ACL2's
    `<` orders complex rationals and our model has NO complex values
    (BUG-009's domain restriction). We derive something STRICTLY STRONGER
    than ACL2, and the guard — correctly written as "ACL2's verdict must
    be INSIDE ours" — rejects it. Reconciling a model-domain restriction
    with an emitted mask is a fidelity-sensitive design question, not a
    consumption arm: STOPPED and recorded rather than loosened.
  - **J-P4a-h (item 2, hypothetical-TP: NOT ATTEMPTED, scouted).**
    `QSORT`'s OWN `:ALL-TPS` entry is UNCONDITIONAL (hyps NIL, basic-ts
    1152) — the conditional rule that matters is `TRUE-LISTP-APPEND` on
    `BINARY-APPEND` (hyps `((TRUE-LISTP B))`, leaves `(1024, 1152)` under
    it). Reaching it needs a new data path end to end
    (`Development.typePrescriptionAllTps` → a `ReplayConfig.allTps` field →
    a widened `TpKit.cors`), and even then the 2026-08-13 fork-emission
    audit's SECOND blocker stands: discharging `(TRUE-LISTP B)` at
    `B = (CONS (CAR X) (QSORT (FILTER 'GTE …)))` routes into the self-call
    arm, which frontiers at `totLiftable` because `QSORT`'s measured
    argument calls the world fn `FILTER`. Two blockers, one of them new
    machinery; `tp:QSORT` ×3 unmoved and the design map is recorded here.
  - **J-P4a-i (RATCHET):** `CoreSpine.lean` was held at its 1539 baseline
    by moving the closer's applicability GATE into `groundConstClose`
    (which is where the fail-closed contract belongs), never by loosening
    the baseline — the J-P3b-f/J-RT2e precedent.

- **P4b (the four-item close) — 2026-08-15.** Items 1 and 4 DONE; item 2
  DIAGNOSED, a bounded fix TRIED, MEASURED as insufficient and REVERTED;
  item 3 STOPPED with a verbatim frontier and a file:line map. FAIL rows
  1 → 0. Row-level conditional rows 10 → 4.
  - **Item 1 — THE ARITHMETIC-RUNE FAMILY: DONE.** All five runes
    (`(+ y x)`, `(+ y (+ x z))`, `(+ (+ x y) z)`, `(+ x (if a b c))`,
    `(equal (if a b c) x)`) RETIRED corpus-wide. The five PROVEN
    statements already existed in `Imported/GzPrelude.lean` but were
    APPLIED BY HAND at ten waypoint call sites; they MOVED DOWN to
    `Replay/GzRules.lean` (same proofs, re-expressed over the Replay
    layer's own `conv_builtin2`/`fuel_eq_of_conv` primitives — the
    `gz_rule_fold_consts_in_plus` idiom) and were registered in
    `d5GzRules`, so `dischargeGzRuleHyp` now discharges each at its CITED
    rune, recompute-checked against the EMITTED `(:RULES …)` entry by
    `mkRuleHypType` as every other registry entry is.
    `ORDEREDP-QSORT` and `QSORT-IS-ISORT` each drop the five. The
    further CASCADE PREDICTED at the outset did NOT happen, and is
    recorded as a wrong prediction: `ORDEREDP-APPEND` is unconditional
    now, yet `rule:ORDEREDP-APPEND` still survives on both rows.
    Diagnosis (not pursued): that rule's stored form does not recompute
    from its defthm Goal by `dischargeRuleHyp`'s standard decode — which
    is exactly why the waypoint layer carries
    `dis_rule_orderedp_append` as its registered DECODE exception. A
    decode-class item, not a D5 one. `Imported/GzPrelude.lean`
    DELETED; the waypoint telescopes in `Waypoints/Qsort.lean` dropped 20
    hand-applied arguments (dated diagnosis comments kept, the
    established deletion+rewiring flow).
  - **J-P4b-a (D5 ADMISSION CRITERION — class (ii), not a new class).**
    The five are arithmetic-3 theorems the qsort/sorts-equivalent logs
    carry as `:SOURCE :INCLUDE-BOOK` with a `(:RULES …)` entry and NO
    tree — exactly `FOLD-CONSTS-IN-+`'s situation (`GzRules.lean`'s
    criterion (ii), ratified at close-out audit O-5), and exactly the
    same retirement condition: the day arithmetic-3 is captured, the
    entries become dependency-replayed discharges. Nothing new is
    trusted: these five statements were ALREADY the ratified D5 set in
    the waypoint provenance gate's `d5Allowed`. What changed is WHO
    applies them — the driver at the cited rune instead of a human at a
    telescope — which is strictly tighter (BUG-023 direction).
  - **J-P4b-b (the provenance gate keeps an EMPTY slot).** With
    `GzPrelude` gone, `Catalog.lean`'s `d5Allowed` list is `[]`. Kept as
    a named, empty slot rather than deleted, so a future gz constant has
    an obvious reviewable place instead of being smuggled into
    `decodeAllowed`. Honest-mistake standard; not hardened.
  - **J-P4b-c (the WP3 pin is SCOPED, and says why).** The five runes are
    emitted only by the two ~150k-line sorting logs, so pinning them in
    `Tests/DriverTests.lean` would mean parsing one there. They are
    instead LIVE-gated by the golden — seven rows are unconditional only
    because `dischargeGzRuleHyp` fires on them — which is a STRONGER
    check than the pin. The pin skips exactly those five, by name, with
    the rows listed at the site.
  - **Item 4 — CD2-BOUND: DONE, FAIL → REPLAYED ✓ UNCONDITIONAL.** Three
    pieces. (a) the `ZP` `recognizer/true` cell — `tsRecogTrue` gains
    `("ZP", -7, logic_zp_t_of_inTs)`, the lemma PROVED (`-7 = ~6` is
    "not a positive integer", which is exactly `Logic.zp`'s truth
    condition). (b) the BUG-009 discount, below. (c) the μ-generic TP
    assembly, below — the row then kept `tp:CD2` and needed it.
  - **J-P4b-d (BUG-009 AT ONE MORE SITE — the guard, decided).**
    `recogVerdictFromTs`'s cross-check ("ACL2's emitted `:TYPESET` must
    be INSIDE the mask we derived") refused a STRICTLY STRONGER
    derivation: from `(< N '0)` true the model derives 48, ACL2 emits
    112 = 48 ∪ {bit 6}, and bit 6 is `*ts-complex-rational*`, which
    `tsIndex` NEVER returns. The delta was verified to be EXACTLY that
    bit and nothing else. `tsAcl2MaskOk` (Driver/TsFacts) therefore
    discounts index 6 and only index 6; every other bit still fails
    closed. Not a weakened verdict — the verdict stays ACL2's and the
    proof still runs on OUR mask and OUR `InTs` fact — but the same
    pinned domain restriction `mkVacuousTruthyBranch` and the induction
    walk already apply. Appended as the THIRD SITE to BUG-009 in
    `docs/BUGS.md`, with the deletion condition (a fix to BUG-009 makes
    index 6 inhabited and `tsAcl2MaskOk` must go).
  - **J-P4b-e (the μ-GENERIC TP ASSEMBLY — the widening `proveTp`'s own
    comment deferred).** `proveTp` accepted ONLY the `count`
    measure-table row because the `tp_*_rec` wrappers were
    `consCount`-hardcoded; `CD2`'s `nfix` row frontiered with
    "no consCount-typed TP assembly". Resolved exactly as that comment
    said to (`μ-generic tp_*_rec_mu twins, not a new classifier`): the
    six wrappers (`tp_1_rec`, `tp_2_rec`, `tp_2_rec_snd`, `tp_3_rec`,
    `tp_3_rec_snd`, `tp_2_rec_av`) took a `(μ : SExpr → Nat)` parameter,
    and `measuredOf` now yields the row's own registered μ head via
    `MeasureShape.muHeads` — the SAME switch `proveTotality` already
    makes, so the two provers still cannot disagree about a measure
    shape. Behaviour-preserving at `μ := consCount` (every existing row
    is the `count` row). Rows with no single-variable registered μ
    (`userFn`, `sumCount`) keep their own honest frontiers.
  - **J-P4b-f (DE-DUPLICATION taken while in these files).**
    `consCount_strong_induction` (Lemmas/Totality) and
    `measure_strong_induction_val` (Lemmas/Judgments) were the same
    theorem stated twice. Now ONE copy, upstream in Totality, with the
    `consCount` one an instance of it — the working discipline's
    "extract what exists in 2–3 concrete copies", behaviour-preserving.
  - **J-P4b-g (A DIAGNOSTIC SINK, env-gated).** A kept `tp:` condition
    DISCARDED its frontier message (`Harness.lean`'s catch), so the
    reason a row stays conditional was invisible to every binary. The
    2026-08-13 fork-emission audit recorded that it "could not execute"
    its check for this reason, this sprint's scouting hit the same wall,
    and so did this executor. `ACL2LEAN_TP_DIAG=1` now prints
    `[tp-diag] <fn>: <frontier>` to stderr. Never a result line, never
    read by a gate; off by default.
  - **Item 2 — `linear:HOW-MANY-BAD-PAIRS-BNEXT` at sorts-equivalent:
    DIAGNOSED, FIX TRIED AND REVERTED, HONEST RESIDUE.** The discharge
    machinery is NOT at fault. `crossBookRegistry`'s demand filter
    (`Runner.lean`, `if !demand.contains cp.name then continue`) is: the
    seed is `bookCitedNames`, whose own docstring says it is NOT a
    superset of what a replay consumes, and neither
    `HOW-MANY-BAD-PAIRS-BNEXT` nor `TRUE-LISTP-BNEXT` is cited by any
    theorem tree in the corpus (the former is cited only inside BSORT's
    ADMISSION waterfall; the latter by nothing at all — both reach a
    telescope as OFFERS). With no registry entry, `depReplayedProofAt`
    falls to the re-replay route, which walls, and the condition is kept
    — where inside `bsort` the same discharge is unconditional because
    the SAME-BOOK registry has no demand filter at all. TWO widenings
    were implemented and MEASURED at the real book: (i) seeding the dep
    books' recorded-ADMISSION citations — zero movement; (ii) seeding the
    consumer's OFFERED `:LINEAR` rune names — reached FURTHER (a new
    `msort/ACL2-COUNT-EVENS-STRONG` cross entry transferred) but STILL
    did not register `HOW-MANY-BAD-PAIRS-BNEXT`, and the new entry
    carries `cond[linear:ACL2-COUNT-CAR-CDR-LINEAR]`, i.e. it risks
    ADDING conditions to the capstone rows. Both REVERTED under the
    movement rule rather than left in as cost without payoff. The
    unanswered question, for whoever takes this next: the name IS in
    sorts-equivalent's `(:GROUND-ZERO-LINEAR-RULES)` snapshot and IS a
    bsort theorem, so it was demanded and still produced no entry and no
    failure line — the pre-pass is dropping it somewhere between
    `developmentTheoremsWithRules` and the registration, and a
    `continue`-site diagnostic (the J-P4b-g treatment, applied to
    `Runner.lean`'s two silent `continue`s) is the cheap next step.
  - **Item 3 — `tp:QSORT` ×2: STOPPED, verbatim frontier + map.** With
    the diagnostic sink the frontier is now READABLE for the first time:
    `proveTp: BINARY-APPEND's corollary class
    ACL2.Replay.Driver.TpCorClass.conspOrArg neither matches nor implies
    the ACL2.Replay.Driver.TpCorClass.trueListp class QSORT's
    prescription needs (frontier)`. It is NOT the `totLiftable`/FILTER
    blocker J-P4a-h named — that one is real but sits two steps LATER.
    The corrected map, verified against the emitted artifacts:
    (1) the `allTps` data path (`Development.typePrescriptionAllTps` → a
    `ReplayConfig.allTps` field → the callee arm) — mechanical, 4 sites,
    and the emitted data IS there (RT2 landed `term` + per-rule
    `leaves`; the "arrives without per-rule leaves" notes in
    `Tests/SortingPins.lean` and `Waypoints/Catalog.lean` are STALE);
    (2) a HYPOTHESIS-CARRYING mode in `proveTp` — `TRUE-LISTP-APPEND`'s
    conclusion class MATCHES `trueListp`, so no new class implication is
    needed, but the rule's hypothesis must be seeded into the walk's
    facts (its `(NOT (CONSP A))` leaf is closed BY the hypothesis) and
    the IH's predicate becomes hypothesis-carrying (a `convToP_mp`-shaped
    lemma); (3a) pinning the OPAQUE MEASURED ACTUAL in `tpWalkCall` —
    the `Totality.lean` opaque-measured-arm device (`totWalk` +
    `exists_conv_elim` + a `DecreaseKit` `valOf`/`convOf` override)
    lifted to the measured position, which is where FILTER's proven
    totality actually pays; (3b) the RECORDED-route decrease —
    `dischargeDecreaseRecorded` + `RecTermInfo` plumbed into `proveTp` as
    `buildTotalEnv` already does for `proveTotality`, because
    `chainLt` cannot walk `(FILTER 'GTE (CDR X) (CAR X))` and QSORT's
    admission is already replayed and green; (3c) the μ-generic TP
    wrappers — **DELIVERED here** (J-P4b-e), and load-bearing for
    CD2-BOUND right now. The `allTps` plumbing was written and then
    REVERTED: unwired, it is exactly the "build the infrastructure now,
    wire it into the real proof later" anti-pattern the working
    discipline bans.
  - **THE REMAINING CONDITIONAL ROWS (5), each named:**
    `rule:ORDEREDP-APPEND` on `ORDEREDP-QSORT` and `QSORT-IS-ISORT`
    (the decode-class item above); `tp:QSORT` on
    `TRUE-LISTP-QSORT` and `QSORT-IS-ISORT` (item 3 above);
    `rule:TRUE-LISTP-BNEXT` on `BSORT-IS-ISORT` (item 2's class — the
    rewrite half; its bounded seed would demand ~52 dep theorems at
    sorts-equivalent, a cost that must be weighed, unlike the 3-name
    linear half); `linear:ACL2-COUNT-CAR-CDR-LINEAR` on
    `ACL2-COUNT-EVENS-STRONG` — NOT in the four items and a DIFFERENT
    class from item 2: it is a GROUND-ZERO `:LINEAR` rule (hyps
    `((CONSP X))`, concl `(EQUAL (ACL2-COUNT X) (BINARY-+ '1 (BINARY-+
    (ACL2-COUNT (CAR X)) (ACL2-COUNT (CDR X)))))`), so no dependency
    theorem exists anywhere to replay. Closing it needs a D5-class
    `dischargeGzLinearHyp` whose prelude constant is proved over the
    world's OWN byte-checked `ACL2-COUNT` body (the `OrdinalSim` S4
    registry-row precedent), which is a new discharger family.

  - **P4b END STATE (measured; `just ci` run to completion, zero recipe
    failures).** Golden header
    `REPLAYED 116/116 (111 unconditional + 5 conditional)`; FAIL rows
    **0** (was 1); row-level conditional rows **5** (was 10);
    `sorry`/`sorryAx` **0**. Golden SPLICED from FRESH sections (all 29
    books re-run under the new driver), then the VERIFYING sweep passed
    byte-exactly and `check-golden-current` confirms the golden IS the
    live assembly. Pins converged in the same pass
    (`Tests/SortingPins.lean`: two telescopes and two pinned status
    lines drop the five arithmetic runes, dated diagnoses in place; the
    stale "arrives without per-rule leaves" note on `tp:QSORT`
    corrected — RT2 emitted them). Ratchets TIGHTENED, never loosened:
    `Imported/Sorting.lean` 4265 → 4246, `Lemmas/Judgments.lean`
    1830 → 1820.

- **P5a (the discharge-side closers) — 2026-08-16.** Items 1 and 3 DONE —
  three of P4b's five remaining conditional rows RETIRED. Item 2
  DIAGNOSED to its exact site, a fix BUILT and MEASURED at the real book,
  then REVERTED under the movement rule (two conditions out, three in).
  Golden: 3 row changes, all condition retirements, ZERO status flips and
  ZERO message churn; header 116/116 (111+5 → **113 unconditional + 3
  conditional**); `sorry`/`sorryAx` still 0.
  - **Item 1 — `rule:ORDEREDP-APPEND` ×2: RETIRED (the DECODE class).**
    P4b's diagnosis was right and the fix is one arm: ACL2's
    `create-rewrite-rule` stores a defthm whose conclusion is
    `(IFF lhs rhs)` as an `:EQUIV EQUAL` rewrite rule when both sides are
    boolean, and `dischargeRuleHyp`'s decode had no route for that shape.
    `routeIff` recomputes exactly that normalization — a REGISTERED route
    beside `routeEqual`/`routeBool`/`routeRel`/`routeNotBool`, keyed on
    the shape, with NOTHING about ORDEREDP-APPEND in it.
    `ORDEREDP-QSORT` and `QSORT-IS-ISORT` each drop the condition
    (QSORT-IS-ISORT keeps `tp:QSORT`, the other lane's). The waypoint
    layer's registered DECODE EXCEPTION `dis_rule_orderedp_append` became
    redundant and was RETIRED by the deletion+rewiring flow: the theorem
    deleted from `Imported/Sorting.lean` (−81 lines), the hand-applied
    argument dropped from `Waypoints/Qsort.lean` with a dated diagnosis,
    and BOTH `Waypoints/Catalog.lean` registrations (`decodeAllowed` and
    the hreplayed-usage scan's seed) emptied to named slots.
  - **J-P5a-a (the decode's soundness content is TWO-VALUEDNESS, and it
    is DEMANDED).** `(IFF a b)` truthy gives `a = b` only when both sides
    are boolean — which is the very fact ACL2 used when it chose to store
    the rule under EQUAL. The arm therefore requires a two-valuedness
    SOURCE for each side (`boolDisj?`: the emitted `:TYPE-PRESCRIPTION`
    corollaries, the trusted core's own boolean lifts, structurally
    through IF-nests) and FRONTIERS when either is missing — no source,
    no decode. The one new lemma (`eq_of_iff_ne_nil_two_valued`) takes
    both disjunctions as premises, so the statement cannot be proved
    without them. This is strictly tighter than the deleted hand decode,
    which established the same two-valuedness by hand-written lemmas
    about ORDEREDP/ALL-REL specifically (the BUG-023 direction).
  - **Item 3 — `linear:ACL2-COUNT-CAR-CDR-LINEAR`: RETIRED (the gz-linear
    family, a new discharger).** A ground-zero `:LINEAR` rule has no
    defthm anywhere in the corpus, so `dischargeLinearHyp`'s
    recompute-from-the-dependency route can never reach it. Reading the
    emitted entry answered the design question outright: its conclusion
    `(EQUAL (ACL2-COUNT X) (BINARY-+ '1 (BINARY-+ (ACL2-COUNT (CAR X))
    (ACL2-COUNT (CDR X)))))` under `((CONSP X))` IS, verbatim, the
    CONSP branch of `ACL2-COUNT`'s own `:SOURCE :GROUND-ZERO` `:DEFUN`
    body — the rule says nothing beyond one definitional unfold.
  - **J-P5a-b (a CLASS, not a per-rule prelude constant).** The D5
    rewrite entries are (name ↦ constant) because each states a different
    theorem. Here one lemma covers the whole class:
    `gz_linear_defn_branch` (`Replay/GzRules.lean`) is parametric in the
    fn, its formal, its body, the rule's variable and the branch, and
    `dischargeGzLinearHyp` RECOMPUTES the instance — it computes
    `substTerm [formal] [x] body` from the world's byte-checked `:DEFUN`,
    reads `(IF test rhs els)` off the result, and checks `test` against
    the emitted `:HYPS` and `rhs` against the emitted conclusion before
    the lemma is applied. Every failure is a FRONTIER (kept hypothesis),
    and the assembled proof is type-hinted against `mkLinearHypType` —
    a drifted emission fails at the kernel, exactly as `dischargeGzRuleHyp`
    does. `d5GzLinearRules` is therefore a NAME list: the reviewable
    record of which boot-stored rules may be discharged without
    replayable evidence, which is a policy question, not a proof one.
  - **J-P5a-c (the totality hypothesis, not a re-derived exec-corr).**
    The unfold needs the body's convergence at the formal binding. The
    waypoint layer already has that for ACL2-COUNT
    (`acl2_count_exec_corr`), but it lives ABOVE the Replay layer and
    re-deriving it below would be the near-clone the working discipline
    forbids. The lemma instead takes the fn's OWN `total:` hypothesis in
    the driver's telescope shape (`mkTotalityHypType`) and reads the defn
    equation backwards (`re_body_conv1`); the branch's value comes from
    the driver's ordinary pinned convergence for the emitted rhs. The
    hypothesis is then discharged by the totality prover in the same
    pass every other consumer uses, so nothing new is trusted and no fn
    is special-cased.
  - **J-P5a-d (LIVE-GATED, not statically pinned — the J-P4b-c
    precedent).** `sorting/msort`'s `ACL2-COUNT-EVENS-STRONG` row is
    unconditional ONLY because this discharge fires, so an emission drift
    or a broken class check turns the row conditional and the golden diff
    shows it. A static pin would additionally need a telescope (the fn's
    `total:` hypothesis), which the ctx-free WP3 pin shape does not
    build, for a WEAKER check. Recorded at both sites.
  - **Item 2 — the `TRUE-LISTP-BNEXT` + `HOW-MANY-BAD-PAIRS-BNEXT` pair
    at sorts-equivalent: DIAGNOSED, BUILT, MEASURED, REVERTED.** P4b left
    an open question ("the name IS demanded and still produced no entry
    and no failure line"). Answered, and the answer is that it was NOT
    demanded: the `[xbook-diag]` census (below) shows both names, plus 11
    other dep theorems, dropped by `crossBookRegistry`'s demand filter,
    and every name the seed DOES demand is registered (58 unregistered
    demands, all of them "offered by: NO dep book" — fn/rune names, not
    theorems). Widening the seed with the consumer's OFFER surfaces
    (stored-rule + `:LINEAR` names) takes the undemanded dep-theorem
    count 13 → 1, and with a second `rule:`/`linear:` discharge pass
    (generalizing the existing D5-only one) BOTH conditions discharge.
    Measured at `Tests/Coverage/BSsortsEquivalent` — the sweep's own
    configuration, not the CLI's:
    `BSORT-IS-ISORT → REPLAYED ✓ cond[rule:TRUE-LISTP-BNEXT,
    linear:HOW-MANY-BAD-PAIRS-BNEXT]` became
    `cond[total:BNEXT, total:BNEXT-SIZE, tp:BNEXT-SIZE]`. Two conditions
    out, THREE in.
  - **J-P5a-e (the pair REVERTED, and why the residue is now precise).**
    The new conditions are the DEPENDENCY's own, mapped onto this
    telescope by the discharge — and they arrive AFTER the totality/TP
    passes have run, so nothing attempts them. That is the same
    structural fact that stranded the pair in the first place, one level
    up. A net cond increase is cost without payoff under the movement
    rule, so both pieces were reverted (the seed widening and the second
    dependency pass); the `[xbook-diag]` sink and the two dated
    in-source notes STAY. The named next step is NOT another pass: it is
    running the post-sweep passes to QUIESCENCE (rule/linear ⇄ total/tp,
    with `totalEnv` REBUILT for the newly-freed names) — a change to
    `replayProofConditional`'s discharge ordering, with a corpus-wide
    cost that must be measured, not a local fix. COST datum for whoever
    takes it: the widened seed added 12 cross-book theorem replays at
    sorts-equivalent; the book elaborates in ~50 min either way (the
    P3c-era "~52 dep theorems" estimate was pessimistic — the citation
    closure already demands all but 13 of them).
  - **J-P5a-f (the `[xbook-diag]` SINK — the J-P4b-g treatment, applied
    to the pre-pass).** `crossBookRegistry`'s two `continue`s and its
    demand filter said NOTHING, which is exactly why P4b could not close
    item 2. `ACL2LEAN_XBOOK_DIAG=1` now prints one line per silent drop
    (not demanded / no proof tree / book's world not included) plus a
    closing census of demanded-but-unregistered names with the books that
    offer them. stderr only, never a result line, never read by a gate,
    off by default. Do not harden it.
  - **J-P5a-g (a P4b BOOKKEEPING GAP, exposed and closed).** Rebuilding
    `Waypoints/Catalog.lean` failed with `lift-coverage gate: green row
    11-custom-measure/CD2-BOUND has NO catalog decision`. CD2-BOUND went
    FAIL → REPLAYED at P4b and its catalog decision was never added; the
    gate never fired because P4b's ci run read a CACHED `Catalog.olean`
    (the same golden-staleness `just coverage-repin` exists to break, one
    module further out). Recorded as `.pending` — no native waypoint is
    claimed. Worth noting for the sprint: a green `just ci` does not
    prove the catalog gate RAN.
  - **J-P5a-h (RATCHET).** `Imported/Sorting.lean` shrank 4246 → 4165
    with the decode exception's deletion; the baseline was TIGHTENED to
    4165, never left loose. No module gained a baseline entry
    (`Harness.lean` 1486 and `GzRules.lean` 581 are both under the 1500
    norm).

- **P6 (the last row) — 2026-08-16. THE SPRINT'S END STATE REACHED:
  golden header `REPLAYED 116/116 (116 unconditional + 0 conditional)`,
  ZERO `cond[…]` on any row, ZERO FAIL rows, ZERO `sorry`/`sorryAx`.**
  `BSORT-IS-ISORT`'s `cond[rule:TRUE-LISTP-BNEXT,
  linear:HOW-MANY-BAD-PAIRS-BNEXT]` retired with NO new condition
  anywhere: the measuring sweep moved EXACTLY TWO golden lines (that row
  and the header); the other 28 books' sections compared byte-identical.
  P5a's item 2 closed as its own note said it had to be — the widening
  PLUS the quiescence composition, landed together.
  - **Piece 1 — the demand seed widened (`Runner.bookDemandSeed`).**
    P5a's measured widening, re-implemented verbatim in intent: the
    cross-book demand seed is `bookCitedNames` PLUS the consumer's own
    OFFER surfaces (`allBookRules` names + `groundZeroLinearRuleSpecs`
    names). `TRUE-LISTP-BNEXT` is cited by NOTHING and
    `HOW-MANY-BAD-PAIRS-BNEXT` only inside `BSORT`'s admission
    waterfall, so neither was ever demanded and neither had a registry
    entry to discharge against. DEMAND-SIDE ONLY: it can make the
    pre-pass replay more dependency theorems (each a full,
    deterministic, kernel-checked replay whose entry is matched by
    STATEMENT), never change what a replay may use.
  - **Piece 2 — the post-replay discharge lane runs to QUIESCENCE
    (`replayProofConditional`).** The two layers FEED EACH OTHER: a
    dependency discharge carries the dependency's own `total:`/`tp:`
    hypotheses onto this telescope, and a recorded-admission totality
    proof carries the admission's own `rule:`/`linear:` conditions onto
    it. One pass of each, in either order, strands whatever the later
    pass introduced — which is why the pair survived (they arrive from
    the admission proof, AFTER the sweep) and why P5a's lone extra
    dependency pass stranded the dependency's `total:BNEXT` +
    `total:BNEXT-SIZE` + `tp:BNEXT-SIZE` (they arrive after the
    totality/TP passes). Both layers now run inside ONE outer loop —
    dependency sweep (itself to quiescence, cap 4) → `total:`/`tp:`
    passes → the D5 ground-zero rule pass — with the P3c discipline
    kept verbatim: STRICT PROGRESS (the free-hypothesis count must
    fall) plus a hard cap (4), the honest-mistake speedbump, not
    hardened. The LATE dependency-discharger copy P5a had tried is NOT
    added: a `rule:`/`linear:` fvar the admission proof introduces is
    picked up by the NEXT ROUND's sweep, which is the same fix without
    a second code path.
  - **J-P6-a (`totalEnv` REBUILT, but only on a NEW name).** The
    quiescence property needs the environment the `total:`/`tp:` passes
    consume to be CURRENT: a hypothesis that arrives mid-loop must be
    attempted with the machinery the current round has, not a pass-1
    snapshot. Rebuilding unconditionally each round would re-PROVE every
    needed fn's totality (the expensive part) for no gain, so the
    rebuild is keyed on the accumulated needed-fn set: a round that
    introduces no new name reuses the environment (a smaller set is
    served by the same one — lookups are by name), and a round that
    does rebuild takes the UNION, keeping the environment monotone. Round
    1 is byte-identical to the pre-P6 behaviour by construction.
  - **J-P6-b (a `tp:` frontier MEMO, cleared on rebuild).** Re-running
    `proveTp` against the SAME `totalEnv` can only frontier again, and it
    is the expensive prover in the lane; a name that frontiered under the
    current environment is skipped until a rebuild drops the memo. Cost
    control only — it can never turn a discharge into a kept condition
    that a re-attempt would have retired.
  - **J-P6-c (the pins take the SAME seed).** `Waypoints/Macro.lean`'s
    cross-book pre-pass was moved to `bookDemandSeed` too: a pin and its
    golden row must demand the same dependency set, or the pin stops
    being a check on what the sweep does.
  - **J-P6-d (RATCHET — a MOVE, not a loosening).** The loop pushed
    `Driver/Harness.lean` to 1548 lines, over the 1500 NORM (it has no
    baseline entry and must not get one). Resolved by moving the five
    DEVELOPMENT-query declarations (`developmentTheoremsWithRules`,
    `rulesBefore`, `findThms`, `findThm`, `derive_world`) — which touch
    none of the walker/discharge machinery — to a new leaf module
    `Driver/DevQuery.lean` that Harness imports, so every existing
    consumer resolves the names unchanged. Bodies byte-identical.
    Harness 1548 → 1483. The J-RT2e / J-P3b-f / J-P4a-i / J-P5a-h
    precedent.
  - **PIN CONVERGENCE.** `Tests/SortingPinsEndgame.lean`'s
    `BSORT-IS-ISORT` pin drops its last two premises (dated diagnosis in
    place, the running record of the row's descent from 15 premises to
    0); the now-unused `linearHyp1`/`linearHMBPB` pin helpers are
    DELETED with their last use (the deletion+rewiring flow — the shape
    is still LIVE-gated, since the golden row is unconditional only
    because the discharge fires). The `BSORT-IS-ISORT` catalog entry's
    prose is corrected: `.pending` now stands on the missing waypoint
    native and the bsort exec kit ONLY, no longer on a replay condition.

## SPRINT END STATE REACHED (2026-08-16, P6)

Every Tier-1 mechanism closed (G1/PERM-TLFIX; the recognizer-under-IF
trio; CD2-BOUND; CLASSIFY-POS). Every Tier-2 condition class retired
(tp:/total:/rule:/linear: — including the four classes DISCOVERED
during the sprint: the arithmetic-rune family, the gz-linear family,
the decode class, the cross-book transfer demand). The hard metrics:

- Golden: **116/116 REPLAYED, 116 unconditional + 0 conditional,
  zero FAIL rows** (122 ✓ rows = 116 theorems + 6 terminations).
- **Zero sorry/sorryAx/native_decide in the repository** — the win
  state. The FORBIDDEN-DEBT class is EMPTY for the first time.
- Full build zero warnings; all statics; mirror layer untouched and
  green throughout (all receipts trio-clean).

Remaining below: the claim gate (full invalidation first, per the
P5 catalog-cache find) and its TRUE_EXIT=0 record.

## CLAIM GATE: TRUE_EXIT=0 on 7b69166
(artifact: `.gate-runs/7b69166-20260816T135429Z.log`; full invalidation
first — every IO-read gate provably ran). THE SPRINT IS COMPLETE.
