<!-- End-of-branch audit report, persisted verbatim from the auditor's final text (2026-08-16). Auditor: A6 — judgment-call governance (Opus). Branch: mdd/t12-sprint @ 388089d. Synthesis: docs/audits/2026-08-16_eob-audit-synthesis.md -->

## A6 — JUDGMENT-CALL GOVERNANCE REVIEW (branch `mdd/t12-sprint` @ `388089d`)

Read: charter ARC LOG (900 lines, `docs/plans/2026-08-14_t12-sprint-charter.md`), the trip report, the 23 sprint commits, and the code/artifacts behind every pre-flagged call.

### 0. Census arithmetic first (a finding in itself)

- **55 distinct J-tags in the ARC LOG.** J1–J10 (10), J-RT2a–e (5), J-P3b-a–g (7), J-P3c-a–e (5), J-P4a-a–i (9), J-P4b-a–g (7), J-P5a-a–h (8), J-P6-a–d (4). J6–J10 and J-P3c-a–e are inline in prose rather than standalone bullets (thin rationale, one clause each); the rest carry paragraph rationales.
- **Two lanes' calls are MISSING from the log.**
  - **J-R3a..h** (phase 2, the unified measure table) exist only as a string in commit `b3f6174`'s message. Grep of the whole repo: no `J-R3` anywhere in `docs/`. Only f/g/h have a one-line rationale (in the commit); **J-R3a–e have no recorded rationale anywhere**. Note the orchestrator's own prompt cited "J-R3g" — i.e. it was working from commit messages, not the log it mandated.
  - **P5b has ZERO J-entries and no ARC LOG section at all** — yet it is the lane that closed `tp:QSORT`, added `Driver/TpProver.lean` (1033 lines) and the **CONDITIONAL stored-rule TP route** (`TsConsumer.lean:213+`: consuming ACL2's *other* stored `:ALL-TPS` rules, e.g. `TRUE-LISTP-APPEND`, as admissibility for a TP walk), and re-landed the `allTps` data path P4b had reverted. That is a new semantic consumption surface with no logged call.
- The trip report says "~40 J-numbered judgment calls". The true figure is **≥63** (55 logged + 8 named-only). The report undercounts by ~35%.

The delegation contract was "each one LOGGED (J-numbered, with rationale) in the ARC LOG below." It was honoured for ~55/63, breached for 8 (rationale-free) and for one entire lane.

### 1. The J-census

| # | ID | One-liner | Class |
|---|---|---|---|
|1|J1|G1 design = adopt the persisted brief's recommendation (option M + 1a + 2a + `:GENEQV`) rather than present it for ruling|**(ii)**|
|2|J2|R-widening lands as a WRAPPER (`replayNodeR`, new Congruence.lean); Node.lean untouched at its cap|(i)|
|3|J3|Class C handled by SPLITTING the recorded node at its R-step (record projection, hard-checked)|(i)|
|4|J4|Cited-rune anchor reads the NODE's own `:RUNES`, not the clause-level set (tighter, BUG-023 direction)|(i)|
|5|J5|Congruence collapse preserves the preprocess lane's error text byte-for-byte|(i)|
|6|J6|`tp:` inside `[DISCHARGE: …]` brackets (119 of 129) declared probe-structural/informational|**(ii)** light|
|7|J7|ts-algebra inventory built demand-driven only|(i)|
|8|J8|`&lt;`-against-zero mask is a Lean-side closure lemma; the VERDICT stays ACL2's|(i)|
|9|J9|Addressed-leaf admissibility taken as GAP-1's payoff|(i)|
|10|J10|Shared extractions + module splits per the weight ratchet|(i)|
|11|J-RT2a|`infra/tp-leaves` collector MOVED `defuns.lisp`→`type-set-b.lisp` (load order, not a clone)|(i)|
|12|J-RT2b|`:ALL-TPS` entries carry the rule's own `:term`; body instantiated formals→args; `er hard` on shape|(i)|
|13|J-RT2c|`:ARG-LEAVES` SCOPED to IF-valued args, inside the structured-log guard|(i)|
|14|J-RT2d|Parser REFUSES the old 4-field `:ALL-TPS` shape rather than half-reading it|(i)|
|15|J-RT2e|New field readers in `ProofLogTypes.lean` to hold `ProofLog.lean` at its ratchet cap|(i)|
|16|J-P3b-a|Ordinal decreases as an S4 REGISTRY ROW, not a new measure-table row|(i)|
|17|J-P3b-b|EQUAL-alias normalization read from the world's OWN definitional aliases, comparison-only|(i)|
|18|J-P3b-c|DP-probe `ReplayConfig` missing `gzDefs` fixed at the source (two paths, one prover)|(i)|
|19|J-P3b-d|`tsFactOf` moved to a new leaf module so both consumers read ONE mask table|(i)|
|20|J-P3b-e|`:IF-TEST-TRUE/FALSE` markers threaded as ANCHORS only; falsity still PROVED|(i)|
|21|J-P3b-f|Ratchet resolved by MOVES; two baselines TIGHTENED|(i)|
|22|J-P3b-g|Items 3/4 STOPPED at verbatim frontiers rather than closed by Lean-side inference|(i)|
|23|J-P3c-a|`evalOpt_world_mono` transport REJECTED; cross-book transfer = re-replay at the consumer's world|**(ii)**|
|24|J-P3c-b|World-inclusion as a meta-level fail-closed gate ("buys principle, not soundness")|(i)|
|25|J-P3c-c|Cross-book misses are frontiers; same-book misses stay defects|(i)|
|26|J-P3c-d|Demand-only rune collector (can only widen reach, never widen what a replay may use)|(i)|
|27|J-P3c-e|Diagnostics never in `res.lines`|(i)|
|28|J-P4a-a|RT3 premise CONTRADICTED by the artifact → no fork round-trip made|(i) exemplary|
|29|J-P4a-b|`ifMarkerCitedCr` reads the marker's own `:JUSTIFICATION` ttree; 3 attested shapes, 4th hard-fails|(i)|
|30|J-P4a-c|New "sharp constant" ts cell `tsPlusConstOf` keyed on the CONSTANT (`'-1`)|**(ii)** light (accretion watch)|
|31|J-P4a-d|`citedCr` threaded through `inTsFromArgLeaves`|(i)|
|32|J-P4a-e|Row-blind μ-route discriminator (latent defect) fixed at source via `MeasureShape` dispatch|(i)|
|33|J-P4a-f|New FOURTH spine closer `groundConstClose` (folds ending in `'T` close the clause)|**(ii)** light|
|34|J-P4a-g|CD2-BOUND STOPPED out-of-class: the ACL2-mask guard question is "fidelity-sensitive design, not a consumption arm"|(i) exemplary|
|35|J-P4a-h|Hypothetical-TP NOT attempted; two blockers scouted and mapped|(i)|
|36|J-P4a-i|`CoreSpine` held at baseline by moving the gate into the closer|(i)|
|37|J-P4b-a|D5 admission: the five arithmetic runes move from hand-applied waypoint constants to the driver's cited-rune registry|**(ii)** (verified non-growth)|
|38|J-P4b-b|`d5Allowed` kept as a named EMPTY slot|(i)|
|39|J-P4b-c|The WP3 static pin SKIPPED for the five runes; "live-gated by the golden" instead|**(ii)** light|
|40|J-P4b-d|**BUG-009 mask discount** — `tsAcl2MaskOk` discounts type index 6, reversing P4a's out-of-class stop|**(ii)** — top brief|
|41|J-P4b-e|μ-generic `tp_*_rec_mu` twins (the prover's own deferred comment executed)|(i)|
|42|J-P4b-f|De-duplication of two identical strong-induction theorems|(i)|
|43|J-P4b-g|`ACL2LEAN_TP_DIAG` diagnostic sink, env-gated, stderr only|(i)|
|44|J-P5a-a|`routeIff` decode admitted; two-valuedness DEMANDED from emitted TP corollaries (frontier without a source)|**(ii)**|
|45|J-P5a-b|New gz-`:LINEAR` discharger FAMILY; `d5GzLinearRules` is "a policy question" decided by the executor|**(ii)**|
|46|J-P5a-c|Totality hypothesis used instead of cloning the waypoint layer's exec-corr|(i)|
|47|J-P5a-d|Live-gated, not statically pinned (the J-P4b-c precedent, second use)|**(ii)** light|
|48|J-P5a-e|Seed-widening pair REVERTED at 2-out/3-in under the movement rule|(i) exemplary|
|49|J-P5a-f|`ACL2LEAN_XBOOK_DIAG` sink over the pre-pass's silent `continue`s|(i)|
|50|J-P5a-g|CD2-BOUND catalog decision recorded `.pending`; cached-`Catalog.olean` masking found|(i) exemplary|
|51|J-P5a-h|`Imported/Sorting.lean` baseline TIGHTENED 4246→4165|(i)|
|52|J-P6-a|`totalEnv` rebuilt only on a NEW needed name; union kept monotone|(i)|
|53|J-P6-b|`tp:` frontier MEMO under a fixed `totalEnv`, cleared on rebuild|(i)|
|54|J-P6-c|Pins take the same `bookDemandSeed` as the sweep|(i)|
|55|J-P6-d|Harness 1548→1483 by moving dev-query decls to `DevQuery.lean`|(i)|
|—|J-R3a–h|**Named in commit `b3f6174` only; a–e have no rationale on record.** f = 7 catalog promotions forced by the gate; g = PERM-TLFIX `.pending`; h = fixing a pre-existing red (`just ci` had been UNRUNNABLE since R2)|**(ii)** as a set (unlogged)|
|—|P5b|**No J-entries at all** for the conditional-stored-rule TP route, the re-landed `allTps` path, `TpProver.lean`|**(ii)** as a set (unlogged)|

**Zero calls I judge wrong on the merits — (iii) count is 0.** Every (ii) below is technically defensible and, where I could check it against code or artifacts, checks out. The failures in this sprint are of *process and escalation*, not of judgment.

### 2. Briefs for Mike (the (ii) set)

**B1 — J-P4b-d, the BUG-009 mask discount (highest stakes).** `recogVerdictFromTs`'s cross-check demanded that ACL2's emitted `:TYPESET` be inside the mask we derived. For `(&lt; N '0)` true, ACL2 emits 112, the model derives 48; 112 = 48 ∪ {bit 6} = `*ts-complex-rational*`. `tsAcl2MaskOk` (`Replay/Driver/TsFacts.lean:161`) now discounts index 6 and nothing else. I verified: `tsIndex` (`Lemmas/TsAlgebra.lean:44`) provably never returns 6 (`tsIndex_lt`, and 6 is the one index in 0–13 no branch produces), ACL2's basic partition is exactly 14 bits, the existing `tsSubsumedM`/`tsDisjointM` already range over 14, and BUG-009 carries the third-site note plus an explicit deletion condition. **What Mike should rule on is not soundness — it is mirroring.** The verdict lemma is proved, so a stronger derived mask cannot yield a false proof; the guard exists so the replay uses ACL2's recorded reasoning rather than our model's stronger reasoning. Discounting is a fidelity-cross-check trade. The escalation-worthy part: **P4a stopped on this exact question and classified it "a fidelity-sensitive design question, not a consumption arm" (J-P4a-g); P4b reversed that classification one lane later with no new information — only a decision, under the pressure of a named residual row.**

**B2 — J-P5a-b, a new D5 discharger FAMILY (`:LINEAR`).** The ratified D5 carve-out covers boot-stored `:REWRITE` rules with no replayable evidence. P5a extended it to ground-zero `:LINEAR` rules via a class lemma `gz_linear_defn_branch` (parametric; the driver recomputes `substTerm` from the world's byte-checked `:DEFUN` body and checks the test against `:HYPS` and the rhs against the conclusion before applying). Content-wise the rule is one definitional unfold, so the trust delta is small. But the entry's own docstring calls `d5GzLinearRules` "the reviewable record of WHICH gz rules may be discharged without replayable evidence, which is a policy question" — a policy question the executor answered. Carve-out *class* extension is the exact accretion pressure the carve-out-drift ruling names.

**B3 — J-P4b-a, the D5 applier move.** Claim: "nothing new is trusted; the five were ALREADY the ratified `d5Allowed` set". **Verified true** — the pre-sprint `Catalog.lean` `d5Allowed` was exactly `dis_plus_comm, dis_plus_comm2, dis_plus_assoc, dis_plus_if_lift, dis_equal_if_lift`, and the new `d5GzRules` entries are the same five statements re-expressed over the Replay layer. The set did not grow; the applier moved from a human telescope to the cited rune (strictly tighter). Low stakes — noted for completeness because it is carve-out administration.

**B4 — J-P5a-a, the `routeIff` decode admission (+ the waypoint exception deletion).** A new registered decode route for ACL2's `create-rewrite-rule` `(IFF l r)`→`:EQUIV EQUAL` normalization. I read it: `Harness.lean:287-306` demands `boolDisj?` for BOTH sides and frontiers with a named message if either lacks a two-valuedness source; `eq_of_iff_ne_nil_two_valued` takes both disjunctions as premises, so the statement is unprovable without them. Genuinely tighter than the hand decode it replaced. The Mike-class part is the **side effect**: it retired `dis_rule_orderedp_append` — a registered, previously audited waypoint-layer DECODE exception — deleting 81 lines from `Imported/Sorting.lean` and emptying both `Catalog.lean` registrations. The charter's out-of-scope clause said the mirror side must remain UNTOUCHED. I confirmed **`ACL2Lean/Mirrors/` was never touched** (zero diff), so the letter holds; the waypoint layer *was* touched, but Tier 2 explicitly mandated retiring the six `Imported/Sorting.lean` sorries, so most of that traffic was chartered. The decode-exception deletion was not.

**B5 — J-P3c-a, re-replay vs transport (design fork + cost).** `evalOpt_world_mono` transport was rejected (callBuiltin's 55-arm match can't produce equation lemmas at the fixed whnf budget) in favour of replaying the dependency's recorded tree once at the consumer's world, `addDecl`'d, matched by STATEMENT. Fidelity-conservative (a real replay, `worldIncludes` fail-closed, demand-bounded). The Mike-class content is the **cost**: sorts-equivalent elaboration went ~50→65 min/book, and the ARC LOG's own words were "weigh at gate" — the weighing was done by the agent. P6 later brought it to ~36.6 min, so the trade came out ahead; that is the outcome, not the process.

**B6 — J-P6 seed widening (Piece 1) + acceptance.** `bookDemandSeed` adds the consumer's OFFER surfaces to `bookCitedNames`. Demand-side only, both call sites (J-P6-c keeps pins and sweep on the same seed). It replays *more* dependency theorems; it cannot change what a replay may use. This is the correct shape and its cost was measured. Flagged only because P5a had measured the same widening at 2-out/3-in and reverted it; P6 re-landed it composed with the quiescence loop and reported exactly two golden lines moving with 28 sections byte-identical. That is the right evidence standard; no concern beyond the fact that the sprint both proposed and graded it.

**B7 — J-P4b-c + J-P5a-d, declining WP3 static pins twice.** Justification: "LIVE-gated by the golden … a STRONGER check than the pin". The practical reason (pinning would require parsing a 150k-line log inside `Tests/`) is legitimate. The "stronger" framing is overstated: a static pin is an independent, hand-written statement checked by the build; the golden is produced by the same code the sprint changed and repinned. Two uses make it a pattern worth a ruling on where the pin regime binds.

**B8 — J6, the metric's denominator.** 119 of the 129 `tp:` occurrences were classified as `[DISCHARGE: …]`-bracket, i.e. on the standalone informational DP probe rather than the row. I verified this against `Runner.lean:939` (`tryDischarge`, counted in `dpTotal`/`dpAssumed`, not in the row's status) and against pre-existing prose in `Waypoints/Basics.lean:476` that says the same thing — so the reading predates the sprint and matches the charter's own "(DP probes stay informational.)" parenthetical. Honest. Flagged because it is the party being measured interpreting its own success metric, and 35 `cond[…]` strings remain in the golden file under that reading (all inside DISCHARGE brackets; 9 probes still `◌` assumed).

**B9 — J-P4a-c and J-P4a-f, the accretion/closer watch.** Not individually wrong. `tsPlusConstOf` is a ts cell keyed on a *constant* (`'-1`), added because one book needed mask 7; `groundConstClose` is a new fourth clause-closer for a terminus ACL2 records no closer for (reconstructed from the recorded folds, fail-closed, with the peeled reconstruction checked to BE the clause's disjunction). Both are one-cell/one-closer additions with the established precedent cited. Two of them in one lane is the shape the carve-out-drift test warns about; worth a periodic census rather than a per-call ruling.

**B10 — J1, adopting the G1 design instead of presenting it.** The brief (`docs/notes/2026-08-14_g1-design-brief.md`) was written as a ruling document — the immediately preceding branch's commits show the standing practice is that design forks go to Mike ("2e design APPROVED as written", "design fork … presented for ruling"). Under the sprint's blanket delegation the agent adopted the brief's own recommendation. Outcome was the minimal, corpus-demand-driven option; the practice question stands.

**B11 — the unlogged sets (J-R3a–h, all of P5b).** For J-R3a–e there is nothing to review: no rationale exists. For P5b the substance is reviewable and looks careful (`TsConsumer.lean:213+`: "Consuming one is not trusting it — the rule's CONCLUSION is re-proved from the fn's body by the same walker, under its hypotheses, and each hypothesis is discharged at the call site"; `TpProver.lean:524+` tries the stored-rule route only when the definitional corollary reaches by neither route). But **the delegation contract's only accountability mechanism — the log — was skipped for the lane that opened a new ACL2-data consumption surface.**

### 3. Priority-order check

Stated order: fidelity rules &gt; two-standard rule &gt; four-line canon &gt; working discipline &gt; persisted rulings.

- **Fidelity first — honoured, repeatedly and expensively.** J-P3b-g, J-P4a-g, J-P4a-h, J-P5a-e, J-P4b item 2 and item 3: five occasions where an item was STOPPED, or a built-and-measured fix REVERTED, rather than closed by loosening or inference. The `sorry` count went 6→0 by retirement/deletion+rewiring, never by re-proof-in-place (the provenance gate structurally forbids that). No call traded fidelity for a row.
- **Two-standard rule — honoured.** Gates and diagnostics were consistently treated as speedbumps: the empty named `d5Allowed` slot (J-P4b-b), both diag sinks marked "never read by a gate, do not harden" (J-P4b-g, J-P5a-f), the quiescence cap-4 explicitly labelled an honest-mistake speedbump. No gate whack-a-mole.
- **Four-line canon — UNDEFINED IN THE RECORD.** Grep of `docs/` finds the phrase only in this charter's own priority list (and in an unrelated sense in the R4 charter). A delegated agent was instructed to rank its calls by a principle with no persisted definition. No call visibly turns on it; fix the charter template.
- **Working discipline — honoured, notably the wire-later ban.** P4b reverted its own `allTps` plumbing as unwired infrastructure; P5b rebuilt it WIRED one lane later. Dedup taken when noticed (J-P3b-d, J-P4b-f). Five separate ratchet resolutions by MOVE with baselines tightened, never loosened (J-RT2e, J-P3b-f, J-P4a-i, J-P5a-h, J-P6-d).
- **Persisted rulings — honoured where they existed; extended where they didn't, without escalation.** J-P4b-a rests on close-out audit O-5 (and I verified the set didn't grow); J-P5a-b *extends* that criterion to a new rule kind; J1 adopts a brief written to be ruled on.

**Calls where a different ordering changes the outcome:**

1. **J-P4b-d.** If "two-standard rule (semantics get adversarial review)" outranked sprint-completion, this goes to Mike instead of being decided — and P4a's own out-of-class classification is the evidence the sprint itself thought so 8 hours earlier. This is the single clearest ordering-sensitive call in the log.
2. **J-P5a-b.** If "persisted rulings bind their own scope" outranked "resolve per principles", extending D5 from `:REWRITE` to `:LINEAR` is a ruling, not a call.
3. **J1.** If the standing *practice* (design forks are presented) counted as a persisted ruling, J1 is a presentation.
4. **J-P3c-a / P6 widening.** If cost-to-the-project ranked with fidelity rather than below working discipline, a ~30% corpus-wide elaboration increase gets weighed with the user at the moment it lands, not at a gate the same agent runs.

### 4. The delegation experiment itself

**Where delegation clearly won (velocity, no quality loss):**
- **Premise refutation.** RT2 ask 4 (ground-zero clauses already emitted since `006bebce9f` — fork edit not made), J-P4a-a (the "missing" `:IF-TEST-FALSE` records existed, line-wrapped past a single-line grep — an entire fork round-trip avoided), J-P4b item 3 (the `tp:QSORT` map was wrong; the real frontier was two steps earlier). Each refutation *shrank* the work. Ask-first would have added round-trips to decisions that deleted themselves.
- **Measure-then-revert.** P4b item 2 and P5a item 2 both built, measured at the real book, and reverted under the movement rule — and P5a's measurement *became* P6's design. A user round-trip here would have bought nothing; the measurement was the argument.
- **Mechanical hygiene.** Module ratchets, dedup, diagnostic sinks, demand-driven registry cells, severity policy for internal errors, fail-closed parser choices. ~35 of the 55 calls. Escalating any of these would have been pure latency.
- **Stopping.** Five clean stops with verbatim frontiers and file:line maps. The delegated agent stopped itself more often than it pushed through.

**Where the sprint was lucky rather than right:**
- **J-P4b-d.** Correct *because* the delta happened to be exactly bit 6 and the model provably never produces it. Had the delta included any other bit, the same end-state pressure ("one FAIL row left") was present and the only safeguard was the executor's own care — there is no structural gate on "loosening a fidelity cross-check". The one structural signal that existed (P4a's out-of-class stop) was overridden by the next lane.
- **P5b.** A new consumption surface with zero logged calls. Nothing in the process would have surfaced a bad call there; it was reviewed by the build and the golden only.
- **The catalog gate.** J-P5a-g establishes that P4b's green `just ci` **did not run** the catalog gate (cached `Catalog.olean`). Any catalog-decision error in that window ships silently. Found by luck — both P5 lanes tripped over it independently.
- **The cwd-persistence incident.** Six orchestrator commands silently ran in a worktree; one produced a *wrong accusation against a correct executor report*, retracted only because the orchestrator re-checked. Honest logging is why we know; it isn't a control.
- **Golden self-certification.** The sprint repinned, multiple times, the metric it is graded by, verifying with its own sweep. The movement rule + row-by-row diagnosis + `check-golden-current` are real mitigations, and the final claim gate ran after full invalidation (`.gate-runs/7b69166-…log`, `TRUE_EXIT=0` — I checked the artifact exists and ends with that line). But the structural weakness is intact: independent end-of-branch review (this round) is the only thing that closes it.

### 5. Recommended delegation boundary for future sprints

**Remain ask-first, even under a sprint goal (five classes):**

1. **Loosening any cross-check between ACL2's emitted data and our derivation** — admissibility guards, verdict comparisons, decode admissibility. (J-P4b-d.) Tightening stays delegated.
2. **Extending a ratified carve-out to a new KIND** — a new rule class, a new discharger family, a new "closes without replayable evidence" entry. (J-P5a-b; and by the same rule J-P4a-f's new closer class.) Adding a *member* to an already-ruled class, with the class's own recompute-check, stays delegated (J-P4b-a is the model — and it should still say, as it did, exactly why the set did not grow).
3. **Design forks with a lasting architecture or a corpus-wide cost profile** (say &gt;10% sweep cost, or a new module family). (J1, J-P3c-a, P6 Piece 1.) Present the fork with the measurement; do not both propose and accept.
4. **Deleting or re-deciding another track's records** — waypoint decode exceptions, provenance registrations, catalog decisions. J-P5a-g's PERM-TLFIX `.pending` is the model to copy verbatim: *"classifying a row as plumbing vs content is a MIRROR-side call, deliberately NOT taken by a driver-layer executor."* The sprint got this exactly right for catalog decisions and exactly wrong for `dis_rule_orderedp_append`.
5. **Re-opening an item a prior lane STOPPED as out-of-class or fidelity-sensitive.** A recorded stop should be an escalation trigger, not a to-do. This one rule alone would have caught the sprint's most consequential call.

**Explicitly delegated (keep):** module moves/ratchets, de-duplication, env-gated diagnostics, demand-driven cells inside an already-proved lemma pattern, error-severity policy, parser fail-closed choices, stops, reverts, premise refutations, sequencing changes.

**Two process fixes independent of the boundary:**
- **A lane may not be collected until its J-entries are appended to the ARC LOG.** Commit messages are not the log (J-R3a–e prove it: rationale that exists nowhere), and a lane can otherwise land with none at all (P5b).
- **Define or delete "the four-line canon"** in the charter template, and have the exit report's J-count be computed from the log rather than estimated (~40 vs ≥63).