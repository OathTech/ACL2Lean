# ACL2Lean — project TODO

**This file is the LIVE BACKLOG: what is open, across every track.** It is not
a work journal. Per-arc narrative — findings, measurements, ruling records,
wave-by-wave state — belongs in that arc's charter under `docs/plans/` or a
dated note under `docs/notes/`; everything the file had accumulated up to
2026-08-19 is preserved verbatim in
[`docs/archive/todo-history-2026.md`](docs/archive/todo-history-2026.md).

New to the project? Start with [`README.md`](README.md), then
[`docs/OVERVIEW.md`](docs/OVERVIEW.md) (pipeline, trust model, how to build)
and [`docs/LEXICON.md`](docs/LEXICON.md) (the three words that matter). The
working rules are [`CLAUDE.md`](CLAUDE.md). Live *status* is never read off
this file — read it off the artifacts, as `docs/OVERVIEW.md` § *Where live
status lives* explains.

**Conventions.** An item is a checkbox plus enough context to pick it up cold,
and a pointer to its record document where one exists. Items are grouped, not
ranked: **the grouping carries no priority order** — priorities are Mike's
call, and the current ones are set in
[`docs/plans/2026-08-12_master-plan.md`](docs/plans/2026-08-12_master-plan.md),
the governing plan. When an item is done, delete it here and let the arc's
charter or the archive carry the record.

<!-- IN-FLIGHT ZONE -------------------------------------------------------
     Arcs in progress prepend their entries directly below this comment and
     above the "## LIVE BACKLOG" heading, newest first. Keep an entry to a
     few lines plus a pointer to the arc charter. At arc exit, fold what
     survives into LIVE BACKLOG and move the narrative to the charter or to
     docs/archive/todo-history-2026.md.

     This zone is deliberately the only place that churns, so two arcs
     landing at once merge cleanly here instead of colliding in the backlog.
     -------------------------------------------------------------------- -->

## In flight

*Nothing recorded here right now.* The 2026-08-19 docs-polish round left this
zone empty on purpose, so in-flight arcs land their entries in a clean file.

## Live backlog

### Release

- [ ] **Cut `v0.1.0`** per `docs/notes/2026-08-19_versioning-policy.md`
      (ratified 2026-08-19) once the toolchain-bump arc AND the docs
      polish are both on `main` and the gate is green — annotated tag on
      a commit with a recorded full `just claim-gate` (`TRUE_EXIT=0`);
      GitHub Release wraps the tag at the next networked push.

- [ ] **Backlog triage pass with Mike — scheduled AFTER `v0.1.0`.** The
      2026-08-19 restructure preserved all 51 open items verbatim by design
      (reorganization, not triage), so the list still carries June-era
      entries whose frontier may have moved or closed. Walk it once with
      Mike: close what is done, drop what is superseded, re-rank what is
      left. Priorities are his call, not the file's.

- [ ] **Toolchain PANIC in the build output — classified, ACCEPTED, not
      fixed (2026-08-19, external claims audit P2).** Lean's own
      `LibrarySuggestions.SymbolFrequency` export pass blows its
      heartbeat budget on the heaviest coverage modules and panics
      AFTER elaboration; olean, receipts, goldens and gates are
      unaffected (`TRUE_EXIT=0` alongside). Investigated for a
      project-local switch and there is NONE: the extension is
      `builtin_initialize`-registered in the shared library, has no
      option gate or CLI flag, and its `Core.Context` is built with
      `options := {}` so `maxHeartbeats` is unreachable from the module
      or the command line (v4.28.0 source).
      **Elimination attempted and REFUTED by measurement (2026-08-19).**
      The same fresh `Core.Context` takes `initHeartbeats := 0`, so the
      check compares the ABSOLUTE thread heartbeat count for the whole
      module elaboration against a fixed 200 000 000 — not the export
      pass's own cost (reproduced directly; byte-identical timeout
      string). At the measured ~16 heartbeat-units/ms of `runBook`, the
      budget is gone after ~12 s of replay; the offending module replays
      for ~477 s (~38x) and `BSqsort` at ~423 s (~35x) does not panic, so
      weight is not the discriminator. A section split cannot reach the
      budget, and `coverage_book%` has no sub-book unit anyway (one
      module per book per golden section; the aggregate tiling check
      requires exactly one section per `corpusOrder` entry). The
      deny-list surface was measured too and NOT taken (an `ACL2` type
      prefix covers 79/81; the residue is a rotting name list). Fix is
      upstream (`withCurrHeartbeats` around the export pass). Disposition:
      `docs/OVERVIEW.md` § *Known limitations*; the full measurement
      record moved to
      `docs/archive/2026-08-19_symbolfrequency-panic-measurement.md`
      (docs-polish round, 2026-08-19).

### Capability and coverage — the named broadenings

- [ ] **G4 — Forcing-round emission + composition.** Emit per-assumption
      `(type-alist, term, assumnotes)` + the round-(k+1) clause list at
      extract-and-clausify-assumptions (single hook); replay rounds locally
      and discharge force-site hypotheses with the round proofs (the
      conditional-proof shape).

- [ ] **G5 — Induction generality.** 3-subgoal/merged schemes, multi-variable
      measures, mutual-recursion flag schemes — scaffold extensions,
      corpus-driven (true-listp-flatten, len-interleave, len-zip2/3 name the
      frontiers).

- [ ] **G6 (REVISED 2026-06-12, MDD) — the sorting corpus as DRIVING TARGET.**
      Replace the grep-sweep with one real development:
      `acl2/books/sorting/` (sorts-equivalent), validated (provenance
      byte-identical to upstream, logs recaptured fresh, capture
      deterministic) and roadmapped R0–R7 in
      docs/plans/2026-06-12_sorting-corpus-roadmap.md. G5 lands incrementally
      inside R1/R3/R4 (real schemes), G4 inside R5 (qsort is where forcing
      actually appears). The frequency sweep is demoted to a validation
      checkpoint before any CORE-tier completeness claim.
      PROGRESS (2026-06-12, branch mdd/sorting-r0 → merged main): R0 DONE
      (perm on the scoreboard, corpus 37→45; EquivSource reconstruction
      extension; translator fail-closed; include-aware capture warnings).
      R1 IN PROGRESS: the G5-v2 multi-case induction scaffold landed
      (docs/plans/2026-06-12_multicase-induction.md) — the scheme wall
      fell, all 17 prior REPLAYED rows byte-identical.
      PROGRESS (2026-06-14, branch mdd/perm-exec-counterpart, post-Fable
      buffer-against-mistakes mode): executable-counterpart steps + closer
      DONE (commit 7fe4d38; faithful ground re-execution, orthogonal/kept).
      comm-rm then revealed a SECOND wall — `sublis-var` display-folding of
      if-simp branches (logging-only, not a missing-reasoning gap) — now
      DEFERRED (A/B/C judgment call, can't measure until earlier walls fall;
      docs/notes/2026-06-14_exec-counterpart-and-folding-wall.md). comm-rm
      stands 1-of-2 done.
      PROGRESS (2026-06-16): clausify-on-multi-literal DONE (new
      evalOpt_congr_if_then/if_else lemmas, axiom-clean; applyStep arity-3
      then/else; replayClause chains disjoinTerm cn.inputClause). perm-cons
      and perm-transitive both cleared that wall and now stop at deeper real
      frontiers (notFlg closer; symbolic (consp y) if-test) — neither REPLAYED
      yet (still 17/45). perm-is-an-equivalence now hard-fails cleanly at the
      conditional-congruence frontier (R1 wall d). Two-reviewer adversarial
      audit (opus, read-only) of the exec-counterpart + clausify-multi-literal
      work: NO soundness/fidelity bug; one MINOR (wall-d catch swallowed the
      underlying error) fixed (commit 392b208). The exec-counterpart +
      clausify-multi-literal work (incl. the wall-d fix) is now MERGED to
      main (through commit 5fea3c7); the mdd/perm-exec-counterpart branch
      is retired. Verified 2026-06-19: main builds clean, `just ci` green,
      golden coverage byte-identical (REPLAYED 17/45, DP ✓9 ◌9 ✗0 of 18),
      ACL2 tags conform. No perm theorem replays yet — all 8 fail-close at
      real R1 frontiers.
      PROGRESS (2026-07-03, branch mdd/perm-r1-frontiers, UNMERGED — 4
      commits, ci green, 17/45 + golden held at every step): the perm-cons
      NODE-LEVEL walls fell, each validated by frontier movement in the
      real tree (never green-in-isolation): notFlg closing literals
      (implicit (not 'c) fold, both directions) + clause-context-resolution
      verify-then-drop (12038b0; also fixed a latent spine defect — the
      disjunction must walk the CLAUSE's literals, ACL2 short-circuits
      scanning at the closer); destructor elimination (replayElim: consp
      split, child at env[v1↦car,v2↦cdr], substN bridge, diffCollapse) +
      if-finish/combined (display-folded lhs → navigate the running term;
      conditional branch congruence evalOpt_congr_if_branches_cond = the
      equal-R wall-d machinery; branchFacts ctx channel) + solidify
      .branchTest + type-alist + if1/boolean + mid-chain equal-self +
      car/cdr-cons child chaining (7de8af5). perm-cons now stops at the
      BRANCH-SPLIT SPINE at *1/2'' (the last structural wall of its *1/2
      subtree). Design + ratified resolution in
      docs/notes/2026-07-03_branch-split-spine.md: clausify is
      TYPE-ALIST-FREE (if-interp's closed syntactic rule set), and the
      adopted PARTIAL LOGGING is LANDED (5043396; submodule 69d4993801):
      the ACL2 fork emits the literal-clausify DECISION TRACE
      (emit/if-interp/test|leaf + Satriani/subsumption fired-markers,
      scoped by infra/clausify-trace; raw-code fns registered in
      *initial-program-fns-with-raw-code* — required or the build fails),
      parsed into LiteralProof.splitTrace/.splitReshaped; regenerated
      corpus is behavior-neutral (golden byte-identical). The Satriani
      marker fires inside perm-cons's own literal-3 split (replacement
      resolution, visible in the leaf trace).
      MILESTONE (2026-07-03/04): the byCases COMPOSER LANDED and
      **perm-cons REPLAYS — 18/45** (commit 77cb6cf; composeSplit +
      collapseEval + parseTraceTree; branch selection by derivable
      segment-falsity with uniqueness — provably transparent to the
      Satriani replacement and the subsumption loop; residual branches
      peel the pushed sibling clause; remove-trivial-equivalences via
      byCases + diffCollapse transport). Adversarial AUDIT passed
      (claim holds; type independently verified as the verbatim mirror;
      axioms clean). Audit F1 fixed (6866121): perm-cons's mirror is
      TYPE-PINNED + axiom-gated in DriverTests (the coverage harness
      alone only Meta.checks). Audit F2 RATIFIED (MDD 2026-07-04):
      deterministic fail-closed record-directed reconstruction is in
      scope; the banned antipattern is introducing SEARCH (recorded in
      the design note). Totality prover: measured-SECOND formals
      (8096e13, totality_2_rec_snd) — rm/memb auto-discharge; perm-cons
      conditions now [total:perm, tp:memb].
      NATIVE BRIDGE DONE (eef8d77, catalog entry 9): perm-cons lifted
      end-to-end to `a ∈ xs → (xs ~ a :: ys ↔ xs.erase a ~ ys)`
      (List.Perm, axiom-clean) via Imported/Perm.lean — memb/rm/perm
      simulate List.contains/erase/isPerm; total:perm and tp:memb
      discharged by world-parametric HAND lemmas = the ratified
      INDUSTRIALIZATION DEMOS for the two named prover extensions:
      (i) totality over user-fn if-tests (conv_if_split shape),
      (ii) a TP prover (boolean body induction + arg strictness).
      MILESTONE (2026-07-05, branch mdd/perm-display-folding):
      **perm-transitive REPLAYS — 19/45** (9ed5dc1) via the RATIFIED
      theorem-dependency design
      (docs/plans/2026-07-05_theorem-dependency-hypotheses.md):
      cond[total:perm, tp:perm, rule:perm-symmetric, rule:perm-memb,
      rule:perm-rm] — rule:<thm> hypotheses (the third telescope
      species) state the STORED rules emitted at create-rewrite-rule
      ((:RULES …) events, fork a58670946d..); the with-lemma recipe
      instantiates strictly by the emitted :SUBST with
      recompute-and-check joints; hyp relief from the recorded
      :KIND HYP chain (HYP path boundary frames), the emitted
      relieve-hyp/* silent-relief markers + spine hoist of
      later-literal case splits, or the clause context. Also landed:
      emit/fncall/expand-permission (induction-machine unfolds were an
      orphaned-EXPANSION-block emission gap), the trivial-path pushed-
      sibling residual, if1/boolean two-valuedness from emitted TPs,
      if-same-branches (re_if_same), and the capture-script pipefail
      fix. AUDITED (2026-07-06, 4 Opus reviewers + verifier): ZERO
      soundness defects; all findings fidelity/generality, addressed same
      day (8098579): relief RECORDS now required per rule hyp (finding A;
      exposed + closed the free-variable relief emission family),
      non-equal rules not offered (finding E), perm-transitive
      TYPE-PINNED + axiom-gated in DriverTests, scoreboard splits
      conditional/unconditional. OPEN audit residue (all fail-safe):
      hyp relief under add-linear-lemma gets no HYP path frame (finding
      B — replay hard-fails if hit; instrument when a tree shows it);
      a book's LAST theorem's rule never flushes (finding C — matters
      for R2 include-book import, not single-log replay); forced hyps
      emit no marker (the G4 forcing seam). Rule-hyp lazy discharge from
      replayed dependency mirrors is the tracked follow-up (v1 step 5).
      MILESTONE (2026-07-06, branch mdd/multi-literal-induction, tip
      9b485d8): **6 of 8 perm-book theorems REPLAY — 23/47 (13
      unconditional + 10 conditional)** — ALL FOUR of perm-transitive's
      rule dependencies (perm-symmetric, memb-rm, perm-memb, perm-rm)
      plus perm-cons and perm-transitive. Walls felled, each
      golden-gated: multi-literal pushed clauses (induction P =
      disjunction, IH cross-product + ACL2's tautology clean-up
      mirrored, IH σ-disjunction value-walk); spine regroup;
      RHS-continuation chains; context demands generalized (type-alist
      nodes + rule markers drive the later-literal hoist);
      generalize-clause; eliminate-irrelevance (subset-clause walk);
      dead-branch display folds (folding-wall option A, data-ratified);
      collapseEval assumption resolution; CONTEXT-SUBST equality
      transport; POOL-PROCESSING emission (emit/pool-consider,
      emit/pool-subsumed, :POOLNAME on pushes — pop-clause's
      subsumption-reordered pool order was invisible, mis-linking
      nested-induction pool roots) + pool-subsumption replay
      (recomputed VALIDATED witness σ, general subtree at the instance
      env, substN bridge, instance walk); duplicate-literal skip
      (add-literal dedup after branch-substitution). AUDIT #2 PASSED
      2026-07-06 (4 Opus reviewers, findings verified inline): ZERO
      soundness defects; induction generalization sound-by-validation
      (non-circular — :SCHEME emit = ACL2's genuine post-cleanup
      clauses); fixes landed same day (03ab23b): fail-closed pool
      guards, root-statement type pin in replayProofConditional,
      coverage ✓ now = AXIOM-CLEAN (collectProofAxioms). Open audit
      residue (fail-safe): forcing-round on pool events when G4 lands;
      subsumed-by-parent unemitted; subsumer subtree DUPLICATED in
      reconstruction (replay proves *1.1.1 twice — revisit if proof
      size matters).
      MILESTONE (2026-07-06, branch mdd/perm-closure): comm-rm REPLAYS
      UNCONDITIONALLY (clause-level equal-self closer + spine routing,
      32dd5d1) and **v1 STEP 5 LANDED (52cc205): every used rule:<thm>
      hypothesis discharges from its dependency's replayed mirror**
      (dischargeRuleHyp — dependency replayed inside the consumer's own
      telescope so conditions compose transitively; mirror→rule decode =
      recompute-and-check of create-rewrite-rule's normalization between
      the two emitted artifacts; reverse-creation-order substitution;
      D6 on failure). THE PERM CHAIN COMPOSES: 7 of 8 theorems replay
      at 24/47 (14 + 10) and the book's whole obligation log is three
      base facts (total:perm + tp:memb + tp:perm — the named prover
      industrialization frontiers). perm-transitive's pin updated to the
      COMPOSED type and axiom-gated.
      **R1 COMPLETE (2026-07-06, 1836aca): ALL EIGHT perm-book theorems
      REPLAY — 26/47 (14 + 12).** The finish: wall d was an elaboration
      artifact (evrel_if_test_siff_collapse's thn/els implicits, supplied
      explicitly); booleanp added to the trusted core (Kestrel-polish
      primitive pattern; also flipped evenlen-booleanp's DP leaf to
      proved); and the MULTI-CLAUSE clausify bridge landed
      (clausifyAllFalse_sound — the conjunction lemma by the same
      11-case induct as clausifyPure_sound; bridgeClausifyMulti with
      every joint recompute-and-checked; post-clausify discharge nodes
      close dropped singleton clauses via the DP carve-out).
      perm-is-an-equivalence replays as cond[total:perm, tp:memb,
      tp:perm] — the WHOLE BOOK's obligation log is exactly the three
      base facts (the two named prover-industrialization frontiers).
      AUDIT #3 PASSED (2026-07-06, 4 Opus reviewers — bridge, discharge,
      trusted-core, outside — findings verified inline): ZERO soundness
      defects across all four. The outside reviewer independently
      reproduced the scoreboard + golden, decoded all 8 mirror
      conclusions against perm.lisp (incl. the defequiv 4-conjunct
      obligation = ACL2's own :INPUTCLAUSE verbatim), verified the
      step-5 inlining is real (rule hyps gone at HEAD with the
      dependencies' own conditions surfacing; proof terms grow
      monotonically with dependency depth), and confirmed none of the
      3 residual base facts is vacuous (all true, all emitted).
      booleanp differentially verified against real ACL2. Fixes landed
      same day: the discharge-pass catch re-throws non-frontier errors
      (dischargeRuleHyp frontier class tagged; dependency-replay walls
      re-tagged into it); booleanp probes added to scripts/diff_eval.sh;
      decode-coverage honesty note in the design doc (and-split/iff/
      not/lambda/builtin-boolean/force shapes FAIL CLOSED, not
      discharged — extend per-shape on a real tree); the equal-self
      closer rejects trailing spine items; the ClausifyBridge
      unused-simp-arg warning fixed. Known scale note (non-fidelity):
      proof terms balloon along the dependency chain (perm-equiv
      ≈557M Expr nodes — inlining + the subsumer-duplication residue;
      revisit if elaboration time bites).
      RATIFIED SEQUENCING (MDD): after perm replays, a LIFTER
      INDUSTRIALIZATION sprint (#63 + the NativeMirrors catalog
      discipline) with the perm book as driving example; replay→lift
      becomes the per-book cadence from isort onward.

Kestrel-readiness polish (2026-06-12, branch mdd/kestrel-polish): README
getting-started/bootstrap + Status & limitations sections; mirror-statement
text corrected to truthiness (post-G2); `.gitmodules` ssh→https. Primitives
`symbolp`/`nfix`/`len` added to the lift (`Logic` defs + `callBuiltin`
routing + `callBuiltin_*` rfl-lemmas + `dpUnary`/`dpLiftHeads`); cheap because
G3's `dpLiftF_sound` is generic over `dpLiftHeads`. Coverage unchanged
(17/37, ✓9 ◌9 ✗0) — the six affected theorems advanced PAST the
missing-primitive walls to their real next frontiers (mostly G5 induction).
NOTE: `len` was misfiled as a "user defun, refute" candidate — it is a
primitive (`Logic.len`), just unregistered; the build investigation caught
the error.

Alongside the G-steps: **the NATIVE MIRROR CATALOG** (task #62, MDD-ratified) —
`ACL2Lean/Imported/WaypointCatalog.lean`, one section per corpus theorem: the
native Lean statement proved THROUGH the driver's mirror (mirror → hypothesis
discharge → enc/`corr_*` simulation → native, axiom-gated), else an explicit
PENDING(blocking frontier) marker; the header table is the native-layer
scoreboard and proved entries are build-enforced regressions. The growing
`enc`/`corr_*` pattern library is the seed of a future STANDARD LIFTING
LIBRARY.

- [ ] **Preprocess-chain replay** — PART A LANDED (`replayPreprocessChain`):
      clause-level eval/abbreviation chains (formula → 't) replay with
      deterministic unique-occurrence positioning (no `:PATH` at preprocess
      sites; ambiguity hard-fails) and `executable-counterpart` nodes re-checked
      by KERNEL REDUCTION of `evalOpt` (enabled by the Env assoc-list change —
      see Layer-1 note below). Coverage 9/38 (ground-arith, sq-of-3,
      cdr-cons-refl, idf-rewrites). PART B LANDED: verdict-only discharge nodes
      compose as ordinary preprocess-node recipes (keyed by ORIGIN) —
      `replayDischargeNode` instantiates the DP machinery from the ambient
      ReplayCtx PINS + TP hypotheses (DischargeLeaf.lean folded into Driver.lean,
      all MetaM; the standalone quantified-telescope harness kept for coverage).
      Coverage 12/38 (equal-symm, equal-trans unconditional; len2-nonneg
      cond[total:len2, tp:len2]). REMAINING: (C) clausify splits — APPROVED
      DESIGN: emit clausify-input CHECKPOINTS from ACL2 (clausify-input1 is a
      pure 6-case if-recursion in acl2 induct.lisp:754, but its expand-and-or
      fallback consults the ens — recompute-in-Lean cannot be faithful;
      emission is the durable route); condition THREADING for ◌-class
      (assumed-fact) discharge composition; `definition:implies`-style
      ground-zero rune recipes (implies is an evalOpt BUILTIN — must not enter
      `groundZeroDefs`, it would shadow `callBuiltin`/no-shadow facts;
      linear-chain blocked on this).

- [ ] **Gate the clausify-checkpoint emission on preprocess HIT** (today a
      'miss pass's events flush into the NEXT step's :REWRITES — handled by
      validated no-op drops in the driver, but gating at the source is cleaner).

- [ ] **Mirror-statement boolean-validity check.** The mirror form
      `eval formula = some t` is STRONGER than ACL2's `formula ≠ nil` — equal
      only for boolean-valued formulas (all of the current corpus). The
      statement builder should hard-fail on a formula not provably
      boolean-valued (or the mirror moves to a `≠ nil` form) — surfaced by the
      clausify-bridge design, where clausify-input1's invariant is iff.

- [ ] **Solidify / IH bridge in the driver** (`equivSource` → `ReplayCtx.caseHyps`;
      the hand proofs' `evalOpt_substTerm_subst1` + `eval_equal_t_implies_eq`
      machinery, mechanized). (task #36)

- [ ] **recognizer + if-simplification nodes** — `re_if_true/false` + recognizer
      reading the CASE HYPOTHESIS (`consp x = nil/t`); lands WITH the scaffold.

- [ ] **def-unfold for REAL def shapes** — multi-arg unfold + if-body whose
      recognizer/if children do the simplification (real `my-app`/`my-len`).
      (task #34)

- [ ] **Totality from admission** — produce per-function totality from the
      termination proof (`WorldEvent.defun.termination` + the emitted measure),
      discharging the DP leaves' `total:…` hypotheses; TP corollaries are
      already consumed as hypotheses. (task #37)

- [ ] **Discharge-leaf composition** — attach `replayDischargeLeaf` proofs as
      clause children inside `replayClause` (today they are validated standalone
      per leaf in the harness).

- [ ] **convergence analyzer (G1), general** — defined-fn totality threading
      opaque witnesses for recursive calls (subsumes the c2 `hConv` hypotheses).

- [ ] **`.boundary` path frames** — child-node congruence inside an unfold /
      rule-RHS (currently hard-fail; aligns with tree child-nesting).

- [ ] **`Expr` blowup** — `let`-bind shared convergence subproofs.

- [ ] Retire/generalize the over-specialized `re_unfold*_var`.

- [ ] **DP-leaf debt:** 11/\*1/4+\*1/5' tactic residue (simp leaves a non-omega
      goal in one case — likely closable); ground-zero type facts (`len`) —
      emission decision; 03/linear-chain rationals → lean-smt (task #50).

- [ ] **Reconstruction coverage** — work through `docs/notes/2026-06-07_silent-drop-inventory.md`
      and the recon-tests findings; ensure no silent drops.

- [ ] **STRINGP DP-lift primitive**: unblocks all 16 qsort +
      sorts-equivalent rows (verified genuine — TO-BE-FOUND's disjunctive
      TP corollary, not a recon artifact).

- [ ] **Positive type-set-verdict marker (the proper J6b).** The
      `typeSetDerived` tag is classification by ELIMINATION (no positive
      marker in the log — a linker bug and a genuine type-set verdict are
      indistinguishable; fails closed at replay). Emit a marker from the
      fork, consume it in the linker, and build the value-level discharge
      recipe.

### ACL2 instrumentation (the `acl2/` fork)

- [ ] **Emission backlog** (each is a known, documented gap):
    - **Ground-zero type facts** — `len` etc. have no emitted `:TYPE-PRESCRIPTION`
      (their facts live in ACL2's bootstrap world); decide emit-at-use vs curated
      ground-zero defuns. Blocks 5 assumed DP leaves (12/16).
    - **Non-default well-founded relation / `include-book`** — lexicographic `l<`
      measures need the ordinals book; `include-book` is untested in capture.
      (See the measure plan's deferred section.)
    - **Termination-proof emission** — the admission's measure-conjecture clause
      tree (`WorldEvent.defun.termination` is parsed but ACL2 doesn't yet emit
      the per-case decrease proofs structured) — needed for c3's
      totality-from-admission.

- [ ] **Rebase the `acl2/` fork on upstream (2026-06-12).** The submodule's
      `acl2-lean-output` branch is based on an aging upstream `master`; rebase
      (or merge upstream forward) at some point. The TRACE-LOG tagging
      convention exists for exactly this — `grep -rn "TRACE-LOG\[" acl2/*.lisp`
      enumerates every inserted region, and `just check-acl2-tags` validates
      the result. After rebasing: rebuild the image, recapture the corpus
      (capture is deterministic — byte-diff the logs to detect upstream
      behavior drift), and rerun the differential harness + `just ci`.

- [ ] **Capture-harness max-line-length assertion** (audit finding 3):
      the fmt margin widen is a threshold, not a guarantee — the sorting
      corpus actively wraps at ~10k cols (qsort max line 9999) and the
      hyphen-split hazard is live. Assert headroom at capture; consider
      `write-for-read`.

- [ ] (carried) **Careful capture/emission infra revision** — see the item below;
      includes `emit/proof-failed` (positive failure signal),
      `recon-test-dump.sh`'s `|| true` (now swallows the non-zero dump exit),
      capture-heuristic re-audit, and differential-testing the EMISSION itself.

- [ ] **Careful revision of the capture / emission infra (2026-06-09).** Repeated issues
      have surfaced here (the `:DEFTHM`-count heuristic was fooled by a FAILED proof —
      a non-theorem rendered a full tree and exited 0; `let`/`let*` semantics diverged;
      untagged ACL2 insertions; measure-instantiation bug). Do a deliberate end-to-end
      pass over stages 2–4 infra, not piecemeal patches. Known sub-items:
    - **Explicit `emit/proof-failed` (the proper positive failure signal).** ACL2 knows
      when a proof fails; emit a structured `(:PROOF-FAILED :NAME …)` (or `:RESULT :FAILED`
      on the `:DEFTHM`-close) at the single event-summary choke point — there are many
      failure paths in `prove.lisp` (≈L202/610/4537/5177/7758), so find the common one.
      Then parse it (`ProofEvent`) and hard-fail reconstruction on it. **Backstop already
      in place** (2026-06-09): `buildDevelopment` hard-fails on any `:DEFTHM` block lacking
      its `:QED`; the CLI exits non-zero; `capture-proof-log.sh` warns on `qed < defthm`
      and on the "proof attempt has failed" prose. The explicit emit upgrades inference→positive.
    - Re-audit the capture script's other heuristics (source `(defthm` count vs logged,
      `:STOP-LD` suppression under `:structured`) and the `recon-test-dump.sh` `|| true`
      (which swallows the new non-zero dump exit — decide if that should surface).
    - Differential-test the emission itself, not just `evalOpt` (does the log faithfully
      reflect the proof? a failed/odd proof should be detectable from the log alone).
    - [x] ~~`abbreviation-expansion` placeholder RHS~~ — FIXED 2026-06-09: the emit now
      carries the instantiated rule RHS (`sublis-var unify-subst rhs`); 08's `cdr-cons`
      step shows `(cdr (cons x y)) ⇒ y`.

- [ ] Smaller: dotted STEP-rune corpus witness (constructed sample);
      covering-clause guard↔ruling-test correspondence; differential check
      of gz-termination-clauses recomputation vs original admissions;
      pool-shaped (clause-list) induction motive.

### Type-set / decision-procedure emission (Track B)

- [ ] **Type-set derivation facts** — e.g. `true-listp x ∧ consp x → true-listp
      (cdr x)` (a recursive-definition type-set fact; closes 01/02's 4 leaves).
      Emit the type-alist entries / rules the forward-chain contradiction used;
      consume as DP-fact hypotheses — NEVER re-derive type-set in Lean.

- [ ] **ts-bits lifting** — `:BASICTS`/`:LEAVES` bitmask facts (04's booleanp
      leaf) as DP hypotheses.

- [ ] **Linear arithmetic over rationals** — 03/linear-chain (`<`-transitivity,
      nonlinear after `toRat` cross-multiplication): beyond `omega`; the concrete
      **lean-smt** target (task #50, gated: toolchain pinning, cvc5, axiom
      hygiene).

- [ ] Tau detail (`tau-clause1p` signature/bounder rules) if the above ever
      proves insufficient — Option 1 of the direct-proof plan, deliberately
      deferred.

### Product and waypoint layers

- [ ] **Future work — polymorphic native statements.** The catalog states
      list-family results over `List SExpr` (what the current encoding
      proves). The idiomatic polymorphic forms (`∀ α, (xs ys : List α), …`)
      follow via `Rep` TRANSFORMERS (`Rep α → Rep (List α)`) — `Rep`
      composes, so this layer drops in without rework; deferred until a
      target theorem needs it.

- [ ] **Lifter industrialization (#63 — SEQUENCED 2026-06-12, MDD: after
      perm replays, with the perm book as the driving example).** The
      end-state test of the pipeline is theorems LIFTED into Lean; this
      sprint makes the mirror library a discipline, not an artifact:
      (a) the NativeMirrors catalog becomes a COVERAGE GATE — every
      driver-replayed theorem gets a native entry or an explicit
      PENDING(frontier) marker, so "replayed but never lifted" cannot
      silently accumulate; (b) Rep transformers — polymorphic
      `Rep (List α)` from `Rep α` (replacing the monomorphic
      `listRep : Rep (List SExpr)`); (c) `lift_decode` automation — the
      per-theorem formula-spine walk (composing `Implements` facts up the
      formula tree) is still manual; a small elab recursing the formula
      (as the driver's `proveConv` does) could emit it; (d) a GUARDED
      `Implements` variant (recognizer hypotheses on inputs) for
      partial/conditional ACL2 functions, fed by the emitted TP facts.
      perm's payoff statement: `perm-is-an-equivalence` as a
      kernel-checked equivalence over a native perm predicate — the seed
      of the mirror library; replay→lift becomes the per-book cadence
      from isort onward.

- [ ] **Native-theorem bridge — generalize.** Currently hand-built for `my-len-my-app`
      (List.length_append) and `app-assoc` (List.append_assoc). Systematize the
      type-morphism + simulation recipe (`docs/comms/2026-03-22_acl2-lean-bridge.md`),
      ideally driver-assisted.

### Automation convenience (explicitly NOT trust surfaces)

- [ ] **Mirror-statement builder / `gen-world`** (`WorldGen.lean`) — completeness &
      correctness for new theorems the driver targets.
      **RE-TAGGED CONVENIENCE (Mike, 2026-08-19):** this is NOT the second
      trust-note circle-breaker and not a 1.0 prerequisite. On the product
      path the user authors the idiomatic Lean `Prop` and the kernel covers
      it, so statement derivation is automation convenience; attribution
      stays review-checked and the caveat keeps its force only on the
      un-mirrored METRIC layer. Rationale + the withdrawn 1.0 bar:
      `docs/notes/2026-08-19_versioning-policy.md`.

- [ ] Replace the hardcoded frontend with **`gen-world`** output; drop hand-built
      test trees once the real tree replays.

- [ ] The **`acl2_replay` tactic** frontend (read the Lean goal, emit the proof,
      close it).

### Interpreter fidelity

- [ ] **`evalOpt` faithfulness to ACL2** — expand the differential harness
      (`scripts/diff_eval.sh`, 51/51) corpus; it is one of the two trust-note
      circle-breakers.

### Audit and correctness debt (revisit — do not drop)

- [ ] **Carve-out drift test (MDD 2026-08-02, standing revisit).**
      The widened DP-leaf premise/verdict machinery is ratified FOR NOW
      under this test: if we find ourselves writing CUSTOM PROOFS OR
      CHECKERS PER CASE, we are no longer mirroring ACL2 — we are
      building custom search to replace it. Revisit at each arc review:
      count the per-case (non-general) discharge code added since the
      last review; a growing count fails the test.

- [ ] **Vacuity-guard audit (2026-07-19, MDD-raised).** Do we have
      SUFFICIENT guards against vacuously-true results across the pipeline?
      Surfaces to assess systematically: (a) CONDITIONAL replays — a
      `cond[total:…, tp:…, rule:…]` hypothesis that is unsatisfiable makes
      the conditional theorem vacuous while displaying ✓-conditional; the
      totality/TP/rule obligations are stated precisely, but nothing yet
      demonstrates their SATISFIABILITY (e.g. discharge-on-real-instances
      spot checks, or the obligation log's eventual full discharge);
      (b) the MIRROR STATEMENT itself — contradictory/vacuous premises are
      banned by doctrine ("don't weaken the statement") but not machine-
      checked; consider a witness-evaluation smoke test per imported
      theorem (evaluate the theorem formula on concrete instances via
      `evalOpt` — a false-on-instances mirror can't be vacuously proved);
      (c) native-lift obligations (the lifter's anti-vacuity notes at the
      #63 close-out — obligation stated against the real mirror, not a
      strawman); (d) TamperTests cover statement-tamper detection — extend
      toward premise-satisfiability tamper (make a cond hypothesis false,
      expect the SCOREBOARD to show it, not a silent conditional ✓).
      Inventory existing guards first (TamperTests, native-axiom gate,
      differential corpus), then close the gaps.
      SCOPE EXTENSION (MDD): fold this into a GENERAL hardening audit
      against NON-MALICIOUS errors of all kinds — not just vacuity.
      Candidate surfaces: silent-success modes (a recipe that "succeeds"
      by proving something weaker than intended — the proveNotSpecial
      lowercase bug was exactly this class, caught only by audit);
      recompute-and-check joints that check one side but not the other;
      display/scoreboard honesty (does every ✓ mean what a reader thinks
      it means); parser leniency drift (fields tolerated-if-absent that
      should be hard-required); golden-review blind spots (error-message
      churn masking a status flip); stale-cache/partial-build hazards in
      the dev loop (the conspT lesson — sweeps passing on stale oleans);
      env/config drift between capture and replay (image version, book
      set). Method: enumerate the check-joints per pipeline stage,
      classify each as hard-fail/checked/UNCHECKED, and burn down the
      UNCHECKED list.
      SPRINT 1 LANDED (2026-07-20, branch mdd/hardening-sprint —
      `docs/notes/2026-07-20_hardening-inventory.md` is the inventory):
      G1 build-acl2 success-marker + fresh-image gate; G2 capture
      provenance sidecars + `check-log-provenance` in ci (stale/partial
      recaptures fail loudly); G3 `just golden-review` structural
      golden diff (status flips vs message churn); G4 `just
      recapture-all` whole-surface recapture; G5 proveNotSpecial
      uppercase-Prop SYNTACTIC pin + special-form rejection tests
      (DriverTests). REMAINING (design-flavored): vacuity/premise-
      satisfiability smoke tests, TamperTests premise-tamper,
      translator/WorldGen joint enumeration.

- [ ] **Exercised-infra audit (MDD, 2026-07-21): find driver/lemma code no
      corpus proof reaches.** As the buildout accumulates recipes, arms, and
      lemmas, some paths are exercised by NO replayed row — inevitable while
      frontier-chasing, but unexercised infra carries the risk that we built
      the WRONG structure and won't find out until something depends on it
      (the S4-lemma-arm precedent: kept fail-closed precisely because it had
      no consumer). Method: (a) instrument or grep-trace which driver arms /
      EvalLemmas lemmas / helper paths fire during a full `driver-coverage`
      sweep (a per-arm hit counter behind a flag, or a coverage-style dump);
      (b) classify every cold path: EXERCISED-elsewhere (tests/#guards),
      FAIL-CLOSED-guard (fine cold), SPECULATIVE (candidate for removal or a
      forcing test row); (c) for load-bearing cold paths, either add a
      corpus/test row that exercises them or remove them (no-unwired-infra
      rule). Periodic, like the de-dup review; first pass after the current
      emission arc.

- [ ] **De-dup / abstraction review of the Lean replay infra (MDD, 2026-07-21).**
      A LIGHT review pass over the driver looking for emerged patterns worth
      consolidating — we have built a lot of code arc-by-arc and duplication
      is accumulating. Known candidates from the qsort-frontiers arc alone:
      the falsity-fact derivation helpers (`deriveFalsity` exists in ~3
      variants across Compose.lean/Core.lean — segment vs residual vs vacuous
      arms); the litFact/segFact TRANSPORT-across-substitution loop
      (duplicated between the two branch-substitution justification arms in
      Core.lean); the residual "peel + ex falso" composition (spine vacuous
      arm vs composeSplit vacuous arm); the `re_if_true`/`re_if_false`
      constant-test collapse construction (identity arm, folded-collapse arm,
      collapseEval — 3 sites); `conv_if_true`-based closer plumbing (2-3
      sites in Core.lean); the `(match … with | some/none)` chainOpt
      threading idiom (`fuel_chain_eq`/`evtrue_of_fuel_eq` compositions).
      Method: enumerate the clones (grep + read), rank by risk-reduction
      (a fix applied to one clone silently missing its twin is the incident
      class), extract shared helpers WITHOUT changing behavior, golden must
      stay byte-identical.
      POLICY (MDD 2026-07-21): KNOWN clones get de-duplicated as an ONGOING
      practice — at latest as an end-of-arc increment on the branch that
      created them (the qsort-frontiers arc will carry one); this backlog
      item is the standing habit + the periodic broader sweep.

- [ ] **Sweep for heartbeat/recursion-limit raises ("heartbeat hacking" — a
      bad smell).** Audit every `withRealMaxHeartbeats` / `withRealMaxRecDepth`
      site (and any `maxHeartbeats`/`maxRecDepth` option set): each raise can
      mask a pathological algorithm (exponential blowup, deep non-tail
      recursion on big worlds) instead of fixing it, and limits tuned to make
      today's corpus pass can silently gate future books (same trap as
      corpus-calibrated budgets — see the #65 two-tier budget policy). For
      each site: justify the bound as a runaway GUARD with stated margin, or
      profile and fix the underlying recursion/cost. Added 2026-07-17 after
      raising maxRecDepth to 8192 for qsort's 206-defun world (DP-leaf
      discharge; default 512 genuinely too small for its clause terms, but
      the depth driver was not profiled).

- [ ] **Committed golden coverage-table snapshot.** Persist the DriverCoverage
      table as a checked artifact so refactor claims of unchanged coverage
      diff against a saved baseline instead of re-asserted numbers (from the
      #37 full-audit finding).

- [ ] **Systematic log↔dump fidelity checker.** The 2026-06-09 dump audit found no
      reconstruction defects, BUT the clause-tree/waterfall layer was verified
      mainly by SELF-consistency (re-dump matches `.dump`), not against the raw
      log — one reviewer over-claimed "byte-identical to expected." Two reviewers
      independently recommended a mechanical checker that re-derives every dump
      claim (steps, ids, results, runes, LHS/RHS) from the raw `.proof-log`.
      Build it; run in ci.

- [ ] **DP-proof sorry/axiom gate.** The coverage harness `Meta.check`s each
      DP-leaf proof, but `Meta.check` does NOT reject `sorryAx` — with
      `assumeFact` there is no `mkSorry` path left, but guard it mechanically:
      scan emitted DP proof terms for `sorryAx`/`Lean.ofReduceBool` (and keep the
      `#guard_msgs` axiom gates on the spike/test theorems).

- [ ] **Audit residue: relativizeFrames prefix frames are contextual, unvalidated.**
      Frames ABOVE the d-th boundary (the parent-context navigation) are dropped
      without cross-checking them against the actual nesting position; a
      log↔replay fidelity checker (see the fidelity-checker item) should
      cross-validate them. Also: strip×boundary composition (a consumed branch
      frame interleaved between residual boundary frames) is unsupported —
      fails loudly today; revisit when a real tree exercises it.

- [ ] **Verify the conditional-proof obligations are REAL statements.** The
      ◌-assumed DP facts are bound hypotheses whose statements were machine-built
      (`dpFactStmt`); spot-audit a sample against the source clauses (a malformed
      lift could state a vacuous obligation and "complete" later against the
      wrong fact).

### Build and iteration performance

- [ ] **`--tstack=524288` measure-then-remove (2026-08-19, the
      toolchain-bump arc's residue).** The explicit tstack the
      sorts-equivalent work added is now SMALLER than the v4.33 default
      (1 GB — 4.30 #12971 / 4.33 #14343), so the flag likely only
      shrinks headroom. Measure a full build without it, then remove;
      record in the bump charter
      (`docs/plans/2026-08-19_toolchain-bump-charter.md`).
- [ ] **Build-gate parallelization (2026-08-01, MDD-raised).** The dev
      machine has many cores/memory; iteration speed is gated by two
      SERIAL artifacts, distinct from what users need:
      (a) OUR GATE: `Tests/DriverCoverage.lean` is ONE module elaborating
      the whole corpus in corpus order (~13 min). The priorTrees/priorRules
      accumulation makes it LOOK serial, but the real dependency structure
      is a sparse DAG (isort needs how-many/orderedp; qsort needs perm;
      most books are pairwise independent) — splitting into per-book
      modules with explicit dep imports would let Lake parallelize the
      independent books across cores, with the golden re-assembled from
      per-book fragments. Similarly `Imported/WaypointCatalog.lean` is one
      giant module (every mirror re-elaborates on any harness change,
      ~15 min); per-book mirror modules would confine rebuilds and
      parallelize. Both are refactors of test/mirror ORGANIZATION only —
      no replay-semantics change — but the golden format and the
      accumulation-order semantics (same-book precedence, corpus order)
      must be preserved byte-compatibly or re-pinned deliberately.
      (b) USERS: care about single-theorem end-to-end replay latency, a
      different axis — intra-replay parallelism (e.g. independent DP
      leaves / independent subgoal replays within one waterfall are
      MetaM-sequential today) and is architecture-dependent (MetaM state
      sharing); assess separately, no commitment implied by (a).
      Lake already parallelizes module-level builds — the win is making
      module granularity match the actual dependency DAG.

- [ ] **Design-level perf round #2** (sequel to #65, ci 25 min → 190 s).
      New corpus scale changed the profile: 206-defun worlds make
      per-theorem telescope construction + world reflection the likely
      hotspot (rebuilt per theorem per book — cacheable per book?); DP-leaf
      discharge and the 8192-depth lifts on big clause terms are the other
      suspects. Profile FIRST (the heartbeat-hacking sweep above shares
      this: know WHAT is deep/slow), then optimize; keep the #65 two-tier
      budget policy (no corpus-tuned gates).

- [ ] **Performance, residuals (stage 2 / opportunistic).** See the note's
      as-built section. Optimization model unchanged: LIBRARY build time
      (EvalLemmas, Lifting, the lemma stack) matters little — it is built
      once and cached. What must be MINIMIZED is the pipeline latency for a
      FRESH OR UPDATED ACL2 proof: capture → parse → reconstruct → replay →
      kernel check. That is the core OODA loop for using the tool. Known
      candidates: the per-theorem lazy-totality prefix still rebuilds decide
      facts per theorem (memoize get?-fact proofs per world); reflected
      worlds are inlined as literals in harness proofs (constants would
      shrink terms and kernel time — the catalog's derive_world pattern);
      mkDecideProof over big worlds is O(world) kernel evaluation per fact;
      proof-term sharing across a development's theorems (totality proofs
      re-proved per theorem — hoist per development behind a cache); profile
      before optimizing (lean_profile_proof / coverage wall-times per file).

Parallel tracks unchanged below (emission infra revision, audit debt, gated
lean-smt).

---

## Where the record lives

- **Completed work** — in the arc's charter (`docs/plans/`) or its dated note
  (`docs/notes/`); the pre-2026-08-19 completed items and the whole arc
  journal are in
  [`docs/archive/todo-history-2026.md`](docs/archive/todo-history-2026.md),
  which also carries an arc → charter pointer table.
- **Known fidelity bugs** — [`docs/BUGS.md`](docs/BUGS.md), the single
  canonical index, cross-checked against the differential corpus by
  `scripts/check-bugs.sh`.
- **Coverage frontiers** — [`docs/notes/2026-07-22_pattern-map.md`](docs/notes/2026-07-22_pattern-map.md),
  the coverage source of truth (ci-gated by `just check-pattern-map`).
  Consult it before building new support.
- **Audits** — `docs/audits/`, by date. The most recent top-level review is
  [`docs/audits/2026-08-19_top-level-claims-audit.md`](docs/audits/2026-08-19_top-level-claims-audit.md).
- **Releases and versioning** —
  [`docs/notes/2026-08-19_versioning-policy.md`](docs/notes/2026-08-19_versioning-policy.md).
