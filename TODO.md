# ACL2Lean — project TODO

> **P4a — THE TRIO'S TERMINATION ROWS RETIRED (LANDED 2026-08-15, T1+2
> sprint; NO fork change).** `termination:COUNT-DOWN`,
> `termination:MY-EVENP` and `termination:CD2` are all REPLAYED ✓.
> P3b's "RT3 emission gap" premise was CONTRADICTED: the
> `:IF-TEST-FALSE` / `IF-FINISH/IF-TEST` marker for the `NFIX` body's
> inner collapse IS emitted by all three books, with the type-set
> ttree as its `:JUSTIFICATION` (11-custom-measure's copy is
> line-wrapped by `fms`, which is what the earlier grep missed). The
> fix was CONSUMPTION, in five pieces: `ifMarkerCitedCr` (read the
> marker's OWN cited compound-recognizer runes — the BUG-023 anchor),
> the sharp `type-set-binary-+` constant cell
> (`tsPlusConstOf (-1, 6) ↦ 7` + `inTs_plus_neg_one`), `citedCr`
> threaded through `inTsFromArgLeaves`, the ROW-DISPATCHING
> `decreaseArgInReach` (the μ-route discriminator had been applying
> the destructor-chain test to the `nfix` row too — a latent defect
> exposed the moment `termination:CD2` flipped), and
> `groundConstClose` + `conv_if_either` (the spine terminus' fourth
> closer: a clause whose recorded exec folds end in a `'T` literal).
> Golden 115/116 (99+16) — header unchanged, 3 status flips, 1 message
> churn. Charter: `docs/plans/2026-08-14_t12-sprint-charter.md` §P4a
> (J-P4a-a..i).
> OPEN AFTER IT:
> - **CD2-BOUND** — advanced through `Subgoal *1/2` and `*1/1` to a
>   THIRD frontier, verbatim: `compound-recognizer: no in-scope
>   falsity fact for (INTEGERP N) (frontier)`. Diagnosed OUT OF CLASS
>   (J-P4a-g): `Subgoal 1`'s `(ZP N) ⇒ 'T` is a TYPE-SET verdict
>   (`:TYPESET 112`, `:TRUETS -7`), and a `tsRecogTrue` entry for `ZP`
>   would be refused by `recogVerdictFromTs`'s `acl2Ok` guard —
>   from `(< N '0)` true our model gives mask 48 while ACL2 emits
>   112 = 48 ∪ *ts-complex-rational* (BUG-009: the model has no complex
>   values). Reconciling a MODEL-DOMAIN restriction with an emitted
>   mask is a fidelity design question, not a consumption arm.
> - **`tp:QSORT` ×3 (hypothetical-TP mode)** — scouted, NOT attempted.
>   `QSORT`'s own `:ALL-TPS` entry is UNCONDITIONAL; the conditional
>   rule is `TRUE-LISTP-APPEND` on `BINARY-APPEND` (hyps
>   `((TRUE-LISTP B))`, leaves `(1024, 1152)`). Needs a new data path
>   end to end (`Development.typePrescriptionAllTps` → a
>   `ReplayConfig.allTps` field → a widened `TpKit.cors`), and the
>   2026-08-13 fork-emission audit's SECOND blocker still stands
>   (discharging the hyp routes into the self-call arm, which frontiers
>   at `totLiftable` because QSORT's measured argument calls `FILTER`).

> **R3 — THE UNIFIED MEASURE/ARITY TABLE (LANDED 2026-08-14, T1+2 sprint
> phase 2; overspecialization audit F6/F7/F8 + F13).** The shape of an
> emitted `:MEASURE` used to be classified INDEPENDENTLY at five sites
> (`proveTotality`'s admission gate, `proveTp`'s `measuredOf`, the
> μ-registry `buildMeasureFn` + `replayInduction`'s route
> discriminator, `dischargeDecrease`'s walk dispatch, `derive_exec%`'s
> `MeasureSpec`) with DIFFERENT row sets — F6 found the admission gate
> alone blocking 100% of the main-row `total:` debt, on shapes its
> siblings already understood. Now ONE classifier
> (`ACL2Lean/Replay/MeasureTable.lean`: `MeasureShape` =
> count / len / nfix / sumCount / userFn, `measureShape?`,
> `MeasureShape.ofJustification?` which CHECKS the emitted `:MEASURED`
> subset, `MeasurePos` = `derive_exec%`'s positional view) plus the
> μ row (`Replay/Lemmas/MeasureMu.lean`, `MeasureShape.muHeads` —
> `nfixNat` NEW), and every consumer dispatches on it with a TOTAL
> match, so a new row forces a decision at each site.
> Landed with it: `totality_2_rec_sum_mu` + `totality_3_rec_fst_mu`
> (`Replay/Lemmas/TotalityArity.lean` — F6's sum cell and F7's missing
> first-formal twin), the recognizer-duality bridge in `totWalk`'s
> decrease kit (CONSP↔ENDP, the gap between the coverage rule and the
> proof plumbing), and the opaque-measured-actual ∃-elimination on the
> 1-ary destructor route (MSORT's `(MSORT (EVENS X))`).
> RESULT: golden 87+27 → 98+16 (row-region `total:` 44 → 23
> occurrences); `total:BNEXT` ×10, `total:MERGE2` ×5, `total:MSORT` ×4,
> `total:INTERLEAVE`, `total:ZIP3` all RETIRED; three FORBIDDEN-DEBT
> sorries deleted (5 → 2).
> RESIDUE (→ RT2, verbatim frontiers):
> - `total:BSORT` ×4 — the recorded route now REACHES BSORT (the
>   userFn/BNEXT-SIZE row is admitted) and stops at
>   `recorded decrease: non-liftable ruler (EQUAL (BNEXT X) X)`: the
>   emitted ruler mentions an opaque call, and `rulerNilConv` only
>   handles liftable rulers even though `totWalk`'s opaque-test arm has
>   already bound that test's value AND its convergence. FIX SHAPE:
>   carry the value+convergence in `totWalk`'s `facts` (today a
>   `(term, sign, signProof)` triple) so the ruler peel can consume
>   them. Secondary, on other rows:
>   `recorded route: condition linear:HOW-MANY-BAD-PAIRS-BNEXT not
>   offered by the consumer telescope`.
> - `total:QSORT` ×1 — NOT a measure-table question (QSORT's measure is
>   the plain `count` row): its decrease actual is the opaque
>   `(FILTER 'LT (CDR X) (CAR X))`, which no destructor walk can state
>   and which must NOT get a per-case registry arm (the carve-out-drift
>   test — EVENS/ODDS are registered with PROVED `CountSim` models, and
>   `consCount (FILTER …) < consCount x` is not even true in general).
>   The recorded route is the right one and DOES fire for
>   `termination:QSORT`; making it available at the consuming rows is
>   the driver-queue item (hypothetical-TP mode).
> - `total:O<` ×12 / `total:O-P` ×6 — the ordinal bootstrap (see the
>   debt registry above).
> - CD2-BOUND — NFIX is now REGISTERED for μ, and the row's frontier
>   moved to its honest next one, recorded verbatim in the golden:
>   `dischargeDecrease: the NFIX measure row has no decrease walk — an
>   NFIX decrease is arithmetic, not a destructor chain (frontier):
>   (NFIX N)`. The emitted obligation is
>   `((ZP N) (EQUAL N '1) (O< (NFIX (BINARY-+ '-2 N)) (NFIX N)))`, so
>   the walk needs (a) an arithmetic decrease lemma and (b) a general
>   in-scope-fact accessor on `DecreaseKit` (today only
>   `conspTrueOf`/`endpFalseOf`). This is the P1 arithmetic backlog's
>   first concrete demand.
> - PERM-TLFIX's catalog decision (a G1-M leftover surfaced here) is
>   `.pending` — a MIRROR-side call, left to the mirror wave.

TERMINOLOGY (2026-08-12): 'mirror'/'native mirror' below means the ACL2-like WAYPOINT layer, not a mirror in the product sense (ACL2Lean/Mirrors/). The 2026-08-12 naming sweep renamed those artifacts — the old `Imported/Mirrors/` directory is now `Imported/Waypoints/`, the old `Imported/NativeMirrors.lean` facade is now `Imported/WaypointCatalog.lean`, the old `Tests/MirrorCensus.lean` is now `Tests/WaypointCensus.lean`, and the old `just mirror-metrics` recipe is now `just waypoint-metrics`. PATH and COMMAND references below were updated to point at the real files; the surrounding narrative was left as the record it is.

> **THIN-LEAN PURGE (2026-08-11, branch mdd/mirror-provenance-purge;
> Mike's ruling — see docs/audits/2026-08-11_mirror-provenance-audit.md
> and the mirror-criterion memory).** The mirror layer's Lean-side
> content re-proofs are GONE: 41 forbidden theorems deleted, 18
> sorried as FORBIDDEN-DEBT (statements kept, `sorryAx` visible), the
> D5 gz five re-homed to `Imported/GzPrelude.lean` (predefined-only
> scope guard), the `derive_exec_tp%`/`derive_exec_total%` macros
> deleted, the hand-replay chain (SimpleWorld/AppAssoc) deleted in
> favor of the driver route. Catalog: `.nativeSorried` status (axioms
> = trio + sorryAx REQUIRED — losing the sorry forces promotion);
> 20 natives reclassified with named debt; the PROVENANCE GATE
> (in-Lean env scan) bans unregistered `dis_*`/`drv_*` in the mirror
> layer and fails any debt entry whose sorry is replaced by a proof.
> ACCEPTED REGRESSION (ruled): the three `*-IS-ISORT` capstone rows
> fell to ASSUMED ◌ (110/116) — the usefi pre-pass lost its forbidden
> dischargers; three capstone statement pins retired to git history.
> **REGRESSION REVERSED 2026-08-13** (the TP-replay arc's ATOM-leg
> increment): all three rows are REPLAYED ✓ again (113/116) with real
> cond sets, the three statement pins are back, and the capstone
> catalog entries returned as honest `.pending` (no capstone waypoint
> native exists — none was invented to satisfy the gate).
> **THE DEBT REGISTRY (each entry names its unlock):**
> - REQUIRED class (replayable — must be wired, not left sorried):
>   `dis_o_lt_total` ONLY — the ACL2 ORDINAL BOOTSTRAP. `O<` is a
>   GROUND-ZERO defun whose emitted decreases run through
>   `(O-FIRST-EXPT X)` / `(O-RST X)`, so no destructor walk states them,
>   and ground-zero defuns carry NO admission clause proof (`:SOURCE
>   :GROUND-ZERO` — nothing to replay), so the recorded route has no
>   input either. Out of scope per the overspecialization audit's F6
>   ("genuinely hard"); UNLOCK: a ground-zero admission emission (or a
>   registered ordinal measure model).
>   RETIRED 2026-08-14 (T1+2 sprint phase 2 — the R3 UNIFIED
>   MEASURE/ARITY TABLE, audit F6/F7/F8): `dis_merge2_total`,
>   `dis_msort_total`, `dis_bnext_total`. `proveTotality`'s admission
>   gate accepted exactly ONE measure shape while the μ-registry and
>   `dischargeDecrease` already carried more; with one shared classifier
>   (`Replay/MeasureTable.lean`) the LEN row (BNEXT), the two-measured-
>   formal SUM row (MERGE2, new lemma `totality_2_rec_sum_mu`) and
>   MSORT's opaque EVENS/ODDS measured actual (∃-eliminated onto the
>   existing registry decrease) all replay from the EMITTED clauses.
>   RETIRED 2026-08-13 (TP-replay arc, the ATOM-leg increment — the
>   FIRST REQUIRED-class retirement): `dis_pce_total`. PCE's emitted
>   termination clause rules on `(ATOM X)`, and the shared branch-fact
>   coverage rule (`Replay/Driver/BranchFacts.lean`) knew only
>   `CONSP`/`ENDP`; teaching it that `atom` IS `(not (consp …))` — one
>   leg, ACL2's own axiom — makes PCE's admission REPLAY (7 sorries →
>   6).
> - TP class (unlock = a TP-replay discharge route, a named coverage
>   item):
>   `dis_acl2_count_tp` (`dis_all_rel_tp`/`dis_append_tp` RETIRED
>   2026-08-13 — increments 4 and 5, below).
>   RETIRED 2026-08-12 (TP-replay arc increment 1 — the BINARY-+
>   return-path shape, discharged from ACL2's emitted corollary +
>   `:LEAVES`): `dis_how_many_tp`, `dis_how_many_smaller_tp`,
>   `drv_tp_len`, `drv_tp_mylen` (20 registered sorries → 16).
>   RETIRED 2026-08-13 (TP-replay arc increment 2 — the CONS
>   return-path shape: the `(CONSP (f …))` and `(TRUE-LISTP (f …))`
>   corollary classes, whose `CONS` closures carry per-class ARG
>   OBLIGATIONS — none / tail-only): `dis_insert_tp`,
>   `dis_sortfn1_insert_tp`, `dis_ssortfn1_insert_tp`,
>   `dis_evens_tp` (16 registered sorries → 12).
>   RETIRED 2026-08-13 (TP-replay arc increment 3 — the CALLEE-TP
>   return path: a return-path call to ANOTHER fn, whose OWN emitted
>   corollary supplies the position, proved by re-entering the
>   prover; new corollary class `.conspOrNil` (`:BASICTS 3200`) and
>   the first class IMPLICATION, `CONSP` ⇒ consp-or-nil):
>   `dis_sortfn1_tp`, `dis_ssortfn1_tp`, and the 2026-08-11 MINTED
>   `dis_bnext_size_tp` (12 registered sorries → 9). The equisort
>   AtCanonical witnesses then carried exactly ONE debt discharger,
>   `dis_pce_total` (REQUIRED class) — RETIRED by the ATOM-leg
>   increment, so **both AtCanonical non-vacuity witnesses are now
>   FULLY BACKED** (trio-clean; the catalog axiom gate's
>   sorryAx-REQUIRED entries duly failed and forced the promotion).
>   RETIRED 2026-08-13 (TP-replay arc increment 4 — ARITY 3: the TP
>   prover's 3-ary assembly, measured position read off the emitted
>   justification): `dis_all_rel_tp` (9 registered sorries → 8).
>   RETIRED 2026-08-13 (TP-replay arc increment 5 — the ARGS-VALUED
>   corollary `(IF (CONSP (f X Y)) 'T (EQUAL (f X Y) Y))`: the
>   prover's args-valued mode + the residue-argument leaf + the
>   args-valued class implication that let REV's callee step through):
>   `dis_append_tp` (8 registered sorries → 7). Main-row `tp:` census
>   18 → 10; survivors with named blockers: `tp:ACL2-COUNT` (×8 —
>   **GAP-1**: `tp-collect-if-leaves` emits CONTEXT-FREE leaf verdicts
>   (empty type-alist, `acl2/defuns.lisp:12029`), so `INTEGER-ABS`'s
>   leaves cannot certify against its class, and refined verdicts would
>   also need a fact-conditioned closure-lemma design (a ruling); plus
>   **GAP-2**: no emitted type facts for ACL2 primitives at all. Both
>   are fork-emission items. *(Corrected R0 item 7, 2026-08-13: the
>   previous diagnosis — "non-world callees `UNARY--`/`INTEGER-ABS`" —
>   is REFUTED. `INTEGER-ABS` IS a world fn: the logs carry
>   `(:DEFUN INTEGER-ABS :FORMALS (X) … :SOURCE :GROUND-ZERO)`. The
>   count was also ×7, measured ×8 on the current golden.)*),
>   `tp:ZIP2`/`tp:ZIP3` (the DISJUNCTIVE ruling literal
>   `(IF (ATOM X) (ATOM X) (IF (ATOM Y) …))` in the emitted
>   termination clause — a `dischargeDecrease` matcher frontier, the
>   same one that keeps `total:ZIP2`/`total:ZIP3`; outside TP scope),
>   `tp:QSORT` (its `BINARY-APPEND` leaf's ACL2 verdict 1024 rests on
>   ACL2's INTERNAL type-set for append; the EMITTED corollary
>   `(consp … ∨ = Y)` cannot give `TRUE-LISTP` — a FORK EMISSION item
>   (scout first), never a Lean-side derivation).
>   `tp:ZIP2`/`tp:ZIP3` CLEARED 2026-08-13 by the ATOM-leg increment
>   (the IF-normal-form decomposition + the ATOM leg together read the
>   disjunctive ruler); main-row `tp:` stays 10 because QSORT-IS-ISORT
>   re-greened and brought qsort's two survivors (`tp:QSORT`,
>   `tp:ACL2-COUNT`) onto a second row: 7+1 → 8+2. `total:ZIP2`
>   cleared with it; `total:ZIP3` did NOT, on an UNRELATED frontier —
>   `proveTotality`'s 3-ary self-call assembly requires the measured
>   formal to be the SECOND formal, and ZIP3 measures its first
>   (probe-verified message: "3-ary measured formal X is not the
>   second formal").
>   NOT mintable and still
>   blocking ORDEREDP-BSORT/HOW-MANY-BSORT:
>   `linear:HOW-MANY-BAD-PAIRS-BNEXT` — the `linear:` class has NO
>   existing unlock (route = linear/DP replay, or a ruling).
> - R-lane class: `dis_convert_perm` (unlock = PERM-TLFIX replay →
>   CONVERT-PERM-TO-HOW-MANY discharged via the replayed tree).
> - usefi class (the THIRD unlock class, ruled 2026-08-11 — it is
>   what regressed the capstones): the `usefi:` kept conditions on
>   the three `*-IS-ISORT` rows. Unlock = the alias-world usefi
>   discharge with totality via `termByFn` ONLY (the replayed-
>   admission route; the named-constant injection channel is deleted
>   — ruled invariant). **CLASS EMPTY 2026-08-13**: the ATOM-leg
>   increment supplied PCE's totality by exactly that route, the usefi
>   discharge succeeded, and `usefi:` + `ASSUMED:fi-self` both went
>   3 → 0 on the main rows. Census: `just waypoint-metrics`.
> **GATE-CRUFT AUDIT (Mike, 2026-08-11 — the gates-are-speedbumps
> memory):** inventory EVERY gate (the catalog five + usage + shape +
> extra-natives + the check-* scripts), rank by trust-value ÷
> fragility, and RUTHLESSLY DELETE the fragile cruft: the load-bearing
> trust is the DESIGN (small high-trust statements over the TCB —
> axiom-exactness checks); everything else is a lightweight anti-cheat
> speedbump, never adversarial-proof, kept only while cheap. Prime
> suspects: count floors, name-pattern predicates, the enumerated
> census, satellite filters. First pass = a dimension of THIS arc's
> exit audit (it added three gates); recurring thereafter at family
> boundaries. Never fix a crufty gate by adding another gate.
> **THE TWO-STANDARD RULE (the process fix, same day):** gates are
> reviewed to the DETERRENT standard — catches the honest mistake?
> simple enough to never be wrong? could we delete it? — NEVER "can
> a motivated construction evade it" (that question manufactures
> infinite hardening; today's evasion-A/B → shape/usage gates was
> generation 1 of that race — it stops here). Adversarial
> refute-by-default review is reserved for semantics, claims, and
> records. Every speedbump gate gets a threat-model comment ("a
> speedbump against forgetting, not a barrier against circumvention;
> do not harden it"). The gate-cruft audit is a DELETION review under
> the honest-mistake standard, not an attack round. Immediate arc
> items: threat-model comments on the usage/shape/extra-natives/
> provenance gates (after the in-flight executor lands — inert files
> meanwhile); propose the two-standard rule for CLAUDE.md's audit
> section at the arc merge.
> The capstone rows/pins/catalog entries return as these retire. The
> mirror-wave arc (bsortL + pending mirrors) must follow the win
> states: discharge via replay or stay honestly conditional/sorried —
> never mint new dischargers.
> **POST-PURGE AUDIT RESIDUE (2026-08-11 verification + framing
> audits; fix round applied same day):**
> - F2 (probe-confirmed limit): the provenance gate is name-prefix
>   only — renamed content lemmas are invisible to it. RESOLUTION
>   HISTORY: the shape gate + `hreplayed`-usage check were built as
>   ruled (2026-08-11), then the SHAPE GATE WAS DEMOTED the same day
>   by the gate-cruft deletion review (two-standard rule) to the
>   printed census in Tests/WaypointCensus.lean — a watched number
>   reviewed at book-family audits, never a build failure. The usage
>   check remains (floor deleted; EvTrue-migration tripwire: DELETE
>   the gate when the predicate stops matching, never teach it
>   EvTrue). See docs/notes/2026-08-11_thin-lean-boundary.md + the
>   gate-cruft review in the arc exit report.
> - F6 (pre-existing hole): `Waypoints/P8ClausifyDetail.lean`'s
>   `cons_neq_detail_native_driver` is a native mirror with no golden
>   row and no catalog entry — outside the seam/axiom gates (clean
>   trio today, verified 2026-08-11). Bring it under the catalog or
>   rule it out of scope.
> - F5 (note): the sim two-valuedness `*_t_or_nil` deletions were
>   liveness-driven, not class-driven — `membExec_t_or_nil` died with
>   its parent while four siblings survive; re-derive freely if a
>   future decode needs one (allowed DECODE-support content).

> **VOCABULARY FOLLOW-UP (naming sweep, 2026-08-12) — DONE
> 2026-08-12 (the replayed-statement pass).** The replay driver's
> third co-opted sense ("mirror" = REPLAYED STATEMENT, class D/E of
> the sweep report) is retired: identifiers renamed repo-wide
> (depMirrorProofAt→depReplayedProofAt, mirrorRegistryExt→
> replayedRegistryExt, mirrorConst→replayedConst, recMirror→
> recReplayed, term_mirror_→term_replayed_, the `mirrors :
> ReplayedRegistry` parameter→`replayed`, p5MirrorLog→p5Log, the two
> spike theorems `*_mirror`→`*_replayed`), prose rewritten across
> Replay/**, the statement pins, Imported/** residue, the root
> modules and docs/BUGS.md (BUG-019/012; header now points at
> docs/LEXICON.md). Every surviving "mirror" in the tree is
> product-sense (ACL2Lean/Mirrors/, check-mirrors-pure), verb-sense
> ("mirrors ACL2's X"), or inside a dated historical doc.
> KNOWN RESIDUE (deliberate): `acl2_samples/**/*.lisp` book comments
> still say "mirror" — those sources are SHA-pinned by the capture
> sidecars, so a comment edit is a check-log-provenance SOURCE-DRIFT
> failure; fix opportunistically at the next recapture of those books.

> **THE FIRST MIRRORS (pathfinder arc, 2026-08-12; third landed
> 2026-08-13):** `MirrorProofs/Basics.lean` — app_assoc_int
> (trio-clean) + len_app_int (TRIO-CLEAN since 2026-08-12: its
> inherited `drv_tp_mylen` debt retired by the TP-replay route, B1
> inc-1) + **len_revAcc_int** (trio-clean; Basics-closeout arc
> increments A+B — the 14-accumulator book's LEN-REV-ACC row promoted
> from `.pending` to `.native` on the back of a `derive_exec%` /
> `derive_sim%` REV-ACC kit, `ACL2Lean/Imported/RevAcc.lean`).
> THE LIST (now 8 items, in the file header) = the transfer kit's
> measured requirements: embed kit + injectivity plumbing (C1),
> the hom/agreement squares (C2 mirror_iso%), waypoint crossings +
> transport assembly (C3), the vocabulary-alignment design point
> (B5/C3), and item 8's new structural demand — an accumulator
> square GENERALIZES over the accumulator, so `mirror_iso%` must
> quantify non-measured arguments inside the motive.
> Expectations-not-gates per Mike's ruling (the charter's arc log has
> it verbatim).

> **G1 R-LANE LANDED (T1+2 sprint Tier-1 item 1, 2026-08-14 — option M
> per docs/notes/2026-08-14_g1-design-brief.md).** The
> R-parameterized rewrite lane's MINIMAL form: an R payload lives for
> exactly one frame and collapses at the node's own congruence frame.
> Pieces: `:GENEQV` parsed (`RewriteStep`/`StepProvenance.geneqv`) and
> REQUIRED to name the collapsed R (fail-closed); the solidify literal
> decode generalized from EQUAL-headed to any in-scope equivalence head
> (`solidifyRFact` — `logic_not_nil_ne` + `evtrue_of_conv_ne_nil`,
> stopping at `EvTrue (R a b)` since there is no value equality);
> `collapseAtCongruenceFrame` + `equivOwnPosCongr` FACTORED into the new
> `Replay/Driver/NodeCore/Congruence.lean` so the preprocess chain and
> the rewriter's literal-chain walker share ONE collapse; `NodeRec.node`
> widened to `Expr × Option RPayload` with every non-collapsing consumer
> hard-failing on `some` (`recNodeEq`). RESULT: **PERM-TLFIX → REPLAYED
> ✓ UNCONDITIONAL** (was the golden's only R-class red) and
> `cond[rule:PERM-TLFIX]` retired from CONVERT-PERM-TO-HOW-MANY.
> Load-bearing check: with the cross-book `PERM-IS-AN-EQUIVALENCE`
> replayed statement removed from the telescope the row FAILS at "0
> step-cited equivfull hypotheses" — every property of PERM is consumed
> from that REPLAYED theorem, none assumed.
> OPEN (recorded, not worked around):
> - the class-D consumption (`cov-cong-consume`, pinned 3/4 in
>   `Tests/PatternPins.lean`) stops at a SYNP-guarded R-rule — ACL2's
>   `syntaxp` becomes a stored-rule HYPOTHESIS (`(SYNP 'NIL '(SYNTAXP
>   …) …)`) and the R-fact route replays hyp-free rules only. SYNP
>   relief is a stored-rule hyp class, not a congruence question;
> - that same R-step's own `:RUNES` are `((:DEFINITION SYNP))` — the
>   licensing `(:CONGRUENCE …)` appears only in the CLAUSE-level
>   `:STEP :RUNES`, so past SYNP the step-level BUG-023 anchor would
>   still find nothing cited. The queued `:CR-RUNE` fork item (brief
>   §Q2 — emit the licensing rune at `find-rewriting-equivalence`'s
>   push site) fixes both lanes' anchor at the source;
> - `dis_convert_perm` is NOT retired by this lane (its unlock is the
>   discharge pass, not the replay row) — the R-lane class note above
>   should be read with its replay blocker now GONE.

> **BASICS 6/6 (R1 item A, 2026-08-14).** The remaining three Props —
> `app_nil_int`, `rev_app_int`, `rev_rev_int` — are proved at `Int`,
> all trio-clean, off the 02-rev book's APP-NIL / REV-APP / REV-REV
> rows (those catalog entries promoted `.pending` → `.native`).
> Decode-layer only, as the fork audit predicted: a new APP/REV kit
> (`ACL2Lean/Imported/Rev.lean` — `derive_exec%` × 2, `derive_sim%`
> × 2, the ALIGNED reading `revL`) plus the three world-parametric
> seam decodes. The two CONDITIONAL rows'
> `(implies (true-listp x) …)` antecedent is DISCHARGED at the
> encoded instance by `Lifting.trueListp_enc` — no transport-level
> notion of hypotheses was needed. `mirror_transport%` grew ONE
> general rung (push the map into the goal, for a spec `Prop`
> carrying a closed list literal like `app xs [] = xs`); the three
> pre-R1 transports still close on the original rung. THE LIST is
> now TEN items. STILL OPEN nearby: the 01-multi-theorem APP-NIL row
> stays `.pending` — the decode exists and is world-parametric, only
> a waypoint entry over the 01 world is unbuilt.

> **THE MIRROR GENERATORS ARE IN (Basics-closeout increments C+D,
> 2026-08-13) — master-plan C2+C3 v1 landed for the basics slice.**
> `ACL2Lean/MirrorProofs/IsoGen.lean`: `mirror_iso%` (the SQUARE
> generator — `agree` / `hom list` / `hom scalar`, induction driven by
> `fun_induction` off the mirror definition's OWN recursion, so item
> 8's accumulator demand is met by construction) and
> `mirror_transport%` (the CROSSING + the mirror theorem from one
> declaration; the user still writes the statement and the receipt).
> VALIDATED BY RETIREMENT: all six hand squares, all three hand
> crossings and all three hand transports regenerated same-name with
> BYTE-IDENTICAL `#check` types (15/15 declarations), zero hand proofs
> left in `MirrorProofs/Basics.lean`; the transfer kit
> (`Acl2Embed`/`intEmbed`/`map_inj`, LIST items 1+4) moved into IsoGen
> unchanged. THE NUMBER (Track REAL's metric): USER LINES PER MIRROR
> 23/20/26 → 9/9/10 (69 → 28 for the three, 2.5×); a fourth mirror
> over already-squared functions costs 3 lines. The square closer's
> fixed rungs are `rfl`-lemmas ONLY (pinned in the file) and the only
> per-invocation input is DEFINITIONS to unfold — a lemma there is a
> hard error, so the content channel stays shut. Gate probes recorded
> and reverted: the reassociating `revAcc` reading, a drifted square
> class, a lemma in `unfold`, a wrong arity, a mismatched waypoint
> theorem, a missing hom square — all six fail closed with the ruled
> messages. STILL OPEN for C: non-list argument/result readings, order
> instances (C1's other embeddings), and the item-3/7 dissolve (waypoint
> statements generated in mirror vocabulary).
> — the ARGUMENT half of that "still open" line LANDED with R1 item B
> (next entry).

> **PER-BINDER ARGUMENT READINGS (R1 item B, 2026-08-14 — audit finding
> F1 closed).** `mirror_iso%` no longer collapses the binder telescope
> to an `allList` boolean: `mirrorFnShape`
> (`ACL2Lean/MirrorProofs/IsoGen.lean`) returns a per-binder READING
> VECTOR inferred from the spec's own Lean binder types — `.list` for
> `List α` (enters the hom statement under `List.map e.enc`), `.elem`
> for the element type `α` itself (enters under `e.enc`), a hard error
> naming the OBSERVED type for anything else. NO new user syntax (the
> mirror level, unlike `derive_sim%`'s, can infer the reading). All 23
> generated Basics artifacts re-`#check` BYTE-IDENTICAL. Witnesses read
> off the sorting spec, landed in the new
> `ACL2Lean/MirrorProofs/Sorting.lean`: `filterRel` (function-valued
> argument) was the pinned frontier — DISSOLVED by R1-E, next entry;
> `howMany`'s `agree` square now
> ELABORATES (the widening's positive witness); `insertOrd` reaches the
> ORDER-INSTANCE blocker (`TotalOrder SExpr` — R1 item C / R4), not a
> shape one. OPEN, both needing a ruling (recorded on that page):
> (1) instance binders are NOT threaded, so every `hom` square of an
> instance-carrying spec fails at synthesis — R1 item C's substance;
> (2) element arguments make the CLOSER want the embedding's
> INJECTIVITY (`e.enc a = e.enc b → a = b`), which is not a `rfl`-lemma
> and therefore not admissible to the fixed ladder as it stands.
> The `hom scalar` class needed NOTHING for a `Nat` result — it carries
> no result codec at all (scalar invariance), so that charter question
> adjudicated clean.

> **FILTER RE-RENDER + THE PASS-THROUGH READING (R1-E, 2026-08-14 —
> ruling batch item 3).** Ruled principle, now in `docs/LEXICON.md`'s
> mirror entry: a mirror is the CLOSEST IDIOMATIC LEAN analog of the
> BOOK — step (1) of a two-step use, step (2) ordinary Lean reasoning —
> so closeness to the book beats Lean-idiom polish. Applied:
> `Mirrors/Sorting.lean`'s FILTER is now the book's `(filter fn x e)` —
> `inductive RelMode` (all four of the book's modes) + `relMode` (=
> `REL`) + `filterRel (fn : RelMode) (e : α)`, with `qsort` calling
> `filterRel .lt p t` / `filterRel .gte p t` (pivot = `(car x)`, list =
> `(cdr x)`, as the book does). The 13 target `Prop`s and every other
> spec declaration are BYTE-IDENTICAL across the change (`#print`
> baseline), which needed one new spec declaration: `decEqOfOrder`, a
> `local`, low-priority `DecidableEq` derived from the order
> (antisymmetry + decidable `≤`), so the book's `(not (equal i j))` can
> be spelled without `qsort` acquiring a `[DecidableEq α]` binder —
> BLESSED as written (Mike, 2026-08-14); no review outstanding.
> `mirror_iso%` gained the third argument reading `.fixed` — an
> explicit binder whose type is CLOSED (no free variables, so no
> occurrence of `α`) passes through both sides of a square unchanged;
> function-over-`α` arguments still hard-error (message now names three
> derived readings). W3 is now a RECORDED frontier, not a pin: both
> `filterRel` squares BUILD their statements and neither closes.
> OPEN, needing a ruling (measured, recorded on the witness page):
> (1) `hom list` wants the embedding to respect the ORDER — W1's
> frontier in FILTER vocabulary; (2) `agree` wants (a) one ladder rung,
> `Bool.decide_eq_true` (`decide (b = true) = b`, a `cases`-lemma, so
> outside the pinned `rfl`-only criterion) and (b) a way to declare a
> square at a SPECIFIC mode (`vars` takes identifiers, and
> `registerSquare` is fail-closed at one `agree` square per definition,
> so four per-mode squares cannot be registered). With a mode-
> specialized reading + that one rung, the per-mode square CLOSES
> (measured both ways, `.lt` and `.gte`). NOTE, for the compliance
> census below: `Worlds.Sorting.filterL` is `xs.filter (…)` — a SIXTH
> library-vocabulary reading the five-item census did not list.
> [R4 wave 0 refined (b): "mode-specialized" here means the READING is
> dispatch-free — instantiating the mode ARGUMENT is not the same thing
> and does NOT close. Next entry.]

> **R4 WAVE 0 — the rung LANDED, the enum-refinement registry BLOCKED
> (2026-08-14, branch `mdd/r4-wave0-refinement`; charter
> `docs/plans/2026-08-14_r4-wave0-charter.md`).** Ruling 1 landed:
> `Bool.decide_eq_true` is in `mirror_square_close`'s fixed kit and the
> pinned criterion reads "`rfl`-lemmas + TWO named plumbing families —
> the embedding's `inj` iff, and Bool/decide coercions", with the
> content-free rationale (it collapses two spellings of ONE Bool;
> it relates no operations and cannot rescue a misaligned square) and a
> statement pin in `LadderPins`. Regression net byte-identical (598
> lines, statements AND proof terms). Ruling 3 landed (`decEqOfOrder`
> blessed, above). Ruling 2 — the ENUM-REFINEMENT registry — NOT BUILT:
> the charter's ESCAPE HATCH fired on its own first trigger. Measured
> (`.tmp`, four modes each, statement shape `filterRel <ctor> ev xs =
> filterL <mapped literal> ev xs`): the ruled ladder FAILS all four;
> the ruled ladder + ground evaluation (`decide := true`) + `ite`'s own
> two cases CLOSES all four; R1-E's dispatch-free measurement
> reproduces unchanged. Cause: `filterL`'s `relL` dispatches at runtime
> (`fv == symV "LT"`), and the fixed closer cannot evaluate a ground
> `SExpr` comparison — `Worlds.Sorting.symV` is PRIVATE, so it is
> neither nameable in `unfold [...]` nor matchable by the existing
> dispatch `rfl`-lemmas `relL_LT`/`_LTE`/`_GTE` (simp matches up to
> REDUCIBLE defeq). OPEN, needing a ruling: admit GROUND EVALUATION to
> rung 2 (new in kind — a closer capability, not a lemma; rung 1 is
> bare `rfl` and already computes) plus `ite_true`/`ite_false`
> (`rfl`-lemmas, the analogue of the admitted `cond` pair) — or rule
> the reading side instead (a dispatch-free per-mode reading, which is
> what the real waypoint drivers already speak). The registry was not
> landed without a live consumer (the "infrastructure now, wire it
> later" ban). Frame recorded per the ruling: DATA REFINEMENT, in
> `IsoGen.lean`'s header + `docs/LEXICON.md`. `hom list` re-probed:
> residual byte-identical to R1-E's (order-field frontier, unchanged).

> **R4 WAVE 1 — THE SQUARE WAVE: 5 new LIVE squares, the ORDER
> DIMENSION landed, 3 new recorded frontiers (2026-08-14).** The
> witness page `MirrorProofs/Sorting.lean` goes 3 → 8 live squares.
> NEW MACHINERY (flagged for Mike at merge): `OrderedEmbed`
> (`MirrorProofs/OrderBridge.lean`) — `Acl2Embed` plus
> `ord : (enc a ≤ enc b) ↔ (a ≤ b)` — consumed through a new
> `mirror_iso%` clause `embed S via [fields]`, which binds the richer
> embedding in THAT square's statement and hands exactly the named
> fields to THAT square's closer. The design point: an order-using
> definition's homomorphism square is NOT TRUE for an arbitrary
> embedding, so the order-respect fact is a HYPOTHESIS OF THE
> STATEMENT, not a rung of the ladder — scoped and visible exactly
> like a registered callee square, proved per instance
> (`intOrderedEmbed`, off `lexorderB_intEmbed`), and unable to rescue
> a misaligned square (tamper-probed: dropping the clause makes
> `insertOrd`'s hom square FAIL). LADDER: `ite_true`/`ite_false`
> added — `rfl`-lemmas, `ite`'s own two cases, the twin of the
> already-admitted `cond` pair, pinned in `LadderPins`. THE LINE
> HELD: lemma rungs that meet the criterion, never a closer
> CAPABILITY (both capabilities measured this wave — W7's case split
> and W3's ground evaluation — are recorded, not taken).
> LIVE: `insertOrd_map_hom`, `isort_agree_isortL`, `isort_map_hom`,
> `evens_agree_evensL`, `evens_map_hom` (all `#guard_msgs`-pinned).
> FRONTIERS, recorded verbatim on the witness page: W7 `merge2`
> (both classes; 3 of 4 cases close, case 2 is the book-faithful
> UNDESTRUCTURED second arm `| xs, [] => xs`, whose guarded equation
> the template cannot use — measured closing condition: ONE case
> split on that argument, then the existing kit, both squares, all
> cases); W8 `msort` (both classes; reduces to exactly `merge2`'s
> corresponding square and nothing else — unblocked by W7 at two
> four-line declarations); W9 `odds` (both classes; NON-RECURSIVE
> spec definition, so `fun_induction` has no theorem — the same
> general bound as `relMode`/`permWitness`; fix shape = a template
> fallback to `fun_cases`. Second, independent gap: there is no
> `oddsL` waypoint READING and no ODDS EXEC KIT to validate one
> against, so the `odds` AGREE square needs an exec kit first).
> OUT-OF-SCOPE MEASUREMENT worth a ruling: W3 `filterRel`'s `hom
> list` frontier — recorded at wave 0 as "the order dimension
> `Acl2Embed` has no field for" — is DISSOLVED by `OrderedEmbed`;
> the residual is now one Bool coercion (`if false = true then …`),
> and with `Bool.false_eq_true` (the already-admitted Bool/decide
> family) the square CLOSES. Regression net: 1455 lines
> BYTE-IDENTICAL, statements AND proof terms. Sorries 6.

> **TEMPLATE-GATE FINDING (Basics-closeout increment A, 2026-08-13 —
> RULED 2026-08-13 by THE VOCABULARY RULE, commit a07d99d: native
> readings and mirror definitions are OWN-DEFINITIONS, so the leak below
> is unrepresentable and the gate is clause-independent; enforcement is
> expectations, per the standing ruling. Kept for the record.)** The
> `derive_sim%` gate's decisive case was
> exercised on REV-ACC both ways. Driving the induction off the
> NATIVE READING'S OWN recursion (`induct functional`), the
> reassociating reading `xs.reverse ++ acc` FAILS with the ruled
> misalignment error — the gate works as ruled. But the same
> reassociating reading PASSES when the invocation supplies
> `induct structural xs generalizing acc`: the bridging facts are
> `List.reverse_cons` + `List.append_assoc`, both in Lean's DEFAULT
> simp set, which is precisely the bound `Imported/SimGen.lean`'s
> threat-model note already declares known-and-accepted. So the
> accumulator class is NOT categorically fail-closed — it is
> fail-closed only under the `functional` induction clause. Options
> (a ruling, not an executor call): restrict/derive the `induct`
> clause, or record the caveat and keep the per-book-family
> provenance audit as the backstop. DO NOT "harden" the closer.

> **GATE-FLOW GAP (TP arc increment 1, needs a ruling or a recipe
> fix):** the coverage repin flow is circular — a book whose section
> differs ERRORS, so the aggregate never assembles
> `driver-coverage.actual` for `coverage-repin` to copy. Increment 1
> worked around it by mechanically assembling the candidate from the
> per-book `.section` artifacts (replicating the aggregate's own
> rules) and then having the re-run sweep VERIFY it byte-exactly. Fix
> options: teach the aggregate to assemble-and-diverge instead of
> erroring, or ship the assembly script; the current recipe text
> cannot work as written.

> **VOCABULARY-RULE SCOPE (exit audit 2026-08-13, two items):**
> (1) COMPLIANCE PASS: five pre-existing derive_sim% readings use
> library functions in their bodies (Perm contains/erase/isPerm,
> Sorting count/append) — the sim_iso_close lane (default simp +
> grind) is vocabulary-dependent, so rewrite those readings in own
> vocabulary (own contains/erase/count defs) at the next waypoint
> touch; the isPerm reading is the exact P1 shape.
> **FOUR REMAIN (R1-D, 2026-08-14):** the HOW-MANY reading is now the
> own-definition `Worlds.Sorting.howManyL` (ruled after `List.count`
> surfaced inside a mirror-square residual); every consumer respelled,
> no statement changed beyond the reading's own spelling and no
> downstream proof needed adjusting (nothing was leaning on a
> `List.count` lemma). Left: Perm contains/erase/isPerm + Sorting
> append. (2) RULED
> (Mike, 2026-08-13 — disambiguate hard, as design practice): spec
> body constructs mirroring a BOOK FUNCTION are own-definitions
> (filterRel=FILTER, rm=RM — applied); pure-Lean idiom fully
> qualified or an own device (iterate — applied); operators (++/∈)
> permitted; waypoint READINGS own-definitions required (the
> compliance pass stands); the linter covers names. Practice, not a
> gate.

Running backlog across all tracks. Keep this current: update when a milestone lands,
scope changes, or a new gap/frontier is found (see the injunction in `CLAUDE.md`).
This is a living index, not a spec — design detail lives in `docs/plans/` and
`docs/notes/`.

> **SORTING-ENDGAME ARC (2026-08-10/11, branch mdd/sorting-endgame) —
> 113/116, sorting 77/78; every claim point full-gated TRUE_EXIT=0.**
> (1) Scout F REFUTED the order-derived-entry theory (the :TA-ENTRY is a
> verbatim tail clause literal — rewrite-clause-type-alist item (a));
> item F became a CONSUMER fix (the taEntry demand hoist) and the
> LEXORDER-ORDER rung retired. (2) Fork batch E+H+I landed (submodule
> → 56de33b5a1): emit/dedup-drop at BOTH member-term drop sites;
> :TERMINATION-RUNES (per-admission, boxed-empty distinguishable);
> :TAU-BASIS (the fn-restricted slice, gz fns trimmed to tau-pair
> identity after the cited-symbol-closure bloat diagnosis — deviation
> documented). (3) Consumers: dedup read-off (expiry retired),
> leaf-rune gating (tau slice gate + the admission-channel gate), the
> tau EVG premise (rule_premise_fact_evg) → HOW-MANY-RM-GENERAL ✓
> (ablation-verified). (4) 2e landed: consumeExpandDetail (detail
> chains as VALUE equalities over EQUAL-headed carriers; nilEquiv
> remains the designed fallback, loud frontier), the recorded-drop
> clausify relaxation (clausifyPure_sound_sub), the positioned
> unresolved probe → ORDEREDP-WHEN-BNEXT-CONSTANT ✓; the p8 pattern
> book at its MDD completion criterion (green + native mirror
> cons_neq_detail_native_driver). (5) W3 one-hyp lift (fn-free hyp
> crossing + hyp-free-consumer weakening) → BSORT-IS-ISORT ✓ (usefi
> DISCHARGED, fi-self gone); seven statement pins in
> Tests/SortingPinsEndgame (a new architecture: pinned against the
> sweep's own registered constants). REMAINING for sorting 78/78:
> PERM-TLFIX only (the R-lane rung-3 arc, design pinned).
> EXIT-AUDIT FOLLOW-UPS (tracked, not landed): (a) emit `:PATH` on the
> two expand-and-or detail emitters (acl2/induct.lisp
> preprocess/equal-self + preprocess/if-iff) so consumeExpandDetail's
> position is READ, not located — the ambiguous both-branches case now
> hard-fails (outside 3.1); (b) the tau leaf-rune gate is FN-granular,
> not rune-granular (the slice does not record which rules FIRED —
> exact-fired threading is the ruled later tightening, outside residual
> 4); (c) TRUE-LISTP-RM name collision across ordered-perms (local
> :REWRITE) and convert-perm (:TYPE-PRESCRIPTION) — the cond label
> cannot distinguish them (outside 4.3); (d) allowRune matches only
> :REWRITE/:LINEAR classes (over-filtering, fail-closed — inside 10);
> (e) HOW-MANY-RM-GENERAL's native mirror (the catalog .pending) and
> the bsort-cluster natives; (f) negative/tamper tests for the arc's
> four new acceptance gates (inside 15) — the attempted p8-based
> dedup-gate tamper turned out untestable there (p8's drop rides the
> TAUTOLOGY path, out=NIL, so the recordedDropHit gate never fires);
> the right vehicle is a dedicated pattern book whose clausify keeps a
> commuted duplicate WITHOUT a complement close, authored + captured
> per the synthetic-books amendment.

> **D2 RESOLVED (2026-08-08, 4c6eb6a, full claim-gate TRUE_EXIT=0):**
> both STRONG capstones (MSORT-IS-ISORT, QSORT-IS-ISORT) discharge the
> functional instantiation IN-SWEEP — usefi: gone from both rows,
> conds now the applied consumer hypotheses; golden repinned (delta =
> the two reviewed rows; 104/116 unchanged). The scaling machinery is
> the first working instance of the compositional-replay architecture.
> Phase 3 residuals remaining: D1 (witness-TP dis_* + the R-lane user
> checkpoint), D3 (BSORT composition, ceiling ◌), D4 (audit-hardening
> items). Branch mdd/phase3-r7b remains the merge candidate.

> **CLOSE-OUT queue item 1 DONE (2026-08-08): D1's in-scope half.**
> Witness-TP kits landed (`Imported/EquisortWitness.lean`); ALL SIX
> AtCanonical constraint `rule:` premises PER CONSTANT discharge
> (wording corrected per close-out audit m7 — the emitted
> `(:CONSTRAINTS …)` events carry six formulas per scope) (inner-ctx
> augmentation: tp/total/equivrefl proof-term entries + demand-driven
> iterated rule pre-discharge in `instantiateParametricAt`); FOUR new
> D5 prelude constants (DEFAULT-CAR, DEFAULT-CDR, CONS-CAR-CDR,
> FOLD-CONSTS-IN-+ in `Replay/GzRules.lean`, WP3-pinned) replace the
> retired Imported/Sorting hand kits corpus-wide — sweep rows citing
> those boot rules discharge them instead of keeping conds (golden
> repinned). AtCanonical KEPT residue = 2 premises with named
> out-of-scope blockers (PCE-chain/R-lane; ORDERED-PERMS tau dp-facts)
> — see the deferral log's D1 close-out update.

> **CLOSE-OUT queue item 2 DONE (2026-08-08): D4's gz agreement-lemma
> half.** TEN new `gz_def_*` lemmas (Derived.lean: IMPLIES, IFF, EQL,
> FORCE, HIDE, IFIX, NATP, POSP, ZP, EVENP) + the fail-closed
> `check-gz-agreement` ci gate (script parses builtinNames + corpus
> snapshots; LEXORDER/EXPT flagged with justification; flag-rot
> detected). Scope-in-force refinement stays deferred (no driving
> book). Queue item 3 (D3/BSORT): bounded attempt closed as
> LOG-AND-MOVE-ON with the exact composition plan in the deferral log
> (node anatomy dumped; the FI arm needs a chain→clausify→verdict
> traversal — its own Core.lean arm; ceiling ◌ regardless).

> **CLOSE-OUT AUDIT (2026-08-09, 2 Opus reviewers inside/outside) —
> fix round applied.** Convergent MAJOR (M1/O-4): the AtCanonical
> docstrings claimed "every premise discharged"/non-vacuity with 2
> premises KEPT — corrected (EquisortParametric + the Macro dispatch
> doc). M2: two stale DISABLED comments on the LIVE usefi
> callback/pre-pass — corrected. Also landed: Class-2 consumer-rule
> lookup now refuses ambiguity (O-2); check-gz-agreement name
> extraction fail-closed + flag justifications restated (m5/m6); the
> D5 admission criterion restated as two classes with FOLD-CONSTS-IN-+
> in the outside-corpus class (O-5); chain-validation route note at the
> Core.lean discard site (O-1/m1). FOLLOW-UPS (tracked, not landed):
> capstone-row statement pins in SortingPins (both reviewers);
> content-level gz_def transcription pin (O-6); mirror-registry
> application for QSORT-IS-ISORT's rule:HOW-MANY-QSORT cond — one of
> its own FI obligations, green as a row in the same sweep (O-3, the
> known Provers.lean:727 gap); addDecl name-key hash hardening
> (m4b). Final report + merge proposal:
> docs/notes/2026-08-09_phase3-closeout-final-report.md — the charter's
> exit criterion is MET; merge sign-off requested (not assumed).

> **FINAL-CLOSEOUT ARC — LIVE STATE (branch mdd/sorting-final-closeout).**
> Increment 0 LANDED (ba9f9bd): capstone statement pins (via the sweep's
> registered constants — no re-replay), AtCanonical KEPT pins, the
> R-lane brief (docs/notes/2026-08-09_r-lane-decision-brief.md — AWAITS
> Mike's 1/2/3 ruling), weight baseline tightened. RED-ROW DEPENDENCY
> MAP (2026-08-09, read off the current golden + TODO history — this
> re-sequences the charter's queue 1↔2: the 8-item batch LANDED
> emissions long ago; the reds are CONSUMER-side plus exactly TWO-THREE
> small fork gaps):
> - FORK GAPS (the whole batch for this arc): (i) the rewrite-equal
>   `(equalityp rhs)` arm at rewrite.lisp:18434 — untagged/unlogged
>   (blocks HOW-MANY-BAD-PAIRS-BNEXT and PCE's wall (b));
>   (ii) :PATH coverage — HOW-MANY-RM-GENERAL's inline-window
>   ambiguity (2 anchorings, entry-path recorded but window frames
>   absent) + ORDEREDP-WHEN-BNEXT-CONSTANT (pathStepsFromFrames,
>   frames []); (iii) investigate HOW-MANY-SMALLER-BNEXT's
>   `:TA-RUNES []` (marker-relieved hyp names no FC relief — basis
>   emission or consumer registration, TBD at the site). Per the
>   standing rule the batch needs Mike's ITEM-BY-ITEM review before
>   the rebuild; the R-lane solidify/with-lemma relation item joins
>   ONLY on a 1/2 ruling (the with-lemma :GENEQV half already emits,
>   fork 24e6dbc; rung-3 is its designated consumer — no piecemeal
>   wiring).
> - CONSUMER CHAIN (post-batch, no user input): HOW-MANY-BAD-PAIRS-
>   BNEXT green → its :linear rule discharges termination:BSORT's
>   ASSUMED dp-fact (the batch-1 :LINEAR snapshot emission is already
>   in the corpus) → BSORT enters termReplayed → the three induction
>   rows (ORDEREDP/TRUE-LISTP/HOW-MANY-BSORT) take the interpCount μ
>   route (Induction.lean route discrimination; BNEXT-SIZE never needs
>   a registry entry — it rides the recorded admission). PCE: resurrect
>   the KILLED tpthm consumer stack (built+audited 2026-08-04, killed
>   in the drift round for lacking a green consumer — the git history
>   has it; its green consumer becomes reachable with wall (a) the
>   IF-TEST-TRUE marker consumption in ProofTree ~346 (consumer-only)
>   + wall (b) fork gap (i)). BSORT-IS-ISORT: the D3 FI-arm
>   composition + the bsort cluster.**
> PROGRESS (69a26c6): item C LANDED — FC-relief anchored on the
> emitted (:FC-DERIVATIONS …) channel (ReplayCtx.fcDerivs + the
> widened marker anchor + the hoist demand thread; keyword plist
> reader). HOW-MANY-SMALLER-BNEXT advances past its relief wall to
> the KNOWN add-literal DEDUP class (*1/4.5: under the E=(CADR X)
> context-subst, clause literals 3 and 6 coincide and ACL2 merges
> them — the recorded item numbering shifts; the rung-2 build log's
> acknowledged loud frontier). NOTE: bsort's golden section text
> changed (red-row error text) — repin due at the next claim point.
> NEXT: the tpthm RESURRECTION for PCE — source = the tpthm hunks of
> `git show 910785a` (the kill) reversed, re-applied over the
> NodeCore module split; spec = the audited worklist (this file,
> TPTHM-CONSUMER SUB-ARC) + docs/audits/2026-08-04_tpthm-consumer-
> audit.md; plus the IF-TEST-TRUE marker adoption at
> ProofTree.lean:392 (wall (a)); wall (b) equal/case-split emission
> ALREADY LANDED. Then: the dedup-class spine composition (assess
> bounded), the D3 arm, and the two Mike gates.**
> PROGRESS (fbb16f8, claim-gate TRUE_EXIT=0): tpthm stack RESURRECTED
> over the module split (all audit fixes preserved; offers at the
> audited 9th telescope position); PCE advances past the recognizer
> frontier to the IF-COLLAPSE RECONCILIATION — reached
> (NOT (IF (IF (TRUE-LISTP (CDR X)) 'T 'NIL) (IF inner 'T 'NIL) 'T))
> vs recorded (NOT inner); the emitted :IF-TEST-TRUE marker
> (IF-FINISH/IF-TEST, :TEST (TRUE-LISTP (CDR X)), :JUSTIFICATION
> fake-rune-for-type-set) carries the collapse's basis; design choice
> pinned: consume at the CHAIN-END RECONCILIATION site (CoreSpine's
> reached≠recorded throw), NOT as parser nodes (parser adoption would
> shift chain shapes corpus-wide). The (IF x 'T 'NIL)⇒x half needs
> the boolean basis (inner is boolean by construction of the emitted
> case-split shape) — RESOLVED (site read): value-level identity via
> the two-valued primitives, NO emission needed; PCE drops out of the
> fork batch entirely (batch review doc updated). The reconciliation
> arm (bridgeEqualNilNorm-class, at CoreSpine's reached≠recorded
> site, marker-anchored + trueListp-CDR closure for the test) is the
> next Lean increment.
> Golden repinned at fbb16f8 (0 flips, 5 red-row message churns).**
> PCE GREEN (c0cb74b, claim-gate TRUE_EXIT=0 — 105/116, sorting
> 68/78, convert 11/13): the wall-demolition round (6939387) landed
> the IF-collapse bridge + FIVE 910785a resurrections (L-fold,
> boolean-TP fold, nil-drop, single-summand + term-vs-sum cells,
> orientation normalization — each now with a live consumer), then
> the elim reorder's LAST-POSITION case (the boolean-wrap collapse
> via the shared boolwrapIdentFor) finished the row. The CONVERT
> row's use:PCE cond discharged in cascade (now conditions on
> rule:HOW-MANY-RM-GENERAL — the genuine remaining red). REMAINING
> REDS (10): HOW-MANY-RM-GENERAL + PERM-TLFIX (convert), the bsort
> six + termination:BSORT, BSORT-IS-ISORT. Next: HOW-MANY-RM-GENERAL
> rides fork gap (ii) (:PATH coverage — batch review item B) OR a
> consumer-side anchoring completion (pin all three of
> frames/preSwap/branchAnchor per the drift round's completion
> condition); then the bsort chain via batch item A.**
> ANCHORING COMPLETION LANDED (b95f14d): position-canonical
> uniqueness + the ratified anchored-over-unanchored argument;
> HOW-MANY-RM-GENERAL advances to the solidify equation-closure wall
> (the R1-expiry class — consume the emitted ta-subst provenance,
> batch-3 item, next). GATE RECORD CORRECTION: b95f14d's message says
> the claim-gate run was interrupted by the maintenance reboot — it
> in fact COMPLETED first, TRUE_EXIT=0, against exactly the tree
> content b95f14d captured (recorded here since the commit is
> immutable): the head commit is fully gated. Batch review item B's
> HOW-MANY-RM-GENERAL half is now MOOT (consumer-side landed) — only
> ORDEREDP-WHEN-BNEXT-CONSTANT's half remains open there.**
> BRANCH-FACT DECOMPOSITION + SYNTHESIZED BRANCH ANCHORS LANDED
> (0307f13, claim-gate TRUE_EXIT=0): the solidify equation-closure
> wall fell (installBranchTrueFacts — ACL2's assume-true-false
> decomposition of truthy composite (IF c t 'NIL) tests;
> cond_tnil_ne_nil_test/_then); HOW-MANY-RM-GENERAL advanced to the
> HOW-MANY-RM hyp-relief wall. THAT WALL FELL NEXT (uncommitted):
> the relief's recorded basis is upstream `assoc-equiv`
> (type-set-b.lisp — the type-alist lookup consults BOTH argument
> orders of an equivalence-relation atom); mirrored as the
> commuted-EQUAL arm of `notAtomFalsity?` (Compose.lean, extracted
> from the Node.lean hyp-relief arm) + the commuted hoist demand
> (Literal.lean). HOW-MANY-RM-GENERAL → ASSUMED ◌ (waterfall fully
> mirrored; residual = the Subgoal *1/3.2 preprocess/tau DP leaf —
> the D3 class). THE D3 ARM LANDED (uncommitted):
> `replayUseHintClausify` (Core.lean) — chain on CONSTRAINT-CL →
> recorded clausify checkpoint → post-clausify verdict leaves
> (replayDischargeNode; ASSUMED:dp-fact surfaces honestly) → bridge →
> the tautology-dropped FI instance route; the constraint proof is
> LET-BOUND into the row term so its assumptions become row
> conditions. BSORT-IS-ISORT expected ASSUMED ◌ (the plan's stated
> ceiling until the bsort frontiers). Fixed en route: buildTotalEnv
> (Runner) now runs under withRealMaxRecDepth 8192 like
> tryReplay/tryDischarge — it sat ~1 frame under the default 512 and
> warm meta caches from the in-node DP discharge pushed one defeq
> path past it (runtime-class throw, uncatchable by plain catch).
> Sweep + golden-review + repin + full gate pending.**
> AUDIT + FIX ROUND + EXIT (2026-08-09): the pre-approved 2-Opus
> audit ran (synthesis: docs/audits/2026-08-09_final-closeout-audit.md).
> Top finding (convergent, rfl-verified): BSORT-IS-ISORT's
> conditionally-green row was VACUOUS (kept usefi == goal) — fixed by
> the ASSUMED:fi-self choke point (Harness marker + Runner/Macro
> guards); the row is ASSUMED ◌ and the corpus count is an honest
> 106/116. Also landed: the anchoring resolver tightened to its
> documented three-component contract; dedupSkipClose + the
> LEXORDER-ORDER rung marked HELD UNDER EXPIRY (emit/dedup-drop and
> entry-derivation provenance queued for the next batch review);
> provenance wording corrections. FINAL REPORT + merge proposal:
> docs/notes/2026-08-09_final-closeout-report.md. Open user gates
> carried out: the emit/dedup-drop fork item; the R-lane rung-3 lane
> (its own charter). Named continuations: the NESTED equal-descent
> composition (→ the bsort cluster); the tau frontier family.**
> RULINGS + THE FORK BATCH ROUND (2026-08-09, ee35d88 + the batch
> commits): Mike ruled R-lane = option 2 (emission-only — and item D
> turned out ALREADY EMITTED at 24e6dbc, so the Lean rung-3 lane is
> the only deferred piece; PERM-TLFIX gate-logged) and approved the
> batch (A + B(ii)). Item A (equal-cars/cdrs decision records)
> landed + round-tripped (recapture surface: exactly bsort/
> ordered-perms/02-rev + a timestamp line). Consumer side landed:
> record ingestion corpus-green (duplicate consumption in the
> decomposition protocol; unresolved-probe no-op block in the chain
> walker; identityLiteralItem at 4 walker guards) +
> HOW-MANY-BAD-PAIRS-BNEXT advanced two walls (resolved decision
> consumed; the LEXORDER-ORDER rung — logic_equal_nil_of_lexorder_nil
> anchored on the recorded :TA-ENTRY basis + the ground-zero order
> axioms). REMAINING NAMED CONTINUATION (not attempted): the NESTED
> equal-descent composition — recursive phase decisions in the
> decomposition protocol (HOW-MANY-BAD-PAIRS-BNEXT's equal-self on a
> nested component pair; ORDEREDP-WHEN-BNEXT-CONSTANT's
> component-pair generic-tail lift is the same family, B(ii)
> classified CONSUMER-side, no emission needed). The bsort μ-route
> rows ride HOW-MANY-BAD-PAIRS-BNEXT → :linear → termination:BSORT.**

> **EQUAL-DESCENT RESTRUCTURE ARC (2026-08-10, branch
> mdd/equal-descent-restructure; charter
> docs/plans/2026-08-10_equal-descent-restructure-charter.md).**
> Item 1 DONE (46ac66b, claim-gate TRUE_EXIT=0): replayEqualDescent
> extracted behavior-preserving (byte-identical sweep). Item 2 DONE
> (this round): the RECURSIVE protocol — per-phase outcomes
> (T/NIL/UNRESOLVED), nested descents at arm (c) (window-pair or
> record detection, enclosing-record cross-check), the rewrite.lisp
> outcome table incl. the negative-side *t* DISCARD (audit C3's
> asymmetry, now reachable and mirrored at the outcome level); the
> probe block subsumed by the none-outcome; HOW-MANY-BAD-PAIRS-BNEXT
> REPLAYED ✓. Item 3 CASCADE LANDED: linear_premise_fact_lt (the
> <-headed :LINEAR premise) + assertDpEqualNilComm (the DP goal-prep
> comm twin — a permutative simp lemma loops, so the
> assertDpOrderFacts pattern) greens termination:BSORT; the
> Induction-route hypFVars gained linear:; the three μ-route rows
> REPLAYED ✓ — bsort 7/8. ORDEREDP-WHEN-BNEXT-CONSTANT burned five
> walls (positioned descent no-op; identityLiteralItem probe forms;
> residual-push close at the spine's empty continuation; the
> CONS-CONS registry arm dpLiftF_equal_cons_cons_expand; the PREFIX
> whole-clause discharge + evtrueExtendTail) and now stands at the
> NAMED 2e wall: the expansion's recorded DETAIL CHAIN contains an
> IFF-class step ((IF x 'T 'NIL) ⇒ x), so consuming it needs the
> expansion-walk composition weakened to nil-equivalence at
> BOOL-tolerant positions — a real sub-project, logged, gates
> nothing else. Sweep/review/repin/gate pending.**

> **RESTRUCTURE-ARC LEFTOVERS (charter items 4–5, 2026-08-10):**
> item 4 REVIEW-LOGGED — the leftovers fork batch awaits Mike's
> item-by-item ruling (docs/notes/2026-08-10_leftovers-fork-batch-
> review.md: E = emit/dedup-drop retiring dedupSkipClose's expiry;
> F = the LEXORDER-class entry-derivation provenance retiring that
> rung's expiry; G explicitly deferred). Item 5: the claim-gate now
> tees a stamped LOCAL artifact (.gate-runs/<sha>-<utc>.log,
> gitignored — session-scope verifiability for auditors without repo
> bloat; the audit's could-not-verify remedy). REMAINING item-5
> leftovers, logged not built: navigateFrames does not validate frame
> fn symbols (pre-existing fail-open, both close-out auditors);
> RATIFICATION QUESTION for Mike: the DP premise scan's breadth
> (Totality's rule pass scans every stored rule and can cite rules
> ACL2 did not — outside CONCERN 3; narrow to recorded-basis-only
> per the tau ruling's creep-watch, or ratify as-is?). SHARPENED by
> the restructure-arc audit's DEFECT 2 (the linear pass is
> RUNE-BLIND — it supplied a rule at leaves whose recorded runes
> cannot cite it): the concrete direction is leaf-rune gating where
> a rune channel exists + EMITTING the rune channel for verdict-only
> admission clauses (a future fork-batch item). Also QUEUED:
> statement pins for the four new bsort greens (needs linear-hyp pin
> helpers; the audit hand-verified all four goal terms are the full
> ACL2 theorems meanwhile).
> BSORT-IS-ISORT's next named wall (88e13fd): the W3 class-2 lift is
> hypothesis-free-only; the WEAK parametric's premises are
> ONE-HYPOTHESIS rules (TRUE-LISTP-SORTFN1/2) — the one-hyp lift
> extension is the row's ✓ path.**

> **TAU LANE — RULED (Mike, 2026-08-10): the MIDDLE PATH.** For
> verdict-only tau leaves (the class behind HOW-MANY-RM-GENERAL's
> *1/3.2 residual and the future tau-frontier family): emit the RULE
> SET the tau verdict rested on (the ta-nil-basis / fc-derivations
> emission precedent — ACL2 computes with these rules; the emission is
> cheap), and discharge with the EXISTING DP kit taking exactly the
> recorded runes' instances as premises — read-off, not matcher
> selection. This dramatically downscopes Lean-side cleverness; full
> tau derivation logging remains the possible END STATE for total-ACL2
> masquerade, and the midpoint is to be WATCHED FOR CREEP (no widening
> of premise selection beyond the recorded basis; when the basis
> emission lands, tau-class leaves drop the broad premise scan for
> recorded-runes-only). FIRST INCREMENT of the future tau charter: a
> SCOUT — confirm the tau verdict site can cheaply report its fired
> rule set (upstream tau is deliberately ttree-free, so this is the
> one open implementation question).**

> **LONG-TERM ARCHITECTURE (direction agreed 2026-08-08): COMPOSITIONAL
> REPLAY AT SCALE — docs/notes/2026-08-08_compositional-replay-design.md.**
> Per-node lemma decomposition as the eventual default emission shape +
> fragment-local certified checkers per L1; D2 is its tactical first
> step. Detailed design open for ratification (questions at the note's
> end). D2 ROOT CAUSE (2026-08-08, trace-confirmed): NOT term depth —
> BINDER-COUNT live frames: withLocalDecls.loop spends one native
> frame per telescope binder, the row's corpus-wide offer list is
> thousands of binders whose frames stay LIVE through every discharge
> pass, and lake worker threads have smaller stacks than the CLI
> (why the probe survived). Demand-filtering the rebuild's offers
> (landed, replayAdmission precedent) was necessary but insufficient.
> D2-a — THE FIX (the ReplayedTermination pre-pass pattern): build
> the usefi constants BEFORE the row replay at the COVERAGE layer
> (coverage_book% pre-scans the parsed log for FI citations and calls
> a new prepareUseFi in ParametricInstantiate — no runBook changes;
> the coverage elaborator's stack is shallow): declare FRESH fvars
> replicating the consumer-hyp surfaces the discharge consults
> (totalHyps/ruleHyps/useHyps offer shapes), run the existing
> composition against them, λ-abstract them into the declared
> constant (Π-params). The row-time discharger = cache lookup +
> per-param row-fvar match by type-isDefEq + application (cheap,
> shallow). D2-a LANDED + ENABLED (de629e9; safe: prepare failures
> skip → usefi kept, rows unchanged). D2-b (the two named channel
> gaps): (i) the Class-2 bridge must discharge a dep-book tree with
> the OWNING dev's channel surfaces (find the owning dev in crossDevs
> by findThm; cfg' := mkBookConfig owningDev consumerWorldVal wExpr
> env — gz fc/tp/recog snapshots from the owner, world stays the
> consumer's; ORDEREDP-MSORT's :TA-RUNES cite LEXORDER-TOTAL, absent
> from the consumer snapshot); (ii) thread termReplayed: for the
> owning dev's recordedTerminationDefuns run replayAdmission at the
> consumer world (cached by name — the ReplayedTermination
> discipline) and pass to the discharge (ORDEREDP-QSORT's FILTER
> decrease). D2-b LANDED (owning-dev
> channels + consumer-world termReplayed pre-pass + user-equiv rule
> filter + the full synthetic offer surfaces incl. cong/equivRefl/
> equivFull): ORDEREDP-MSORT and the qsort chain now DISCHARGE; the
> msort citation reached [husethm_ORDERED-PERMS]-only before the
> latest round. D2-c (the current blockers, both in the ASSEMBLY not
> the semantics): (i) the STRONG prepares now fail 'Application type
> mismatch' — inspect the bridge/lift applications' argument order
> against the lemma signatures (likely the fuelEq lift's hint or the
> Class-1 crossing under the with-hyp shape); (ii) a PREPARED
> constant's TYPE is kernel-rejected ('type expected' at module
> finalization even with everything else green) — inspect the
> constructed declTy/tyA (mkForallFVars over the collected fvars +
> env; suspect ordering or a Prop/Type slip) — BOTH the callback and
> the pre-pass are gated off (if true then pure acc) until fixed;
> tree green at 104/116 throughout. Then the STRONG prepares close;
> sweep, golden row-review (capstone usefi: conds flip discharged),
> gate.

_Last updated: 2026-08-08 (Phase 3 R7b: EARLY EXIT declared — exit report docs/notes/2026-08-08_phase3-exit-report.md; exit gate TRUE_EXIT=0; branch mdd/phase3-r7b is the merge candidate)._

> **PHASE 3 — LIVE STATE (branch mdd/phase3-r7b, charter
> docs/plans/2026-08-08_phase3-r7b-charter.md, ratified at goal-set
> 2026-08-08; deferral log docs/notes/2026-08-08_phase3-deferral-log.md).**
> Standing queue: (1) non-vacuity instantiation of the two parametric
> constants at the equisort canonical world (audit O6); (2) the FI
> :USE-HINT arm (emitted :LMI-LST/:CONSTRAINT-CL composition, route
> a1 pre-ratified); (3) MSORT-IS-ISORT; (4) QSORT-IS-ISORT;
> (5) BSORT-IS-ISORT (rides bsort's 6 red frontiers — partial OK);
> (6) touched-if-relevant Phase 2 audit deferrals; (1b, ADDED
> 2026-08-08) witness-TP `dis_*` hand lemmas (tp:SORTFN1-INSERT class)
> + registry-composed constraint-premise discharge — narrows D1's
> residual. Exit = every item DONE or DEFERRED (log entry) + full gate
> + exit report. STATUS: (1) PARTIAL — AtCanonical constants landed
> kernel-checked via the new `instantiate_parametric%` (name-guided,
> defeq-checked dispatch to existing provers; generic `totals`
> registered-discharger route consuming dis_pce_total/dis_how_many_tp;
> keep-on-frontier for rule:/use: per D6); residual = deferral-log D1.
> Now: item (2), the FI :USE-HINT arm. DESIGN (pinned 2026-08-08,
> from the emitted payload + Core.lean:1790-1893): the capstones'
> :USE-HINT has :LMI-LST ((:FUNCTIONAL-INSTANCE STRONG-… (SSORTFN1
> (LAMBDA (X) (MSORT X))) …)), :CONSTRAINT-CL = the IF-conjunction of
> the constraint instances WITH ITS RECORDED DISCHARGE CHAIN (the
> concrete rules HOW-MANY-ISORT etc. — replayPreprocessChainCore
> already walks it to 't), :APPLICATION-CLAUSES NIL (tautology-dropped
> — goal == the :HYPS instance). 2a (conditional green): (i)
> lmiFnInstance? parser for the FI LMI shape; (ii) substFnCalls — the
> functional substitution on SExpr (beta of the emitted LAMBDAs at
> application sites), recomputed from the dep's translated Goal +
> cross-checked VERBATIM vs the emitted :HYPS entry; (iii) UseFiSpec
> offers (husefi_ binders, usefi:<name> conds) derived from the tree's
> FI payloads; (iv) the arm: allow non-trivial :CONSTRAINT-CL iff its
> recorded chain reaches 't; allow :APPLICATION-CLAUSES NIL iff hyps ==
> inputClause (conclusion = the usefi hyp directly); (v) no discharge
> initially — usefi: kept (D6), rows conditionally green. 2c (the a1
> composition, closes usefi:) — IMPLEMENTATION PLAN (pinned
> 2026-08-08, post-2a): (i) the alias world is built as a CONCRETE
> VALUE — wAlias := (consumer dev).toWorld with (sig ↦ ([formals],
> lambda-body)) inserted per the emitted :LMI-LST — and REFLECTED
> (derive_world-style), so EVERY existing concrete prover
> (proveNoShadow/buildTotalEnv/proveTp/dischargeRuleHyp/
> instantiate_parametric%'s whole dispatch) applies at wAlias
> UNCHANGED; the parametric constant instantiates at wAlias exactly
> like the canonical-world instantiation (item 1 machinery reused
> verbatim — same elaborator, different world + a commutation step).
> (ii) THE NEW CONTENT is one lemma family (new module,
> ACL2Lean/Replay/Lemmas/FnAlias.lean; substFnCalls MOVES there from
> Driver/NodeCore/Ctx — the Lemmas layer cannot import Driver; Ctx
> opens ACL2.Replay so call sites keep working). FINALIZED DESIGN
> (2026-08-08): decidable predicates `fnFreeTerm names t : Bool` (no
> non-quoted occurrence of any alias name; skips QUOTE bodies — data)
> and `aliasFreeWorld names w : Bool` (every defs-entry body fnFree).
> LEMMA A (pointwise invariance, fuel induction mirroring
> EvalOpt.evalOptStep_mono's case skeleton): hagree (∀ s ∉ names,
> w'.defs.get? s = w.defs.get? s) + aliasFreeWorld names w +
> fnFreeTerm names t → ∀ f env, evalOpt f w' env t = evalOpt f w env
> t (SAME fuel — the extra defs are never consulted). LEMMA B (the
> transport, ONE direction suffices for EvTrue): strong induction on
> the CONVERGING fuel F: evalOpt F w' env t = some v → ∃N ∀f≥N,
> evalOpt f w env (substFnCalls σ t) = some v; alias-call case
> composes IH(args) + Lemma A on the alias body (fnFree, side
> condition) + evalOpt_substTerm_substN (WellScoped bodyᵢ by decide,
> lengths from the step's own bindArgs success); non-alias defined-fn
> case: body untouched by substFn (aliasFreeWorld) + the existing
> defined-fn conv composition; builtins/IF/quote/var structural.
> Preconditions all DECIDE at the concrete alias world. NOTE
> substFnCalls's QUOTE guard (d0f549b) is load-bearing for B.
> LEMMA A PROVED (9fd9b87). LEMMA B-PRIME + B-DOUBLE-PRIME BOTH PROVED (17b0203, round gated TRUE_EXIT=0 2026-08-08 — the semantic layer is BIDIRECTIONAL; aliasArgsSimple side condition per the pinned subtlety): evalOpt_fnexpand_transport, zero sorries; substFnCalls gained a binder-respecting LAMBDA arm (substSafe apparatus deleted). 2c SEMANTIC LAYER COMPLETE + GATED (full claim-gate TRUE_EXIT=0 on the FnAlias round, 104/116 golden byte-identical, 2026-08-08; ed985c8/3d2b460): evtrue_fnalias (the kernel-checked functional-instantiation step) + World.withAliases with constructive hσdef/hagree. WIRING DISCOVERY (2026-08-08, pinned
> post-gate): premise discharge AT wAlias cannot re-replay the dep's
> pass-1 constraint trees (they unfold the WITNESSES, absent from the
> consumer world — the witness-deref guard would rightly fire).
> The premises must come from the CONSUMER's concrete rules
> (ORDEREDP-MSORT etc.) lifted INTO the alias world — which needs
> LEMMA B'' — the CONVERSE transport (β-contraction: evalOpt f w
> (substFnCalls σ t) = some v → eval wAlias t ≐ some v; the mirror
> induction of B', roles swapped, same case skeleton and ingredient
> lemmas; arity-mismatch/improper arms excluded by the converging
> hypothesis on the IMAGE this time). Then each parametric premise at
> wAlias = (dischargeRuleHyp at the CONSUMER world for the SUBSTITUTED
> rule spec, e.g. ORDEREDP-MSORT) + B''/A statement-level bridging
> (the rule-hyp fuel-EQ shapes transport value-exactly). B''
> SUBTLETY (analyzed 2026-08-08): the naive converse is FALSE — a
> diverging alias-call ARGUMENT that the alias body ignores lets the
> image converge while the original's step (which evaluates ALL args
> via mapM) diverges. B'' therefore carries a decidable side condition
> `aliasArgsSimple σ t` — every alias application's arguments are
> variables or quoted constants (trivially converging; exactly the
> premise formulas' reality: (ORDEREDP (SSORTFN1 X)) etc.). Alias
> case then: args converge trivially; evalOpt_substTerm_substN is an
> EQUALITY so it bridges backward; freevar_congr closes the env gap;
> reassemble the call step. All other cases mirror B' with roles
> swapped. WIRING PROGRESS (all rounds gated
> TRUE_EXIT=0 2026-08-08): W1 DONE (631b035 — the instantiation engine
> at Replay/ParametricInstantiate, Runner layer; namespace rename
> queued cleanup); W2 DONE (c27736a — usefiDischarge callback param +
> kept-pass in replayProofConditional, all sites none = byte-identical
> sweep). W3 NEXT (the statement-level lift lemmas, FnAlias companion
> module per the size norm): transport the consumer's rule-hyp shapes
> (∀env', fuel-EQ of ⟦lhs⟧ vs ⟦rhs⟧) into the alias world — constant-
> rhs rules are pure value transport (A on the image + B'' inside
> wAlias); non-constant-rhs (the HOW-MANY pair) need a convergence
> side-fact for one side from the totality machinery (the fuel-EQ
> shape alone is convergence-free). W4 THEN: the callback builder in
> ParametricInstantiate (find dep dev in crossDevs → σ from the
> spec's emitted lambdas → wAlias := worldVal.withAliases σ,
> REFLECTED → replayProofParametric on the dep theorem →
> instantiateParametricAt at wAlias with the rule-premise dispatch
> extended by the W3 bridging → evtrue_fnalias → ∀env' wrap); thread
> crossDevs: depPayload (Tests/Coverage/Harness) already parses dep
> devs — extend its return + runBook params + the callback
> construction at the coverage call sites; then sweep + golden
> row-review + gate. W4a DONE (91a2e54 — callback threaded runBook →
> tryReplay → replayProofConditional, default none). W4b RECIPE
> (pinned in full, 2026-08-08): mkUseFiDischarger (crossDevs) : cfg →
> spec → proof of `∀ env', EvTrue w env' ⟦spec.formula⟧`; per spec:
> find dep dev (findThm over crossDevs); σ := spec.subst;
> wAliasVal := cfg.worldVal.withAliases σ (meta-side data);
> wAliasE := mkAppM ``World.withAliases #[cfg.worldExpr, ⟦σ⟧] — the
> SYNTACTIC form, so withAliases_get/_agree apply constructively AND
> decide reduces through the consumer constant (NO addDecl needed);
> withLocalDeclD env': (1) parametric proof := replayProofParametric
> (dep cfg with envExpr := env'); (2) premises at wAlias via
> instantiateParametricAt (worldVal := wAliasVal, worldExpr :=
> wAliasE, extraJusts := consumer justs) EXTENDED with (a) a
> ruleBridge fallback for constraint rules — consumer-side
> dischargeRuleHyp on the SUBSTITUTED spec + the W3 lifts
> (fuelEq_fnalias_lift_const / _lift with a totality-derived rhs
> convergence; hyp-carrying rules cross their hyps by
> evtrue_fnfree_agree_iff) — and (b) ALIAS-WRAPPER TOTALITY: the
> total:SSORTFN1-at-wAlias premise needs a new small lemma
> `conv_defcall` (hdef + args-conv + body-conv-under-bindArgs → app
> conv; the B''-non-alias reassembly as a standalone) composed with
> the inner fn's totality — buildTotalEnv has no justification for
> alias wrappers; (3) evtrue_fnalias (side conditions by decide on
> the CONCRETE values; hσdef/hagree via withAliases_get/_agree +
> (σ.map ·.1).Nodup decide); spec.formula == substFnCalls σ Φdep
> holds as VALUES by the 2a offer check, so the reflected conclusion
> matches syntactically; (4) mkForallFVars [env'] + isDefEq-check
> against mkUseHypType's shape (∀ env', EvTrue w env' ⟦formula⟧ —
> read verbatim at Waterfall:181). W4b DONE (the discharger builds; e69df24+successor commits) + W4c: coverage WIRED with the callback DISABLED — the first live run STACK-OVERFLOWED (SIGABRT, deep withLocalDeclD/whnf frames inside tryReplay); NEXT: isolate the discharger OUTSIDE the sweep on the msort spec (a scratch elaboration calling mkUseFiDischarger directly), profile which decide/rebuild blows the stack (suspects: aliasFreeWorld decide over the 214-defun consumer world through the syntactic withAliases form — may need the REFLECTED-VALUE alias world (addDecl a constant) instead of the syntactic form for decide performance, trading the constructive withAliases lemmas for decided hσdef/hagree at the concrete value — BOTH routes sound; or the in-replay parametric rebuild depth needs withRealMaxRecDepth raised locally). W4d DONE (kernel-route decides fixed the
> overflow; wrapper_total_1 + the alias-wrapper dispatch fallback
> landed) — the PROBE (.tmp/pinscratch/usefi_probe.lean, maxRecDepth
> 8192) now runs the WHOLE composition and stops at: 'wrapper
> SSORTFN1's inner fn MSORT has no pool totality' — buildTotalEnv
> cannot prove MSORT (recorded-termination class; even the sweep
> keeps total:MSORT as the row's cond). W4e (the final link):
> transport the CONSUMER TELESCOPE'S OWN total:MSORT hypothesis into
> the alias world — (i) a tiny step-INVERSION lemma (app converges →
> body converges under bindArgs, given hget/length — the evalOptStep
> defn-arm read backward); (ii) total_fnalias_transport: consumer
> totality hyp (at w) + alias-free body + hget at both worlds →
> totality at wAlias — proof: given conv-a at wAlias to va, apply the
> consumer hyp at a := (QUOTE va) (trivially converging), invert its
> step to body-conv under bindArgs at w, cross by A (body
> alias-free), reassemble by conv_defcall at wAlias; (iii) plumbing:
> the usefi discharge pass hands ctx.totalHyps to the callback
> (extend the callback signature or pass via cfg); the wrapper
> fallback's inner-fn pool miss consults them through (ii). The
> resulting usefi proof is CLOSED (the consumer telescope hyp is an
> fvar the pass letBinds — same discipline as every other discharge).
> W4e DONE (total_fnalias_transport +
> defcall_body_inversion + the ctx-carrying callback + the wrapper
> fallback consult — the PROBE now closes ALL no-shadow/totality/tp
> premises including both alias wrappers and stops at exactly:
> [hrule_CONVERT-PERM-TO-HOW-MANY, the six SSORTFN constraint rules,
> husethm_ORDERED-PERMS]). W4f — THE FINAL BRIDGING (fully determined,
> no unknowns): the discharger needs the CONSUMER Development (extend
> the callback signature: Development → ReplayConfig → ReplayCtx →
> UseFiSpec → …; runBook applies its parsed dev). Then per kept
> premise at wAlias: (CLASS 1 — alias-free content, e.g.
> rule:CONVERT-PERM-TO-HOW-MANY, use:ORDERED-PERMS): bind to the
> MATCHING CONSUMER-TELESCOPE FVAR (ctx.ruleHyps/useHyps — these are
> kept conds of the consumer row itself) crossed by Lemma A — needs a
> tiny fuelEq/EvTrue A-crossing at the STATEMENT level (all terms
> alias-free → pointwise rw of evalOpt_fnfree_agree inside the
> ∀env'∃N∀f shape; evtrue_fnfree_agree_iff already covers the use:
> shape). The resulting usefi proof stays CONDITIONAL on those
> consumer fvars — which the usefi PASS letBinds like every other
> discharge, so the row's cond set gains nothing new. (CLASS 2 —
> alias-mentioning, the six constraint rules): build the SUBSTITUTED
> RuleSpec (substFnCalls lhs/rhs; hyps — STRONG's six are all
> hypothesis-free), CONTENT-MATCH it against the consumer's full rule
> accumulation (developmentTheoremsWithRules — ORDEREDP-MSORT etc.
> exist verbatim), discharge via dischargeRuleHyp at the consumer
> world (cfg/ctx/consumer depProofs from the dev), lift via
> fuelEq_fnalias_lift_const (4 rules, rhs 'T) /fuelEq_fnalias_lift
> (the HOW-MANY pair — rhs convergence from the consumer totality
> hyp probed at variable args). Note msort/qsort cite STRONG whose
> constraints are ALL hypothesis-free — the with-hyp lift is only
> needed for bsort's WEAK citation (ceiling ◌ anyway; frontier it).
> THEN re-enable + coverage call sites build
> the callback (depPayload already parses dep devs — extend its
> return + pass crossDevs); sweep flips the two capstones' usefi:
> conds to discharged; golden row-review; gate. REMAINING for 2c
> after W4: nothing. Prior pin (superseded detail kept below): (i) refactor instantiate_parametric%s premise-dispatch core into a reusable MetaM function taking the parametric proof Expr + offer channels; (ii) dischargeUseFiHyp in Harness: build wAlias := (consumer world).withAliases σ (σ from the specs emitted lambdas; REFLECT the concrete value), rebuild the deps parametric statement (replayProofParametric on the dep dev), discharge its premises at wAlias via (i), apply evtrue_fnalias (side conditions decide at the concrete worlds; hσdef/hagree via withAliases lemmas; hfree/hws decide on the formula; the conclusion formula == spec.formula ALREADY holds by the 2a verbatim offer check since both use the same substFnCalls); wrap ∀env; letBindFVar; (iii) wire into the usefi kept-pass; sweep + golden review + gate. LEMMA B PLAN (pinned post-A): statement —
> ∀ F env t v, evalOpt F w' env t = some v → ∃N ∀f≥N, evalOpt f w env
> (substFnCalls σ t) = some v; strong induction on F; NO condition on
> t needed for fn-freedom (dead substFnCalls fallthroughs are excluded
> by the converging hypothesis) BUT add decidable side conditions:
> σ names not special forms (QUOTE/IF/LET/LET*), alias bodies
> fnFree+WellScoped+CLOSED (free vars ⊆ formals), letFree t +
> letFreeWorld w (new quote-skipping predicates — the LET/LET* arm is
> then unreachable and closes by contradiction; translated artifacts
> are always let-free, decide-checked at composition). Case plan:
> REFINED (post-A discovery sweep): split B into B' (SINGLE-WORLD
> β-expansion, w' only) + A on the alias-free image — B' := WellScoped
> t → evalOpt F w' env t = some v → ∃N ∀f≥N evalOpt f w' env
> (substFnCalls σ t) = some v. WellScoped is THE side condition on t
> (it already EXCLUDES surface LET/LET* and bare lambdas — Core.lean
> :631 — killing the messy fold arm; spine/lam preservation via
> WellScoped_of_mem_spine/WellScoped_lam_parts). NON-ALIAS defined-fn
> bodies are UNTOUCHED by subst in B' → no conditions on the world at
> all; bodies handled by evalOpt_ge_fuel only. σ side conditions
> (decidable): defined-in-w' with the emitted formals/body; names not
> special forms; body WellScoped + CLOSED (freeVars ⊆ formals).
> INGREDIENTS ALL EXIST: evalOpt_ge_fuel/evalOpt_fuel_mono (EvalOpt
> :519/:534), evalOpt_substTerm_substN (Core :1861, w'-world, needs
> body WellScoped), evalOpt_freevar_congr (Core :821 — the
> bindArgs↔bindArgsOver-env bridge on closed bodies, with
> bindArgsOver_get_of_mem :802), conv_if_true/false, the spine mapM
> conv helper (~Core :1881). COMPOSITION: EvTrue wAlias Φ --B'-->
> EvTrue wAlias (substFn Φ) --A (fnFreeTerm (substFn Φ) decide +
> aliasFreeWorld w decide + hagree from DefMap.insert get? lemmas)-->
> EvTrue w (substFn Φ) = the usefi hypothesis. evalOpt_world_mono
> (:712) covers the w→wAlias direction where premises transport. (iii) the usefi: discharge pass in Harness (keyed
> like the use: pass): per kept usefi spec, rebuild the dep's
> PARAMETRIC statement (replayProofParametric on the dep dev — or
> import the registered constant when same-module), instantiate at
> wAlias, commute, letBindFVar. (iv) BSORT (item 5): the
> useHint+clausify composition in Core's clausify branch — chain on
> CONSTRAINT-CL, clausify the residual, post-step tau leaf, FI hyp
> peel — ceiling ASSUMED ◌ until the bsort book frontiers. 2a RESULT (pre-repin):
> MSORT-IS-ISORT + QSORT-IS-ISORT REPLAYED ✓ cond[total:<sort>,
> usefi:STRONG-…] — 102→104/116 pending repin+gate. BSORT-IS-ISORT
> sized from its emission: SAME tautology-dropped FI shape BUT the
> weak constraint chain leaves a residual conjunct that ACL2
> clausifies (((NOT (TRUE-LISTP X)) (TRUE-LISTP (BSORT X)))) and
> closes by a TAU leaf that resolves ASSUMED:dp-fact (TRUE-LISTP-BSORT
> is red in the bsort book) — so the useHint+clausify composition
> (item 5 work, in-scope, Core.lean's clausify branch + the FI
> hypothesis) lifts it to ASSUMED ◌ at BEST; ✓ needs the bsort book's
> Phase-1 frontier family first (deferral-classifiable).

> **PHASE 2 — LIVE STATE (branch mdd/phase2-equisort, charter
> docs/plans/2026-08-07_phase2-equisort-charter.md, goal running).**
> Ground truth: the 14 equisort frontiers are all "constrained fn not
> in the world/registry" classes — the ratified R6 design
> (docs/notes/2026-08-02_r6-encapsulate-design.md, MDD 2026-08-02)
> resolves them via: (1) toWorld = the CANONICAL MODEL — constrained
> scopes contribute their WITNESS bodies (the witness IS the model);
> BUG-019's protection MOVES to the parametric statement (∀ w,
> ScopeHolds S w → EvTrue w env Φ) — witness facts can never
> masquerade because post-encapsulate theorems get the parametric
> form; (2) the sweep then replays equisort at the canonical model
> with EXISTING machinery (pass-1 constraint rows = conservativity,
> kernel-checked); (3) the generic ScopeHolds statement builder
> (design item 3) for the post-encapsulate theorems; (4) a
> witness-dereference in a post-encapsulate tree is a HARD-FAIL
> sanity check (design item 5). EXECUTION ORDER: (a) toWorld
> canonical-model change + scope bracketing (ClauseTree), (b) sweep +
> row-by-row review (rows should flip green at the canonical model),
> (c) ScopeHolds builder + parametric statements for STRONG/WEAK,
> (d) witness-deref guard, (e) cov-encapsulate 2 rows, (f) gate +
> golden re-pin per increment. Charter exit: 14/14 + 2/2 or named
> frontiers. PROGRESS (3475546): (a)+(b) DONE — canonical model
> landed, 86/116 → 100/116 (equisort 12/14 + cov-encapsulate 2/2,
> zero regressions, gate TRUE_EXIT=0, catalog per the R6 doctrine).
> (e) DONE (9622eb3): both capstones GREEN — 102/116; the frontier
> was a GROUND residue ((IMPLIES 'T 'NIL)) evaluated silently by
> rewrite-atm; the arm recomputes toward the RECORDED rhs (ratified
> class). equisort 14/14 + cov-encapsulate 2/2 — the charter's ROW
> criterion is met. (c) DONE + (d) DONE: BOTH capstone parametric
> constants LANDED, kernel-checked, axiom-clean —
> `weakSortfn1IsSortfn2Parametric` /
> `strongSsortfn1IsSsortfn2Parametric`
> (Imported/Waypoints/EquisortParametric.lean, `parametric_replayed%`).
> Mechanism (exactly the pinned design reading): `replayProofParametric`
> replays the SAME recorded trees over an ABSTRACT `w` — the
> conditional telescope with `discharge := false` (every used
> hypothesis KEPT), def-pinning hypotheses for every canonical-model
> fn EXCEPT the scope sigs, no-shadow hypotheses for all builtins;
> on-demand world facts route through hypothesis tables
> (ReplayConfig.defFactHyps/noShadowHyps in deriveDefInfo/N,
> proveNoShadow, replayExecGround-via-dpValProof, dpNoShadow
> fold). Premises = the six scope constraints as rule: hyps + sig
> totality + pre-scope rule/total/tp conds — NO witness vocabulary,
> NO def-pins consumed (the trees never dereference witnesses). (d):
> a sig-fn unfold/no-shadow demand over abstract w now throws a NAMED
> witness-dereference error (R6 item 5). Catalog entries updated to
> .replayedOnly naming the constants. NodeCore re-slice: Ctx's tail →
> Compose.lean (move-only; Ctx had regrown past its baseline).
> EXIT ASSESSMENT (3ae3f8e, gate TRUE_EXIT=0): the charter criterion
> is MET — 14/14 + 2/2 rows green; the L3 world-parametric statements
> exist for exactly the class the R6 design requires them for (the
> post-encapsulate capstones — design item 5: the constraint theorems
> need no parametric form, they ARE ScopeHolds' components). The
> constants quantify over all implementations: sig existence/totality
> rides the total:SORTFN1/total:SORTFN2 premises, the constraints ride
> the rule: premises; the telescope is WIDER than bare ScopeHolds
> (pre-scope rule/total/tp + builtin no-shadow premises kept
> undischarged) — the honest conditional form; Phase 3 (R7b)
> discharges them at concrete worlds. PRE-MERGE AUDIT (2026-08-08,
> inside+outside, both Opus): NO soundness defect, NO blocker; fix
> round applied on-branch — (I1 MAJOR) the unpinned set now excludes
> witness HELPERS too, not just sigs (SORTFN1-INSERT would have been
> offered a def-pin); (I3/O7 MAJOR) statement pins landed
> (Tests/ParametricPins.lean — binder inventory, conclusion vs the
> log's :TFORMULA, stored-rule lhs/rhs, no-witness tripwire);
> (I2/O4 MAJOR) docs corrected: the constraint premises are ACL2's
> STORED-RULE forms (EQUAL-to-'T — stronger than the bare truthy
> constraints over unpinned ORDEREDP; model class = worlds satisfying
> the stored rules); (O5/I5) docstrings now describe the actual types.
> DEFERRED (tracked below): O6 non-vacuity → Phase 3's first work
> item; I4 charter/R6 wording reconciliation → user; O13
> gz-agreement-lemma ci check. AWAITING: merge sign-off
> (mdd/phase2-equisort → main).

> **AUDIT 2026-08-08 DEFERRED ITEMS (Phase 2 pre-merge).**
> (1) NON-VACUITY of the capstone parametric telescopes (outside F6):
> kernel-check satisfiability by instantiating both constants at the
> equisort canonical world and discharging all premises — this IS
> Phase 3 (R7b)'s first work item; until it lands the constants are
> honest conditionals with no exhibited model (nothing in-repo claims
> otherwise). (2) CHARTER RECONCILIATION: RESOLVED
> 2026-08-08 — Mike ratified the dated addendum now at the bottom of
> the charter (mechanism sentence superseded by the older ratified R6
> design; the intent clause binds and is pin-enforced). (3) GZ
> AGREEMENT-LEMMA GAP (outside F13): builtin-named ground-zero defuns
> (IMPLIES, IFF, LEXORDER, NATP, POSP, EQL) have no kernel-checked
> agreement lemma vs their Logic.* builtins (TRUE-LISTP etc. do —
> gz_def_true_listp); the parametric conclusions' meaning rides the
> builtin under no-shadow, so add gz_def_implies + a ci check that
> every emitted builtin-named gz snapshot has an agreement lemma or a
> flag. (4) sig-set over-abstraction (outside F16): the unpinned set
> is the UNION over all scopes; a post-scope-1 theorem legitimately
> unfolding a scope-2 fn would spuriously hit the witness-deref guard
> — refine to scopes-in-force when a book needs it (hard-fails
> honestly today).

> **CAPSTONE-DEMO ARC — LIVE STATE (branch mdd/capstone-demo-arc,
> HEAD b611dfd).** Phase 0 DONE (ff70eb2). Phase 1: the 8-item fork
> batch is LANDED (d8b83cb — fork submodule 68ce6cb, all emissions
> live, corpus recaptured through the fatal gates, golden
> BYTE-IDENTICAL at 86/116) and B1 is RETIRED (b611dfd — the
> complement arm consumes the recorded DROPPED clausify leaf or the
> item-7 event; inference-from-absence gone; NOTE the mechanism for
> TRUE-LISTP-BNEXT was clausify-under-assumptions, not add-literal —
> the outside auditor's could-not-verify #6 was right to doubt).
> In-batch withdrawal: emit/if-finish/test-left-iff (redundant record
> class, no consumer). REMAINING Phase-1 work (2/2b) — the three
> retirements: R1 — EMISSION LANDED (user-approved 2026-08-07, fork
> e549d119: the equal/type-alist-nil verdict BASIS — :CANON1/:CANON2
> the canonical representatives + :TA-ENTRY the bound disequality,
> recomputed at the verdict site from assoc-equiv+'s own inputs; live
> in perm ×16 / convert-perm ×31; parsed into RewriteStep
> canon1/canon2/taEntry). R1 WIRED as a TWO-RUNG structure
> (2026-08-07, commit 3678b6d): rung A DIRECTED (recorded canons +
> entry, deterministic toward recorded targets); rung B — the bounded
> search SURVIVES under a SHARPENED expiry for DERIVED type-alist
> entries only (subst-type-alist builds them during assume-true-false;
> MEMB-RM's class; the next-batch item is subst-type-alist provenance
> — the same emission HOW-MANY-RM-GENERAL's frontier names);
> R2 + ground-hyp RETIRED (2026-08-07): the gates are now EMITTED
> DATA — recogVerdictGate checks the fn's TP :BASICTS numerically
> against the cited recognizer tuple's true-ts (disjoint for FALSE
> verdicts, contained for TRUE; tsAnd = two's-complement Int bitwise,
> ACL2's own type-set encoding); the ground-hyp arm requires a cited
> tuple for the hyp's head fn. INTERPRETATION FLAGGED FOR USER REVIEW:
> the per-fn trusted-core VALUE lemmas (logic_consp_len_nil etc.)
> remain — they are kernel facts no emission can supply (the ratified
> per-function-evaluation-lemma class); the R2 expiry's "delete this
> table" is read as "retire the NAME-KEYED GATE", which is done. BONUS
> — item 9 UNPARKED: the compound-recognizer world-fn route now
> derives natp from the fn's BOUND tp: hypothesis (resurrected
> logic_natp_t_of_int_tp_fact, now with a consumer);
> termination:BSORT advanced from the loud parked frontier to honest
> ASSUMED ◌. BSORT RESIDUE CLASSIFICATION (Phase-1 exit item): (a)
> termination:BSORT ASSUMED:dp-fact — the v1 linear-premise consumer
> is EQUAL-conclusion-only; BSORT's decrease needs the emitted LOCAL
> inequality linear rules (HOW-MANY-BAD-PAIRS-BNEXT) as premises — a
> consumer-scope extension, named frontier; (b) the 3 μ-registry rows
> (ORDEREDP/TRUE-LISTP/HOW-MANY-BSORT): measure head BNEXT-SIZE needs
> the μ-registry route extended to world-fn measures (R3's whitelist
> is ACL2-COUNT/LEN) — consumer work, named frontier; (c)
> HOW-MANY-SMALLER-BNEXT: marker-relief on the item-3 expunge records
> (consumer pending); (d) HOW-MANY-BAD-PAIRS-BNEXT: rewrite-equal CAR
> phase recorded-decision gap; (e) ORDEREDP-WHEN-BNEXT-CONSTANT:
> equal-cars generic-tail lift. All classified; none block Phase 2.
> INCLUDE-DAG GATE WIRED (2026-08-07, 5cd2edd): sweep offers filtered
> inside runBook against each consumer's own emitted
> :INCLUDE-BOOK-EDGE set — review-1 P1-8's over-offer half RESOLVED,
> byte-identical; the ordering half (ordered-perms after its
> consumers) is a recorded promotion candidate. PHASE 1 EXIT
> ASSESSMENT: gate green ✓; expiry markers — B1 retired ✓, R2
> gate-retired ✓ (interpretation flagged for user review), ground-hyp
> gate-retired ✓, R1 rung A directed ✓ / rung B under a SHARPENED
> expiry blocked on an un-batched emission (early-exit (d) declared);
> bsort residue classified ✓; item 9 unparked (bonus). Phase 1
> COMPLETE (2026-08-07, both user rulings received): D1 — the R2
> lemmas-stay interpretation RATIFIED; D2 — the ta-subst emission
> APPROVED and LANDED (emit/ta-subst at subst-type-alist1's
> substitution arm; corpus recaptured), and R1's rung B′ is now
> DIRECTED off the recorded (:TA-SUBST) provenance (parent entry +
> substituted pair) — the candidate×orientation SEARCH IS DELETED.
> ALL FOUR expiry-held mechanisms are fully retired on recorded/
> emitted content. Golden byte-identical at 86/116 throughout.
> PHASE-1 AUDIT (2026-08-07, single Opus lane; remediated same day):
> M1 the ci-side :CAPTURE-END rung was a no-op (conditional on its own
> presence) — now UNCONDITIONAL + (:EVENT-FAILED) rung (S7) + the M1
> fixture pinned in test-provenance-gates; M2 the boundary-verdict
> records had NO consumer and a dead node arm — dead arm DELETED,
> validateBoundaryVerdicts now consumes every record as a value-level
> cross-check at literal replay; S1 rung B′ selects by recorded :TS
> polarity (128 only — both polarities coexist in qsort); S2 rung A's
> error-swallowing catch REPLACED by a data-driven direct/derived
> branch (rung-A failures now THROW); S3 the never-a-cons guard is
> TP-presence-driven with a world-fn consp fallback (twin lemma
> logic_consp_nil_of_int_tp_fact); S4 recogVerdictGate rewired to
> ACL2's type-set-recognizer semantics (step :TYPESET preferred,
> falseTs consumed, TRUE = intersects-true ∧ disjoint-false);
> S5 clause-level ta-subst records kept as ClauseItems (34 were
> dropped); S6 rung B′ cross-checks the verdict basis's :TA-ENTRY
> against the derived entry; N1/N9 script hardening. REMAINING
> (recorded, not fixed): S8 include-edge fires before include failure
> (fail-safe: the Lean parse throws on :EVENT-FAILED); N2 ta-subst
> omits the entry's justification runes (next-batch candidate); N5
> complement-close records carry no clause id (presence-test consumer);
> N7 the DAG gate matches basenames, :PARENT asymmetric (sysfile vs
> familiar name — emission normalization candidate); N8 .meta include
> closure under-approximates on :BOOKS + no ci dirty-tree check; N10
> golden-diff lacks an ASSUMED class. All byte-identical through the
> round. NEXT: (i) the PERFORMANCE ARC (user-approved 2026-08-07,
> short + focused, before Phase 2): (1) split DriverCoverage into
> per-book Lake modules along the include DAG (parallel + incremental;
> goldens split per book, ONE row-by-row review at the split); (2)
> parallelize recapture-all (xargs -P; disjoint outputs); (3) split
> NodeCore into cohesive modules (edit-loop cost); (4) pins-vs-sweep
> de-dup DEPRIORITIZED (highest risk — only if it buys a lot); (5)+(6)
> two-tier gating + gate batching RATIFIED and recorded in CLAUDE.md.
> Items 1+2 LANDED (70e259a: 29 per-book coverage modules, byte-exact
> sections + tiling aggregate, cold sweep 6m28 vs ~15m, NO-OP 1.1s;
> parallel capture). ITEM 3 + STRUCTURAL DEBT PASS (user-approved
> 2026-08-07 — "make the structure support future build-out"): sizes:
> NodeCore 6517, EvalLemmas 6356, Sorting.lean 5104, ProofLog 1697.
> Plan, MOVE-ONLY (no body edits; fast-gate per step, ONE claim-gate
> at the end, golden byte-identical): (3a) NodeCore → Driver/Ctx
> (ReplayConfig/ReplayCtx/val helpers/tsAnd/recogVerdictGate/taBases),
> Driver/TypeSetWalk (the walker + rung A/B′), Driver/Recognizer
> (replayRecognizer + TP arms), Driver/Rewrites (window machinery +
> replayRewrites), Driver/Literal (replayLiteral*/boundary validator),
> Driver/Node (replayNodeWith dispatch) — split ALONG the existing
> non-mutual boundaries; the one tied knot (NodeRec) stays in Node.
> (3b) EvalLemmas: ESCAPE HATCH FIRED on the subject split
> (2026-08-07 — mechanical group-dependency analysis: the subject
> groups are FULLY CYCLIC, Equal↔Conv↔ListNum↔If; a clean split needs
> real dependency untangling, not moves). Fallback options for a later
> increment — SUPERSEDED (2026-08-07, user discussion): the file's OWN
> /-! sections are the true subjects (Layer 0/1/congruence/subst →
> Layer 2/derived/D4/combinators/induction → totality walks → DP
> leaves/clausify/TP → R-judgment/EvTrue/μ-pack) and sit in dependency
> order — so a SECTION-ALIGNED POSITIONAL split (the NodeCore
> technique, ~5 modules: Core/Derived/Totality/Discharge/Judgments) is
> dependency-correct by construction, subject-coherent, token-diff
> provable, facade-preserved. EXECUTES after the coverage-gate audit's
> fix round (user-approved; no further audit — kernel-checked content,
> not the gate/TCB).
> (3c) Imported/Sorting.lean → per-book modules (the Mirrors/* pattern
> already half-exists). (3d) record a soft module-size norm (~1500
> lines; new lemma FAMILIES get their own module) in CLAUDE.md's
> engineering-quality bullet. Escape hatch: stop and report if a split
> changes any golden row (beyond formatting), hits a mutual-def knot
> that demands real refactoring (not moves), or a Lake/elab
> constraint. PERF ARC COMPLETE (2026-08-07, sprint-closing claim-gate
> TRUE_EXIT=0, golden byte-identical): 1 ✓ (per-book coverage: cold
> 6m28 vs ~15m, NO-OP 1.1s), 2 ✓ (parallel capture), 3a ✓ (NodeCore →
> six positional slices, move-only, import chain = def-before-use
> order; facade preserved; Ctx/Node grandfathered), 3b escape-hatched
> (cyclic subject groups — analysis recorded), 3d ✓ (size ratchet in
> ci + CLAUDE.md norm), 4 deprioritized (user ruling). Branch
> mdd/perf-arc READY FOR MERGE on sign-off. RECORD CORRECTION +
> GATE-AUDIT REMEDIATION (2026-08-07, the coverage-gate audit — 3
> stale-pass routes DEMONSTRATED, all fixed): 0ec18cb's "closing
> claim-gate TRUE_EXIT=0" claim was FALSE (its referent was a
> fast-gate commit; the last true full gate was 70e259a, before
> 3a/3d) and fe146a1's tree failed ci (ratchet red — the ls-files
> miss) — both corrected by THIS round's genuine tip claim-gate.
> Fixes: A1 invalidation now runs BEFORE capture (partial parallel
> captures can't leave cached-green modules); A2 log-sha256 binds
> every log's BYTES in the sidecar (out-of-band edits fail ci); A3
> check-golden-current in ci (hand-edited golden vs assembled .actual)
> + the repin recipe named in the harness error; A4 .actual sections
> written BEFORE the golden throw; A5 check-proof-logs covers the
> IO-read corpus; A6 one invalidation script (recursive) for capture +
> repin; B3 zero-edge sentinel + corpus-list length tie; D1-D4 ratchet
> exact-match/dup-fail/stale-fail/untracked-universe. Residual notes
> (recorded, accepted): B1/B2 golden-format assumptions (safe today),
> B4 counts-from-golden semantics, A6-note rm-list no longer
> duplicated, C4 remaining fast-gate claims verified OK. EvalLemmas
> SPLIT LANDED (68d2e92: five section-aligned slices, token-diff
> proven 55,864 identical; facade preserved; user-ruled no further
> audit — kernel-checked content). ARC-CLOSING claim-gate TRUE_EXIT=0
> at the post-split tip; golden byte-identical. mdd/perf-arc READY
> FOR MERGE on sign-off. THEN (ii) Phase 2
> (equisort = parametric encapsulate).
> Exit criterion: gate green, all remaining drift markers gone,
> bsort residue honestly classified. Then Phase 2 (equisort =
> parametric encapsulate).

> **CURRENT STATE (2026-08-06): the close-out arc MERGED to main
> (c85d2be, ff; sign-off at the moment of merge). B1 and R4 both
> user-ruled and expiry-marked. Two external reviews received and
> verified (docs/audits/2026-08-06_overall-project-audit.md +
> 2026-08-06_full-acl2-forward-design-review.md). GOVERNING NEXT:
> docs/plans/2026-08-06_capstone-demo-arc.md (DRAFT, awaiting MDD
> ratification) — sorts-equivalent by PURE REPLAY (fork batch, now 8
> items → equisort/parametric-encapsulate → R7b functional
> instantiation → capstone mirrors), with Phase 0 remediating the
> reviews' P0 authenticity findings and every review finding mapped to
> a phase or an explicit recorded deferral. The demo framing and the
> banned content-supplying-bridge line are user-ruled 2026-08-06.
> Open user gates: ratify the arc plan; item-by-item fork-batch
> review before the Phase-1 rebuild.

> **SORTING-ABSOLUTE ARC (branch `mdd/sorting-absolute`, opened
> 2026-08-01 at main 557c37b) — CLOSED (superseded by the close-out
> arc; kept for history).**
> MDD-ratified charter: docs/plans/2026-08-01_sorting-absolute-arc.md.
> Goal: the 11-book sorting family to ABSOLUTE completion,
> generalization first. Phase 1 INDUSTRIALIZATION (1a
> driver_replayed%/runner unification; 1b the exec-kit generator
> `derive_exec%` validated by regenerating + retiring the ~20 hand kits;
> 1c the total:/tp: discharger registry; 1d decode-kit v2 into
> Imported/Lifting.lean); Phase 2 WHOLE-BOOK FEATURES (2a cross-world
> rule: discharge + how-many/orderedp/convert-perm-to-how-many
> first-class; 2b the msort ACL2-COUNT-EVENS frontiers; 2c ORDERED-PERMS
> dp-fact emission; 2d R7 :use/functional-instantiation DESIGN NOTE —
> the arc's planned MDD checkpoint; 2e the bsort clausify-region recon
> wall; 2f BUG-027 ratify-or-narrow); Phase 3 REST OF BOOK (bsort +
> equisort/R6 into the sweep, mirrors via the generator, pins toward one
> per book).
> **2e SCOPED (read-only, 2026-08-01): the bsort recon crash is
> `collectClausify: expected split/out, got rewriteStep` (ProofTree.lean
> ~390-417): inside a clausify block, CLAUSIFY-EXPAND markers interleave
> with the ordinary REWRITE-STEP events DETAILING each expansion's
> internal chain (the second expand-abbreviations pass inside
> clausify-input — bsort log line ~18428: CONS-EQUAL expand, then
> preprocess/equal-self (EQUAL X4 X4)→'T + preprocess/if-iff steps,
> then the next expand). Census: 4 interleaved steps in the whole bsort
> log — small class. Fix shape: collect the steps into the clausify
> structure attached to their expansion (recon), then bridgeClausify
> replays the expansion chains (the BSORT-IS-ISORT
> "replayPreprocessChain lhs mismatch" downstream blocker). Verify
> against the fork's emission order which side of the marker the steps
> attach to before building.
> RECON LANDED (sub-arc mdd/bsort-recon): fork emission order settled
> the attachment — the marker is pushed AFTER expand-and-or returns
> (induct.lisp emit/clausify/expand), so detail steps PRECEDE their
> marker; steps between markers N and N+1 belong to N+1.
> ClausifyExpansion.detail carries them (raw events, emission order);
> collectClausify accumulates pending steps per phase and hard-fails
> on trailing steps with no owning marker; runCheckedExpand hard-fails
> (never ignores) an expansion carrying detail — the detail-chain
> REPLAY is the remaining 2e follow-up (it gates the BSORT-BOOK rows'
> clausify regions; BSORT-IS-ISORT itself is R7-gated — the fold-back
> audit F10 confirmed its clausify block has NO expands/detail, and
> its wall is the useHint/clausify composition, now a precise R7
> hard-fail per F12). bsort's dump-proof-tree now reconstructs
> end-to-end;
> p4-iff-or-shape re-pinned truthfully to its next frontier (or-shape
> iff chain still IFF at literal root — the R-parameterized
> literal-chain class, the book's original target class).**
> **PHASE 1 COMPLETE (2026-08-01, commits 5e01361..89e64ea).** 1a: one
> shared replay-channel builder (bookChannels/mkBookConfig/
> replayAdmission) for runner + macro — found and fixed the macro's
> missing gzTps channel. 1b (sub-arc mdd/exec-gen, AUDITED — 1 Opus,
> zero soundness findings, F1/F2/F3/F4b fail-open holes fixed):
> `derive_exec%` generates exec def + stage-1 corr (M1 destructor
> chains + M2 pair sums), kit registry, canonical telescopes; RETIRED
> same-name+same-statement 8 kits (~600 hand lines) — insert, isort,
> how-many, rel, all-rel, filter, evens, merge2; M3
> (decrease-through-function: msort/qsort/oLt) stays hand, named
> frontier. 1c: derive_exec_total% / derive_exec_tp% (wrapper generated,
> value-shape ending human, u0…uN binder contract) — 5 dischargers
> retired. 1d: five decode combinators promoted to Imported/Lifting.
> Every increment build-green + sweep golden byte-identical.
> **2a CROSS-WORLD RULE DISCHARGE (sub-arc mdd/cross-world, 2026-08-01):
> convert-perm-to-how-many is a first-class sweep book (13 rows, 7
> green; how-many/orderedp are DEFUN-ONLY — nothing to replay); prior
> books' theorem trees ride the shared depProofs channel (sweep
> corpus-order accumulation / macro `deps [devs]` clause / CLI
> `--deps`), so included rule: hypotheses discharge by re-replaying the
> dependency tree AT THE CONSUMER'S WORLD (dischargeRuleHyp's
> no-registry route, formula cross-checked against the stored rule,
> fail-closed at every layer). Sweep 71/79 → 78/92; the 9
> rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0 conditions DISCHARGED across
> isort/qsort/msort rows; dis_not_memb_how_many_0 DELETED; SortingPins
> telescopes re-transcribed. rule:CONVERT-PERM-TO-HOW-MANY stays a
> condition (its own replay is R7-blocked — retires with 2d);
> arithmetic-3/gz rules stay on value-level gz dischargers (no captured
> logs, by design). En-route defect fixed: an `elab` optional
> multi-parser group binds `none` even when present — the deps clause
> now a named syntax node (same lesson as derive_exec%'s corrClause).
> **SEQUENCING AMENDMENT (Mike, 2026-08-01, going AFK): the R7 design
> note (2d) is DEFERRED TO LAST — do not block on it while Mike is
> unavailable; draft it en route, present for ratification when they
> return, build NOTHING on it before ratification. Order is now
> 2b → 2c → 2e → R7-independent P3 work (bsort sweep entry, mirrors,
> pins), THEN 2d + its dependents (the *-IS-ISORT capstones,
> dis_convert_perm retirement, equisort/R6 pairing).**
> **2b IN PROGRESS (sub-arc mdd/linear-verdicts): increment 1 LANDED —
> the LINEAR-EQUALITIES CASE SPLIT arm (Core.lean, the branch-
> substitution none-justification route): byCases on the derived
> equation's escape literal; equation-holds peels the child's ¬eq head
> (evtrue_tail_of_if_head_nil) + diffCollapse transport; equation-fails
> closes by the DP carve-out on the constructed obligation
> `eq ∨ parent-clause` (replayDischargeNode; BRANCH-granularity
> verdict class — see the ratification queue). Child adopted via
> rec.clause on the exact recorded clause. + logic_not_equal_ne_nil_
> eq_nil (EvalLemmas). ACL2-COUNT-EVENS-STRONG advanced TWO frontiers;
> now at: *1/2.3''s spine carries CLAUSE-LEVEL rewriting-equivalence/
> rewrite/definition items the linker left unattached (a definition
> item targeting (ACL2-COUNT X) which does NOT occur in the child's
> clause — investigate buildLiteralProofs' linking for this record
> class BEFORE writing replay support; raw log line ~2937, msort book).
> Increment 2 LANDED: clause-level solidify/with-lemma SETUP MEMOS
> consumed under the ratified positional gate (forensics agent report:
> they are rewrite-linear-term's pot-setup rewrites of the instantiated
> :LINEAR lemma conclusion — not clause transformations; the real
> change is re-recorded at its literal; the step's :RUNES omit the
> memos' runes — witness). STRONG now at *1/2.3''' —
> process-equational-polys ADDS the derived equation literal
> (NOT (EQUAL (AC (CAR X)) (B+ '-1 (AC X)))) with NO transforming
> item. CONVERGED DESIGN with WEAK: both need DP obligations that
> consume the cited :LINEAR rule's fact (ACL2-COUNT-CAR-CDR-LINEAR —
> an in-book theorem; feed its replayed statement/instantiated fact
> into replayDischargeNode's premise set alongside tpData, or as a
> rule:-condition). CORRECTION: ACL2-COUNT-CAR-CDR-LINEAR is a
> GROUND-ZERO linear rule (acl2/axioms.lisp:30540), NOT an in-book
> theorem — its fact takes the gz value-level route (provable from the
> acl2CountExec kit: count(cons) = 1 + count(car) + count(cdr)) as a
> linear:-class hypothesis/discharger, not a replayed statement. STRONG's remaining piece
> (increment 3, DESIGN SETTLED): an items-exhausted arm for the
> equation-ADD shape — gate: exactly one recorded child whose
> inputClause = ¬eq :: (current lits unchanged), step runes citing
> fake-rune-for-linear-equalities + a :LINEAR rune. byCases on v(¬eq):
> nil peels the replayed child's head (evtrue_tail_of_if_head_nil — no
> transport, clause unchanged); ≠ nil = the DP obligation `eq ∨ parent`
> WITH the cited gz :LINEAR rule's content as a NEW HONEST HYPOTHESIS
> CLASS `linear:ACL2-COUNT-CAR-CDR-LINEAR` (the D6 pattern: declared in
> the conditional harness like tp:/rule:, consumed by
> replayDischargeNode's premise set alongside tpData, kept in cond[…]
> until the Imported-side discharger proves it from the acl2CountExec
> kit — count(cons) = 1 + count(car) + count(cdr), which the kit
> states directly). The obligation is NOT valid without it
> (independent-opaque counter-model) — no shortcut exists.
> **2b COMPLETE (sweep 80/92): ACL2-COUNT-EVENS-WEAK ✓ (tp + 2 gz
> rules), ACL2-COUNT-EVENS-STRONG ✓ (+ linear:ACL2-COUNT-CAR-CDR-LINEAR
> and one honest ASSUMED:dp-fact whose full closure needs WEAK's own
> content as a same-book linear rule — the replayed-statement route,
> queued). CORRECTED (fold-back audit F1, experimentally refuted): the
> ASSUMED leaf needed the CAR-trigger instance of the SAME emitted rule
> — the harness dedup discarded per-max-term records; FIXED (offers
> carry every emitted spec sharing the content-deduped fvar), STRONG's
> ASSUMED:dp-fact is GONE, that follow-up retired. Audit follow-ups
> queued instead: F2/F4 provenance gates; F5 gz-defun closure over
> linear/fc entry fns; F7 user-defined :LINEAR rules (no snapshot).
> DP-PREMISES fold-back follow-ups (2026-08-01) queued: leaf-class
> gating for the rule pass (plumb the leaf origin into
> replayDischargeNode — the open ratification sub-question);
> :rule-classes/:equivalence provenance emission (equivrefl gate is
> shape-parse only); audit F6 — a throwFrontier while BUILDING a
> premise downgrades the leaf to the ASSUMED fallback even if
> provable premise-free (needs a design that never silently drops a
> premise); substN scaffold extraction DONE (mkSubstNBridge — the
> linear/rule/instantiateEvTrueHypAt copies retired, σ-term pinning
> now uniform, audit F3 fixed).
> The linear-verdicts machinery end-to-end: gz :LINEAR spec
> emission → linear: hypothesis class → max-term-matched DP premises
> (bounded-fixpoint instantiation; premise-free fallback twin for the
> harness offer) → the equation-ADD and case-split spine arms → the
> POSITIVE-SUM type-set cell → the linear-contradiction discharge
> emission (fork 1a8e379684). Fold-back audit NEXT.**
> NUMERIC CELL LANDED: the second registered
> equal/type-set-nil disjointness cell — POSITIVE-SUM vs '0
> (logic_equal_nil_of_plus1_nonneg; x = (B+ '1 (B+ p q)) with p q's
> EMITTED nonneg-int TP corollaries at pinned values; falls through to
> cons-vs-atom otherwise). STRONG advanced past *1/2.1 → now at
> *1/2.1.2' = a simplify :RESULT :PROVED by linear verdict with NO
> discharge record — EXACTLY WEAK's wall (raw log line ~6430). ONE
> remaining 2b piece: the fork discharge record for linear-PROVED
> simplify leaves (emit a discharge node when simplify closes a clause
> with fake-rune-for-linear + :LINEAR runes and no transforming items;
> the existing DP-leaf machinery + the landed linear: premises replay
> it). Closes BOTH rows.
> 3b-iv LANDED: oneWayMatch (the replay's ONLY
> matcher — verdict-class :LINEAR premises record no :SUBST; pattern =
> the EMITTED max-term), linData premises in replayDischargeNode
> ((IF hyp (EQUAL l r) 'T) — cond-shaped like TP corollaries, zero new
> lift machinery; concrete facts via the substN scaffold
> (bindArgsOver/evalOpt_substTerm_substN — inline twin of the
> with-lemma recipe's, extraction queued) + linear_premise_fact
> (EvalLemmas); premise opaques EXTEND the obligation's opaque set;
> v1 gates: exactly 1 stored hyp, EQUAL concl, all rule vars bound).
> + the EQUATION-ADD close in the spine's base case (tryEqAdd probe:
> one child = ¬eq :: unchanged lits; byCases; nil peels the replayed
> child, ≠ closes by the DP obligation eq ∨ clause). ACL2-COUNT-EVENS-
> STRONG advanced THROUGH *1/2.3''' — now at a NEW class:
> "type-set-equality: no consp evidence for (BINARY-+ '1 …)" with
> induction vars X3/X4 — the numeric-TP ⇒ ¬consp lattice rung (the
> INC-1a recognizer class) missing at the type-set-equality consumer;
> extend typeSetWalk's isConspT/isNil evidence with the
> arithmetic-value route (TP nonneg-int of the BINARY-+ args ⇒ the
> sum is a number ⇒ not a cons).
> 3a LANDED (50e6ec9 + fork c85dcd80): the gz :LINEAR spec emission
> end-to-end (collectors + event + parser + Development accessor +
> recapture-all at clean stamps; ci green, rows unchanged).
> 3b REFINED DESIGN (dpFactStmt read): (i) ReplayConfig gains
> linearRules from dev.groundZeroLinearRuleSpecs via mkBookConfig (one
> site, 1a); (ii) NEW hypothesis class `linear:<rune>` in the
> conditional harness — schematic over env' like mkRuleHypType:
> ∀ env', EvTrue hyps → EvTrue concl; (iii) replayDischargeNode
> matches opaques against specs' maxTerm (unify → substitution),
> instantiates (hyps→concl) as an IMPLIES term, adds it to dpFactStmt's
> premise row as a tpCors-STYLE value premise (v(implies-term) = t);
> the concrete fact at application: linear-hyp fvar at env → EvTrue →
> conv pin → ne_nil → two-valued implies → = t; (iv) proveDpFact's
> INT-VIEW lift may need an implies-decomposition row (iterate on the
> real error); (v) stage-5 accounting: linear: conds ride the
> used-filter like tp:; assemblies discharge them from the
> acl2CountExec kit later (or keep honest conds).
> Then: the STRONG equation-ADD arm (items-exhausted, design settled
> above) consumes the same premise machinery; WEAK additionally needs
> the fork discharge record for linear-PROVED simplify leaves
> (*1/2.2', :RESULT :PROVED, no transforming items) — the remaining
> fork half.
> ROUTING DECISION (2026-08-01): the cited :LINEAR rule's FORMULA is
> NOT emitted (rune name only — verified against the msort log), and
> CLAUDE.md's emit-more rule forbids hand-stating it Lean-side. So
> increment 3 is FORK-FIRST: one fork batch emitting (a) gz
> :LINEAR-rule spec snapshots for cited runes (the
> groundZeroFcRuleSpecs precedent — hyps + trigger + concl), and
> (b) the WEAK discharge record — a discharge node when simplify's
> linear arithmetic closes a clause (*1/2.2', :RESULT :PROVED with
> linear runes and NO transforming items). Then recapture-all; then
> the walker consumes the spec as the DP obligation's premise
> (replayDischargeNode premise set alongside tpData) for BOTH the
> STRONG equation-ADD arm and WEAK's discharge leaf.
> WEAK (*1/2.2') detail: whole clause closed by
> linear:ACL2-COUNT-CAR-CDR-LINEAR verdict, no discharge record
> emitted.**
> **PROCESS NOTE (2026-08-01, for the fold-back audit): a plain
> `lake build` did NOT re-elaborate Tests.DriverCoverage after a
> Driver-core change in one observed instance (stale .actual, golden
> gate silently not exercised) while it demonstrably DID in earlier
> increments — unresolved lake target/caching inconsistency. Golden
> verification now ALWAYS via explicit `lake build
> Tests.DriverCoverage` or `just ci`; auditors should not accept
> "build green" as "sweep gate ran" without timings/actual-freshness
> evidence.**
> **2c DESIGN (post-2b reassessment): the ORDERED-PERMS dp-fact gap is
> now the ESTABLISHED premise pattern, likely NO fork emission needed —
> the four ASSUMED obligations need value-defining links ((PERM A A)
> truthy = reflexivity; the ORDEREDP/PERM functional ties), and 2b's
> replayDischargeNode premise architecture is the vehicle: instantiate
> the ALREADY-OFFERED equivrefl:/fc-rule content as tpCors-style
> premises via the same substN transport (oneWayMatch on (R u u)
> opaque shapes for equivrefl; cfg.fcRules' trigger/concls for FC).
> REFINED (Subgoal 2 dumped, op-tree line 1675): the leaf
> {…¬(EQUAL A B) ∨ (EQUAL (PERM A B) 'T)} needs the premise
> `(IF (EQUAL A B) (EQUAL (PERM A B) 'T) 'T)` — the equivrefl instance
> (PERM u u truthy) carried to the pinned (PERM A B) opaque across an
> ARG-CONGRUENCE eval transport (va = vb → eval (PERM A B) = eval
> (PERM A A); the fuel_eq/diffCollapse machinery). Same conditional
> cond-shape as 2b's linear premises; implement as an equivreflHyps
> premise row in replayDischargeNode with the substN + congruence
> transport. The other three leaves (ORDERED-PERMS' OWN *1/3
> type-set-fc, *1/4 tau, *1/6 tau — NOTE: grep the dump WITHIN the
> ORDERED-PERMS theorem region; the first *1/3-*1/4 matches are
> ORDEREDP-RM's unrelated subgoals) to be classified the same way;
> CLASSIFICATION COMPLETE (region-scoped, op-tree 1647+): ALL FOUR are
> replay-side premise work — NO fork emission needed (the catalog's
> 'blocked on emission' is SUPERSEDED by 2b's premise architecture):
> (1) Subgoal 2 — equivrefl (PERM u u) + arg-congruence transport
> under the clause's A = B (designed above); (2) *1/3 — the
> TRUE-LISTP/CDR value-defining link: a DEFN-UNFOLD premise (one conv
> unfold of the opaque (TRUE-LISTP A) at pinned values relates it to
> (TRUE-LISTP (CDR A)) — the emitted defn body IS the link); (3) *1/4
> — TRUE-LISTP-RM's content: the SAME-BOOK replayed-statement premise
> route (the theorem is a GREEN row in this very book — apply its D1
> mirror as a dp premise, the dischargeRuleHyp pattern
> premise-shaped); (4) *1/6 — ORDEREDP-RM's content, same route.
> Implementation order: (3)/(4) first (the same-book premise row —
> one mechanism, two leaves), then (1), then (2).
> INCREMENT 1 LANDED (sub-arc mdd/dp-premises): rule_premise_fact +
> the RULE-content premise pass in replayDischargeNode (boolean-
> strengthened equal/'T one-hyp stored rules; lhs as the trigger; the
> substN scaffold's THIRD copy — extraction queued). ORDERED-PERMS
> 4 → 3 ASSUMED:dp-fact (the flipped leaf was *1/6/ORDEREDP-RM).
> INCREMENTS 2–4 (all four leaves now close IN-TELESCOPE — the
> composed cond row carries zero ASSUMED:dp-fact,
> conds = [rule:CONS-CAR-CDR, rule:ORDEREDP-MEMB,
> equivrefl:PERM-IS-AN-EQUIVALENCE]; the standalone DISCHARGE probes
> have no premise machinery, so three still read ◌ there and the DP
> scoreboard moved 45→46 (the trueListp bridge only) — legend now in
> Tests/DriverCoverage.lean, audit F8):
> (2) *1/4 — the v1 opaque-only trigger MISSED lift-primitive-headed
> rule LHSes ((TRUE-LISTP (RM E A)): TRUE-LISTP lifts to
> Logic.trueListp, only the inner RM is opaque) — match targets
> widened to ALL application subterms (collectAppSubterms in
> NodeCore + ruleTargets in the rule pass).
> (3) *1/3 — NOT a premise class after all: the missing link is the
> trusted-core primitive's OWN recursion (Logic.trueListp under consp
> evidence), a DP-leaf BRIDGE in the endp/len precedent —
> Logic.trueListp_cdr_of_consp added to dpLeafTactic's simp sets
> (the split path's cone mode clears the A-hyps, so the DIRECT
> simp_all path is the closer, as in *1/4).
> (4) Subgoal 2 — equivrefl premise class, SIMPLER than classified:
> the probed leaf's application is syntactically reflexive
> ((PERM A A) — no arg-congruence transport needed): premise
> (NOT (NOT (R u u))) via instantiateEvTrueHypAt (the SHARED substN
> slice — no new scaffold copy) + equivrefl_premise_fact (EvTrue
> gives ≠ nil; the TP booleanp cell closes to 'T inside the fact).
> The classified congruence-transport variant ((PERM A B) under
> EQUAL A B) did NOT occur in the real obligation — not built (would
> be a new class if a book ever needs it).
> NEXT: full-sweep golden review (widened triggers + the trueListp
> bridge can move OTHER rows — review row by row), then the
> dp-premises comprehensive audit + fold-back. [DONE — audited,
> fixes applied, folded back.]**
> **P3 MIRROR PROBE FINDING (2026-08-01, the ORDERED-PERMS mirror):
> the mirror is GATED on CROSS-BOOK RULE OFFERS — discharging
> equivrefl:PERM-IS-AN-EQUIVALENCE re-replays the perm-book tree at
> the ordered-perms world, which transitively cites
> rule:PERM-SYMMETRIC, a rule the ordered-perms log NEVER re-emits
> (grep: zero occurrences) — the consumer telescope cannot offer it.
> Fix = the 2a completion: bookChannels carries the dep books' STORED
> RULES alongside their trees (crossRules), the telescope offers them,
> and the discharge loop closes them transitively from crossTrees.
> NOT a hand discharger (the flagged non-opportunity species).
> dischargeEquivReflHyp is BUILT (Harness; the and-projection route,
> fail-closed, sweep byte-identical) and fires when the channel
> lands. rule:ORDEREDP-MEMB's discharge frontiers on the same
> transitive-offer class. Queued as the first item of the
> post-ratification arc segment.
> CHANNEL LANDED (sub-arc mdd/cross-rules, same day): allBookRules +
> combineRules + BookChannels.crossRules; corpus-order priorRules in
> the sweep; deps[devs] in the macro; --deps in the CLI. Sweep diff
> exactly the ORDERED-PERMS row: equivrefl:PERM-IS-AN-EQUIVALENCE
> DISCHARGED (the equivrefl arm fires); row now
> cond[rule:CONS-CAR-CDR, rule:ORDEREDP-MEMB]. v1 gap logged in the
> allBookRules docstring (a book's LAST theorem's own rule is in no
> snapshot — fail-closed). NEXT for the mirror: probe why
> rule:ORDEREDP-MEMB's same-book discharge still frontiers (its D1
> registry constant keeps rule:DEFAULT-CAR — the registry route
> should map it to the consumer telescope), then the native
> statement assembly.
> CAPSTONE LANDED (bfc93ed): ordered_perms_native_driver —
> (xs == ys) = xs.isPerm ys for lexorder-sorted lists + the List.Perm
> corollary (sorted permutations are EQUAL), kernel-checked from the
> replay, axioms clean, seam gate green, catalog .native — the last
> pending ordered-perms mirror. En route: routeNotBool (the negative
> boolean strengthening, ORDEREDP-MEMB's shape — no TP pin needed,
> Logic.not is nil-dichotomous) and the MACRO-SIDE D1 REGISTRY
> (mirrorRegistryExt in Provers + getDeclName? registration +
> world-filtered mirrors — parity with the runner's
> ReplayedStatements route; the re-replay route frontiered on
> TRUE-LISTP-RM inside the consumer telescope where the registry
> route composes; trueListpRmReplayed registered as the dep).
> Sub-arc audit COMPLETE (2 Opus reviewers, both
> fold-back-with-fixes; mirror confirmed FAITHFUL incl. the
> PERM/isPerm duplicate-semantics question refuted; tamper probe
> fail-closed; fixes applied in a7e9469: axiom-gate names,
> PER-DISCHARGE heartbeat windows — the golden-nondeterminism root
> cause, a dep re-replay racing the theorem budget over the O(corpus)
> telescope, 3 data points — combineRules topological order, widening
> doc + provenance-gate queue, enc_beq warning, docstrings).
> FOLDED BACK; definitive just ci (pipefail): CI_EXIT=0,
> GOLDEN_MATCH.
> ARC MERGE POINT (2026-08-02) — PLAIN NUMBERS (rewritten per the
> pre-merge outside audit F1/F2/F4/F5; the earlier "everything
> remaining is ratification-gated" framing was overstated): sweep
> 71/79 → 80/100 (sorting: 45 green of 62 rows; family-wide 45 of
> ~103 theorems — equisort's 41 defthms are NOT in the sweep and R6
> is UNBUILT fork-emission + design work, not ratification-gated);
> +2 green on rows that existed at arc open (the msort count rows);
> 0 new unconditional rows; red rows 8 → 20 (bsort's 8 entered as
> honest frontiers; 3 newly-red rows are NOT yet frontier-tagged —
> named below); statement pins 11 → 11 (ZERO new pins this arc — the
> P3 "pins toward one per book" bullet was skipped; existing pins
> strengthened instead); 3 native-worthy convert-perm mirrors still
> .pending (carried debt below). What the arc genuinely delivered:
> the industrialization (generator −773 hand lines), the premise/
> cross-rules/registry machinery (each unblocking a named target),
> bsort recon + corpus entry, the ORDERED-PERMS capstone mirror
> (verified non-ornamental), and 6 audited sub-arc fold-backs
> (consolidated record: docs/audits/2026-08-02_sorting-absolute-
> arc-audits.md). Post-ratification the residual is DECIDED-BUT-
> UNBUILT (R7a, R6, BNEXT-SIZE admission route, BUG-027 emission),
> not externally gated.**
> **CARRIED DEBT (pre-merge audit F3/F4/F12, explicit): (a) three
> native-worthy convert-perm green rows still .pending — HOW-MANY-RM,
> NOT-MEMB-IMPLIES-RM-IS-NO-OP, NOT-MEMB-IMPLIES-HOW-MANY-IS-0
> (small mirrors: List.count_eq_zero / List.erase_of_not_mem class);
> (b) statement pins: 0 added this arc, 2 of 8 sweep books covered —
> next arc's P3-equivalent owes pins for convert-perm + bsort at
> minimum; (c) three newly-red rows lack the (frontier) tag and are
> unclassified frontier-or-bug: ORDEREDP-WHEN-BNEXT-CONSTANT
> (pathStepsFromFrames, frames []), PERM-COUNTER-EXAMPLE-IS-
> COUNTEREXAMPLE-FOR-TRUE-LISTS (replayRecognizer does not reduce to
> T), PERM-TLFIX (solidify: source literal heads NOT/PERM) — all
> hard-fail (no silent skip), classification owed; also the
> (frontier) suffix is per-message prose, not a mechanism — a
> frontier-classification mechanism is a queued improvement;
> (d) derive_exec% FIDELITY CAVEAT (surfaced from the
> industrialization note per audit F7): the generator reads
> HAND-TRANSCRIBED Lean SExpr body constants + hand-supplied measured
> indices, NOT the emitted :DEFUN :BODY/:MEASURE — fidelity holds
> because every consumer pins the body against the log-derived world
> by decide, but the generator-reads-the-log step is still owed
> (12 hand exec defs remain of the ~20; 8 retired).**
> **AUDIT FIX ROUND (2026-08-03, per docs/audits/
> 2026-08-03_emission-cluster-audit.md — the ratified remedy):
> brackets structural (include-path BEGIN + empty-encapsulate END +
> honest invariant comments + Lean depth enforcement with stray-END/
> unclosed-EOF hard-fails + the cov-defun-sk misdiagnosis fixed to
> name the missing :QED); TamperTests arms; :CLASSES → Option SExpr
> threaded into ClauseProof; dead literal-window fcDerivations branch
> DROPPED (hard-fails if the shape ever appears); collect-parents +
> :fc-round in both fcd emissions; provenance BANNER cross-check in
> check-log-provenance (catches image/commit skew); claim-gate.
> STANDING OBLIGATIONS RECORDED: (a) PHASE-4 per-scope :DEFTHM dedup
> (both passes re-emit inside the bracket — the parser does NOT dedup
> yet; two earlier present-tense claims corrected); (b) the PHASE-6
> :FC-DERIVATIONS consumer must HARD-FAIL on a missing :CONCL join —
> the event is silently absent when no log is open (forward-chain-top
> also runs from induct/built-in-clausep/bdd), so absence must never
> read as "no forward chaining" (audit F10).**
> **PHASE 1 COMPLETE (2026-08-03, folded back at 2dbb289): fresh
> verifier returned FOLD-BACK-WITH-FIXES (N1-N6, recorded in the audit
> file); fix set a-e executed — include-path :empty-encapsulate END
> (the FOURTH success exit, fork 286e7ac871) pinned by the new
> cov-encapsulate-empty-{helper,include} pattern books (sig pins +
> encapsulate_empty_pins%), pattern-map re-pin, :CLASSES threaded
> through includedTheorem, sidecar image-mtime + banner fail-closed,
> stale-block strike-through. Round gates: recapture 91 logs,
> provenance 91/91 banner==stamp, golden BYTE-IDENTICAL (80/100
> unchanged), claim-gate TRUE_EXIT=0. Phase 2 (R7a) unblocked on the
> :LMI-LST payloads.**
> **PHASE 2 (R7a) BUILT (2026-08-04, sub-arc mdd/r7a): the plain-:use
> composition — `use:<thm>` premise channel (UseSpec + lmiInstance? +
> mkUseHypType + demand-driven offers read off the tree's :LMI-LST +
> dischargeUseHyp from the dependency's replayed statement +
> depMirrorProofAt use: arm), and the apply-top-hints-clause arm:
> constraint chain on CONSTRAINT-CL (trivial-('T)-only — non-trivial =
> R7b hard-fail), per-lmi σ-transport via instantiateEvTrueHypAt with
> verbatim :HYPS cross-check, application clause (¬hyps ++ input,
> shape-checked) proved by its child, ¬Lᵢ heads peeled by
> evtrue_extract_else. Sweep 80→81: LEN2-APP-VIA-USE REPLAYED ✓
> cond[tp:LEN2] (use: hyp discharged); CONVERT-PERM-TO-HOW-MANY
> advances past the R7 frontier to the congruence-collapse wall
> (PERM arg 0 under PERM, cited runes [] — Phase-3 class);
> MSORT/QSORT-IS-ISORT re-pinned at the precise R7b frontier
> (non-trivial :CONSTRAINT-CL named). Golden re-pinned row-by-row
> (4 changes reviewed).**
> **R7a AUDIT FOLLOW-UPS (READY-WITH-FIXES, 2026-08-04; F1-F4 fixed
> in-arc — see docs/audits/2026-08-04_r7a-use-composition-audit.md):
> (F5) the arm's `negs` re-derives dumb-negate-lit as a naive (NOT h)
> wrap while ClausifyBridge.dumbNegateLit exists — a (NOT p) hyp's
> app clause won't match (hard-fails honestly); unifying needs the
> peel's falsity derivation per dumbNegateLit arm. (F6) the R7b
> frontier message is inferred from constraint-clause SHAPE, not the
> lmi — :use (:theorem …) would be mislabeled; label off the lmi when
> R7b lands. (F7) dischargeUseHyp's formula check is a same-source
> assert, documented as such. (F8) the depMirrorProofAt use: registry
> arm is corpus-unexercised (no row keeps a use: cond yet) — exercise
> when a multi-book :use chain appears. Also: include-book :use
> citations need the TRANSLATED statement emitted (the F1 fallback was
> dropped as untranslated) — an emission follow-up.**
> **PHASE 3 CLASSIFICATION + FIRST CLASS FIX (2026-08-04, sub-arc
> mdd/convert-perm-reds): (1) GROUND-HYP KNOWN-TRUE class FIXED —
> RELIEVE-HYP/KNOWN-TRUE markers on a CLOSED hyp instance
> ((TRUE-LISTP 'NIL)) are ACL2 type-set computations recorded
> verdict+runes only (the ratified carve-out shape); replayed by
> replayExecGround (the SYNP treatment). TRUE-LISTP-RM + RM-TLFIX
> flip green (sweep 81→83); PERM-COUNTER-EXAMPLE-TLFIX-2's cond set
> shifts honestly (rule:RM-TLFIX now DISCHARGED, transitive
> rule:CONS-CAR-CDR surfaces). (2) PERM-TLFIX CLASSIFIED: the
> R-SOLIDIFY class — the solidify source literal is the IH under the
> USER EQUIVALENCE PERM ((NOT (PERM (TLFIX (CDR X)) (CDR X)))), and
> solidify only decodes EQUAL equations; the fix is the L2
> R-parameterized solidify lane (type-alist equivalence classes under
> R). (3) CONVERT-PERM-TO-HOW-MANY's post-R7a wall CLASSIFIED: same
> lane — replayCongCollapse needs a PERM-arg-0-under-PERM congruence
> frame with EMPTY step-cited congruence runes (ACL2's type-alist
> R-class rewrite cites no defcong; the license is the equivalence
> rule itself). (2)+(3) are ONE class: type-alist-under-R. Remaining
> unclassified: PERM-COUNTER-EXAMPLE-…-TRUE-LISTS (replayRecognizer:
> no TP for RM), HOW-MANY-RM-GENERAL (ambiguous anchoring),
> ORDEREDP-WHEN-BNEXT-CONSTANT (pathSteps frames []).**
> **THE R-SOLIDIFY LANE, ARTIFACT-ANCHORED DESIGN RECORD (2026-08-04;
> the L2 build the class needs — read the PERM-TLFIX Subgoal *1/2'
> literal-3 chain, e.g. `lake exe acl2lean dump-proof-tree
> acl2_samples/sorting/convert-perm-to-how-many.proof-log`): the
> failing node is `rewriting-equivalence:NIL [solidify/rewriting-
> equiv] ⟨rhs⟩ (TLFIX (CDR X)) => (CDR X), equiv: (PERM (TLFIX (CDR
> X)) (CDR X)), justified by hypothesis literal 2 (the IH)` — an
> R-rewrite at PERM's OWN arg-1 position, runes citing
> equivalence:PERM-IS-AN-EQUIVALENCE and NO defcong. THE LICENSE IS
> ACL2'S BUILT-IN GENEQV RULE: an :EQUIVALENCE rune doubles as
> congruence at the relation's own argument positions. So the build
> is: (a) R-frames for equivalence-rune-licensed positions (the L2
> "congruence-rune recipe" with the equivalence rule as the recipe);
> (b) solidify decode for an R-source literal — (NOT (PERM A B))
> assumed false gives EvTrue (PERM A B); (c) value-level composition
> v(PERM A b) = v(PERM A' b) from the equivalence rule's replayed
> statement (booleanp+sym+trans conjuncts — widen the equivrefl
> channel to the FULL defequiv statement or reuse the whole-formula
> hypothesis shape) + the R-fact; (d) the follow-on reflexive close
> `type-alist:NIL [solidify/type-alist] (PERM (CDR X) (CDR X)) =>
> 'T` rides the existing equivrefl truthy arm. Same machinery closes
> CONVERT-PERM-TO-HOW-MANY's replayCongCollapse wall (its congruence
> frame with cited congruence runes [] is the same equivalence-rune
> license).**
> **PHASE 3 FINAL CLASSIFICATIONS (2026-08-04, closing the sub-arc):
> (A) PERM-TLFIX assigned to the PHASE-6 R-LANE (the p4-pinned
> R-parameterized literal-chain class): its solidify R-step rides the
> with-lemma RHS chain (`rec.rewrites` + `chainReqEq` at
> NodeCore:~3975 rejects non-equal chains), so the fix is the
> rung-2 relation threading through the literal-chain composer with
> the one-frame collapse (equivOwnPosCongr, already built) at the
> parent R-application — NOT a sub-arc-local patch. Emission facts
> pinned (CORRECTED per audit 2026-08-04 F12): emit/solidify/
> rewriting-equiv HARDCODES :equiv 'equal (rewrite.lisp ~5244) but
> the licensing relation IS recorded as the :EQUIV-TERM's head
> (find-rewriting-equivalence guarantees geneqv refinement) — AND the
> mislabeling is NOT confined to solidify: the enclosing WITH-LEMMA
> step records the RULE's :equiv (EQUAL) against a :RHS that is the
> rule rhs AFTER the R-solidify (rewrite.lisp ~20627), making its
> recorded lhs/rhs pair a FALSE EQUAL equation (holds only up to R;
> harmless today — the solidify child hard-fails first and the kernel
> would reject the equation). The fork emission fix (true per-step
> relation at solidify AND with-lemma sites) is therefore a
> PREREQUISITE for the rung-2 R threading, not optional — an R-aware
> consumer must never trust a with-lemma step's :EQUIV for its
> recorded pair. Fork-batch item.
> (B) PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS is a
> CONSUMER GAP, not emission: TRUE-LISTP-RM is `:CLASSES
> :TYPE-PRESCRIPTION` (a THEOREM-classed TP rule; RM has NO admission
> TP in the log) and replayRecognizer consults only defun-admission
> tp: hypotheses. THE FIRST :CLASSES CONSUMER (Phase-1 cluster item 5
> + fresh-verify N3 threading exist for exactly this): offer
> TP-classed theorems' whole-formula statements (the use:/equivfull
> hypothesis shape), consumed by replayRecognizer's fallback —
> match the recognizer term against the theorem conclusion (σ via
> substTerm cross-check), relieve the hyp instance from the clause
> context falsity facts, MP + boolean pin to the exact-'T verdict.
> Anchor to the node's cited rune per BUG-023. (C) HOW-MANY-RM-GENERAL
> (ambiguous anchoring) stays the :PATH-emission batch item.**
> **TPTHM-CONSUMER SUB-ARC WORKLIST (mdd/tpthm-consumer, opened
> 2026-08-04 — every piece located): (1) `matchPattern? (pattern term)
> : Option (List (Symbol × SExpr))` — deterministic one-way
> first-order matching (consistent bindings; no emitted σ exists for
> type-set TP applications, and unique matching is a read-off — the
> no-match case is a loud frontier). (2) `tpthm:<name>` offers: per
> depProofs entry whose `ClauseProof.classes` names TYPE-PRESCRIPTION
> (bare keyword like TRUE-LISTP-RM's, or a member of the classes
> list), the whole-formula ∀env statement (mkUseHypType shape; the
> FIRST :CLASSES consumer — Phase-1 item 5 + fresh-verify N3 exist
> for this). Same 4-site telescope alignment discipline + a
> dischargeCongHyp-clone + depMirrorProofAt arm. (3) Consumption in
> replayRecognizer's fallback (NodeCore ~2405 "no TP hypothesis
> for"): for each node-cited (:TYPE-PRESCRIPTION <name>) rune with an
> offer (BUG-023: cited runes only — the target node cites
> TRUE-LISTP-RM verbatim, log lines 5905-5911): parse the theorem
> formula (IMPLIES hyp concl | bare concl), matchPattern? concl
> against the recognizer term → σ; relieve σ(hyp) truthiness from the
> clause-context falsity facts (litFactByTermChecked? on (NOT hypσ) /
> segFacts — the marker-relief arm-1 lookups); instantiateEvTrueHypAt
> at σ → implies_value_mp → concl-instance ≠ nil; close the exact-'T
> verdict via the coreBool registry (logic_trueListp_ne_nil_t /
> logic_consp_ne_nil_t — dischargeRuleHyp routeBool's table at
> Harness ~225; USER-fn recognizers consume the emitted TP instead,
> per the type-facts-from-ACL2 rule). Target:
> PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS green
> (convert-perm 11/13); then sub-arc audit → fold-back.**
> **TPTHM OUTCOME + THE ROW'S NEXT WALL (2026-08-04; CORRECTED per
> the sub-arc audit F6/F7): the route FIRES and its guards pass (the
> recognizer wall falls — the sweep message advances past it), but
> NOTHING tpthm-built is kernel-checked yet (the row still FAILs, so
> Meta.check/axiom-filter/addDecl never run; dischargeTpThmHyp and
> the depMirror tpthm arm are corpus-unexercised — a green consumer
> row is the validation gate). The next wall, audit-corrected: TWO
> distinct gaps. (a) CONSUMER gap: the fork ALREADY EMITS the
> IF-collapse marker (:IF-TEST-TRUE :ORIGIN IF-FINISH/IF-TEST with
> its own :JUSTIFICATION :RUNES, log ~5888) and ProofTree.lean
> ~346-348 DISCARDS it ("IF-test markers … not standalone nodes") —
> fix at the consumer, NOT the fork. (b) EMISSION gap, precisely
> located: rewrite.lisp:18434-18440's `((equalityp rhs) …)` arm
> produces the (IF eqhm (EQUAL lhs 'T) (IF lhs 'NIL 'T)) boolean
> case-restructuring and is UNTAGGED/unlogged (its four neighbours
> at 18316/18332/18377/18392 all emit) — THIS one joins the fork
> batch. Audit follow-ups recorded: F2 flattenAnd for conjunctive TP
> hyps; F4 hard-fail :COROLLARY-bearing TP class specs; F11 the
> trusted-core two-valued registry now has THREE diverged copies
> (NodeCore ~2082/~2532, Harness ~232) — extract; TamperTests pins
> for the two anchoring gates.**
> **PHASE 4 OPENING STATE (2026-08-04, Phase 3 complete at d102d72):
> equisort.proof-log carries the full Phase-1 surface — both scopes
> bracketed with (:CONSTRAINTS :FNS (SORTFN1 SORTFN2)/(SSORTFN1
> SSORTFN2) …), 6 :SOURCE :LOCAL-WITNESS defuns, 14 QEDs — and recon
> currently REFUSES at the first witness (the BUG-019 fail-closed
> parse guard, pinned by cov-encapsulate). The ratified resolution
> (2026-08-02 R6 + BUG-019-by-tag+scope): witnesses enter recon
> SCOPED (never the certified world), the constraint theorems become
> the ConstraintsHold surface, constrained-book theorems get
> world-parametric statements (∀ w, ConstraintsHold w → …, per the R7
> (a) ratification), and the equisort waterfall replays over abstract
> w (the WATCH ITEM: cfg.worldExpr abstract — stop per condition 1 if
> the artifact resists the ratified note). Build order per the R6
> note: parse/world scoping → sweep entry → parametric statements →
> the recorded-tree replay over abstract w. Phase-3 residue riding
> the FORK BATCH: rewrite-equal (equalityp rhs) arm tagging+emission
> (rewrite.lisp:18434); :PATH coverage (HOW-MANY-RM-GENERAL);
> per-step relation at solidify/with-lemma (Phase-6 prerequisite);
> include-book translated statements (R7a follow-up). Phase-3
> CONSUMER residue (no fork): the IF-TEST-TRUE marker consumption
> (ProofTree ~346).**
> **EQUISORT STRONG/WEAK FINAL WALL DIAGNOSED (2026-08-04, closing
> the equisort-r6 sub-arc): the capstone-shape rows' remaining
> failure is EMISSION-BLOCKED on the fork batch's rewrite-equal item.
> Read off the WEAK-SORTFN1-IS-SORTFN2 Goal'' literal-1 chain: after
> the constraint rules close the antecedent and CONVERT-PERM-TO-
> HOW-MANY closes (PERM s1 s2) ⇒ 'T, the recorded chain JUMPS to
> (EQUAL 'NIL 'T) ⇒ 'NIL — the intermediate collapse of
> (EQUAL (SORTFN1 X) (SORTFN2 X)) ⇒ 'NIL from the clause context
> (literal 3's assumed falsity, ACL2's rewrite-equal type-alist
> route) is UNRECORDED. SITE CORRECTED (equisort-r6 audit F5): the
> responsible untagged arm is the ASSOC-TYPE-ALIST lookup at
> rewrite.lisp:18348-18354 ((assoc-type-alist (fcons-term* 'equal
> lhs rhs) …) with silent *ts-t*/*ts-nil* returns) — NOT the
> equalityp arms at 18428/18434 (the collapsed lhs (SORTFN1 X) is
> not an equality; the tagged ts-equality/solidify routes at
> 18377/18392/5270 would have emitted). Tagging only 18428/18434
> would NOT unblock these rows — the batch item covers BOTH the
> equalityp arms AND the 18348 type-alist arms. The batch item
> carries THREE consumers: the counter-example row, HOW-MANY-RM-
> GENERAL's family, and the equisort capstone-shape rows. Everything
> Lean-side up to that emission is BUILT and validated: R7a resolves
> the :use ORDERED-PERMS payload cross-book, the constraint rules
> apply as ordinary rule: hyps over the constrained telescope, the
> chain walks with no witness dereference (the watch item holds).**
> **IF-TEST-TRUE CONSUMER, REFINED DESIGN (2026-08-04, the
> counter-example row's LAST wall — post-batch the row reaches within
> one wrapper of the recorded result): the marker is
> (:IF-TEST-TRUE :ORIGIN IF-FINISH/IF-TEST :TEST (TRUE-LISTP (CDR X))
> :JUSTIFICATION (:RUNES ((:FAKE-RUNE-FOR-TYPE-SET NIL)) …)) — a
> verdict-only type-set resolution of an enclosing IF's test (TRUE →
> then-branch taken). ProofTree drops IF-test markers at recon
> (~:346); the consumer must thread them into the IF-FINISH window
> composition (BEGIN-IF-REWRITE/END-IF-REWRITE brackets) so the
> walker can collapse (IF test then else) ⇒ then justified by the
> test's truthiness — which for THIS instance rides the EXISTING
> TRUE-LISTP/CDR closure in typeSetWalk.isTruthy (literal 4's
> (TRUE-LISTP X) falsity context). The marker does NOT carry the
> enclosing IF term — the window brackets do. Queue position: after
> the sub-arc audit, alongside the anchoring-preference fix
> (HOW-MANY-RM-GENERAL: prefer the emitted entry path when it is
> among the anchoring candidates — a read-off, not inference), the
> R-lane rung-2, and BNEXT-SIZE wiring.**
> **EMISSION-BATCH AUDIT RESIDUE (READY-WITH-FIXES, 2026-08-04; F5/F6/
> F7 fixed in-arc — see docs/audits/2026-08-04_emission-batch-audit.md):
> (F1) equal/type-alist-t fires ZERO times in the corpus (348 for
> -NIL) — a shipped, sweep-unvalidatable path; its consumer (the
> truthy branch on an (EQUAL a b) ⇒ 'T node) is untested until an
> artifact exercises it. (F2) :GENEQV landed EMISSION-ONLY — no
> parser field, no consumer; the with-lemma gate still reads the
> RULE's :equiv (the F12 under-report is still live; the rung-2
> R-threading is its consumer). (F3) :TFORMULA landed EMISSION-ONLY —
> the R7a include-book use: consumer is pending; the emit/defthm TAG
> TEXT is now stale ((:DEFTHM name :FORMULA :SOURCE :CLASSES) — says
> nothing of :TFORMULA) — QUEUED for the next fork round (comment-
> only, but any fork commit forces a full recapture). (F4) :TA-RUNES
> on the new type-alist steps is parsed-and-dropped (rewrite-step has
> no taRunes field). (F9) the case-split consumer models fcons-term*
> where ACL2 uses cons-term (constant-folding) — a folded emission
> would trip the divergence error blaming the emitter; no corpus
> instance. (F11) the batch's third consumer (equisort strong/weak)
> is still outstanding — zero equisort rows moved (they also need the
> IF-collapse composition + the abstract-world statements). (F13) the
> equal/type-alist origins share the (:TYPE-ALIST NIL) rune with
> solidify/type-alist; dispatch is rune-only — the docstring narrows
> honestly but the distinction survives only in :ORIGIN.**
> **BNEXT-SIZE ROUTE, LAYER 2 (2026-08-04, consumer-queue sub-arc):
> the recorded-termination demand filter widened — a USER measure fn
> head (non-ACL2-COUNT) always takes the recorded route (it can never
> ride the μ-registry, whose interpretation covers the trusted-core
> family only). BNEXT and BSORT now ENTER the admission pre-pass and
> both replays fail at ONE shared class: the measure obligations of a
> non-ACL2-COUNT measure state ordinal machinery — dpValExpr lacks
> POSP and O-FIRST-COEFF as DP-lift primitives ((POSP (O-FIRST-COEFF
> (LEN X))) / (… (BNEXT-SIZE X))). NEXT INCREMENT: register the
> ordinal-on-naturals family in the DP lift + the leaf tactic (the
> Count-library extension the ratified carve-out anticipates —
> additive registration, no per-case content): posp, o-first-coeff /
> o-first-expt / o-rst on NATP arguments (where they are the
> identity/0/0 — the natp branch of ACL2's ordinal defs), enough for
> natural-valued user measures. The 3 μ-registry rows flip when the
> admission replays register (they fall back only on pre-pass
> failure).**
> **BNEXT-SIZE ROUTE, LAYER 3 DESIGN (2026-08-05, read off the bsort
> admission trees at Subgoal 3/2 of termination:BNEXT/BSORT): the two
> remaining node classes share ONE route — `builtinIntVal?` (the
> emitted-corollary-gated int-atom refinement, NodeCore ~1523).
> (a) recognizer/false (CONSP (LEN X)) ⇒ 'NIL, cited (:TYPE-
> PRESCRIPTION LEN): Logic.len is STRUCTURALLY recursive (stuck on an
> opaque arg — the isDefEq route can't reduce), but builtinIntVal?'s
> value' is literally (SExpr.atom (Atom.number (Number.int k))) —
> Logic.consp of it reduces to nil DEFINITIONALLY. Wire the
> recognizer/false arm: inner fn ∈ builtinIntTps → builtinIntVal? →
> re-cast the application's conv to value' → isDefEq closes.
> (b) RECOGNIZER/TRUE with rune ty compound-recognizer
> ((NATP (LEN X)) ⇒ 'T, rune NATP-COMPOUND-RECOGNIZER, cited TP LEN):
> dispatch arm for the "compound-recognizer" rune ty; NATP is now a
> DP primitive; needs value' PLUS the corollary's NONNEG conjunct —
> extend builtinIntVal? to also return the (NOT (< app '0)) fact
> (its gate already pins the full intTpCorollary shape), then
> Logic.natp (int k≥0) = t closes. The nfix-measure rows' (CONSP
> (IF (INTEGERP N)…'0)) class: the value composes fully through DP
> primitives — needs a cond-case consp lemma (all branches atoms) —
> same family, third consumer. BNEXT-SIZE (a WORLD fn) rides the
> EXISTING pinTermOpaques TP-refinement (tpHyps has BNEXT-SIZE's
> emitted corollary) — verify its admission tree after (a)+(b).**
> **BNEXT-SIZE ROUTE, LAYER 4 (2026-08-05, consumer-queue sub-arc):
> BUILT — (i) the compound-recognizer WORLD-fn branch: the natp fact
> from the fn's emitted nonneg-int TP corollary through the tpHyps
> channel (`logic_natp_t_of_int_tp_fact` on the lifted fact at the
> application's pinned value; corollary instantiated at the actual
> arg must BE `intTpCorollary inner` — drift-fails); (ii)
> `mkRecTermInfo` generalized off its two ACL2-COUNT hardwirings,
> both read off the artifact: cntSym is now the justification
> measure's HEAD, and the goal-conjoin check also accepts ALL emitted
> clauses (a USER measure's `(O-P (cnt v))` obligation survives into
> the waterfall — bsort's Goal conjoins both clauses; the ACL2-COUNT
> class keeps the non-O-P-only spine; `interp_decrease_decode` was
> already generic over cnt). termination:BSORT → REPLAYED ✓
> cond[total:BNEXT, total:O<, total:O-P, tp:BNEXT-SIZE,
> ASSUMED:dp-fact]. FINAL WALL for the 3 μ-registry rows
> (ORDEREDP/TRUE-LISTP/HOW-MANY-BSORT), diagnosed to the emission:
> the assumed dp leaf is Subgoal 1' — simplify-clause/linear-
> contradiction citing (:LINEAR HOW-MANY-BAD-PAIRS-BNEXT), a LOCAL
> defthm's linear rule. The fork's gz-linear collectors
> (infra/gz-linear-rules, ld.lisp ~5474) walk only PREDEFINED syms,
> so a cited LOCAL :LINEAR rule's stored hyps/concl/max-term are
> never snapshotted → the DP premise is unstatable → the leaf falls
> back to ASSUMED:dp-fact → consumers honestly refuse ("recorded
> route: condition ASSUMED:dp-fact not offered"). QUEUED FORK ITEM
> (next round, batched): extend the cited-closure linear collector to
> LOCAL :LINEAR rules (same (rune hyps concl max-term) entry shape,
> same event; information ACL2 already stores in the linear-lemma
> record). The three rows flip when the premise threads (they then
> also need linear:HOW-MANY-BAD-PAIRS-BNEXT in the consumer
> telescope, which the existing 2b channel provides).**
> **CONSUMER-QUEUE AUDIT REMEDIATION (2026-08-05 — see
> docs/audits/2026-08-05_consumer-queue-audit.md, NOT-READY, both
> reviewers):**
> **(1) VACUOUS ASSUMED GREEN FIXED (S1/S2/S4): termination:BSORT's
> `REPLAYED ✓ cond[…ASSUMED:dp-fact]` was vacuous — the assumed
> dp-fact hypothesis quantifies opaques INDEPENDENTLY, severing the
> (BNEXT-SIZE (BNEXT X))/(BNEXT-SIZE X) link, and can be FALSE.
> (Correction 2026-08-06, pre-merge audit S3: the refutation constant
> `bsortDpFact_false` originally cited here was never committed — the
> structural fix stands on the severed-quantification argument alone.)
> `tryReplay` now renders any
> ASSUMED-conditioned composed replay `ASSUMED ◌` and refuses
> registration (single choke point — no consumer can resolve the
> condition); the DriverCoverage legend invariant is enforced; the
> catalog entry removed. ROOT-CAUSE FOLLOW-UP (queued): state assumed
> obligations at the ACTUAL applications instead of independent
> opaques — would make BSORT's leaf hypothesis the true
> HOW-MANY-BAD-PAIRS-BNEXT fact; also affects every ◌-assumed probe
> row. The REAL fix for the row remains the queued fork item: local
> :LINEAR rule snapshot (gz-linear collectors walk only PREDEFINED
> syms — extend the cited-closure to LOCAL :LINEAR rules).**
> **(2) WALKERS REVERTED per ratified policy (D1–D4): tsRecogWalk +
> integerpTWalk + their 7 lemmas recomputed "type-set inside the
> rewriter", which generality-design §3(c) directs to TARGETED
> EMISSION instead ("recomputation would have to clone the lattice +
> cycle-breaking heuristics bug-for-bug"), and violated the July-31
> one-typeSetWalk consolidation charter (walkers 1→3, consumer-local
> fact scans, new derivation power). Reverting conforms to standing
> policy — re-ratifying walkers stays open to MDD. QUEUED FORK ITEMS
> (next round, batched): (a) emit `:FALSETS` alongside the existing
> :TYPESET/:TRUETS at the two recognizer sites (rewrite.lisp ~5556/
> 5618 — already in scope there); (b) snapshot the cited recognizer
> tuples ('recognizer-alist entries: fn, true-ts, false-ts, strongp)
> — together these make recognizer verdicts DATA-DRIVEN off emitted
> content (one rule, no per-recognizer code), the shape of ACL2's own
> type-set-recognizer. The 3 nfix-measure termination rows
> (COUNT-DOWN/MY-EVENP/CD2) and their downstream IF-FINISH
> window-composition wall wait on this route. Also queued: consume
> :TYPESET/:TRUETS as a cross-check on recognizer replays (D9 — cheap
> even before the redesign).**
> **(3) Hardening landed with the remediation: `thmAt` now
> `Meta.check`s the mirror application (S3 — string-keyed positional
> condition resolution could silently accept a defeq mis-pairing).
> RECORDED, not yet done: dedupe the two `chainOk` clones
> (Runner.lean vs Induction.lean — DELIBERATELY different reach, the
> CONS arm; unify with an explicit parameter, S7/D7); the μ-route
> discrimination predicate is a calibrated heuristic (D7) — honest
> comment queued with the dedupe; builtinRecogFacts deviates from the
> 97190e1 designed builtinIntVal? route (D5) — KEPT (it gates the
> **PCE-IS-COUNTEREXAMPLE — RESOLVED TO THE EMISSION ROUTE
> (2026-08-05, the drift tidy-up): the session's per-class chase of
> this row (the IFF-normalization tower bridge + the tlp-cdr demand
> emitter) was KILLED as infra-mirroring — a bounded rewriter loop
> over the term's own shape plus an invented hoist demand
> re-implemented rewrite-atm's silent literal-boundary normalization,
> which the fork can emit instead (fork batch item 6: record the
> iff-context normalization steps at the literal boundary). KEPT from
> the same stretch, as single-composition replay pieces: the
> complement-tautology close (greened TRUE-LISTP-BNEXT), the two
> call-stack folds (rewrite.lisp:3791/18089 — the ratified
> bridgeEqualNilNorm class), the boolean-TP fold, the two registered
> disjointness cells (single-summand, term-vs-sum — emitted-TP-keyed;
> subsume under the recognizer-tuple emission when it lands), the
> type-set-equality orientation normalization, and the last-position
> nil-drop completion. The row is honestly red at the literal-3
> chain frontier until the emission lands. Distinguishing test
> (ratified in practice by this tidy-up): REPLAY consumes a recorded
> step or emitted fact in one deterministic composition, or
> recomputes a step dictated by the RECORDED TARGET where the
> artifact genuinely cannot record it (the normalizeSwapsToward /
> BUG-026 precedent); a walk over the term's own shape with
> fact-gated moves is INFRA-MIRRORING — emit instead.**
> **BRANCH DRIFT AUDIT — SECOND KILL ROUND EXECUTED (2026-08-05, the
> commissioned Opus branch-wide review; verdict: "the branch's
> direction is right; its tail accreted" — 28-feature inventory, 9
> per-case mechanisms of which 6 had ZERO dependent green rows,
> verified per-commit by golden-diff dependency read-off). KILLED
> beyond the first round (zero scoreboard cost, error-text-only
> golden diffs): the tpthm consumer stack (Harness offers + the
> replayRecognizer tpthm arm + the tpthm demand emitter), the
> chain-end deep-walker fallback and the last-position nil-drop
> completion in Core, the L-orientation call-stack fold + the
> boolean-TP fold, the single-summand and term-vs-sum disjointness
> cells (the nested-sum cell + its match-capture fix KEPT), the
> type-set-equality orientation normalization, the world-fn
> compound-recognizer route, the ambiguous-position preference
> (hard-fail restored), and 12 orphaned EvalLemmas. HELD UNDER
> EXPIRY (drift markers in-code): R1 the equation-closure
> disequality rung (3 green rows; EXPIRES at fork item 3 —
> fc/type-alist provenance); R2 builtinRecogFacts (termination:BNEXT
> rows; EXPIRES at fork item 2 — recognizer-tuple snapshot); R3 the
> μ-route discrimination heuristic (honest-heuristic comment;
> revisit at the fork-batch review). Frontier moves from the round
> (all red→red): PCE now reds EARLIER, at the recognizer TP frontier
> (no TP hypothesis for RM — the killed tpthm consumer's row; both
> its frontiers are fork-blocked); termination:BSORT's assumed leaf
> is now the LOUD parked frontier (fork item 1). EXPLICIT KEEP: the
> unwired
> emission surfaces (:TA-DERIVATIONS, :FC-DERIVATIONS,
> Development.scopes, encapsulate events) — they are the queued fork
> batch's consumers, not ornament. OPEN MDD QUESTION (R4, for Mike):
> whether GROUND-HYP discharge (evaluating a rule hypothesis's
> ground instance) sits inside the DP-leaf carve-out's scope or
> needs its own ratification. bnextBody transcription verified
> MECHANICALLY against the log's :DEFUN BODY (parse-and-compare,
> equal). Complement-tautology close re-commented as
> inferred-from-absence (fork does not yet emit the close).**
> **PRE-MERGE AUDIT — RUN + REMEDIATED (2026-08-06, two decorrelated
> Opus lanes; full outcome in the close report's "Pre-merge audit —
> RUN" section; the drift audit's committed record is
> docs/audits/2026-08-05_branch-drift-audit.md). Fixed in the
> remediation round: M1 (audit record committed), M2 (convert-perm
> HOW-MANY-RM pin — P4 honestly 7/7 now), B2 (complement-close
> children guard), N5 (explicit witnessDefun world-exclusion arm), N8
> (:use topological guard fail-closed), S3 (phantom
> `bsortDpFact_false` citations reworded), R4 marker at the
> ground-hyp arm, close-report number corrections (P2/P3), this
> header. B1 — USER-RULED (2026-08-06, post-merge): KEEP under expiry,
> "must be fixed soon" — the arm carries a drift marker expiring at
> fork-batch item 7 (add-literal complement-close emission); item 7 is
> thereby PRIORITY within the batch. R4 — USER-RULED (2026-08-06,
> option 2): NOT a carve-out extension; the ground-hyp arm is held
> under expiry, retiring onto the emitted recognizer-tuple verdict
> when fork-batch item 2 lands (rationale: ACL2 holds the verdict's
> BASIS — the recognizer-alist tuple — as emittable data in a system
> we instrument, so "the artifact genuinely cannot record it" fails
> and reconstruction is not licensed; emission is). No open user
> decisions remain from the pre-merge audit; the fork batch (7 items,
> items 2 and 7 carrying expiries) awaits its review round-trip. QUEUED HARDENING (pre-merge audit N-items, none
> load-bearing today): (N4) a golden rendering distinction for green
> rows whose conds cite RED rows (CONVERT-PERM-TO-HOW-MANY reads as ✓
> while resting on rule:PERM-TLFIX + use:PCE from FAIL rows); (N6)
> derive the mirror axiom-gate name list from liftCatalog instead of
> the hand-maintained literal list (Waypoints/Catalog.lean ~275); (N7)
> nested-:use cyclic-let robustness in dischargeUseHyp (unreachable
> today; kernel would reject loudly); EVENS/ODDS in destructorChainOk
> is a specialization watch item (pre-existing on main, extended to a
> second consumer this branch — retire with R2/fork item 2). GENEQV
> CONSUMER (pre-merge audit S2): the fork now emits `:GENEQV` on
> with-lemma pushes (the honest net-step relation when the rhs chain
> used a weaker R — emitted as the R-lane prerequisite, fork commit
> 24e6dbc) and nothing parses it yet; the rung-3 R-lane arc is its
> DESIGNATED consumer (the R-gate currently keys on the
> under-reporting `:EQUIV` — a latent fidelity gap the rung-3 arc
> must close; do not wire piecemeal before it).**
> **PERM-TLFIX — CLASSIFICATION SHARPENED (2026-08-05, read off the
> dump + the ratified equiv-lane design): the failing node is the
> IH-as-rewriting-equivalence with equiv (PERM (TLFIX (CDR X))
> (CDR X)) nested at a PERM-arg congruence position — the R-VALUED
> PAYLOAD class that docs/plans/2026-07-29_equiv-lane-design.md
> EXPLICITLY deferred: "Congruence CHAINS … need the R-valued payload
> rung 2 skipped; rung 3 adds it additively" (the built rung-2
> collapse routes cover the with-lemma one-frame class and the
> branch-substitution class only; this node is the solidify recipe
> with a live R payload). Its red is DESIGN-CONSISTENT per the
> ratified rung boundary — building rung 3 is the follow-on arc's
> item, with the design outline already in the note (extend the
> collapse route to the solidify node kind: the R-fact from the
> clause context's (NOT (PERM …)) falsity, then the same one-frame
> congruence collapse — verify the :PATH frame structure first).
> Downstream of this row: the capstone mirror's rule:PERM-TLFIX
> discharger and P3's last gap.**
> **PCE MIRROR — OUTCOME (2026-08-05): the plan below was probed and
> the honest blocker is NOT simulation work. The PCE exec kit already
> existed (pceExec/pce_exec_corr/dis_pce_total — the discharger-
> registry arc); a pceL + pceExec_enc + capstone decode were drafted,
> BUILT GREEN, and then REVERTED per the unwired-infrastructure ban:
> the capstone row's conds include rule:PERM-TLFIX and
> use:PCE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS, both from RED rows (the
> rung-2 wall; the spine literal-chain frontier), and their only
> criterion-clean dischargers are those theorems' replayed statements
> — a hand bridge is the banned ornamental-import pattern. The
> capstone mirror wires the moment those two rows green (the draft's
> shape is in this entry's git history at the phase7-close commits).
> ORIGINAL PLAN (kept for that moment):**
> **PCE MIRROR BUILD PLAN (2026-08-05, in flight — the LAST P3 gap,
> CONVERT-PERM-TO-HOW-MANY): the value-level kit already exists in
> Imported/Perm.lean (membExec/rmExec/memb_exec_corr/rm_exec_corr/
> perm_exec_corr — perm's body recursion is nearly IDENTICAL to
> pce's, the direct template). Build: (1) pceExec (consCount on x;
> body (IF (CONSP X) (IF (MEMB (CAR X) Y) (PCE (CDR X) (RM (CAR X)
> Y)) (CAR X)) (CAR Y))) + pce_exec_corr on the perm_exec_corr
> pattern + dis_pce_total (the row's total:PERM-COUNTER-EXAMPLE
> cond); (2) pceL : List → List → SExpr native ([],ys ↦ ys.headD
> nil; x::xs,ys ↦ bif ys.contains x then pceL xs (ys.erase x) else
> x) + pceExec_enc; (3) the decode: formula (EQUAL (PERM X Y) (EQUAL
> (HOW-MANY pce X) (HOW-MANY pce Y))); native `xs.isPerm ys =
> (xs.count (pceL xs ys) == ys.count (pceL xs ys))` — corr_perm_enc
> gives the bif-isPerm side, how_many_exec_corr both counts,
> Logic.eq_of_equal_ne_nil then boolEnc-injectivity cases; (4) the
> assembly in Waypoints/ConvertPerm.lean (the row's conds per the
> sweep golden line for CONVERT-PERM-TO-HOW-MANY — incl. the use:
> and rule: conds discharged via deps [permDev?] / registry; READ
> the golden line and mirror the qsort capstone's discharger set) +
> catalog flip + axiom gate.**
> **PHASE7-CLOSE SUB-ARC (mdd/phase7-close, opened 2026-08-05 after
> the consumer-queue fold-back): the arc's final Lean-side stretch.
> (1) P4 DONE at c10baf1 — pins for perm/ordered-perms/msort/bsort
> (7 of 7 amendment-scoped books; sorts-equivalent + equisort
> amendment-excluded). (2) P3 IN PROGRESS: 6 sorting .pending catalog
> entries — the 3 convert-perm mirror targets
> (NOT-MEMB-IMPLIES-HOW-MANY-IS-0 → contains=false ⇒ count=0;
> NOT-MEMB-IMPLIES-RM-IS-NO-OP → List.erase_of_not_mem class;
> HOW-MANY-RM → count-of-erase) via the Imported/Sorting.lean decode
> pattern (per-theorem *_native_of_replayed over the enc/corr kit;
> the conditional-IMPLIES eliminator precedent is Worlds.Perm's
> perm_cons decode) + TRUE-LISTP-RM / CONVERT-PERM-TO-HOW-MANY /
> HOW-MANY-BNEXT (native or .replayedOnly-with-rationale per the
> mirror criterion). (3) Then machinery debt (allBookRules walk,
> dp-premises F6, include-book provenance gate, leaf-class gating,
> generator-reads-the-log), then the mechanical P1–P6 predicate
> check under the amendment, the accumulated fork-batch list for
> review, and the pre-merge audit proposal. P2 remains OPEN by
> design: bsort walls + PERM-TLFIX wait on the queued fork round /
> R-lane rung-2 — declared with numbers at close.**
> valid termination:BNEXT green and the audit verified it sound and
> properly emission-gated) with the redesign queued alongside the
> recognizer-tuple emission, which subsumes it. VERIFIER RESIDUALS
> (fresh re-verification, READY): N1 closed — the driver_replayed%
> registration path now refuses ASSUMED conds loudly (Macro.lean;
> the with_termination sub-path already failed loudly). RECORDED:
> S6 — position-canonical disambiguation (d136e6a) pins candidate
> FRAMES but not preSwap?/branchAnchor across survivors, then
> prefers the branch-anchored one (fail-closed downstream, LOW-MED;
> pin all three or prove uniqueness). N2 — "ASSUMED:dp-fact" is a
> string literal at three sites (Runner ×2, Harness, now Macro);
> extract one named constant so a rename cannot silently disable
> the guard.**
> **ITEM-4 SMOKE DIAGNOSIS (2026-08-02): :TA-DERIVATIONS is all-NIL
> at the relief site — CONFIRMED CAUSE: expunge-fc-derivations
> (simplify.lisp:1655) flattens every fcd into a 'lemma rune tag
> BEFORE the type-alist entries are built (that's why :ta-runes shows
> (:FORWARD-CHAINING LEXORDER-TOTAL) but the structure is gone). FIX:
> emit at the EXPUNGE CALL SITES (simplify.lisp ~1713-1731, where the
> pre-expunge ttree still carries fcds): run structured-ta-derivations
> on the ttree BEFORE expunging and emit one (:FC-DERIVATIONS …)
> block (per clause/round), keyed by :CONCL; the relief-site replay
> JOINS by concl-term equality with the relieved hyp (deterministic).
> ACL2's own prettyify-fc-derivation (simplify.lisp ~1620, the
> fc-report facility) confirms the fields incl. :LITERALS =
> collect-parents (the parent clause literals). The :TA-DERIVATIONS
> field at the relief marker STAYS (it is correct when a future path
> carries unexpunged ttrees; NIL is honest). LMI-LST + CLASSES smoke
> PASS ((:INSTANCE LEN2-APP-HELPER (X (CONS A B))) verbatim;
> (:CLASSES (:REWRITE))).**
> **PHASE-1 CLUSTER STATUS (2026-08-02): fork code COMPLETE + BUILT
> (saved_acl2 rebuilt; encapsulate-pass-2 registered for the parity
> check) + SMOKE-TESTED: the recaptured equisort log carries
> (:ENCAPSULATE-BEGIN :SIGS (SORTFN1 SORTFN2)) + (:CONSTRAINTS :FNS …
> :FORMULAS …) with the six constraint formulas VERBATIM (incl. the
> IMPLIES-guarded true-listp forms) — the R6-ratified shape exactly.
> Lean parsers: :LMI-LST (useHint) + :CLASSES (defthm) DONE, building
> green. REMAINING to close the cluster: (a) smoke-check :LMI-LST
> (05-hints capture), :TA-DERIVATIONS (a bsort/qsort capture);
> (b) parser layer for the three bracket events (ProofEvent
> constructors + ClauseTree pass-through — scope SEMANTICS land with
> Phase 4's scoped extensions; for now buildDevelopment records them
> without changing toWorld, equisort still parse-fails at
> :LOCAL-WITNESS until Phase 4) + hypRelief.taDerivations field;
> (c) the FULL corpus recapture (scripts/capture-proof-log.sh — one
> pass, all books) + golden re-pin ROW-BY-ROW (stop-early condition 4
> if churn exceeds review); (d) cluster sub-arc audit + fold-back to
> mdd/sorting-closeout. Smoke capture parked at the session scratchpad
> (NOT the corpus — the corpus recapture is one deliberate pass).**
> **PHASE-1 EMISSION CLUSTER WORKLIST (close-out, 2026-08-02 — the
> single fork round-trip; every insertion TRACE-LOG-tagged, round-trip
> checked by just check-acl2-tags; ONE recapture at the end, goldens
> re-pinned row-by-row):
> (1) :LEMMAS in the use-hint payload — extend the existing
> emit/use-hint/payload site (acl2/prove.lisp:754) with the hint's
> lemma names + substitutions (the translated :use hint carries them;
> read off, no computation). Unblocks R7a.
> (2) IN PROGRESS — design settled, sites located: BRACKET MARKERS,
> not per-event tags. [STALE PLAN-TIME CLAIMS, corrected by audit
> 2026-08-03 F2/F5 + fresh-verify N1/N6 — see the CORRECTED entry
> above: brackets are balanced only across the FOUR success exits
> (BEGIN on both entry paths), error exits abort the capture, and the
> parser does NOT dedup — per-scope :DEFTHM dedup is the Phase-4
> obligation.] (:ENCAPSULATE-BEGIN) before pass 1
> (other-events.lisp:8669's process-embedded-events 'encapsulate-pass-1,
> inside the state-global-let* at 8660, within encapsulate-fn 8452) and
> (:ENCAPSULATE-END) at encapsulate-fn's success exit — ~~ALWAYS
> balanced~~ (trivial encapsulates included); the constraint DATA is a
> separate (:CONSTRAINTS :FNS sig+constrained :FORMULAS (car
> constraint-lst-etc)) event at the putprop-constraints call site
> (other-events.lisp:6452, inside encapsulate-pass-2 at 6132) —
> present only for constrained scopes. Parser: bracket = scope; the
> census showed BOTH passes emit :DEFTHM events (duplicates!) —
> ~~the parser dedups within a bracket by name~~. Emission style: top-level
> fms like emit/defthm (gated on raw-proof-format :structured), needs
> state threading through encapsulate-fn's er-let* chain — read the
> monadic structure fresh before inserting.
> ORIGINAL: encapsulate close in
> acl2/other-events.lisp (constraint-lst-etc machinery ~5114 computes
> exactly the list; emit verbatim per signature group + tag the
> scope's :LOCAL-WITNESS defuns and exported defthms with the
> encapsulate id). R6-ratified shape.
> (3) RECLASSIFIED (2026-08-02, artifact check): admission waterfalls
> are ALREADY logged (steps + (:QED) precede each :DEFUN — bsort's
> BNEXT admission tree confirmed in-log) AND recon'd (ClauseTree
> 715-726 attaches them as the defun's `termination` field; the
> runner's replayAdmission pre-pass consumes them — the qsort
> with_termination route). The ratified BNEXT-SIZE route is LEAN-SIDE
> replay wiring (extend the termination pre-pass to bsort's scheme in
> the sweep) — moves to Phase 6, OUT of the fork cluster.
> ORIGINAL: BNEXT-SIZE admission-waterfall logging — the defun admission
> path (defthm.lisp/defuns admission → prove): when a REAL waterfall
> runs for termination, route the structured logging through it (the
> carve-out's 'termination field' follow-up; ratified route for
> BNEXT-SIZE). bsort is the activating instance.
> (4) IN PROGRESS — site + gap precise: the free-type-alist relief
> emission (rewrite.lisp:19483-19511) grabs the entry's ttree runes
> (:ta-runes via all-runes-in-ttree (cddr entry)) but FLATTENS AWAY
> the fc-derivation structure. The extension: extract the ttree's
> fc-derivation records (defrec fc-derivation — read its fields
> first) and emit per derivation the deriving rune + instantiated
> concl + supporting facts, as :TA-DERIVATIONS alongside :ta-runes.
> FIELDS (linear-a.lisp:711): fc-derivation = :concl (instantiated
> conclusion) / :ttree (nested — supporting chain, recursively more
> fcds or literal-level tags) / :rune (the FC rule) / :inst-trigger /
> :unify-subst / :fc-round. The walker: tagged-objects 'fc-derivation
> on the entry's ttree, recurse nested ttrees; ground leaves carry
> 'pt (parent-tree) tags naming the CLAUSE LITERAL indices — exactly
> the parent-literal provenance the replay needs. Emit
> :TA-DERIVATIONS ((:RUNE r :CONCL c :TRIGGER t :SUBST s :PARENTS
> (lit-idxs…) :SUPPORTS (nested…)) …).
> The SAME extraction serves BUG-027's equation-edge justifications
> (the solidify sites' emitted equiv provenance) — one ttree-walker,
> two consumers. Also apply at the marker twins (19676, 19749 — 'as
> emit/relieve-hyp/free-type-alist' comments).
> ORIGINAL: Type-alist derived-entry provenance — the relieve-hyp/
> free-type-alist + type-alist emission points (rewrite.lisp): emit
> parent literal(s) + deriving FC rule per derived entry. Serves
> BUG-027 (narrow-via-emission), the LEXORDER-TRANSITIVE marker-relief
> class (bsort HOW-MANY-SMALLER-BNEXT + parked backlog), and the
> free-type-alist relief class.
> (5) :RULE-CLASSES on defthm events — extend emit/defthm
> (acl2/defthm.lisp:12211) with the event's rule-classes (closes the
> equivrefl shape-parse caveat).
> Lean-side parsers extend with each (fail-closed on absence for old
> logs); the recapture activates them together.**
> **R7a PROBE FINDING (close-out, 2026-08-02): the :USE-HINT payload
> lacks the used LEMMA NAMES + substitutions (only instantiated hyp
> formulas are emitted — LEN2-APP-VIA-USE payload inspected).
> Recovering them by matching prior theorems would be Lean-side
> inference (banned); the hint names the lemma, ACL2 has it — EMIT
> IT. `:LEMMAS ((name . subst) …)` joins the Phase-1 emission
> cluster; R7a's Lean composition builds against the recaptured
> payloads (fail-closed on absence for old logs). Sequencing:
> fork-first (the cluster gates R7a activation anyway).**
> **R6 CENSUS PASSED (close-out arc increment 0, 2026-08-02): the
> exported-tree census over equisort.proof-log confirms the ratified
> expectation — witness leakage (SORTFN1-INSERT/SSORTFN1-INSERT
> helpers, :DEFINITION unfolds of constrained symbols) occurs ONLY in
> the twelve constraint theorems (pass 1, correct and required);
> WEAK-SORTFN1-IS-SORTFN2 and STRONG-SSORTFN1-IS-SSORTFN2 have CLEAN
> trees (constrained symbols in formulas only). Stop-early tripwire 1
> does not fire; the justified-extensions design is safe to build on.**
> **R6 RATIFIED (MDD 2026-08-02, all four questions — the close-out
> arc's Phase 0 checkpoint, cleared BEFORE the arc opened):
> docs/notes/2026-08-02_r6-encapsulate-design.md. (1) the
> JUSTIFIED-EXTENSIONS design ("not a special case, but general
> machinery" — Mike's direction): scoped extensions as the
> Development primitive, toWorld = canonical model uniformly (witness
> bodies = the constrained scope's canonical model), sweep at the
> canonical model, ONE generic scope-abstraction statement builder
> (encapsulate = the constrained-scope instance; defchoose/defaxiom/
> partial-encapsulate are future scope KINDS); (2) emission =
> :CONSTRAINTS verbatim from ACL2's constraint-lst + :ENCAPSULATE
> boundary tags; (3) equisort catalog doctrine (re-proofs
> .replayedOnly → originals; parametric constants for
> post-encapsulate theorems; the three capstone native shapes);
> (4) BUG-019's equisort instance resolved by tag + scope structure
> (general bug stays open for unmarked witnesses). The justificatory
> reading validated against equisort.lisp + both logs: constraints
> are AXIOMS, witnesses are the (meta) conservativity argument made
> object-level, post-encapsulate theorems are ordinary
> constrained-theory proofs, functional instantiation = the derived
> rule with constraint-instance obligations.**
> **RATIFICATION QUEUE — RESOLVED (MDD 2026-08-02, all five):
> (1) R7 RATIFIED in full: option (a) world-parametric constrained
> theorems + (a1) alias-world commutation lemma; the note's Q2-Q4 are
> determined by it (R7a first, R6-gated R7b; abstract-world driver
> parameter at minimal reach; ConstraintsHold = emitted constraint
> terms, guards as-is). R7a is buildable next arc.
> (2) The widened DP carve-out (2b linear + 2c premise classes + the
> spine arms + oneWayMatch + the trueListp leaf bridge) RATIFIED for
> now, with MIKE'S DRIFT TEST as the standing revisit criterion:
> "if we find ourselves writing custom proofs or checkers per case,
> we are no longer mirroring ACL2 — we are building custom search to
> replace it." Revisit-TODO below.
> (3) BUG-027: NARROW via emission (emit the type-alist equation-edge
> justifications; gate the truthy-equal edges on them) — recorded in
> docs/BUGS.md; open until the emission lands.
> (4) BNEXT-SIZE: the ADMISSION-WATERFALL route (log + replay bsort's
> real admission proof — replay-don't-infer decides it; the CountSim
> Lean-model route is rejected). Fork emission + termination-field
> replay, next arc.
> (5) Count rows (ACL2-COUNT-EVENS-*): .replayedOnly, NO native
> mirror — internal admission lemmas absorbed by the exec-kit sim
> (the measure-absorbed doctrine); introduce an acl2Count native
> vocabulary only if a user-facing count theorem ever needs it.
> ORIGINAL QUEUE TEXT (kept for the record): (1) the R7 design note (2d) — DRAFTED:
> docs/notes/2026-08-01_r7-use-functional-instantiation-design.md
> (recommendation: world-parametric constrained theorems + alias-world
> commutation lemma; R7a plain-:use split off, R6-independent; four
> ratification questions at the bottom of the note); (2) the 2b carve-out-boundary
> call — WIDENED per fold-back audit H2, ratify the DELIVERED scope:
> BOTH new spine arms (the LINEAR-EQUALITIES CASE SPLIT and the
> EQUATION-ADD close) close their ≠-case by verdict-only linear
> arithmetic at BRANCH granularity via CONSTRUCTED obligations
> `eq ∨ parent` (emitted substitution equation + the clause, nothing
> else; never ASSUMED — prove-or-hard-fail, audit F2a), plus
> oneWayMatch (the replay's only matcher, emitted max-term patterns)
> and the linear: premise instantiation. Auditor caveats: the arms
> gate on SHAPE, not the emitted fake-rune-for-linear-equalities
> provenance (F2 — recommends ratifying WITH a provenance-gate
> condition; queued follow-up with F4's memo-rune assertion); ACL2's
> conclusion is modulo unemitted forced numericity assumptions (F6 —
> the replay's burden is strictly HARDER, conservative). Full
> assessment in the audit report. Mike to ratify-or-narrow.
> **EXTENSION (dp-premises sub-arc, 2026-08-01 — the 2c fold-back
> audit found the queued 2b wording covers NONE of these; design note
> docs/notes/2026-08-01_dp-premise-classes.md): additionally ratify,
> at a verdict-only DP leaf, premises drawn from in-scope stored
> content — (i) boolean-strengthened :REWRITE rules (equiv EQUAL, rhs
> 'T, one hyp) whose stored LHS one-way-matches ANY application
> subterm of the emitted clause, GATED on ACL2's tau Signature Form 1
> shape (tauSigForm1 — distinct-variable args, recognizer hyp on one
> of them; added post-audit per soundness F1); (ii) the reflexivity
> conjunct of an equivalence-shaped theorem at syntactically
> reflexive application subterms (mirrors ACL2's
> assoc-equiv+/(equal arg1 arg2) verbatim; auditor F2 caveat: the
> defequiv provenance (:rule-classes :equivalence) is NOT emitted —
> shape-parse only; closing it needs instrumentation); (iii)
> trusted-core recursion equations of DP-lift primitives in the leaf
> tactic's simp set (trueListp_cdr_of_consp — mirrors type-set-cdr's
> rune-free *ts-proper-cons* → *ts-true-list* propagation). Each
> premise is PROVED at the leaf's pinned values and kernel-checked;
> none is assumed. OPEN sub-question for Mike: should (i) also gate
> on the LEAF's class (tau vs fake-rune-for-type-set)? — the leaf
> origin is not currently plumbed into replayDischargeNode;
> (3) BUG-027 ratify-or-narrow (2f, carried).**

> **FULL-PIPELINE AUDIT (2026-07-26, user-run 6-dimension team + refutation
> pass; report `docs/audits/2026-07-26_full-pipeline-audit.md`) — GOVERNS
> THE CURRENT ARC.** Headlines: F0 GitHub REMOTE CI RED since 2026-07-23
> (4 merges pushed onto it; every arc close-out's "gates green" was the
> LOCAL `just ci` only — close-out ritual now requires pasting the REMOTE
> CI conclusion. AMENDED 2026-07-28, MDD: development now runs in a
> network-blocked sandbox, so local merges gate on LOCAL `just ci` +
> sign-off only; remote CI is validated at the next networked push,
> fix-forward — see CLAUDE.md "Sandbox protocol". check-push-ready keeps
> its remote-CI gate for actual pushes); F1 SOUNDNESS-class statement
> substitution (encapsulate
> local witnesses enter the World; cov-encapsulate reports 2/2 replayed
> ABOUT THE WITNESS — known since the 2026-07-20 design note, new fact is
> it fails GREEN; not in the 62/79 golden by accident); F2 TamperTests
> dark since 2026-07-05 + 3 of 4 tampers are no-ops (pre-BUG-002
> lowercase literals); F3/F7/F0 three live clone hazards (rewrite-if
> emitter const-fold twin of S2b inc-3; duplicated dischargeOrigins —
> the golden DP scoreboard UNDERCOUNTS FC-contradiction discharges;
> CI capture-list derivation applied to one directory); F10 fresh-book
> generalization 10/144 replayed (7%) vs golden 78%, ALL fail-closed at
> named frontiers; the SEQUENCING PREMISE of
> docs/notes/2026-07-23_mapping-plan-impact.md is INVERTED by fresh-book
> data (capture 7/7 robust, RECONSTRUCTION 5/7 is the narrow layer —
> crash sites ProofTree.lean:339 + :281). Also: F11 statement-anchoring
> (~8% of rows have hand-pinned statements), F5 reader terminating-macro
> chars (fail-open; BUG entry due), F6 four unlogged latent Logic
> divergences, F9b gate weaknesses. 2 CONFIRMED / 17 PARTLY CONFIRMED /
> 3 REFUTED of 22 verified findings; zero false theorems kernel-certified.

> **AUDIT-HARDENING ARC (branch `mdd/audit-hardening`, opened 2026-07-26)
> — IN PROGRESS.** Scope = audit recommendations 0–3 (ratified by MDD;
> land before any feature arc):
> (0) DONE (pending remote validation on push): workflow captures BOTH
> derived demand sets (all git-tracked acl2_samples books + include_str'd
> sorting); check-push-ready HARD-gates on the remote CI conclusion via
> gh (ALLOW_RED_CI=1 escape for the fix push; verified live — it reports
> main's current 'failure').
> (1) F1 DONE (BUG-019, fixed): every world-entering :DEFUN carries
> explicit provenance (:ADMITTED/:INCLUDE-BOOK/:GROUND-ZERO/
> :LOCAL-WITNESS via in-local-flg — the `local` macro's own binding);
> parser HARD-FAILS on witnesses and on missing/unknown provenance.
> Discrimination verified (CF + defevaluator's MEV/CPEV tag; KEEP-TERM
> doesn't). CASCADE the net caught: DEFSTUB is a local witness too — the
> four S2b probe books' green rows were themselves witness-substituted
> (H := λ_.'NIL); rewritten to disabled REAL defuns, all pins hold,
> p2-beta-preprocess still 2/2 on honest ground; the equiv-iff probe
> rewritten with a boolean-TP bar + provable iff rule (a truthy-TP bar
> let type-set close the IF before any iff rewriting — first rewrite's
> lesson), and now also corpus-pins the composite-node IFF case.
> :CONSTRAINT-list emission deferred to an encapsulate-support arc (no
> consumer yet); local defTHM rule provenance noted in BUG-019 as the
> adjacent surface.
> (2) F2 DONE: literals fixed, suite wired into Tests.lean, and the
> 21-day-unknown ANSWERED — all four tampers REJECTED at their expected
> joints (T2's expected message updated to the joint's real text);
> check-dark-files ci gate added (static import-graph reachability, NOT
> .olean presence — stale artifacts mask darkness; first dry run
> correctly interrogated DriverCoverage, resolved as a ci direct-target
> root).
> (3) DONE: F3 rewrite-if const-fold twin fixed (plain construction —
> the 143 tautology records are real IF-collapse steps again; the
> LHS==RHS integrity check deliberately NOT added: legitimate identity
> emissions exist, residual 24 records across 3 origins left for the
> next audit's scope); F7 single dischargeOrigins (golden DP scoreboard
> honestly ✓37 ◌6 of 43 — was undercounting 7 leaves); check-no-shadow
> scrape-contract guard (fault-injection verified); check-acl2-tags
> zero-input guard; tryDischarge axiom filter (golden byte-identical —
> all 37 ✓ leaves axiom-clean).
> DEFECT-CLOSURE (branch mdd/audit-paperwork, 2026-07-26; per MDD
> "trust/error issues only" — coverage recs 4-6 DROPPED, doc premise
> corrected in mapping-plan-impact): tier-1 paperwork (BUG-020/021
> entries, ⚠ marks, consCount rename, CLAUDE.md stage-5 fix) PLUS all
> four open defects FIXED:
> - BUG-020 FIXED: isAtomChar carries the full terminator set
>   (isCharTokChar's / *acl2-read-character-terminators*); pinned by
>   reader-terminators.lisp (4 match vs real ACL2); the reader's one
>   fail-open gap closed.
> - BUG-021 FIXED + WIRED: evenp/oddp/expt/string-append to guard-off
>   semantics, into callBuiltin/builtinNames (47 names); pinned by
>   evenp-expt-string.lisp (21 match incl. (expt 0 -1)=0, (expt 5 'b)=1,
>   (evenp nil)=T); 8 corpus entries ratchet-reclassified
>   unsupported→match; 2 LogicTest #guards that pinned the DIVERGENT
>   behavior updated to oracle values; qsort/sorts-equivalent worlds
>   shrink by 2 (EVENP/ODDP snapshots now no-shadow-excluded — zero
>   row changes).
> - F4 FIXED (fork ea4f00dfa1): all three free-var retry loops
>   checkpoint/rollback per ATTEMPT (infra/free-log-tail) — abandoned
>   bindings' backchain steps no longer leak into committed HYP blocks;
>   relieve-hyps1-unify-subst-lst registered raw-code.
> - F3 residue FIXED: recognizer/true+false emit fcons-term* lhs (12
>   'T⇒'T tautologies were folded records); the remaining LHS==RHS
>   corpus records — 8 instances (across 7 logs) of the ONE deliberate
>   shape, preprocess/type-set-fc 'T⇒'T on an already-true clause —
>   triaged DELIBERATE and documented at the emitter (post-fix scan
>   2026-07-27: recognizer/rewrite-if tautologies ZERO);
>   if-finish/combined verified safe by path shape.
> Gates: diff-test 432 match/0 FAIL; golden 62/79 ✓37/43 (header-only
> world counts); local ci 0/0. MERGED to main 2026-07-28 (local ff merge
> under the sandbox protocol, incl. the sandbox-robustness commits; push
> + remote-CI validation pending next networked session).

> **EQUIV-LANE ARC (branch `mdd/equiv-lane`, opened 2026-07-29) — IN
> PROGRESS; GOVERNS THE CURRENT WORK.** Charter: the ratified L2 design
> note `docs/plans/2026-07-29_equiv-lane-design.md` (R-parameterized
> replay; user equivalence = the INTERPRETED relation; every property of R
> consumed from replayed :equivalence/:congruence mirrors, never assumed;
> native relations only at the Imported/ lift boundary). Sequencing:
> increment 0 = STATEMENT PINS (audit rec 6 debt, both pre-merge auditors:
> first item, not deferrable); rung 1 = iff (targets ORDEREDP-APPEND + the
> p3-conj or-shape tripwire, which also first-validates the conjunction
> composer's mid-literal arm); rung 2 = perm (bootstrap-DAG check on the
> real logs, then PERM-IMPLIES-EQUAL-ALL-REL-2, then ORDEREDP-QSORT).
> **PERM-LANE ARC (branch `mdd/perm-lane`, opened 2026-07-30) — IN
> PROGRESS; GOVERNS THE CURRENT WORK.** Rung 2 of the equiv-lane design
> (docs/plans/2026-07-29_equiv-lane-design.md): the congruence registry
> + the interpreted-relation instance (user equivalence = EvTrue of the
> world's PERM on quoted values; every property CONSUMED from replayed
> :equivalence/:congruence mirrors). Targets:
> PERM-IMPLIES-EQUAL-ALL-REL-2 (branch-substitution under :EQUIVALENCE
> PERM), then ORDEREDP-QSORT (two :EQUIV PERM PERM-QSORT steps at
> ALL-REL-arg-2 congruence positions — the headline sorting row;
> conditional on rule:ORDEREDP-APPEND until the type-alist relief class
> lands). Fold-in candidates en route: the type-alist spine-facts
> relief (4 rows), the linear-in-simplify emission gap (p6).
> INC-0 DONE (2026-07-30): the BOOTSTRAP DAG verified on the real logs
> (the design note's precondition, flagged absent by the outside
> auditor) — no circularity/forward/self citations in the perm or qsort
> books; the perm book's equivalence facts are 8/8 green mirrors; the
> two record classes pinned in the design note.
> INC-1 DONE (2026-07-30): PERM-IMPLIES-EQUAL-ALL-REL-2 → REPLAYED ✓
> UNCONDITIONAL (sweep 64/79, 30 unconditional; zero other row
> changes). Five pieces, all Core/NodeCore/Preprocess: (a) the
> non-EQUAL branch-substitution arm — the OBSERVED class has the
> substituted variable ONLY in the justifying `(not (R var val))`
> literal, so the mirror is pure clause structure (byCases: truthy
> closes the disjunction, falsity collapses the literal's if-frame
> out; NO R-facts consumed); occurrences elsewhere stay a loud
> congruence-transport frontier; (b) if-test falsity DEMANDS: every
> if-test subterm of a chain node's lhs/rhs (+ EQUAL-flips) and — the
> world-aware half — of a definition node's UNFOLDED body (the
> recorded rhs shows ACL2's post-resolution view, so context-resolved
> tests appear only world-side) feed the existing later-literal hoist,
> mirroring rewrite-clause's all-other-literals type-alist; (c) the
> SILENT-TAUTOLOGY close at spine exhaustion (no items, no children,
> complementary pair — ACL2 drops taut clauses as *t* with no record),
> via the shared `tautClauseClose` extracted from the clausify
> bridge's inline copy; (d) the unemitted-test
> equality-substitution loop takes clause-literal falsity facts as
> equation sources alongside segment facts (CORRECTED per audit F1:
> the separately-added nilFactFor segFacts arm was DEAD CODE —
> litFactByTerm? already falls through to segFacts — and was removed;
> the eqSources extension is the real enabler, now type-checked per
> audit F8); (e) the
> unemitted-test frontier message now self-locates (running term +
> in-scope facts).
> **SORTING-COMPLETION II ARC (branch `mdd/sorting-completion-2`,
> opened 2026-07-30 at main a1c25c2) — IN PROGRESS; GOVERNS THE CURRENT
> WORK.** MDD-ratified charter:
> docs/plans/2026-07-30_sorting-completion-2-arc.md. Goal: every sweep
> sorting row green + ORDEREDP-QSORT's rule:ORDEREDP-APPEND condition
> discharged. **COMPLETION CRITERIA AMENDED (MDD 2026-07-31): no merge
> until (1) ALL EPICYCLES ELIMINATED — the type-set closure kits
> consolidated into a bounded value-level type-set walker, whole-clause
> dedup, CAR/CDR-symmetric silent refutation — and (2) NATIVE MIRRORS
> for every reasonable green sorting row (pending catalog entries do
> not count); see the charter's amended-criteria section.**
> Sequencing A→D→C→B, then epicycle elimination, then mirrors.
> **SUB-ARC CLOSED (2026-07-31): `mdd/path-emission` folded back (ff
> 371b7a6..4202c06; audit passed, gate byte-identical)** — fork-side
> term-relative :PATH emission (MDD-picked option b), charter
> docs/plans/2026-07-31_path-emission-subarc.md; retires the
> relativize/strip/boundary trio; folds back into this branch at
> ≥69/79 parity. ORDEREDP-APPEND is its validating case.
> **Fold-back audit RUN + fix round LANDED (2026-07-31): all 8
> verified findings fixed (BUG-024/025/026 emission fixes at acl2
> 9f12ded573 + full recapture; collapseEval rung deleted and replaced
> by record-directed descriptor/real-frame anchoring; depth/strip
> remnants deleted; :SWAPPED-P parsed + consistency-checked;
> occurrencePaths lambda-arg descent). BUG-027 (J6 truthy-equal
> closure widening) OPEN — ratify-or-narrow at the parent merge
> review. NEW parent-arc epicycle item: emit :SWAPPED-P on the
> if1/if11 record family and RETIRE the ~190-line swap-bridge
> inventory (normalizeSwapsToward/bridgeIfNegTestSwap/findSwapPos)
> in favor of record-directed swap replay — see the census fix-round
> section.**
> **Class A: 3 of 4 green as of
> 2026-07-31 (TRUE-LISTP-MSORT, ORDEREDP-MEMB, ORDERED-PERMS;
> ORDEREDP-APPEND still red at the nested if-finish/combined strip
> composition). ORDERED-PERMS took a fork speculative-rollback fix
> (rewrite-atm abandoned-reduction, b236e17c28) + 11 replay-side
> frontiers incl. the rewrite-equal cons-decomposition, the S4
> lemma-arm FIRST CONSUMER (EQUAL-CONS), ASSUMED:dp-fact condition
> threading (the documented replayDischargeNode TODO), the CONSP
> closure kit (deriveConspT), and the adjacent-dup collapse.**
> **LANDED 2026-07-31 (post-fold-back): HOW-MANY-QSORT GREEN (71/79 —
> the truthy branch-fact channel + EQUAL two-valued pin; the qsort book
> 6/6). Class B DOWN: the :use-hint payload emission
> (emit/use-hint/payload) roots the apply-top-hints chain at
> CONSTRAINT-CL; MSORT-IS-ISORT/QSORT-IS-ISORT/LEN2-APP-VIA-USE now
> fail truthfully at the R7 functional-instantiation frontier (the
> following arc's scope).**
> **TYPE-SET WALKER LANDED (2026-07-31): the epicycle-elimination
> criterion's kit consolidation is done —
> deriveNilFact/deriveConspT/conspEvidence? DELETED, every consumer one
> `typeSetWalk` call over the unified `falsitySources` channels
> (incl. the ATOM-from-CONSP-false arm and the TRUE-LISTP/CDR direct
> route); EQUAL-flip = the CAR/CDR-symmetric refutation, inside isNil.
> Sweep byte-identical 71/79, ci green. Surviving structural scans +
> the kit-5 equation closure (BUG-027's one-place home) are inventoried
> in docs/notes/2026-07-31_type-set-walker-design.md §status. The
> swap-inventory retirement half CLOSED as a census-recorded NEGATIVE
> result (empty-window markers under-determine multi-level silent
> contexts; normalizeSwapsToward is target-directed recompute-and-check,
> a general rule, retained).**
> **SORTING MIRROR PROGRAM COMPLETE (2026-07-31): every green sorting
> row DECIDED. 24 new native rows across ordered-perms/isort/msort/
> qsort (+ IsChain/List.Perm corollary forms), incl. the flagships —
> ORDEREDP-ISORT/ORDEREDP-MSORT/ORDEREDP-QSORT (insertion/merge/quick
> sort SORT), HOW-MANY-* (all four sorts/splits PRESERVE MULTIPLICITY),
> PERM-QSORT (QUICKSORT PERMUTES, List.Perm form), ORDEREDP-APPEND.
> Support: ~5.5k-line Imported/Sorting.lean (exec kits for 20+ defuns
> incl. the ordinal O< pile, acl2-count, merge2's pair measure, msort's
> evens-decrease, qsort's filter-decrease; the discharger library:
> gz rules, arithmetic-3 family, TP corollaries, totalities, the
> value-level CONVERT-PERM-TO-HOW-MANY characterization, in-book rule
> discharges from sibling replayed statements). Mirror criterion
> (MDD-ratified) written into the catalog header + the SEAM GATE
> (in-Lean, deterministic). driver_replayed% gained the runner's
> missing channels (fcRules, termination pre-pass with world-scoped
> cache, equivRefls) — unify with the runner as an industrialization
> item (docs/notes/2026-07-31_mirror-industrialization.md).
> replayedOnly decisions: TRUE-LISTP-{RM,ISORT,MSORT,QSORT} (sim
> subsumption), termination:QSORT (internal admission obligation).
> SOLE remaining pending row: ORDERED-PERMS — BLOCKED ON EMISSION
> (probed: the four ASSUMED:dp-fact hypotheses are unprovable as
> emitted; the DP-value abstraction drops the value-defining links —
> the replayDischargeNode threading follow-up). Remaining at merge
> review: BUG-027 ratify-or-narrow.**
> Then originally: the type-alist relief family
> (ORDEREDP-APPEND/ORDEREDP-MEMB/ORDERED-PERMS/TRUE-LISTP-MSORT — the
> FC-conclusion third of rewrite-clause-type-alist; expected landing =
> emitted entry provenance + bounded relief registry), then
> HOW-MANY-QSORT's J6 value-level type-set discharge, then the three
> msort record classes, then the sorts-equivalent walls (the shared
> :PATH misnavigation + the :use-hint class). OUT of scope: bsort
> recon wall, equisort encapsulate (R6), functional instantiation (R7)
> — the following arc.

> **VALIDATOR/LIFTER ARC (branch `mdd/validator-lifter`) — TRANCHE 1
> MERGED to main a1c25c2 (2026-07-30, audited: single Opus, zero
> soundness findings, all conditions actioned pre-merge). Tranche 2
> (p3 mirror + dischargers, lift_decode elab, W1 items 2/4/5/8-15,
> Rep transformers, pattern-map tighten) QUEUED after
> sorting-completion II.** Charter:
> docs/plans/2026-07-30_validator-lifter-arc.md (direction MDD-approved
> 2026-07-30; detail sequencing per its "Sequencing" section). Two
> workstreams: W1 = the validation-surface survey's 15-item gap list
> (statement pins for unpinned green rows, termination-status visibility,
> axiom gates, tamper/diff-test/gate tightening); W2 = lifter
> industrialization (#63 a-c: the mirror coverage gate, Rep
> transformers + exec-def generation, the lift_decode elab), driving
> examples p7 → p5 → p3 mirrors, second exercise the PENDING natives.
> Terminology per CLAUDE.md (2026-07-30): mirror = native theorem
> exclusively; replayed statement = the embedded EvTrue theorem.
> TRANCHE 1 COMPLETE (2026-07-30, at the merge point):
> - inc-0: the p7 MIRROR (l.map (fun _ => '0)).length = l.length —
>   the FIRST validation-book mirror, rung 2's ground truth. New
>   name-generic machinery: mapConstBody/corr_mapconst_enc,
>   drv_tp_len/dis_len_int_val (the len-class TP discharger,
>   generalized from the MY-LEN-hardcoded chain), public conv_fix.
> - inc-1: the p5 MIRROR duppRec (e::tl) → duppRec (e::e::tl) — the
>   chain2 schematic's first instance (chain2Body/chain2Rec/
>   corr_chain2_enc, comparison-generic: dupp=EQUAL, p3's ordd=LEXORDER
>   and p6's ordn are the same shape), boolEnc, the IMPLIES hypothesis
>   decode, junk-disjunct elimination.
> - W2(a): the LIFT-COVERAGE GATE — 66-row catalog over the golden's
>   green rows; a new green row without a decision fails the
>   NativeMirrors build. SCOPE (audit F4): the ratchet covers the 25
>   SWEEP books only — pattern-test books (incl. p5/p7 themselves) are
>   outside the golden and gated separately (PatternPins + the axiom
>   run_cmd). Post-audit reclassification (F1/F7): 17 native /
>   6 replayed-only / 43 pending — the five TRUE-LISTP-* "type-absorbed"
>   claims were REFUTED by the file's own TRUE-LISTP-FLATTEN native
>   (the image-of-enc fact) and demoted to pending; the four stale G5
>   reasons corrected to the real lift blockers.
> - W1 item 1: fsq-unfolds STATEMENT pin (the lambda/beta path's gap).
> - W1 item 3: TRUE-LISTP-ISORT + HOW-MANY-ISORT pins (isort complete).
> - W1 item 6: termination-replay rows in the sweep (golden +1 row:
>   termination:QSORT — the class is no longer invisible).
> - W1 item 7: build-failing axiom gate for DriverTests' 11 constants.
> NEXT TRANCHE (charter): the p3 mirror (chain2/LEXORDER + the
> conditional dischargers: tp:INS cons-producer + gz DEFAULT-CDR at
> entry level), the lift_decode elab (3rd assembly = extraction
> trigger), W1 items 2/4/5/8-15, Rep transformers, the pattern-map
> reverse-check tighten.

> PRE-MERGE AUDIT ACTIONED (2026-07-30, 2 Opus inside/outside; ZERO
> soundness findings from both; outside verdict MERGE-with-conditions).
> Convergent top finding fixed pre-merge: the congruence-license
> (fn,pos,R) lookup was a shape INFERENCE while the step-level :RUNES
> cites (:CONGRUENCE <name>) — now ANCHORED to the citation (BUG-023;
> fork-side rule-classes/cr-rune emission open). Also actioned: dead
> nilFactFor segFacts arm removed (F1); kIdx-1→kPos coordinate fix at
> both branch-substitution posL sites (F2, dormant); iff explicitly
> excluded from the R-rule offer filter (F4); equiv added to the
> with-lemma stored-rule match (F5, twin-clone fix); eqSources loop
> type-checked per the litFactByTermChecked? discipline (F8);
> ORDEREDP-APPEND pin's iff→equal strengthening source-checked in the
> docstring (F7); design note amended (outside F1/F4/F7/F8: the
> literal-weakening justification cited, the equivalence-mechanism
> inventory extended with refinements/self-congruences/pequivs, the
> polarity open item CLOSED with the real residual classes, the
> "no R payload needed" claim restated as a two-row observation);
> p7's degeneracy on the inference axis recorded (outside F9,
> pattern map). DEBT (not blocking, tracked): taut closes don't
> consult :RUNES NIL (F6 — needs rune threading into the spine);
> branch-substitution condition/remove-flg/lit-position emission
> (outside F2); taut-close commuted-IFF/double-negation/dedup arms
> (outside F3); a non-degenerate congruence validation book (outside
> F9); rung-3 classes: R-out congruences + implicit self-congruences
> (convert-perm-to-how-many's PERM-TLFIX records) + refinements +
> non-singleton geneqv + origin-dependent :EQUIV semantics.
> MERGE POINT (2026-07-30, inc-2 committed 0dd7c08): both arc targets
> green, decorrelated validation pinned, full local ci green. Queued
> post-merge (NOT blocking): the type-alist relief class
> (LEXORDER-TRANSITIVE marker, :TA-RUNES [LEXORDER] — flips
> ORDEREDP-APPEND/ORDEREDP-MEMB/ORDERED-PERMS/TRUE-LISTP-MSORT and
> discharges ORDEREDP-QSORT's biggest kept condition), the
> linear-in-simplify emission gap (p6), HOW-MANY-QSORT's J6 solidify
> frontier, and the audit-disclosed debt list above.
> INC-2 DONE (2026-07-30): ORDEREDP-QSORT → REPLAYED ✓ (sweep 65/79,
> 35 conditional; zero other row changes) — the headline sorting row,
> conditional ONLY on pre-existing debt (rule:ORDEREDP-APPEND +
> totality/TP/arithmetic classes); the perm reasoning is
> SELF-CONTAINED: rule:PERM-QSORT (the new interpreted-relation
> hypothesis shape, mkRuleHypType R-route + routeRel discharge) and
> cong:PERM-IMPLIES-EQUAL-ALL-REL-2 (the new `cong:` whole-formula
> hypothesis class, CongSpec shape-parse + no-decode discharge) both
> DISCHARGED from replayed mirrors. The use site is
> `replayCongCollapse` (Preprocess): the R-payload collapses at its
> congruence frame by value-level MP + the two-valued EQUAL decode —
> no chain-threaded R payload needed (see the design note's rung-2
> build log). DECORRELATED VALIDATION: p7-cong-collapse 4/4 (fresh
> SAME-LN relation family, arity-1 congruence position; pinned in
> PatternPins; pattern-map entry added). En route: the multi-clause
> clausify bridge's TAUT-DROPPED split class (recorded :CLAUSE ('T))
> + tautClauseClose's COMMUTED-EQUAL pair arm. Statement pin for
> ORDEREDP-QSORT added to Tests/SortingPins.lean (incl. the
> iff→equal-strengthened ORDEREDP-APPEND stored-rule hypothesis and
> ALL-REL's boolean TP shape).

> PRE-MERGE AUDIT ACTIONED (2026-07-30, 2 Opus agents inside/outside;
> ZERO soundness findings from both; outside verdict "merge it — the
> foundation is right"; the inside F1 lhs claim REFUTED — term is
> rebound to the expanded-args form at induct.lisp:306). Confirmed
> findings actioned: BUG-022 — the :EQUIV mislabel class swept (the
> rewrite-if quotep-arm's diverging :RHS/:equiv and the
> *geneqv-iff*-guarded if11/type-alist-disjoint arm fixed in the fork
> at 25609a38; the must-be-true silent-collapse emission gap documented
> open in docs/BUGS.md); p5's two factually-wrong rationales corrected
> (the or-collapse does NOT fire there — type-set kills the test,
> constant-test path, the or survives clausify intact; p5 validates the
> iff PREPROCESS lane only); p4's map entry notes its IFF-combined
> records all sit below the literal root; the stale inc-2b/2c
> value-pin paragraph corrected; budget-margin wording fixed (~1.55x).
> AUDIT-DISCLOSED DEBT (not merge-gating, do not let rot): (a) the
> or-collapse bridge has ONE gated green instance (p3) — p6 exercises
> it 7x more but its 0/1 pin would stay green if the bridge regressed;
> tighten p6's pin to the frontier MESSAGE once its post-BUG-022 status
> settles, and add the bridge's :UNREWRITTEN-TEST cross-check (the
> record carries the primary datum; the bridge currently infers the
> collapse from prov.equiv + a sibling node's shape); (b) the
> taut-dropped clausify arm skips the recorded-vs-recomputed round-trip
> for that pass (sound — the proof is over our recompute — but the
> docstring overclaims and the recorded pair is not cross-checked);
> (c) the type-set-equality / disjunctive-TP-consp recipes derive
> mid-chain type facts from clause context instead of emitted type data
> (fail-closed and evidence-backed, but CLAUDE.md's emit-more rule
> points at fork emission — policy debt; ORDEREDP-MSORT shows the
> decode out-running ACL2's record, caught by the rhs check); (d) tp:
> condition labels do not distinguish value-only from args-valued
> hypothesis shapes (latent — no green row consumes an args-valued one
> yet); (e) statement pins anchor the THEOREM TERM, not the world's
> defun bodies (gen-world remains the missing independent anchor).
> RUNG 1 COMPLETE (2026-07-29, commits through e47d50c, all CI-green):
> the p3-conj-mid-literal tripwire FLIPPED — ORDD-INS-MID REPLAYED ✓
> cond[tp:INS, rule:DEFAULT-CDR] (1/1, kernel-checked, axiom-filtered),
> the conjunction composer's MID-LITERAL arm's first genuine validation.
> The final pieces (inc-2c complete): SINGLETON spine arms (with
> restLits empty the goal is the BARE literal; evtrue_dp_if_split's
> (IF l 'T 'NIL) conclusion mismatched — byCases directly, the nil
> branch's EvTrue 'NIL closing ex falso via evtrue_quote_nil_false);
> else-bodies extracted so split and singleton arms share one
> construction. PLUS p4-iff-or-shape (e47d50c): the decorrelated IFF
> validation book (wild anchor ORDEREDP-APPEND; snoc/has-e family) —
> LANDS ON the known clausify-region RECON wall (the bsort wall:
> clausify-input's second expand-abbreviations interleaves steps into
> the clausify event stream), PatternPins-gated as a truthful recon
> tripwire (flips when the wall falls → also unblocks bsort).
> REMAINING (post-merge follow-ups, each its own increment):
> (a) the type-alist spine-facts relief class — ORDEREDP-APPEND's
> LEXORDER-TRANSITIVE marker relief (:TA-RUNES [LEXORDER]; the fact
> derives from an assumed-true user-fn application's body walk) — the
> SAME class as the parked ORDEREDP-MEMB/ORDERED-PERMS/TRUE-LISTP-MSORT
> backlog item; (b) the clausify-region recon wall (p4 + bsort);
> (c) RUNG 2 (perm): bootstrap-DAG check, congruence registry,
> interpreted-relation instance → PERM-IMPLIES-EQUAL-ALL-REL-2,
> ORDEREDP-QSORT.
> INC-2b/2c LANDED (2026-07-29, commits c61d166/b5649c6/1e5bbe7 —
> every commit sweep-green, 63/79 29u byte-identical golden): the
> literal-chain R-THREADING is LIVE (chain payloads carry (Expr × Bool),
> chainReqEq/chainWithR/chainIffWithR/evtrueWithR mixed composition;
> composeSplit + the conjunction composer + trivial paths consume IFF
> literal chains via siff_val_nil_transport/siff_val_ne_nil_transport/
> evtrue_of_evrel_siff); the OR-COLLAPSE BRIDGE works (chainPrefix
> trailing param on replayRewritesWith; the test-position prefix
> re-replayed on the then-copy via the branch-children strip pattern
> (myKind, 1); evrel_siff_if_or_bridge); TAUT-DROPPED clausify outputs
> (bridgeClausify pOut? + tautDropped — the proof built over the
> RECOMPUTED split clause's complementary pair / 'T literal);
> NON-VARIABLE branch substitution (replaceTermOcc) with recorded
> SCONS-TERM/EXEC folds (consumed only when they change the clause),
> 'NIL-literal drops + renumbering, justifying-branch entry, pushed-
> residual and VACUOUS closes (justifying equality stays unsubstituted);
> ordinary-theorem guard recalibrated 1M→3M (p3 legitimately costs
> 1–2M/~80 s). [RESOLVED 2026-07-29 in inc-2c: the "value-pin
> divergence" p3-conj then hit was the SINGLETON-SPINE shape
> (evtrue_dp_if_split's (IF l 'T 'NIL) conclusion vs the bare-literal
> goal) — fixed by the singleton byCases arms; p3-conj REPLAYS 1/1.]
> ORDEREDP-APPEND's LEXORDER-TRANSITIVE type-alist relief remains the
> open rung-1 follow-up; then rung 2 (perm).
> INC-2a DONE (2026-07-29): the OR-SHAPE IFF STEP replays end-to-end
> (zero status flips; 63/79, 29u). (a) FORK (acl2 2265010346): the
> rewrite-if-finish combined step's or-shape collapse ((IF a a b) ⇒
> (IF a 'T b), rewritten-left := *t*, geneqv-iff-guarded) was emitted
> :EQUIV EQUAL — a fidelity MISLABEL caught by the p3-conj tripwire; the
> :equiv now recomputes the guard (iff exactly when the collapse fired);
> recapture-all at 2265010346. (b) applyStepSIff MOVED to NodeCore and
> extended with the IMPLIES arg-1/2 COLLAPSE rows
> (evrel_implies_arg1/2_siff_collapse — boolean consumers make SIff
> arguments eval-EQUAL); the or-shape node's SIff payload
> (evrel_siff_if_or_shape) lifts along its :PATH and MUST collapse at a
> boolean-consumer frame before the literal root (root-iff chains are a
> named frontier — the full R-threading of literal chains stays queued).
> (c) the TYPE-SET-EQUALITY node class (equal/type-set-nil): the
> cons-vs-atom disjointness cell (logic_equal_nil_of_consp_t_nil),
> consp evidence via the shared conspEvidence? helper (dedup with the
> args-valued-TP derivation). (d) if1/boolean extended to IF-HEADED
> tests: two-valuedness derived STRUCTURALLY from the branches
> (boolDisj?: quoted constants / equal / lexorder / boolean-TP fns,
> recursive; cond_toBool_of_t_or_nil). p3-conj-mid-literal advanced
> FOUR frontiers and now sits at the named OR-COLLAPSE BRIDGE frontier:
> the combined node's then-branch is the unrewritten test's copy
> replaced by 'T with no recorded step — replaying it needs the test's
> recorded chain re-composed at the sub-position (the chainPrefix
> plumbing; NEXT). ORDEREDP-APPEND's frontier (LEXORDER-TRANSITIVE
> type-alist relief, :TA-RUNES [LEXORDER]) is the other open rung-1
> item.
> INC-1 DONE (2026-07-29): the IFF-UNFOLD EMISSION GAP + four walker
> advances, zero status flips (63/79, 29u — golden message-only census:
> ORDEREDP-APPEND advanced 5 frontiers to the LEXORDER-TRANSITIVE
> type-alist relief; ORDEREDP-MSORT advanced 2 to a spine result
> mismatch). (a) FORK (acl2 f6f84fa4): expand-abbreviations' boot-strap
> non-rec arm (IFF + no-ops) recorded only the rune — the body adoption
> was invisible, so ORDEREDP-APPEND's preprocess chain could not thread
> its recorded if-iff steps; now an entry-style
> emit/expand-abbreviations/nonrec-body rewrite-step (recapture-all,
> logs at f6f84fa4; 6 logs changed). (b) replayIffDef — the
> (:DEFINITION IFF) ground-zero recipe against the builtin semantics
> (logic_iff_cond), the replayImpliesDef pattern. (c) the ARGS-VALUED TP
> hypothesis shape (mkTpHypTypeAv): emitted corollaries whose residue
> mentions formals BARE (BINARY-APPEND/MERGE2 `(EQUAL (fn X Y) Y)`
> disjunct class) — previously silently unofferable — bind the argument
> VALUES; consumed by the recognizer's disjunctive-cons derivation
> (logic_consp_t_of_tp_disj2/3: 2- and 3-disjunct, per-disjunct consp
> evidence from syntactic cons / clause-context facts); stays
> hypothesis-backed at stage 5 (honest cond — prover targets the
> value-only shape). (d) chained ELIM rounds: a later record whose
> guard literal σ-descended into the clause pushes NO guard child
> (ACL2's tautology drop) — close via the clause's own literal,
> level-generic. (e) composeSplit consumes CLAUSE-CONTEXT facts for
> assumed-resolved tests (all-others-false: direct falsity + the
> (NOT t)-complement); env-crossing hygiene — elim resets
> segFacts/branchFacts, and term-keyed fact lookups at the crash-prone
> consumers are TYPE-CHECKED (litFactByTermChecked?) so a stale
> cross-env fact falls through instead of crashing (the *1.1 pool-root
> crossing surfaced it). NEXT (inc-2, the rung-1 core): the recorded
> or-shape collapse ((IF a a b) ⇒ (IF a 'T b), rewrite-if-finish) is
> EMITTED :EQUIV EQUAL but is iff-only — fix the fork label (the
> geneqv-refinementp guard is the truth source), then thread R through
> the LITERAL chain (the p3-conj tripwire flip + the mid-literal
> composer's first green validation).
> INC-0 DONE (2026-07-29): STATEMENT PINS delivered —
> `Tests/SortingPins.lean` (the scalable per-book statement-pin home, in
> `just ci` via the Tests root): ORDEREDP-ISORT, PERM-QSORT,
> TRUE-LISTP-QSORT, and the QSORT TERMINATION MIRROR each pinned as an
> `example` whose TYPE is hand-transcribed from the acl2/ submodule
> sources (isort.lisp, qsort.lisp, convert-perm-to-how-many.lisp,
> arithmetic-3 fold-consts-in-+) and discharged by the machine mirror
> constant (runBook — exact sweep semantics), so a stage-5 statement drift
> fails elaboration; the full cond[…] hypothesis sets transcribed + the
> exact status lines pinned; all four constants axiom-clean. Retires open
> validation debt item (3) of the sorting arc. Cost: ~4 min module build
> (the qsort book re-replay dominates).

> **SORTING-COMPLETION ARC (branch `mdd/sorting-completion`, opened
> 2026-07-28) — MERGED to main 2026-07-29 (local ff to 200ab39 under the
> sandbox protocol on explicit sign-off; 2-agent pre-merge audit, zero
> soundness findings; push + remote-CI validation pending next networked
> session).** Target: flip the
> 17 remaining sorting rows, qsort first. Increments in value order (from
> the 2026-07-28 driver-coverage frontier census):
> (1) `dischargeDecrease` beyond destructor chains — the decrease argument
> is a DEFINED-function application (`(FILTER 'LT (CDR X) (CAR X))`), not
> a destructor chain; blocks ORDEREDP-QSORT (the headline correctness
> theorem) + HOW-MANY-QSORT (feeds the already-conditional PERM-QSORT).
> (2) `replayPreprocessChain` path/lhs navigation — blocks ORDEREDP-APPEND
> and ALL THREE sorts-equivalent capstones (MSORT-IS-ISORT,
> QSORT-IS-ISORT, BSORT-IS-ISORT).
> (3) type-alist spine falsity facts — ORDEREDP-MEMB, ORDERED-PERMS,
> TRUE-LISTP-MSORT.
> (4) singles: NUMERATOR in the builtin registry (2 msort admission-lemma
> rows), MERGE2 TP recognizer cell, ORDEREDP-ISORT split trace.
> INC-1a DONE (2026-07-28): the ACL2-COUNT primitive head set — NUMERATOR/
> DENOMINATOR/REALPART/IMAGPART/COMPLEX-RATIONALP as trusted-core builtins
> (the un-snapshotted axiomatic heads of ACL2-COUNT's emitted gz body;
> INTEGER-ABS/LENGTH have snapshots and ride the world/D4 route),
> differential-pinned FIRST (numerator-denominator.lisp 35/35 vs oracle;
> corpus 480 match/0 FAIL, 13 ratchet-reclassified). Ground truth found en
> route: qsort's admission IS a real waterfall (verified live — two
> induction pushes), the fork ALREADY emits it, buildDevelopment ALREADY
> attaches it (termination field) — the gap is REPLAY-side only. The
> recorded termination proof now replays past convergence and stops at
> replayRecognizer: (CONSP (ACL2-COUNT …)) ⇒ NIL wants the type-set
> lattice step (integerp TP ⇒ not-consp) — SAME class as the MERGE2
> recognizer single; that lattice step is the next sub-increment, then
> wire termination-ClauseProof replay into the totality prover (supersedes
> dischargeDecrease's destructor walk where a recorded proof exists).
> msort's ACL2-COUNT-EVENS rows advanced NUMERATOR→hyp-relief-spine
> (message-only golden churn, 0 status flips).
> INC-1b DONE (2026-07-28): the qsort admission waterfall replays through
> BOTH inductions — TP-lattice recognizer derivation (integerp TP ⇒
> ¬consp, trusted-core), BINARY-+ range derivation, add-literal DEDUP
> mirror at induction case construction (the Preprocess dedup's twin),
> fully-dropped cases + ruling-test complement arm + definitionally-nil
> vacuous branches (COMPLEX-RATIONALP on the complex-free space). Golden
> BYTE-IDENTICAL.
> INC-1d/e (2026-07-28/29): the recorded QSORT admission waterfall
> REPLAYS end-to-end (kernel-checked; clausify multi-bridge per-split
> expansions, induction dedup re-intro via evtrue_intro_else, proveDpFact
> INT-VIEW pre-pass — 7-value linear leaves close with NO shape splits;
> admission-class replay budget by the original calibration methodology;
> COERCE + Logic.neg oracle-pinned into the trusted core). WIRED into the
> totality prover AND the theorem-side induction: interpCount (the
> INTERPRETED count, Classical.choice definite description — design-I1
> bookkeeping, appears in no statement) as the μ for recorded-termination
> defuns; termination mirrors replayed once per book (the D1 pattern);
> decreases decoded from the replayed theorem's O< facts against
> byte-checked O</O-FINP gz shapes (interp_decrease_decode); Stage-5
> hypothesis accounting recomputed post-discharge. The FILTER-decrease
> frontier is RETIRED: HOW-MANY-QSORT → J6 solidify frontier,
> ORDEREDP-QSORT → split-trace frontier (successor classes, queued).
> Bonus: CONSP/ENDP coverage duality + vacuous definitionally-nil
> branches + 3-ary call fall-through + 3-ary totality
> (totality_3_of_body/_rec_snd_mu, triple bindArgs lemmas, the shared
> goApp application dispatch) — 15 totality conditions discharged across
> 14 rows (HOW-MANY/INSERT/ISORT/ORDEREDP/REL/FILTER/ALL-REL/
> BINARY-APPEND/EVENS…), ORDEREDP-RM now FULLY unconditional (tally
> 28→29 uncond at 62/79). The build-time sweep stack overflow was the
> termination replay's RULE OVER-SUPPLY (one nested binder per offered
> rule): fixed by the citedRuneNames demand filter. Residual:
> total:MSORT/MERGE2 still hypothesis-backed (honest conds); the qsort
> rows' NEXT walls are J6-solidify + split-trace + preprocess-path
> (increments 2-4).
> MID-POINT OPUS AUDIT (2026-07-29, authorized minimal, 1 agent): ZERO
> soundness findings (kernel-check/axiom-gate/Stage-5 accounting all
> verified fail-closed; interpCount_eq airtight). Fidelity F1 (HIGH,
> actioned): the totWalk-side recorded route was DEAD — its ruler gate
> missed the CONSP/ENDP duality its siblings got (the audit's own
> "fix-lands-on-one-twin" callout); fixed + the O<-class hyp-backed
> totality augmentation + pure-phase-first fixpoint ordering — total:QSORT
> now DISCHARGES in green rows (PERM-QSORT/TRUE-LISTP-QSORT conditional
> only on the irreducible total:O< + tps + rules), validating the whole
> decode chain end-to-end. Also actioned: F2 positional gate on the
> setup-memo no-op; F3 mirror circularity guard; F4 recorded-route
> arity-1 gate (untagged-abort hole); F5 covering-clause selection
> unified; F6 conjoinDisjTerm dedup. Remaining audit note: the
> ruler-coverage idiom still has near-clones (documented).
> INC-2a SCOPED (2026-07-29, recon from the real ORDEREDP-ISORT *1.1/3'
> record): the "2 branches without a split trace" class is the AND-SHAPE
> conjunction strip — the literal's rewritten result (IF L R 'NIL) is
> clausified via :CLAUSIFY-CONJUNCTION (STRIP-BRANCHES/AND-SHAPE) with
> TWO SEGMENT-OPEN leaves and NO if-interp split test; the walker only
> has the split composer (Core.lean hasSplit region). Fix: a CONJUNCTION
> composer — EvTrue(parent) from both children's EvTrue (valid: all-
> others-false forces L from child1 and R from child2, so the literal's
> cond-value is truthy); rows blocked: ORDEREDP-QSORT (the headline),
> ORDEREDP-ISORT.
> PRE-MERGE AUDIT (2026-07-29, 2 Opus agents inside/outside + synthesis):
> ZERO soundness findings from BOTH; outside verdict "the right
> foundation — recommend merging"; all 5 golden promotions verified
> honestly classified; F1-F6 verified real. OPEN VALIDATION DEBT (both
> agents, restated here per the audit — not just in test comments):
> (1) the recorded-termination decode chain has exactly ONE working
> instance (QSORT) — the p3 decorrelation book's mirrors frontier at the
> nested-*1.1 admission shape, so THIN/PRUNE validate nothing of the
> route yet; (2) the conjunction composer's MID-LITERAL arm has ZERO
> coverage (probe-verified byte-identical golden without it) — the
> p3-conj tripwire flips when the or-shape normalization lands;
> (3) STATEMENT PINS (audit rec 6, promised this arc) NOT delivered —
> Tests/DriverTests.lean untouched; the FIRST item of the next segment,
> not deferrable past it (both auditors), for ORDEREDP-ISORT +
> TRUE-LISTP-QSORT/PERM-QSORT + the QSORT termination mirror
> [RESOLVED 2026-07-29: equiv-lane arc inc-0, Tests/SortingPins.lean];
> (4) the fork's :CLAUSIFY-CONJUNCTION left/right marker is emitted but
> UNCONSUMED (the composer infers from lp.result syntax — P8 follow-up);
> (5) sorts-equivalent capstones are CROSS-BOOK (:INCLUDED defuns carry
> no termination proofs) — the route is per-book until WP5 transfer;
> the capstone wall is encapsulate + :functional-instance (L3), the
> ":PATH does not navigate" surface text is NOT the real blocker.
> ERRATA on earlier records (inside audit): c36330a's gate line says
> "500 match" — the correct figure is 497; "15 totality conditions
> across 14 rows" (407c28a/TODO) — the artifact count is 29 dropped
> total: occurrences over 10 distinct fns across 14 rows.
> INC-2a DONE (2026-07-29): the AND-SHAPE CONJUNCTION COMPOSER — both
> spine positions (mid-literal: value-cases dispatch to the branch
> continuations under the forced-nil conjunct's fact; LAST literal: both
> pushed children peeled to their conjuncts' truth, the AND-value truthy
> via cond_true_val). ORDEREDP-ISORT FLIPS (63/79); ORDEREDP-QSORT
> advances to the PERM equivalence lane (the planned-LAST increment-5
> class, joining PERM-IMPLIES-EQUAL-ALL-REL-2).
> INC-1c DONE (2026-07-28): spine hyp-relief markers + setup-phase
> definition memos consumed as validated no-ops (linear-pot setup records
> between CLAUSIFY-OUT and BEGIN-LITERAL; the literal chains re-record
> and validate the real transformations); multi-include rule RE-STORAGE
> dedup (13 identical FOLD-CONSTS-IN-+ specs are ONE rule; distinct
> matches still hard-fail). msort EVENS rows advanced two more frontiers
> (0 status flips). THE REMAINING QSORT-ADMISSION BLOCKER: proveDpFact's
> bounded strategy (split bound 3) vs the 7-value linear-arithmetic DP
> leaves — needs the lift-to-rational-images bridge (no shape splits);
> then wire termination-ClauseProof replay into the totality prover.
> (5) the equivalence lane (PERM-IMPLIES-EQUAL-ALL-REL-2, branch
> substitution under PERM) — the genuine S3-iff/equiv item, LAST.
> Folded in (audit rec 6): statement pins for the sorting books toward
> one per book. Also folded in (MDD 2026-07-28): any DEFECT found en
> route — fidelity bug, emission gap, clone hazard — is fixed IN this
> arc, not deferred. Discipline unchanged: emitted facts only, hard-fail
> at frontiers — where an increment needs data ACL2 didn't emit, the fix
> is fork emission, not Lean inference.
> MDD DECISION (2026-07-28) on audit recs 4–6: SORTING-FIRST. The target
> remains the sorting book — the qsort proof reconstruction — and its
> remaining blockers are named per-row replay frontiers, not the fresh-book
> crash sites (sorting reconstructs 100%; the ProofTree crash sites fire
> only on fresh books). Disposition: rec 4 (ProofTree.lean:339/:281) PARKED
> until sorting completes; rec 5 adopted as a CHEAP NON-GATING instrument
> (`just fresh-report`, run occasionally, drift visible — deferred until it
> is the bottleneck or sorting completes); rec 6 folded into the sorting
> arc for the sorting books specifically (statement pins toward one per
> book — the qsort result is only worth having if it provably says what
> qsort says). Rec 7 (F6 BUG entries + acl2Count rename) was already DONE
> in the defect-closure arc (BUG-021 + consCount).

> **Mapping arc (branch `mdd/mapping-arc`, 2026-07-22/23) — COVERAGE
> COMPLETE at increment 8; UNMERGED.** Scope as executed (MDD
> corrections during the arc): COVERAGE ONLY — no pipeline changes, no
> support work, no sweep wiring; a frontier-landing book is a SUCCESS.
> Deliverables: `docs/notes/2026-07-22_pattern-map.md` (the gated map:
> top-down coverage frame over ACL2's own inventory, frontier tier,
> driver fake-replay inventory graded [bridge]/[rederive]/[mirror],
> quirk backlog, MDD triage — corpus-need > obvious-deficiency >
> ACL2-importance, bad design outranks missing features); 46 books in
> `acl2_samples/pattern-tests/` all through real ACL2; an independent
> Opus gap audit (actioned: LET/lambda blind spot, all 19 rule-class
> tokens, C1 prose-leak correction); the REPLAY dimension (26 pattern
> theorems replay end-to-end, 23 named-frontier in ~7 classes);
> `scripts/check-pattern-map.sh` in ci (bidirectional + logs + pin
> signatures — the map cannot rot). Support backlog now PIN-DERIVED:
> P2 capture-halt family (defattach/local/ratio-literals/#c/exotic
> rule classes), untagged-prose suppression, guard proofs unlogged,
> LET/lambda frames, backchain-limit emission; P3 L2 lane (obligation
> multi-bridge + :EQUIV consumption artifacts on disk), forcing
> rounds, defun-sk, nonlinear. Native lifts + differential families:
> deferred to support-side arcs (visible in map, not silently
> dropped).

> **POST-MAPPING SUPPORT SEQUENCING (MDD triage, 2026-07-23 — see
> `docs/notes/2026-07-23_mapping-plan-impact.md`, which supersedes all
> earlier next-arc orderings):** S1 capture/emission hardening fork
> batch (halt family, prose suppression, guard-proof emission,
> backchain field, + the emission-arc queue) → S2 LET/lambda
> (core-path-blocking, was in no plan) → S3 the L2 lane designed from
> the captured artifacts (MDD review first) → S4 corpus singles per
> demand. Standing direction for ALL support work: principled replay —
> prefer fork emission + recorded-step replay; retire the fake-replay
> inventory's bridges as emissions land; missing features acceptable,
> baked-in bad design not.

> **S2b arc (branch `mdd/s2b-beta-emission`, opened 2026-07-25) — the
> beta-emission completion fork batch.** Queue, from the S2 audit:
> Inc-1 DONE (39dd013): audit probes → gated pins. Inc-2 DONE (fork
> 845ae4233f): ALL FOUR beta sites emit (site 2 REWRITE/LAMBDA-BODY-QUOTED;
> site 3 EXPAND-ABBREVIATIONS/LAMBDA-BODY, entry-style on all three beta
> arms + boundary frame on the open expansion + documented no-emit on the
> survives arm; site 4 EXPAND-HINT/LAMBDA-BODY at rewrite-with-lemmas'
> lambda arm — NOT fncall/expand-permission, whose nil-rune named-fn case
> stays as-was) + geneqv-derived :EQUIV (ratified option B,
> structured-geneqv-equiv) at all beta sites and the fncall keep-arm
> twins. TWO in-flight design amendments (fail-closed-preserving, need
> ratification at review): compound :EQUIV parsed CANONICALLY to fail at
> NODE granularity (a parser hard-fail killed six unrelated ordered-perms
> rows — book granularity too blunt); the G1 equiv gate EXEMPTS composite
> nodes (definition/lambda-body — the replay never uses the label; it
> composes recorded children and hard-checks the recorded rhs). Golden
> BYTE-IDENTICAL at 62/79; p2-beta-expand-hint REPLAYS with zero new
> driver code. Inc-3 DONE (fork 8b67373306 + 94ed1abfa1): the emitters'
> :RHS instantiation is PLAIN substitution (sublis-var's cons-term
> const-folding made entry-style rhs jump AHEAD of the recursion's own
> recorded steps — incoherent chains, hit the pre-existing
> abbreviation-expansion emitter too); nested-lambda boundary frames
> anchor as the SYMBOL lambda; proveConv beta-descent (re_conv_lam1/2)
> + findOccurrences lambda-ACTUALS descent. p2-beta-preprocess REPLAYS
> 2/2. Named frontiers left open (map close-out section):
> p2-beta-quoted-actuals (constant-IF-collapse chain shape),
> p2-beta-equiv-iff (stub convergence; genuinely needs the S3 iff
> lane), cov-mv-let (the NESTED-let class — body-congruence PathStep
> does not exist; findOccurrences deliberately skips bodies).
> Inc-4 DONE: 2-Opus RE-AUDIT (2026-07-26) — ZERO soundness defects,
> BOTH amendments verdicted SAFE (kept-hypothesis attack: no path — every
> assumed hypothesis is built from separate events behind independent
> equal-only gates); all findings actioned (fork da1f5336a4): entry-style
> betas emit :equiv EQUAL (F1 — pure substitution is an EQUAL fact; the
> context label cost coverage, recovered: p2-beta-iff-context REPLAYS);
> singleton geneqv reads its :equiv field (Q1 — the structural
> *geneqv-iff* check missed real-rune singletons, cov-defchoose);
> (:hide-normalize nil) step at the HIDE arm (F2); gstack boundary
> anchor symbol fix (F3 — 3-deep lets parsed again); site-3 emitted
> :PATHs now HONORED by the chain replay (F2-lean); findOccurrences
> body-occurrence POISONING (F3-lean — a body+actual double occurrence
> read as a false unique); s2bBetaBooksPin DriverTests gate
> (p2-beta-preprocess 2/2 + p2-beta-iff-context 1/1, was ungated — F6);
> p2 books in the map's reverse check; wrapping-proof presence-sigs;
> comment/map/design-note corrections (F1-lean/F4/F5/F7). ARC COMPLETE
> pending merge sign-off.

> **S2 arc (branch `mdd/s2-let-lambda`, 2026-07-24/25) — the
> REWRITE-FNCALL beta path landed + 3-Opus AUDIT ACTIONED; corpus
> scoreboard unchanged at 62/79; MERGED main 3fd03f5 + PUSHED
> 2026-07-25 (fork b48faff962 pushed first).** AUDIT (2026-07-25, zero
> soundness defects; two of my claims refuted): ACL2 beta-reduces at
> FOUR sites and S2 emitted at ONE — the pattern map's S2 section
> carries the authoritative four-site table; the beta step's hardcoded
> `:EQUIV EQUAL` is a false claim under an IFF context (L2 violation;
> driver proves obligations so not exploitable). NEXT FORK BATCH:
> sites 2–4 emission + the real `:EQUIV` + promote the audit probes
> (site2b/site2c/iff, in the session scratchpad) to pinned books +
> re-audit. AUDIT FIXES LANDED: freeVars unconditionally
> over-approximates (lambda residual kept); NoLet rejects bare
> `(LAMBDA …)`; dpValExpr checks the NoLet certificate its proof twin
> discharges; walker arity parity (1..2 both); known-head-wrong-arity
> is a HARD error again (frontier reclassification narrowed to
> genuinely-unknown heads); dpLiftProof frontiers lambda-bearing DP
> leaves by name (dpLiftF has no lambda arm — documented asymmetry);
> asLamApp requires the LAMBDA name; capture stamps `-dirty` on an
> uncommitted fork tree and the provenance check rejects it; BUG-018
> (duplicate `let`/lambda bindings: ACL2 refuses, our two spellings
> disagree 1-vs-2) + BUG-017 widened to special forms; lambda corpus
> header corrected (extension semantics; the nested entry is THE
> discriminating pin) + declare-lambda masquerade gap pinned
> unsupported; `fsq_unfolds_real_mirror` ci-gates the whole lambda
> replay path (was gated by nothing).** `let`/`mv-let`
> translate to `((LAMBDA (formals) body) actuals)`, so this was
> core-path-blocking. S2.1 interpreter LAMBDA arm (lexical extension —
> semantics DECIDED by the differential pin: the fresh-env `ev`
> variant diverged on a nested open lambda) + shared `lamFormals?`;
> S2.2 `PathFrame.argLam`; S2.3 binder-aware `freeVars`/`NoLet`/
> `substTerm` with real lambda cases in all four induction lemmas, the
> beta lemma pack (`conv_lam`, `evalOpt_lam_beta_conv`,
> `re_lam_beta{1,2}_{conv,val}`) and arity-1/2 lambda congruences.
> FORK (b48faff962): the beta step is EMITTED
> (`:RUNE (:LAMBDA-BODY NIL)`, origin `REWRITE-FNCALL/LAMBDA-BODY`) —
> ACL2 fires no rune there, so the LAMBDA-BODY block had no adopting
> step and its nodes were mis-parented onto the next chain step; same
> site gained the speculative-rollback checkpoint the fncall path had.
> Driver: `PathStep.lamHead` congruence walk, `replayLambdaBody`,
> DP-lift walkers descend into the beta-reduct. `cov-let-lambda`
> replays end-to-end; the wall also fell in cov-mv-let /
> cov-meta-rule / cov-clause-processor (now at unrelated frontiers:
> MV-NTH DP-lift, SYMBOLP recognizer cells, SYNP preprocess shape).
> Also: unmodeled DP primitives are now tagged FRONTIERS, not hard
> errors (they are capability limits, and the lambda descent surfaces
> them where the lambda frontier used to mask them).
> Follow-ups: rename `NoLet` (it now admits a binding form) and
> collapse the `envUpdate`/`bindArgsOver` clone (end-of-arc cleanup);
> emission for `rewrite`'s all-quoteps lambda fast path; lambda
> binders of arity >2.

> **S1 arc (branch `mdd/s1-capture-hardening`, 2026-07-23) — COMPLETE
> at 62/79 (28 uncond + 34 cond), DP ✓32 ◌4 ✗0 of 36; UNMERGED.**
> S1.1 the halt family DISSOLVED (`:EVENT-FAILED`; all were suppressed
> ordinary event failures) + `:FORCING-ROUND`; S1.2 `:VERIFY-GUARDS`
> wrapper + backchain 6th field + `:CLAUSIFY-CONJUNCTION`; S1.3
> FC/type-alist contradiction discharge emitters (`*true-clause*`-gated
> after an MDD-caught epicycle) + spine consumer; S1.4 the DP lexorder
> ORDER THEORY + cone-mode budget fix (HOW-MANY-FILTER-1 replays);
> S1.5 clause-context threading — demand orientation, solidify index
> demands, TRANSITIVE solidify via deterministic equation closure
> (MDD-ratified: emit what ACL2 records, derive in Lean what it
> doesn't), add-literal dedup bridge, endp DP bridge
> (HOW-MANY-EVENS-AND-ODDS replays). Fork: a291c2ec22 → a90dd10679
> (5 commits; fork pushes FIRST). Remaining S1-adjacent follow-ups:
> gz-snapshot backchain field, P8 conjunction spine consumer,
> guard-obligation REPLAY, J6-beyond-closure solidify verdicts.

> **Emission arc (branch `mdd/emission-arc`, 2026-07-21/22) — GRIND
> COMPLETE at increment 12, 47→60/79 (28 uncond + 32 cond), DP ✓29 ◌7
> ✗0 of 36; UNMERGED, awaiting pre-merge audit.** Landed: 3 fork
> emission batches (fertilize detail, :TA-RUNES, gz FC-rule snapshots,
> runout inner block); fertilize recipe; FC-derived relief registry
> (LEXORDER-TOTAL); multi-record elim rounds; the RUNOUT pass;
> clausify-alongside class; unicity-of-0 builtin class
> (`builtinIntVal?`); pass-local strip tagging; rewrite-if SWAPPED-P
> bridge + joint normalization; lenNat DP bridge; EQUAL-commuted rule
> match; induction clean-up mirror (`trivial-clause-p`/`if-tautologyp`)
> + carve-out discharge of dropped clauses; gz_def_not;
> compound-recognizer recipe (ZP); 'pt-solidify linking; FC-source
> demand hoisting. Full increment log + the singles-queue CLOSING STATE
> (every remaining FAIL row classified: fork batch ×3, design-class
> backlog ×5, full-increment singles ×2, MDD-parked walls) in
> `docs/notes/2026-07-21_emission-arc.md`.

> **Expand-and-or arc (branch `mdd/expand-and-or`, 2026-07-19) — S1–S3
> LANDED + follow-on relief recipes; scoreboard 32/79 (24 uncond + 8
> cond), diff-test 389/0.** Plan `docs/plans/2026-07-19_expand-and-or-mirror.md`
> (status updated inline). Landed: fork emits `:FROM`/`:RUNES`/`:SUBST`
> on clausify-expand + abbreviation pushes; `expandTerm` (single
> structural def, kernel-refl walk facts) + definitional
> `clausifyChecked` + proved registry lift-equalities + 12-case
> `expandTerm_liftEq` + transport; EVERY corpus clausify-bridge wall
> fell. Follow-on recipes: negated-hyp relief (atm-rooted chain, lifted
> through `not`), SYNP definitional discharge (`(:DEFINITION SYNP)`
> ttree-gated), preprocess-proved full-clause verdict routing,
> abbreviation-rule consumption (hyp-free enforced). Rows forward this
> arc: LEN-INTERLEAVE→unicity, TRUE-LISTP-{ISORT,MSORT}→real deep
> frontiers (type-alist DERIVED entries; ◌-class assumed-fact
> composition), HOW-MANY-{MERGE2,MSORT} ✓, LEN2-APP-{VIA-INDUCT,
> NO-HELPER} ✓. S4 lemma arm: NO current consumer (6 events, all in
> rows failing upstream) — stays fail-closed per the no-unwired-infra
> rule. Next frontier classes by row count: STRINGP dpValExpr lift (×8
> qsort-class), definition-chain IF-normalization `(EQUAL X 'NIL)` vs
> `(IF X 'NIL 'T)` (×5), unicity-of-0 TP int fact (×3),
> marker-relieved falsity facts (×3, J6b), type-alist derived entries,
> ◌-class discharge composition, NUMERATOR (H3 pin-first), LEN-ZIP2/3
> simplify-path off-frame, elim/induction one-offs.

> **External-knowledge arc (branch `mdd/external-knowledge`) — design
> RATIFIED, prerequisites + order proofs DONE (2026-07-11/12).** The design
> doc `docs/plans/2026-07-10_external-knowledge-design.md` (D1–D8,
> audit-incorporated, four MDD decisions ratified) governs the arc; work
> proceeds per its WP0–WP6 queue. Landed so far, each gate-verified
> (differential 386 match / 0 FAIL; ci golden byte-identical):
> **BUG-012** canonical-by-construction `Number` (junk unrepresentable);
> **BUG-013 minimal** canonical nil/t symbol identity (`canonSym`); **BUG-014**
> KEYWORD-package duplicate eliminated (keywords' home package — third
> instance of the duplication pattern, found exactly where the antisymmetry
> proof needed it); and the **four lexorder ORDER THEOREMS**
> (`LexorderOrder.lean`: `lexorder_refl`/`_antisymm`/`_trans`/`_total`,
> kernel-checked, core-only imports, axioms ⊆ {propext, Classical.choice,
> Quot.sound}) — the Lean-proved counterparts of ACL2's boot-admitted
> ground-zero rules, resting on `lexView?` injectivity (`unview`
> retraction), which is what the BUG-012/013/014 canonicity fixes bought.
> **WP0 DONE (2026-07-14, working tree)**: D8 per-defthm rule flush (the
> last theorem's `(:RULES)` entry now reaches its own log — verified live:
> HOW-MANY-ISORT's rule was stranded, now emitted); D3 ground-zero defun
> SNAPSHOTS (`(:DEFUN … :SOURCE :GROUND-ZERO)`, cited-closure via the
> prin1$ printed-symbol collector, termination clauses RECOMPUTED by
> `termination-theorem-clauses` — isort carries 29, perm 19); D5
> ground-zero rule snapshots (`(:GROUND-ZERO-RULES …)` with `:match-free`;
> the lexorder rules' stored `:EQUIV EQUAL`/rhs `'T` shape CONFIRMED on
> the real snapshot — the audit-F2 fail-closed check passes); parser
> consumes both fail-closed, events INERT in the Development (golden
> byte-identical; ci exit 0; diff-test 389/8/0). Parse-sweep finding:
> qsort/sorts-equivalent logs have NEVER parsed (dotted-suffix runes
> `(:REWRITE FLOOR-POSITIVE . 1)` in `(:RULES)` — pre-existing parser
> frontier, R3 material, verified pre-D8 by flush-position argument);
> bsort/msort/ordered-perms fail reconstruction on known frontier classes.
> **WP1 DONE (2026-07-15, working tree)**: non-builtin snapshot defuns are
> World entries at `Development.toWorld`; `groundZeroDefs` RETIRED; the
> no-shadow exclusion (`builtinNames`, EvalOpt.lean) is CI-enforced
> (`scripts/check-no-shadow.sh` scrapes `callBuiltin`'s arms and diffs);
> D6 = snapshot justifications (recomputed clauses) flow to the totality
> prover; `ReplayConfig.gzNames` feeds the lazy `upTo` bound. **FIX
> interim keep** (`worldEntryInterimKeeps`, ClauseTree.lean): FIX is the
> one builtin with a live world-unfold consumer (MY-LEN-MY-APP's step
> case replays its `definition:` rune — full exclusion regressed it,
> caught by the native-axiom gate), so its snapshot still world-enters
> until WP2's D4 definition fact replaces the unfold — REMOVE AT WP2.
> New frontier class surfaced: LAMBDA (translated LET) applications in
> snapshot bodies (SYMBOL<) — dpVal walkers now throw it as a TYPED
> frontier (was an escaping error). Golden updated: exactly the 21
> predicted world-count rows (audit F1 confirmed — no status/cond flips;
> REPLAYED 26/50 unchanged). Pins: exclusion/entry/keep/justifications
> guards in Tests/DriverTests.lean.
> **WP2 DONE (2026-07-15, working tree)**: D4 definition facts for
> TRUE-LISTP, LEN, NFIX, FIX, BOOLEANP, ENDP, ATOM. Per fn a proved
> `gz_def_<fn>` lemma (EvalLemmas): `Logic.<fn> v = <value composition of
> ACL2's own ground-zero body>` — each is a kernel-checked
> callBuiltin-vs-ACL2-definition agreement (a fidelity validation of the
> trusted core). Replay: `replayBuiltinDefUnfold` (Driver) discharges a
> `definition:` rune for a world-absent builtin by `conv_builtin1` + the
> lemma, with formals/body read off the EMITTED snapshot
> (`ReplayConfig.gzDefs` ← `Development.groundZeroSnapshotDefs`) — a
> drifted emission fails the lemma application (fail-closed
> recompute-check); registry `d4DefFacts` guarded in-sync with `dpUnary`/
> `builtinNames`. `Logic.fix` added (callBuiltin's FIX arm refactored to
> it, behavior-identical); FIX joined `dpUnary`/`dpLiftHeads`; the WP1
> FIX interim keep is RETIRED — builtin exclusion from the world is now
> TOTAL. Golden: 6 world counts −1 (the FIX-citing logs), REPLAYED 26/50
> and all DISCHARGE columns unchanged, and all 7 target rows ADVANCED to
> later walls: APP-NIL ×2 / TRUE-LISTP-REV / REV-REV now at the
> `(EQUAL X 'NIL)` vs `(IF X 'NIL 'T)` chain mismatch (same frontier as
> TLP-APP-NIL; verified on the real tree: the node's final iff-
> normalization `(EQUAL X 'NIL) ⇒ (IF X 'NIL 'T)` is NOT recorded as a
> child — an emission-gap class, fix at the source per the no-inference
> rule); CD2-BOUND at `compound-recognizer` rune (ZP-COMPOUND-RECOGNIZER,
> new frontier class, ◌ leaves kept per audit F9); LEN-REV-ACC at
> unicity-of-0 needing a TP int fact for builtin (LEN …); TRUE-LISTP-ISORT
> at a recognizer composition (TP of INSERT through CONS). Pins: emitted
> bodies of TRUE-LISTP/LEN/FIX guarded against the parsed snapshots in
> DriverTests.
> **WP3 DONE (2026-07-15, working tree)**: D5 ground-zero rules as PRELUDE
> CONSTANTS. `Replay/GzRules.lean`: `gz_rule_lexorder_reflexive` /
> `gz_rule_lexorder_transitive` — the ∀-env mirror statements of the
> boot-admitted (proofs-SKIPPED) lexorder rules, world-parametric with a
> LEXORDER no-shadow hypothesis, PROVED from the `LexorderOrder` order
> theorems + `lexorder_boolean` through `evalOpt` (zero added trust).
> Wiring: `Development.groundZeroRuleSpecs` seeds the rule-offer telescope
> (gz rules precede every theorem; the emitted event sits at the log
> tail); `d5GzRules` registry + `dischargeGzRuleHyp` discharge a used
> gz-rule hypothesis by instantiating the constant and type-hinting it
> against `mkRuleHypType` of the EMITTED spec (fail-closed
> recompute-check) — exercised LIVE by a DriverTests pin (both constants
> kernel-checked against the parsed isort snapshot specs). Audit F2's
> anticipated dischargeRuleHyp builtin-boolean branch was NOT needed: the
> constant route bypasses dischargeRuleHyp; two-valuedness lives in the
> constants' proofs; the if1/boolean LEXORDER branch already existed.
> Audit F3 caveat checked on the real isort log: FC rules
> (LEXORDER-TOTAL) appear only in DP-leaf/step rune SUMMARIES (carve-out
> territory) and inside with-lemma RELIEF rune sets — never as standalone
> rewrite nodes. Golden: exactly one row moved — ORDEREDP-ISORT advanced
> past `no stored-rule hypothesis in scope` to the NEXT wall,
> `marker-relieved hyp (LEXORDER (CAR IT) X1) has no (not …)-falsity
> fact in scope` (the transitive rule's hyps were relieved by
> FC/type-set facts whose derivation the replay does not yet consume —
> the FC-relief frontier).
> **WP4 DONE (2026-07-15, working tree)**: D1 MIRROR REGISTRY. Each green
> replay in the coverage harness is `addDecl`'d as a per-theorem mirror
> constant (`∀ env, <kept-condition telescope> → EvTrue w ⟪Goal⟫`;
> axiom-checked first); `dischargeRuleHyp` APPLIES a registered
> dependency's constant at the consumer's own telescope fvars instead of
> re-replaying its tree per consumer (the re-replay path remains as the
> fallback for unregistered deps — DriverTests/NativeMirrors still use
> it). Registry is per-book (`MirrorRegistry`), reset per corpus file —
> cross-book reuse needs WP5's world transfer. The harness was already
> one-session + dependency-ordered (audit F7's rework amounted to
> threading the registry through the existing loop).
> MEASURED (PERM-IS-AN-EQUIVALENCE, the design-§4 baseline):
> inline 13,506,883 nodes / 5.9s build / 2.0s check → registry
> 777,719 nodes / 1.2s / 0.4s — 17.4× size, ~5× time; same conds ([]).
> (The design's ≈557M figure was historical — pre-letBindFVar-era rule
> hyps; the current inline baseline is already 40× below it.) Golden:
> BYTE-IDENTICAL (the regression gate); perm coverage wall 21-49s → 13s.
> **WP5(a) DONE (2026-07-15, working tree)**: D2 `evalOpt_world_mono`
> PROVED as stated in the design (EvalOpt.lean): a convergent evaluation
> over `w1` transfers to any extension `w2` under `hext` (defs preserved)
> + `hnew` (no builtin shadowing — the side condition world-first
> dispatch forces). Fuel induction over a two-world `evalOptStep_world_mono`
> (the `evalOptStep_mono` case bash with the call branch split four ways
> on `w1/w2 defs.get?`; none/def refuted via `hnew`'s callBuiltin-none
> disjunct). Fuel-shape preserving — `∃N∀f≥N` facts transfer directly.
> **WP5(b) D7 assembly DEFERRED — scope finding (2026-07-15, verified on
> the real logs):** the CURRENT corpus has NO exercisable cross-book rule
> discharge. Every rewrite rune applied in any isort SIMPLIFY-CLAUSE step
> is GROUND-ZERO (CAR-CONS ×30, CDR-CONS ×36, DEFAULT-CAR ×1,
> LEXORDER-REFLEXIVE ×15, LEXORDER-TRANSITIVE ×15); the perm/how-many
> rule names appear only in `(:RULES)` storage re-emission, never
> applied. The real D7 consumer is sorts-equivalent.proof-log (applies
> HOW-MANY-ISORT ×3, ORDEREDP-ISORT ×3, TRUE-LISTP-ISORT ×3 + the
> msort/qsort/bsort variants in actual steps) — but it (i) never parses
> (dotted-rune `(:REWRITE F . 1)` entries in `(:RULES)`, pre-existing
> frontier) and (ii) depends on msort/qsort/bsort theorems, whose books
> wall at the induction-generality frontier (single-controller
> `(acl2-count v)` cdr-decrease limit) — both OUTSIDE the ratified WP
> queue. Building D7 now would be un-validatable machinery (the banned
> anti-pattern). The D7-enabling path: dotted-rune parse → induction
> generality → then D7 assembly against sorts-equivalent.
> WP queue status: WP0-WP4 + WP5(a) landed; WP5(b)/WP6 + the queue-external
> frontiers (FC-relief, compound-recognizer, unrecorded iff-normalization,
> builtin-TP pins, dotted runes, induction generality) return to design.

> **BUG-002 (symbol case) FIXED (2026-07-08, this branch).** The parser now
> adopts ACL2's readtable-case :upcase EXACTLY: bare symbols/keywords upcase,
> `|bar|` (incl. `:|bar|`) reads verbatim, `|NIL|`/`|T|` map to nil/t. Symbol
> NAMES are stored uppercase on the whole identity path (SExpr.t, isNamed,
> callBuiltin keys, world/theorem/rune names); internal DISPATCH TAGS (rune
> type/equiv/processor/origin/clausify outcome-verdict-how-kind/extraField
> keys) are lowercased at the ProofLog parse boundary. `just ci` + `just
> diff-test` green (289 match, 0 FAIL); the 12 BUG-002 discriminators are now
> `match` regression guards. See docs/notes/2026-07-08_symbol-case-semantics.md
> + docs/BUGS.md BUG-002. This UNBLOCKS lexorder (nil-as-COMMON-LISP-symbol
> handling depends on faithful names).

> **`just ci` is GREEN** and includes the driver-coverage sweep: hard-fails on
> any item-less PROVED leaf (emission gap) and reconstruction-integrity
> failures; reports per-theorem replay + per-leaf DP-discharge status —
> currently **REPLAYED 26/50 (21 unconditional + 5 conditional)** (see
> `Tests/driver-coverage.golden`), DP leaves ✓11 ◌9 ✗0 of 20, and a
> replayed ✓ is AXIOM-CLEAN by construction (the harness collects each
> proof's axioms).

## CURRENT PRIORITIES (confirmed with MDD 2026-07-06, post-R1)

Ordered by project-wide leverage — general machinery over special-case walls:

> **Long-term roadmap PROPOSAL (2026-07-06, awaiting MDD review):**
> `docs/plans/2026-07-06_long-term-roadmap.md` — the spine past R2
> (cross-book rule discharge as the remaining R2 architecture item, R3–R7
> walls named), the industrialization cadence, the trusted-core growth
> policy, and the post-corpus arcs (live tactic, breadth sweep, upstreaming).

> **Differential harness rebuilt (2026-07-07, branch mdd/differential-surface).**
> Toward the TOTAL ACL2 MASQUERADE objective (roadmap H3): the Lean
> interpreter is now a PEER of ACL2 — `acl2lean eval [eval-in <book>]` reads a
> STREAM of forms from stdin and emits one value per form, same interface as
> `acl2 < forms`. The value PRINTER was made ACL2-faithful for dotted/nested
> lists (`(1 2 . 3)`, not `(1 . (2 . 3))`); symbol-case still diverges
> (parser lowercases — a pending masquerade item, folded in the comparator).
> The old single-file `scripts/diff_eval.sh` is RETIRED and replaced by a
> file-based corpus (`Tests/differential/corpus/*.lisp`, syntactic ACL2 with
> `;@` metadata comments both readers skip) + a pure comparator
> (`scripts/diff-test.sh`, `just diff-test`) with three expectation classes:
> `match` (must agree), `unsupported` (not modeled yet — pins ACL2's value),
> `known-bug lean <val>` (known fidelity gap — records the wrong Lean value;
> fails when it changes → reclassify). Current (edge-case sprint #2,
> 2026-07-07): **211 match, 124 unsupported, 15 known-bug, 0 FAIL** across 17
> category files. unsupported surface = list-ops/alists, lexorder/ordering,
> int div/mod + comparison ops (`<=`/`>`/`>=`/`=`, pervasive) + expt/mod/floor
> negatives + numerator/denominator/realpart, bitwise, string/char ops,
> control MACROS (cond/case/when/mv/mbe/the/ec-call + n-ary `+`/`*` + `and`/
> `or`/`eq`/lambda). known-bug (real fidelity gaps, pinned NOT fixed): (a) the
> NUMBER-NORMALIZATION family — parser builds unreduced rationals bypassing
> Logic.mkNumber → `2/4`≠`1/2`, `4/2`/`5/1` not integerp (one-line root cause);
> (b) CHARACTERS — no character atom, so `#\a` is a symbol → `(equal #\a #\b)`
> is t (distinct chars collapse!) and `(symbolp #\a)` is t; (c) `(symbolp
> :foo)` (keywords ARE symbols); (d) SYMBOL-CASE (parser lowercases, so
> `|abc|`=`abc`); (e) quote-abbrev printing (`'x` vs `(quote x)`). Parse-level
> boundary findings (radix literals rejected by our parser though ACL2 accepts;
> floats accepted though ACL2 rejects; ill-formed forms both refuse) are
> deferred to a `refuse`-class phase — see Tests/differential/DEFERRED-FINDINGS.md.
> Gated in CI as its own step. Spec: `Tests/differential/README.md`.

0. **Fail-closed fix sprint — DONE (2026-07-06, branch mdd/fail-closed-fixes).**
   All actionable findings of `docs/notes/2026-07-06_fail-closed-audit.md`
   landed: `panic!`→`Except` through `Event.classify`/`fromSExprs`; the TYPED
   frontier tag (`throwFrontier`/`isFrontierErr`) replacing string-prefix
   frontier/defect classification in buildTotalEnv + the rule-hyp discharge
   (N1); `:ORIGIN`/`:PARENTS` parser throws (N2/N3); reader-conditional
   hard-fail (N4); translator package hard-fail + `escapeStringLit` (N5/N6);
   `evalOptStep` malformed shapes → `none` — unbound-var nil default kept as
   the documented ∀-env modeling choice (F15, trusted core); the fncall
   rollback `(cons t …)` tag in the fork (N7). Gates: ci green, golden
   byte-identical 26/47, logs regenerated on the patched ACL2, `(quote)`
   non-convergent via CLI probe. Investigation residuals stay tracked (N8
   settled-down-clause, free-var relief no-marker path, built-in-clausep at
   induct.lisp:1310, Parser.lean unterminated-block-comment panic, Driver
   `rebuild` panic default).
1. **LIFTER INDUSTRIALIZATION sprint (#63) — LANDED on mdd/lifter-sprint
   (2026-07-06, UNAUDITED; sprint-end audit next).** THE WHOLE PERM BOOK IS
   IMPORTED: all 8 mirrors UNCONDITIONAL (obligation log EMPTY; scoreboard
   26/47 = 21 uncond + 5 cond, was 14+12) and all 8 native facts proved
   axiom-clean (entries 9–16, incl. `isPerm_equivalence_driver` — ACL2's
   defequiv as a Lean `Equivalence` — and `comm_rm_native_driver` =
   List.erase_comm). The machinery, all general: (a) totality prover covers
   user-fn if-tests (`conv_if_split_ex`) + opaque non-measured self-call
   args, + the buildTotalEnv dev-order/fixpoint fix; (b) the TP PROVER
   (`proveTp`/`tpWalk`/`ConvToP` family) — emitted corollaries proved from
   the body, forward-only, by the #37 precedent (MDD-confirmed: consuming
   the emitted fact and constructing the proof object ACL2 never had is NOT
   the banned inference); (c) proof-term scale — `letBindFVar` sharing,
   perm-is-an-equivalence 3.87e9 → 1.09e8 nodes (14–36×; both are
   sizeWithoutSharing of the REPLAY OUTPUT the harness kernel-checks — the
   STORED NativeMirrors constants are ~10× smaller again via Lean's
   abstractNestedProofs; audit #4 measured stored permEquivMirror ≈1.0e7);
   (d) the LIFTING
   DECODE KIT (Lifting.lean: `mirror_pins_ne_nil`, `bool_of_cond_eq`,
   `conv_and_conds`, `mirror_peel_guard`, `booleanp_cond`) — anti-overfit
   gauge held: entries 10–16 ≈40 lines each vs entry 9's ≈130. Open TP
   frontiers (honest, named): builtin-headed return paths (tp:my-len /
   tp:len2 need natp-through-+ value lemmas) — evenlen's cddr decrease
   CLOSED by the #37 decrease-prover rework (2026-07-18);
   pool-subsumption subsumer still replayed twice (scale residual).
2. **Proof-term scale — DONE within the lifter sprint** (letBindFVar
   sharing, 14–36×; residual: subsumer subtree still replayed twice in
   pool subsumption — revisit if R2 sizes bite).
3. **R2 (isort) — IN PROGRESS (2026-07-07, branch mdd/lifter-sprint tip;
   include-book composition LANDED).** The isort book parses, reconstructs,
   and sits in the coverage corpus (26/50): included defuns re-emit with
   `:INCLUDED T` (fork defuns.lisp — justification, no clauses; total: stays
   D6-kept until the termination-machine recomputation emission), included
   theorems reconstruct as `.includedTheorem` events (statement + rules, no
   proof tree; `rule:<thm>` citations replay, their step-5 DISCHARGE stays
   hypothesis-backed until cross-book proof import). Machinery ADDED
   (proven + guarded, but NOT yet exercised end-to-end — see below): endp-
   spelled induction decrease (`consp_toBool_of_endp_nil`; the case tree
   records the STRIPPED positive test with sign=false), endp/atom DP-lift
   registration.
   **`lexorder` WALL FELLED (2026-07-08, Task #7).** lexorder is wired into
   callBuiltin + dpBinary/dpLiftHeads + callBuiltin_lexorder rfl-lemma; the
   function was already alphorder-faithful (BUG-006/007/008) and the
   nil-as-smallest bug is fixed (`lexAtom?`: nil/t are ordinary COMMON-LISP
   symbols — verified `(lexorder nil 5)`=NIL). Grounded + pinned:
   docs/notes/2026-07-08_lexorder-semantics.md + target-ordering.lisp
   (34 match vs real ACL2). All 3 isort theorems now advance PAST lexorder
   to their NEXT frontiers (coverage golden updated; DP leaves ✓10→✓11):
   ORDEREDP-ISORT → recognizer `(CONSP (INSERT …))` value; TRUE-LISTP-ISORT
   → `TRUE-LISTP not defined in the world` (its lexorder total: obligation
   now discharges ✓); HOW-MANY-ISORT → clausify-spine residual at *1/3'4'.
   *Honest status of the endp machinery (audit #5, 2026-07-06): the
   falsy-endp induction-decrease branch in `replayInduction` +
   `consp_toBool_of_endp_nil` are proven and triple-guarded, but reached by
   NO completing replay yet — the isort theorems that would exercise them
   (orderedp/how-many/true-listp-isort) hard-fail EARLIER at `lexorder`, and
   the other endp/atom-testing corpus fns fail at unrelated frontiers. So
   this is built-ahead infrastructure whose consumer (isort induction) is
   named but blocked; it is validated end-to-end only once `lexorder` lands.
   The scoreboard is honest about this (those rows show as FAIL); still NOT
   exercised end-to-end — an isort theorem must replay THROUGH the endp path
   to validate it.*
   **Recognizer-via-TP + lexorder-if1/boolean LANDED (2026-07-09).**
   `replayRecognizer` now discharges `(REC (fn args)) ⇒ t` from `fn`'s emitted
   :TYPE-PRESCRIPTION corollary (e.g. `(CONSP (INSERT E X))`, ACL2's
   `type-prescription:INSERT` justification) — consumed, not inferred; and the
   `if1/boolean` closer handles a LEXORDER-valued test directly via
   `lexorder_boolean`/`cond_toBool_lexorder` (a builtin boolean, no TP hyp).
   ORDEREDP-ISORT advanced through BOTH and now sits at
   `rule LEXORDER-TRANSITIVE: no stored-rule hypothesis in scope`.
   **CORRECTED FRAMING (2026-07-10, assessment note
   docs/notes/2026-07-10_external-knowledge-assessment.md):** that rule is a
   GROUND-ZERO BUILT-IN theorem (axioms.lisp:27162), NOT an included-book
   rule — no book's log can carry a (:RULES) entry for it. The R2(c) design
   doc must cover the full EXTERNAL-KNOWLEDGE problem, four species measured
   from the real isort log: (1) ground-zero built-in defuns
   (TRUE-LISTP/NFIX/LEN — blocks TRUE-LISTP-ISORT + 6 recon rows),
   (2) ground-zero built-in rules (LEXORDER-REFLEXIVE/-TRANSITIVE, cited
   60×/43× — blocks ORDEREDP-ISORT), (3) included-defun totality (= R2b),
   (4) genuinely cross-book included rules (NOT-MEMB-IMPLIES-HOW-MANY-IS-0
   17×, HOW-MANY-RM 4× from convert-perm-to-how-many). Design doc BEFORE
   building (the R2 rule); implement in leverage order 1→2→3/4. Outside the
   family: HOW-MANY-ISORT clausify-spine residual at Subgoal *1/3'4'
   (investigate on the real tree, independent of the design). The endp
   induction machinery above is the likely consumer once these clear.
   THE TWO-STAGE LIFT as the following work item: The
   lift-automation analysis (MDD-ratified intent 2026-07-06; per-theorem
   cost is now low, per-FUNCTION corr lemmas are the scaling bottleneck):
   (a) **Two-stage lift — HAND-VALIDATED on the perm book (2026-07-06,
       branch mdd/r2-isort; design docs/plans/2026-07-06_two-stage-lift.md).**
       The split is real: `membExec`/`rmExec`/`permExec` (total Lean body
       mirrors, `termination_by acl2Count`) + stage-1 corrs
       (`ConvTo w env (fooT a…) (fooExec av…)` over ALL SExpr values —
       the conv_builtin interface shape, so exec'd fns COMPOSE: perm's
       walk cites memb/rm corrs like builtin lemmas) + stage-2 pure-Lean
       simulations; the three `corr_*_enc` lemmas are now 4-line
       corollaries (~325 hand lines deleted, statements byte-identical,
       ci + native axiom gate green). Kit lemma `conv_if_lift`
       (EvalLemmas). REMAINING: (i) mechanize stage 1 as an elab command
       (spec in the design note §Next — walk arms are exactly the three
       hand proofs' moves; hand-offable); (ii) isort/insert once
       `lexorder` lands (its exec needs the primitive).
   (b) **Decode-theorem generator** (fold in once TWO books exercise the
       schema): parsed formula + (fn ↦ corr) registry → the whole
       per-theorem decode emitted, fail-closed outside the schema; takes
       entries from ~40 lines to a declaration. Kernel-checks everything
       it emits (certifying-walker pattern; swallows the env/decide
       boilerplate).
   (c) **Named frontier lemmas** (steady drip, do opportunistically):
       natp-through-binary-+ value shapes (flips tp:my-len/tp:len2),
       the cddr decrease (flips total:evenlen).
   NOT to be automated: choosing the idiomatic native statement (human
   judgment — Lifting.lean's "target theorems stay user-supplied"), and
   anything on the fidelity-critical replay path (done, fail-closed).
   R2 also exercises the include-book rule flush (audit finding C) and
   the G4 forcing seam.

Explicitly deprioritized: coverage drilling for its own sake (remaining
failures are deeper walls R2+ reaches naturally). (Differential expansion is
NO LONGER deprioritized — the rebuilt harness above makes it cheap and it now
drives trusted-core growth per roadmap H3.)

## THE GOVERNING PLAN — `docs/plans/2026-06-10_generality-design.md` (ratified)

The architecture is the HYBRID: certifying walkers as the production/discovery
lane; stable fragments consolidate into verified functions FRAGMENT-LOCALLY.
**Binding invariants (plan §7, mirrored in CLAUDE.md): L1 judgments are the
open interface (no monolithic Derivation inductive); L2 `R` is an abstract
relation, never an enum; L3 mandatory world-parametricity.** The sequencing —
each step lands with the standing discipline (real artifact first, fail
closed, ci as scoreboard, audits at milestones):

- [x] **G1 — R-parameterized rewrite judgment + geneqv emission (DONE
      2026-06-10, commit 3ae8352).** `EvRel R` over an abstract value relation
      (L2), Eq/SIff instances; congruence-table rows by (fn, position, R-in,
      R-out) — if-then/if-else preserve SIff, if-test collapses it; equal
      steps inject by refinement; `:EQUIV` emitted at all sites and REQUIRED
      by the parser (fail-closed); iff/user-equivalence RULE applications are
      precise named frontiers. THE IFF FRONTIER IS RETIRED: app-nil, rev-rev,
      true-listp-app compose through chain + clausify bridge and now stop at
      the G5 induction frontier (multi-literal pushed clauses). The interim
      boolean-head strengthening (`formulaBooleanFact`) is removed by G2.
- [x] **G2 — `EvTrue` migration (DONE 2026-06-11, branch mdd/g2-evtrue,
      audit-passed).** Clause/mirror judgments state ACL2's truthiness
      (`∃N∀f≥N ∃v, eval = some v ∧ v ≠ nil`); exact-t survives at the VALUE
      level, injected at the clause boundary (`evtrue_of_eq_t`). The
      boolean-valuedness frontier class is GONE: `formulaBooleanFact`/
      `strengthenIffChain` deleted (iff chains end natively), the clausify
      walk's mid-spine positive-literal restriction dissolved
      (`LeafFact.exactT` deleted, D9), discharge verdicts compose honestly
      as SIff steps (D10). Mirror-statement validity check SUBSUMED. Golden
      table byte-identical (17/37, ✓9 ◌9 ✗0); audit: 5 reviewers + verify,
      zero surviving findings (incl. the G1 retro-dimension). Design +
      decisions: docs/plans/2026-06-11_g2-evtrue-migration.md.
- [x] **G3 — Tier-1 consolidations (2026-06-12, branch
      mdd/g3-consolidations).** Fragment A: `dpLiftF` (the DP value lift
      as a pure function over an explicit vars assoc list, D-A5) +
      `dpLiftF_sound` proved once (12-case induct); discharge spine/close
      consume ONE lemma instantiation with a defeq lift fact. Fragment B:
      `clausifyPure` made total, `clausifyPure_sound` proved once
      (11-case induct, cond-algebra value route, nil/truthiness only —
      G2/D9 honored); `bridgeClausify` on ONE instantiation; the
      peel/walk kit (~318 lines: `peelClause`, `walkPosT`, eight `val*`
      walkers, `LeafFact`) + six dead walker-era `EvalLemmas` lemmas
      DELETED. Per invariant L1: both fragments local
      (`Replay/DpLift.lean`, `Replay/ClausifyBridge.lean`). Golden table
      byte-identical throughout (17/37, ✓9 ◌9 ✗0). Follow-up: retire
      `dpValProof` when consumer-free (totality walk + TP instantiation
      remain). Design + as-built:
      docs/plans/2026-06-12_g3-consolidations.md.
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

- [x] **Entry 1 — my-len-my-app (2026-06-10).** `(xs ++ ys).length = xs.length
      + ys.length` (`my_len_my_app_native_driver`) proved through the DRIVER's
      conditional mirror over the LOG-DERIVED world; axioms clean. The pattern
      pieces, all reusable: driver-shape dischargers (`drv_total_*`,
      `drv_tp_mylen`) restate the hand dischargers in the driver's v-fixed
      hypothesis forms; `evalOpt_app1_arg`/`conv_arg1_of_conv_app` (argument
      strictness, inversion) recover argument convergence from the TP
      hypothesis's application convergence; `my_len_my_app_native_of_mirror`
      is the single-seam native assembly any mirror proof plugs into.
      RETROFITTED same day to the world-parametric route: all SimpleWorld
      dischargers/`corr_*`/assembly generalized over any `w` with def-facts
      (L3), instantiated at `simpleWorldD` by `decide`; the
      `worlds_get_eq`/`eval_eq` transfer glue is deleted. `evalOpt_defs_ext`
      stays in EvalOpt as the documented fallback for world-concrete
      machinery.
- [x] **Entry 2 — app-assoc (2026-06-10).** `(xs ++ ys) ++ zs = xs ++ (ys ++
      zs)` (`app_assoc_native_driver`) via the driver's mirror over the
      02-rev log-derived world (`app` AND `rev`); axioms clean. The L3
      payoff, demonstrated: the `AppAssoc` support lemmas were generalized to
      world-PARAMETRIC form (any `w` with the `app` def + unshadowed
      builtins), so NO world-transfer was needed — they instantiate directly
      at the log-derived world with `by decide` facts. This, not
      `evalOpt_defs_ext` transfer, is the preferred catalog pattern going
      forward (entry 1's transfer route remains as the fallback when hand
      machinery is world-concrete).
- [x] **Entry 3 — ground-arith (2026-06-10).** `(1 + (2 + 3) : Int) = 6`
      (`ground_arith_native`) via the driver's unconditional mirror over the
      00-direct log (executable-counterpart class); axioms clean. The GROUND
      DECODE pattern: both sides evaluated symbolically to `int`-values over
      UNREDUCED Lean arithmetic, equated by the mirror's equal⇒t fact — the
      arithmetic comes from ACL2's replayed evaluation, not a Lean decision
      procedure.
- [x] **Entries 4–7 (2026-06-10).** sq-of-3 `(3 * 3 : Int) = 9` (DEFN-UNFOLD
      decode: `conv_defn_1` + symbolic body evaluation); cdr-cons-refl
      `Logic.cdr (cons u v) = v` (SYMBOLIC-VALUE decode — the lhs is
      deliberately left unreduced so the mirror's equality is the content);
      equal-symm / equal-trans (HYPOTHESIS decode: the native hypothesis
      truthifies the `implies` antecedent via `Logic.equal_t_iff`, the
      mirror's implies⇒t fact forces the conclusion; equal-trans adds the
      formula's if-spine via `conv_if_true`). All axioms clean. Also: the
      four bespoke per-entry mirror elaborators were unified into ONE
      parametric `driver_mirror% dev world "name"` elaborator.
- [x] **Entry 8 — app-cons-car (2026-06-10).** `Logic.car (cons u v) = u`
      (`car_cons_native`): instantiate `b ↦ nil` so the app-value collapses,
      unfold `app` TWICE in the decode layer (cons-case then nil-case), keep
      the outer `car` symbolic. The deepest decode; axioms clean.
- [x] **Honest classification of the rest (2026-06-10).** sq-rewrites,
      idf-rewrites, count-down-zero, my-evenp/oddp-3 are MIRROR-ONLY: their
      decode is reflexive (our own evaluation computes both sides to the
      same value), so no non-vacuous native fact exists; DriverCoverage is
      their regression. Still pending with real frontiers: app-nil/rev-rev/
      true-listp-* (G5), linear-chain (#50), len2 family (needs that world's
      dischargers — the entry-1 recipe).

- [x] **The lifting library + its SPINE (2026-06-10, MDD-ratified).**
      `Imported/Lifting.lean`: `Conv` (eventual convergence) / `Rep α` (a
      Lean type represented in ACL2's value space — injective encoding onto
      an ACL2 RECOGNIZER; `idRep`, `intRep`/`integerp`,
      `listRep`/`true-listp` with the genuine isomorphism
      `List SExpr ≃ {s // trueListp s = t}`) / `Implements₁/₂` (an ACL2
      function symbol computes a Lean operation along representations) +
      `native_of_mirror_equal`, the generic equational ender every
      equational entry now finishes with. Instances: `implements_plus`,
      `implements_times` (builtins), `implements_append`, `implements_len`
      (NAME-GENERIC over append/length-shaped defuns — `corr_append_enc`
      proved once replaced the two ~100-line per-world copies; the len
      instance pre-builds the pending len2 family). Both native assemblies
      and catalog entries 3–8 run through the spine. Target theorems remain
      user-supplied; the algebra only structures decodes.
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

- [x] **#37 totality from admission (2026-06-11, branch
      mdd/totality-from-admission).** Recursive :DEFUN events emit the
      admission justification + RAW termination clauses (fail-closed parse);
      the driver's totality prover (proveTotality/totWalk, WF-induction on
      acl2Count with case-split body walks, decrease obligations matched
      against the EMITTED clauses and discharged via the Count library per
      the carve-out) auto-discharges EVERY total: hypothesis on every
      replayed theorem (17/37, theorem-level cond[] now tp:-only) and the
      TP-free per-leaf total:(…) conds in the DP-leaf diagnostics
      (exists_conv_elim). Decision log:
      docs/notes/2026-06-10_totality-from-admission-decisions.md (D1–D9 +
      solo-audit findings A1–A4). Follow-ups (next task): leaf TP hyps in
      fn-level shape (lifts the TP-paired retention), measured-formal
      permutation, sum/custom measures (interleave/cd2 frontiers),
      non-trivial admission waterfall replay (the termination field).

- [x] **Performance pass, STAGE 1 — DONE (2026-06-11, branch mdd/perf-pass,
      commits 8628466+3e9dc1b): sweep 1361 s → ~82 s (16.5×), golden gate
      byte-identical.** Profile-driven (the full campaign:
      `docs/notes/2026-06-11_perf-profile.md`): 99% of the sweep was the
      DP-leaf machinery — P5 (proveDpFact's failing DIRECT simp_all attempt,
      ~40–860 s each → SPLIT-FIRST, direct only past the split bound) and
      P6 (the caller's telescope hypotheses riding into every split leaf's
      simp_all → prove the closed fact statement in a PRISTINE context;
      worst leaf 23.2 s → 0.99 s). The old candidate list (caching reflected
      worlds/totality envs, world constants vs literals) measured as NOISE
      and is retired. Remaining residuals (stage-2, recorded in the note):
      08-equality's direct-success regression (3→18 s; bounded-direct-first
      hybrid, blocked on P1 — heartbeat caps bind only loosely); 16/12's
      ~17 s leaves (not proveDpFact; suspects: totWalk walking zip bodies,
      hasFVar fail-safe); per-attempt cap tuning (P1).
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

## Track A — the rewriting-replay driver (`ACL2Lean/Replay/Driver.lean`)

A recursive, fail-closed `replayClause`/`replayNode` over the real tree; grow by
tree complexity, each step driven by a real tree, with positive + negative
tests. The c3 goal (replay `my-len-my-app`, then `app-assoc`, end-to-end via
the driver) is DONE; the track now serves the G-steps above.

### Done (driver foundations)

- [x] **S1/S2** — fail-closed dummy; `equal-self` node → universal mirror fact; native
      `Nat` bridge. Axiom-clean.
- [x] **S3** — congruence + with-lemma rewrite (`cdr-cons`) via the PATH-DIRECTED
      congruence emitter (`:PATH` emitted from ACL2, threaded, navigated —
      `findPath`/`occursIn` retired); multi-node literal chaining.
- [x] **definition-unfold (basic)** — 1-arg, direct body (`re_unfold1_conv`,
      ∀-env body convergence). FIRST REAL TREE replayed: `sq-rewrites` from
      `09-defn-unfold.proof-log`.
- [x] **convergence (easy shapes)** — var/quote/`car`/`cdr`/`consp`/`cons`/
      `binary-+`/`binary-*` in `proveConv`; value-characterized variants
      (`re_val_*`, incl. value-level `if` as `cond`) in the DP lift.
- [x] **Eliminate hand-marshalling (P0–P4)** — `DefMap` repr; driver derives
      no-shadow/`DefInfo` by kernel `decide`; `Development.toWorld` +
      `reflectWorld` derive everything from the log; coverage harness
      (`just driver-coverage`, in `just ci`) sweeps the corpus per theorem.
- [x] **Decision-procedure discharge leaves (c1+c2, ratified carve-out)** —
      `Replay/DischargeLeaf.lean`: lift to Logic primitives, spine fold
      (`re_dp_if_split`), DP fact closed by fixed simp/split_ifs/omega; opaque
      user-fn subterms as quantified values with totality + emitted-TP
      hypotheses; unclosable facts become BOUND HYPOTHESES (conditional proofs,
      no `sorryAx`). ✓6 ◌13 ✗0 of 19; obligations explicit in the proof types.

### c3 — COMPOSITION (current focus; first end-to-end inductive proof)

Target: `my-len-my-app` (then `app-assoc`) replayed by the driver from the real
log, `#print axioms` clean. The pieces exist; c3 wires them:

- [x] **Induction scaffold (WF)** — LANDED (pending audit #38):
      `my_len_my_app_real_mirror` replays the real `simple.proof-log` end-to-end
      as the conditional generic mirror (`total:my-len/my-app/fix + tp:my-len`
      bound hypotheses; only USED hypotheses bound); axioms
      `[propext, Classical.choice, Quot.sound]`. Coverage (quantified env,
      `Meta.check`ed): REPLAYED 5/38 — + sq-rewrites ×2, len2-app,
      len2-app-helper. Includes `replayLiteralChain` (`:NOT-FLG` atom chains),
      rewrite-if branch-frame STRIP, comm-rune children chaining,
      `groundZeroDefs` (fix) in `toWorld`, uniform pinning in `replayClause`.
      (task #52; details in docs/plans/2026-06-09_c3-composition-plan.md)
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
- [x] **`mutual-recursion` `:DEFUN` emission (2026-06-09).** mutual-recursion
      reaches defuns-fn directly, bypassing defun-fn's emitter — a clique
      produced ZERO (:DEFUN …) events. Fixed at the source: shared
      emit-structured-defuns hooked after install-event-defuns (acl2 submodule
      2e797e9bfd); corpus re-captured. my-evenp-3-is-nil / my-oddp-3-is-t now
      REPLAY UNCONDITIONALLY (16/37); the clique's admission proof now attaches
      to its defun's `termination` field instead of orphaning as a
      pseudo-theorem (what #37 consumes). Follow-up: the coverage harness
      should also sweep `WorldEvent.defun.termination` trees for DP leaves
      (one ✓ leaf moved out of the theorem sweep).
- [x] **IFF-aware preprocess chain — RETIRED by G1 (2026-06-10, 3ae8352).**
      The `*geneqv-iff*` chain replays via `EvRel SIff` + the congruence table
      + backward truth transport (`truthy_of_evrel_siff`) + the interim
      boolean-head strengthening; app-nil / rev-rev / true-listp-app now stop
      at the G5 induction frontier instead.
- [ ] **Gate the clausify-checkpoint emission on preprocess HIT** (today a
      'miss pass's events flush into the NEXT step's :REWRITES — handled by
      validated no-op drops in the driver, but gating at the source is cleaner).
- [ ] **Mirror-statement boolean-validity check.** The mirror form
      `eval formula = some t` is STRONGER than ACL2's `formula ≠ nil` — equal
      only for boolean-valued formulas (all of the current corpus). The
      statement builder should hard-fail on a formula not provably
      boolean-valued (or the mirror moves to a `≠ nil` form) — surfaced by the
      clausify-bridge design, where clausify-input1's invariant is iff.
- [x] **Env made kernel-reducible (Layer-1 trusted-core change, 2026-06-09).**
      `Env` was `Std.HashMap Symbol SExpr`; string hashing is kernel-opaque, so
      `evalOpt` of defined-fn calls could not be re-checked by reduction.
      Replaced with a minimal assoc list (`Syntax.lean`) — smaller trusted core,
      same observable insert/get? semantics, all kernel proofs rebuilt,
      differential test vs real ACL2 re-run as the semantic guard.
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

### Later (Track A backlog)

- [ ] **convergence analyzer (G1), general** — defined-fn totality threading
      opaque witnesses for recursive calls (subsumes the c2 `hConv` hypotheses).
- [ ] **`.boundary` path frames** — child-node congruence inside an unfold /
      rule-RHS (currently hard-fail; aligns with tree child-nesting).
- [ ] Replace the hardcoded frontend with **`gen-world`** output; drop hand-built
      test trees once the real tree replays.
- [ ] The **`acl2_replay` tactic** frontend (read the Lean goal, emit the proof,
      close it).
- [ ] **`Expr` blowup** — `let`-bind shared convergence subproofs.
- [ ] Retire/generalize the over-specialized `re_unfold*_var`.
- [ ] **DP-leaf debt:** 11/\*1/4+\*1/5' tactic residue (simp leaves a non-omega
      goal in one case — likely closable); ground-zero type facts (`len`) —
      emission decision; 03/linear-chain rationals → lean-smt (task #50).

## ACL2 submodule (instrumentation hygiene)

- [x] **Comprehensive `TRACE-LOG` tag review** — DONE 2026-06-09: full systematic
      survey (all 81 hunks vs upstream, with context), ratified namespaced
      convention (`emit/` round-trips `:origin`; `suppress/`; `infra/`), enforced
      by `just check-acl2-tags` (bidirectional). Convention documented in
      CLAUDE.md + `docs/notes/2026-06-09_acl2-tagging-survey.md`; reviewed by two
      decorrelated agents (conformance + semantic accuracy).
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

## Track B — type-set / decision-procedure facts (richer emission)

Status change 2026-06-09: every verdict-only decision-procedure closure now emits
an explicit **discharge node** (`preprocess/tau*`, `preprocess/type-set-fc`, …),
and the driver replays these leaves under the ratified carve-out (✓6 ◌13 of 19).
What remains is the RICHER fact emission for the ◌-assumed leaves — each missing
obligation is stated precisely in its conditional proof's type:

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

## Other pipeline / cross-cutting work

- [ ] **Carve-out drift test (MDD 2026-08-02, standing revisit).**
      The widened DP-leaf premise/verdict machinery is ratified FOR NOW
      under this test: if we find ourselves writing CUSTOM PROOFS OR
      CHECKERS PER CASE, we are no longer mirroring ACL2 — we are
      building custom search to replace it. Revisit at each arc review:
      count the per-case (non-general) discharge code added since the
      last review; a growing count fails the test.

- [x] **Build-gate parallelization — INCREMENT 1 DONE (sprint,
      2026-08-02, merged 9b1403d):** NativeMirrors split into 12
      per-book modules + facade (behavior-preserving: decl set,
      body-line multiset, axiom lines, gates, golden all verified
      identical). Full mirror re-elaboration 15m31s → 9m13s (parallel,
      32 cores); SINGLE-BOOK edit 15m31s → 41s. Remaining ceiling:
      Qsort.lean (540s critical path — sub-split when it hurts).
      INCREMENT 2 (the sweep split) DEFERRED to the close-out arc by
      design: sweep parallelism requires replacing linear corpus-order
      accumulation with the real include graph = the queued
      include-book provenance gate, and it moves golden rows —
      deliberate row-by-row review in-arc. Original item follows.
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
- [ ] **Rebase the `acl2/` fork on upstream (2026-06-12).** The submodule's
      `acl2-lean-output` branch is based on an aging upstream `master`; rebase
      (or merge upstream forward) at some point. The TRACE-LOG tagging
      convention exists for exactly this — `grep -rn "TRACE-LOG\[" acl2/*.lisp`
      enumerates every inserted region, and `just check-acl2-tags` validates
      the result. After rebasing: rebuild the image, recapture the corpus
      (capture is deterministic — byte-diff the logs to detect upstream
      behavior drift), and rerun the differential harness + `just ci`.
- [ ] **Native-theorem bridge — generalize.** Currently hand-built for `my-len-my-app`
      (List.length_append) and `app-assoc` (List.append_assoc). Systematize the
      type-morphism + simulation recipe (`docs/comms/2026-03-22_acl2-lean-bridge.md`),
      ideally driver-assisted.
- [ ] **`evalOpt` faithfulness to ACL2** — expand the differential harness
      (`scripts/diff_eval.sh`, 51/51) corpus; it is one of the two trust-note
      circle-breakers.
- [ ] **Mirror-statement builder / `gen-world`** (`WorldGen.lean`) — completeness &
      correctness for new theorems the driver targets.
- [ ] **Reconstruction coverage** — work through `docs/notes/2026-06-07_silent-drop-inventory.md`
      and the recon-tests findings; ensure no silent drops.

### Induction-generality arc follow-ups (pre-merge audit 2026-07-18 —
### full record in docs/notes/2026-07-18_induction-generality-closeout.md)

- [x] **Decrease discharge via the #37 admission-decrease prover — DONE
      (2026-07-18, branch mdd/37-decrease-prover, audited):** general
      `dischargeDecrease` (emitted-clause match + ruler verification +
      Count walk) replaced the J2/J4 fragments at all three call sites;
      EVENS/ODDS sim-lemma registry (CountSim.lean, Route A — models
      proved, trusted core untouched). HONEST OUTCOME: all 7 decrease rows
      discharge their decreases and moved to downstream frontiers (none
      REPLAYED yet — the 4→5→3 follow-up arc targets that); the one
      coverage flip is EVENLEN-BOOLEANP conditional→unconditional.
      Follow-ups: (a) S4 registry path gets its end-to-end kernel-checked
      consumer when an msort row replays (4→5→3 arc); (b) the J4 SWAP
      branch has NO corpus consumer (LEN-INTERLEAVE fails upstream at the
      clausify bridge) — revalidate when that frontier falls; (c) NUMERATOR
      trusted-core growth via the H3 pin-first process (2 rows).
- [x] **msort-frontiers arc (4→5→3 + knock-outs) — DONE (2026-07-19,
      branch mdd/msort-frontiers, audited):** chain-to-child preprocess
      route; generalize type-restriction literals + gz snapshot TP
      emission (EVENS/ODDS had no emitted TP; one DP leaf flipped
      assumed→discharged); :PATH at preprocess sites (infra/abbrev-path);
      clause-scoped litFacts (the real item-3 fix). All 7 msort rows'
      original walls gone; 3 rows now share ONE wall — the clausify
      recompute's un-mirrored EXPAND-AND-OR normalization ((ENDP x) vs
      (NOT (CONSP x))) — the next-arc candidate (likely unlocks beyond
      msort: the annotation appears corpus-wide). Audit: zero soundness
      defects; the generalize HEAD-DROP construction has no kernel-checked
      consumer yet (fail-closed infra; the expand-and-or arc is the
      unlock). Close-out: docs/notes/2026-07-19_msort-frontiers-closeout.md.
- [ ] **Positive type-set-verdict marker (the proper J6b).** The
      `typeSetDerived` tag is classification by ELIMINATION (no positive
      marker in the log — a linker bug and a genuine type-set verdict are
      indistinguishable; fails closed at replay). Emit a marker from the
      fork, consume it in the linker, and build the value-level discharge
      recipe.
- [ ] **Capture-harness max-line-length assertion** (audit finding 3):
      the fmt margin widen is a threshold, not a guarantee — the sorting
      corpus actively wraps at ~10k cols (qsort max line 9999) and the
      hyphen-split hazard is live. Assert headroom at capture; consider
      `write-for-read`.
- [ ] **STRINGP DP-lift primitive**: unblocks all 16 qsort +
      sorts-equivalent rows (verified genuine — TO-BE-FOUND's disjunctive
      TP corollary, not a recon artifact).
- [ ] Smaller: dotted STEP-rune corpus witness (constructed sample);
      covering-clause guard↔ruling-test correspondence; differential check
      of gz-termination-clauses recomputation vs original admissions;
      pool-shaped (clause-list) induction motive.

### Iteration-loop performance (MDD 2026-07-17 — "the current loop is
### killing our productivity"; consider soon)

- [x] **Focused runs — DONE (WP1, 2026-07-18 branch mdd/perf-ooda):**
      `just replay <log> [THM]` (`acl2lean-replay` runtime CLI, shared
      `Runner.runBook` harness — rows comparable to the golden); lazy
      per-book totalEnv (WP1b). Per-ACL2-proof loop: was 4-6 min, now ~4 s
      end-to-end (capture ~1 s + env import 2.4 s + replay ~1 s).
- [x] **Driver modular refactor — DONE (WP2 Stages 0-3a, 2026-07-17/18,
      branch mdd/perf-ooda):** Driver.lean (6,868-line monolith, 3 mutuals)
      → 16 modules; both recursion knots untied behind `NodeRec`/`ClauseRec`
      (thin 2-member tie mutuals, public signatures unchanged); one
      waterfall processor per file (`Driver/Waterfall/Induction.lean` = the
      #37 rework home; siblings untouched by an edit). Every stage golden
      byte-identical + ci + diff-test 389/0. Measured warm loops: processor
      edit → fresh exe ~30-35 s (vs ~55-65 s monolith); re-elab tail now
      dominates. Node-side 3b extraction recommended AGAINST (no loop win)
      — see docs/plans/2026-07-18_driver-modular-refactor.md, MDD call.
      Follow-up levers (unscheduled): shorten Core→Harness→root tail;
      interpreter-mode replay entry (skip codegen+link ~8-11 s); DAG-flatten
      Discharge/Totality off the Preprocess path (compiler-verified).
- [ ] **Design-level perf round #2** (sequel to #65, ci 25 min → 190 s).
      New corpus scale changed the profile: 206-defun worlds make
      per-theorem telescope construction + world reflection the likely
      hotspot (rebuilt per theorem per book — cacheable per book?); DP-leaf
      discharge and the 8192-depth lifts on big clause terms are the other
      suspects. Profile FIRST (the heartbeat-hacking sweep above shares
      this: know WHAT is deep/slow), then optimize; keep the #65 two-tier
      budget policy (no corpus-tuned gates).

### Audit / correctness debt (revisit — do not drop)

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
- [x] **c3 end-to-end audit (2026-06-09, task #38) — DONE.** 3 decorrelated
      adversarial reviewers (schematic fidelity / statement / lemma soundness) +
      per-finding independent verification. Statement + lemma dimensions: CLEAN
      (statement = the genuine defthm mirror; hypotheses honest and non-vacuous;
      `fix` matches axioms.lisp; axioms `[propext, Classical.choice, Quot.sound]`,
      no cheats on the path). Fidelity: 1 critical refuted (relativizeFrames does
      NOT over-strip — paths are absolute, verified against the raw log); the
      solidify litFact "incoherence" finding refuted by spot-check (the spine
      stores the BRIDGED proof at the post-rewrite value, Driver.lean
      `replayClauseSpine`; any mismatch is a kernel type error). Actionable
      residue landed: strip-scope docstring, strip-mismatch negative test, and a
      type-PINNING `example` asserting the mirror's exact conditional statement
      in Tests/DriverTests.lean.
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
- [x] **#24** — `fix` modeled as a defined function in the hand-proof world (ACL2 ground-zero
      body); base-case node3 unfolds it via `definition:fix`. (Other `definition:`-runed
      ground-zero fns: add as needed.)
- [x] **#29** — `my-len-my-app` base case *1/2 reworked to schematic per-rune replay (driver
      combinators: re_unfold{1,2}_var ; recognizer ; re_if_false/true ; unicity-of-0 + fix
      unfold ; equal-self) — no more compute-and-match. Found+fixed via the adversarial audit.

## Done (recent milestones, for context)

- **2026-06-09 (the measure/emission/discharge arc, merged to main):**
  - Measure emission: `(:INDUCTION …)` carries measure/rel/mp/controllers/per-case
    tests + IH substitutions, instantiated at the conjecture; dump renders it;
    validated on boundary recon-tests 10–16 (multi-IH, custom measure,
    multi-controller, swap/constructor IHs, nested induction, 3-way).
  - Failed-proof safety net: QED-less `:DEFTHM` hard-fails reconstruction; CLI
    exits non-zero; capture script keys on QED-per-DEFTHM.
  - Black-box-leaf emission gap CLOSED: preprocess eval chains emitted
    (cons-term folds, ev-fncall, if/equal-self, real abbreviation RHS) +
    explicit discharge nodes at all verdict-only decision-procedure sites;
    harness hard-fails item-less PROVED leaves; `just ci` gates it.
  - Decision-procedure-leaf carve-out ratified (CLAUDE.md); DP-lift replay
    (`Replay/DischargeLeaf.lean`): ✓6 ◌13-conditional ✗0 of 19, kernel-checked,
    no `sorryAx`; missing obligations explicit in proof types (MDD's
    conditional-proof design).
  - ACL2 tag convention ratified + enforced (`just check-acl2-tags`); 4-reviewer
    dump audit (found: 00-direct empty-capture bug → fixed + integrity gate).
- Faithful sorry-free hand proofs of `my-len-my-app` and `app-assoc` (schematic;
  no functionality facts), each lifted to an idiomatic native Lean theorem; ACL2
  pipeline untrusted for both.
- Differential testing of `evalOpt` vs real ACL2 (51/51).
- Driver S1+S2 + native Nat bridge (first real proof-tree replay).
- Driver S3 (first real rewrite rune): `(equal (cdr (cons a b)) b)` via a `cdr-cons`
  node + path-directed congruence (`equal arg1`) + equal-self — axiom-clean mirror.
- Driver 3a(i) convergence analyzer recurses into compound operands (`cons`).
- Driver 3a(ii) DEFINITION-UNFOLD node: `(defun pair (x) (cons x x))`,
  `(equal (pair x) (cons x x))` via `re_unfold1_conv` (body ∀-env convergence threaded
  to the bindArgs env) + carried `DefInfo` (def/closed/no-let) + equal-self. Axiom-clean.
- Adversarial audit (3 decorrelated reviewers): driver confirmed GENUINE replay — no
  hand-hacking, no answer-smuggling, axiom-clean, fail-closed.
- **FIRST REAL TREE replayed end-to-end**: `sq-rewrites` (`(equal (sq n) (* n n))`)
  parsed from the real `09-defn-unfold.proof-log` → driver → `sq_real_mirror`, axiom-clean
  (`binary-*` convergence + def-unfold + equal-self). The hard real tree `my-len-my-app`
  fail-closes cleanly at the `Goal` (push→induction) frontier.
- `capture-proof-log.sh` failure detection hardened.
- SExpr reader now supports dotted pairs (`(a . b)` → true `.cons`); fixes the `(. x)`
  artifact in `:subst` and `:path` frames (previously `.` was read as a symbol).
- Driver made heuristic-free: removed `proveBySimp` (default-simp); all side-conditions
  via kernel `decide` (`proveByDecide`); world non-shadowing facts now CARRIED in
  `ReplayConfig.noShadow` (established once, never re-derived).

---

_Conventions: `[ ]` open, `[x]` done. Task numbers (#NN) refer to the live task list.
Tracks A and B are independent; A needs no new instrumentation, B does._
