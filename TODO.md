# ACL2Lean — project TODO

Running backlog across all tracks. Keep this current: update when a milestone lands,
scope changes, or a new gap/frontier is found (see the injunction in `CLAUDE.md`).
This is a living index, not a spec — design detail lives in `docs/plans/` and
`docs/notes/`.

_Last updated: 2026-07-25._

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
> (1) emission at beta sites 2–4 (rewrite all-quoteps ~17337; preprocess
> expand-abbreviations induct.lisp 317–441 — the COMMON ground-actual
> case; :expand :lambdas ~12835); (2) the REAL `:EQUIV` on the beta step
> (geneqv-derived, not the hardcoded EQUAL — and assess the identical
> fncall/non-recursive defect); (3) replay support for what the new
> emissions surface; (4) RE-AUDIT (new emission). Increment 1 DONE: the
> audit's three probes promoted to pinned books
> (p2-beta-quoted-actuals / p2-beta-preprocess / p2-beta-equiv-iff,
> captured from the committed fork; the gap pins are nosig-style, so
> each fork fix fails its pin loudly and forces the map update).
> Fork-batch DESIGN needs MDD discussion before building — especially
> the geneqv→:EQUIV mapping (L2-adjacent).

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
`ACL2Lean/Imported/NativeMirrors.lean`, one section per corpus theorem: the
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
