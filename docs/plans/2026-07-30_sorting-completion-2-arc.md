# Sorting-completion II — arc charter

**Status: RATIFIED (MDD conversation 2026-07-30 — "yes, that sounds great,
let's work that arc"). Branch `mdd/sorting-completion-2`, opened at main
a1c25c2 (post validator/lifter tranche 1).**

## Goal

Every SWEEP sorting row green + ORDEREDP-QSORT's `rule:ORDEREDP-APPEND`
condition discharged. Explicitly OUT of scope (the following arc, R6/R7
character — recon/statement-builder work): the bsort book's
clausify-region recon wall (p4-pinned), equisort's encapsulate
(BUG-019-refused, roadmap R6), functional instantiation (R7).

## The red inventory (from the golden at a1c25c2), classed by machinery

### Class A — the type-alist relief family (4 rows; FIRST — highest leverage)

- `ORDEREDP-APPEND` — rule LEXORDER-TRANSITIVE's marker-relieved hyp
  `(LEXORDER A3 (CAR A4))`, `:TA-RUNES ["LEXORDER"]`, no falsity fact in
  scope, no registered FC relief.
- `ORDEREDP-MEMB` — `type-alist: no spine falsity fact for E`.
- `ORDERED-PERMS` — needs `(PERM (CDR (CDR A)) (CDR (CDR A)))` truthy — a
  REFLEXIVITY fact on the type-alist (the equivalence-rule entry class).
- `TRUE-LISTP-MSORT` — `type-alist: no spine falsity fact for MT`.

Shared semantics (pinned by the perm-lane outside audit, F6):
`rewrite-clause-type-alist` = rewritten earlier literals + ORIGINAL later
literals + FORWARD-CHAINED conclusions (`select-forward-chained-concls…`,
acl2/simplify.lisp:5002). The later-literal half is covered by the
demand-hoist machinery (perm-lane inc-1); the FC-conclusion third is
unreachable by case-splitting — expected landing: EMITTED type-alist-entry
provenance (the fork already computes `:TA-RUNES`; emit the entry/its
derivation) + a bounded relief-registry extension (the LEXORDER-TOTAL
registry precedent, rule-of-three watched). Per the project rule: type
facts come from ACL2 — if insufficient, EMIT MORE, never re-derive.
Discharges ORDEREDP-QSORT's biggest kept condition as a side effect.

### Class D — HOW-MANY-QSORT (1 row; SECOND — self-contained named frontier)

`solidify: type-set-derived equivalence (EQUAL (CAR X) E) — not in the
clause context's equation closure; value-level type-set discharge not
implemented (J6)`.

### Class C — msort internals (3 rows; THIRD — three distinct record classes,
ground-truth read each before building)

- `ACL2-COUNT-EVENS-STRONG` — branch-substitution justifying literal
  `(not (equal (ACL2-COUNT (CDR X)) '0))` neither in clause nor segment.
- `ACL2-COUNT-EVENS-WEAK` — ran out of items with no closer at *1/2.2'
  (a silent close the taut arm does not cover).
- `ORDEREDP-MSORT` — literal 9 chain reached 'NIL, recorded result
  `(NOT (CONSP (MERGE2 MT0 (CONS MT3 MT4))))` (chain divergence —
  possibly an emission gap; suspect any stage).

### Class B — the sorts-equivalent walls (3 rows; FOURTH — likely 2 causes)

- `MSORT-IS-ISORT` + `QSORT-IS-ISORT` — one shared message (emitted
  `:PATH` misnavigates to `(HOW-MANY E (ISORT X))`; frames
  `[(1 . IF), (1 . EQUAL)]` land on X) — suspect one emission/alignment
  bug.
- `BSORT-IS-ISORT` — node lhs is a DIFFERENT theorem's formula
  (`(IMPLIES (TRUE-LISTP X) (TRUE-LISTP (ISORT X)))`) — the `:use`-hint
  class (apply-top-hints; `LEN2-APP-VIA-USE` recon-05 is the same
  family). A real feature gap, not a bug.

## Discipline

The standing rules apply: drive off the real artifact (dump the tree
before reasoning); emitted evidence over Lean-side reconstruction;
hard-fail at frontiers; each class lands with decorrelated validation
where it generalizes (pattern books through real ACL2 + capture);
byte-identical sweep outside the intended flips; small verifiable
increments, commit at checkpoints; pre-merge audit at the merge point.

Adjacent debt that may fold in if a class touches it (else stays queued):
the linear-in-simplify emission gap (p6's tripwire), the perm-lane
audit-disclosed items (taut-close commuted-IFF/double-neg/dedup arms,
branch-substitution condition/remove-flg/lit-position emission, the
:RULES cr-rune per-step emission).

## Class A diagnosis (inc-1, 2026-07-30 — COMPLETE; one fix landed)

- **FIXED (25e436a): the checked-hoist asymmetry.** ORDEREDP-APPEND's
  LEXORDER-TRANSITIVE relief was stranded by an env-crossed segFact
  (leaked from the parent elim walk, typed in the nested bindArgsOver
  env) satisfying the hoist's UNCHECKED in-scope test while the
  consumer's CHECKED lookup refused it. The hoist's .term/.equivClass
  arms now use litFactByTermChecked?. The row ADVANCED to a new class:
- **ORDEREDP-APPEND now blocks on the NESTED if-finish/combined strip
  composition** — the ALL-REL iff-unfold child sits under TWO nested
  combined nodes; `relativizeAndStrip` documents this composition as
  not-handled (branch frame interleaved between residual boundary
  frames) and fails closed. The build: compose strips across nested
  combined children (the rung-1 chainPrefix machinery's second story).
- **ORDEREDP-MEMB / TRUE-LISTP-MSORT**: solidify/type-alist nodes
  `E ⇒ 'NIL` / `MT ⇒ 'NIL` — bare-VARIABLE entries whose source is not
  in the walk's fact lists and not a hoistable later literal at the
  failing site. Source unidentifiable from the record:
- **ORDERED-PERMS**: `(PERM (CDR (CDR A)) (CDR (CDR A))) ⇒ 'T` — perm
  REFLEXIVITY on the type-alist; the record's :RUNES is the CUMULATIVE
  ttree ((:DEFINITION RM) (:DEFINITION MEMB) (:FAKE-RUNE-FOR-TYPE-SET))
  — no entry provenance. CONFIRMS the expected landing: the fork must
  EMIT the type-alist ENTRY's provenance (which literal/mechanism
  created the matched entry) at the solidify/type-alist and
  relieve-hyp/(free-)type-alist push sites. Instrumentation increment:
  fork emission → recapture-all → Lean consumption keyed on the emitted
  source (clause literal index / equivalence-rune reflexivity / FC
  conclusion), replacing the current search-the-fact-lists recipes.

## Class A inc-2 progress (2026-07-30)

- **LANDED: `deriveNilFact`** — the bounded value-level type-set closure
  (direct facts + equation transport + car/cdr completion defaults, all
  type-checked, depth 3) + the `logic_car/cdr_of_consp_nil` kernel
  lemmas; the type-alist nil-verdict arm consumes it.
- **ORDEREDP-MEMB advanced**: the `E ⇒ 'NIL` sites clear; new frontier
  `if-finish/combined: children chains reached (IF (EQUAL 'NIL (CAR A))
  'T (MEMB 'NIL (CDR A))), node rhs (IF (CAR A) (MEMB 'NIL (CDR A)) 'T)`
  — ACL2's (if (equal nil x) t y) → (if x y t) NORMALIZATION at the
  combined-children joint (the bridgeEqualNilNorm family; add the arm
  at that joint).
- **TRUE-LISTP-MSORT diagnosed to the fact list**: `MT ⇒ 'NIL` with
  in-scope (CONSP MT) FALSE + (NOT (TRUE-LISTP MT)) FALSE (truthy
  true-listp) — the missing closure step: trueListp v = t ∧ consp v =
  nil → v = nil (kernel lemma + a deriveNilFact rule consuming a
  TRUTHY (NOT …)-false fact).
- ORDERED-PERMS' (PERM x x) ⇒ 'T truthy arm untouched (the
  equivalence-reflexivity consumption — rung-2 cong-style machinery).

## Class A inc-3 design (checkpointed 2026-07-30; next to build)

**ORDEREDP-MEMB's remaining joint** — the equal-nil test swap:
children chains reach `(IF (EQUAL 'NIL c) a b)` where the recorded rhs is
`(IF c b a)` (ACL2 normalizes an equal-nil test by strip+swap, unrecorded).
Build:
1. Kernel lemma `re_if_equal_nil_test_swap (w env c a b) (hNoEqual)` :
   `∃N ∀f≥N, eval (IF (EQUAL 'NIL c) a b) = eval (IF c b a)` — template =
   `re_if_neg_test_swap` (EvalLemmas:5042; by_cases on c's convergence,
   per-value split, none-case symmetric) with the inner term an EQUAL
   builtin call (needs the EQUAL-unshadowed premise like `re_equal_self`;
   evaluate `(EQUAL 'NIL c)` to `Logic.equal nil vc` at fuel; case on
   vc = nil / ≠ nil via Logic.equal's two-valuedness).
   Also the symmetric `(EQUAL c 'NIL)` orientation.
2. Extend `findSwapPos`'s `fire?` (NodeCore:3477-ish) with the equal-nil
   test shapes, tagging the variant; `normalizeSwapsToward` dispatches to
   `liftNegTestSwap` or a new `liftEqualNilTestSwap` (same lift mechanics,
   the new lemma + hNoEqual/pins).

**ORDERED-PERMS' truthy arm** — perm reflexivity: consume the
:EQUIVALENCE rule's reflexivity as the type-alist truthy source — the
rung-2 `cong:`-style machinery: offer the equivalence theorem's
whole-formula replayed statement, instantiate its `(perm x x)` conjunct
at the entry's term via the premise-free substN bridge
(`instantiateEvTrueHypAt`), decode the AND-conjunct truthy (the decode
kit), yielding v(PERM u u) ≠ nil → = t via the two-valued pin (the
truthy arm's existing TP route may need the equivalence-fn's emitted TP
instead).

**ORDEREDP-APPEND** — the nested if-finish/combined strip composition
(the biggest remaining Class-A piece; relativizeAndStrip's documented
not-handled case). Then Class D (HOW-MANY-QSORT J6 — note deriveNilFact
is adjacent machinery: the J6 solidify wants the same equation-closure
at the solidify site), Class C, Class B per the charter.

## Class A inc-3 progress (2026-07-30)

- **LANDED: the equal-nil test swap** — `re_if_equal_nil_test_swap`
  (EvalLemmas, the re_if_neg_test_swap template with the EQUAL-builtin
  inner + unshadow premise) + the tagged `findSwapPos` variant +
  `liftEqualNilTestSwap`; `normalizeSwapsToward` dispatches on the tag.
- **ORDEREDP-MEMB advanced again**: now at a DP-LEAF discharge frontier —
  `proveDpFact: omega could not prove the goal (no usable constraints)`
  — the previously "◌ assumed" fc-contradiction leaf (*1/1.2) is now on
  the required path and its obligation is LEXORDER-flavored (not linear
  arithmetic; omega cannot). Next: inspect the leaf's emitted clause +
  type facts; either the lexorder facts aren't reaching the obligation
  or the leaf needs a lexorder-aware discharge (the ratified carve-out
  allows lean-smt where needed; check what ACL2's fc actually derived).

## ORDEREDP-MEMB's DP leaf (inc-4 target; goal captured 2026-07-30)

The *1/1.2 fc-contradiction leaf's lifted obligation (from the replay
error, full text via
`acl2lean-replay …ordered-perms… ORDEREDP-MEMB | grep proveDpFact`):
hyps over `cons car✝ cdr✝` — ¬consp(x)=nil-decode, equal(car(cdr x),
car x)=nil, consp(cdr x)=nil, not(lexorder nil (car x))=nil — PLUS the
discharge machinery's synthesized dpOrd_anti_0/dpOrd_tot_0/dpOrd_tot'_0
lexorder facts; GOAL `Logic.car (cons …) = SExpr.t` under a ∀ dpv0
clause lift. The closer is simp_all<;>omega — lexorder-flavored, omega
cannot. Investigate: (a) is the goal correctly lifted (the = t goal
looks odd — check the emitted clause and whether the two-valued decode
should apply); (b) whether the just-added completion lemmas
(logic_car_of_consp_nil) close the car(cdr)=nil step and the
contradiction is nil ≠ car x vs …; (c) whether the leaf needs a
lexorder-aware closer (the carve-out allows it — check what ACL2's fc
derived, drive off the emitted record).

## Inc-4 FINDING (2026-07-30): the DP lift over-strengthens bare-term literals

Ground truth (the emitted *1/1.2 record): INPUTCLAUSE
`((NOT (CONSP A)) (EQUAL E (CAR A)) (NOT (EQUAL E (CAR (CDR A))))
(CONSP (CDR A)) (NOT (LEXORDER 'NIL (CAR A))) (CAR A))` — the final
literal is the BARE TERM `(CAR A)`, whose truth in a disjunction is
`v ≠ nil`. The dp-fact lift states the goal as `Logic.car dpv0 =
SExpr.t` — TOO STRONG (car a is any non-nil value under the hyps; the
correct ≠-nil goal IS provable: E-elimination gives car(cdr) ≠ car,
consp(cdr)=nil + the completion lemma give car(cdr)=nil, hence
car ≠ nil). Fail-closed (unprovable goal), not unsound — but it blocks
the leaf. FIX: the lift's final-literal convention for a bare
(non-recognizer, non-EQUAL) literal must be truthiness (≠ nil), not
exact-t — find the convention in the discharge clause-lift (dpLiftF /
proveDpFact's obligation construction) and correct it; then the leaf
closes with logic_car_of_consp_nil + the equal-nil decode (omega not
needed — check whether the closer needs a small extension for the
final ≠-nil step). Note the E-ELIMINATION already performed by the
lift is correct (literal-3 equation + literal-2 rewrite).

## ORDERED-PERMS root cause (2026-07-30): abandoned-rewrite log orphan (fork fix b236e17c28)

The `TRUE-LISTP/CDR closure` frontier chased through THREE wrong hypotheses
before ground truth settled it. Record for the audit trail:

1. **Auto-TP emission (fork 7790095ce9)** — patched the TP emitter to
   reconstruct auto corollaries via `convert-type-prescription-to-term`.
   Correct generalization of the emitter, but it did NOT fire for RM:
   probe `(getpropc 'myrm 'type-prescriptions …)` → the property is
   genuinely EMPTY. RM returns `(cdr x)`-shaped results — its ts is
   unknown, so ACL2 stores NO type prescription at all. Patch retained
   (it is right for functions that do get placeholder-corollary TPs).
2. **Evidence machinery (replay side, this branch)** — the closure arm
   gained a cons-fact route + equation-transport route, and a `tlpCons`
   PATTERN demand (`ContextDemand.tlpCons` + hoist arm): ACL2's
   type-set justification here is the LATER literal
   `(NOT (TRUE-LISTP (CONS a w)))` whose falsity gives
   `trueListp (cons a w) ≡ trueListp w` definitionally
   (`logic_trueListp_ne_nil_t`). This machinery WORKS (the arm
   discharged) and stays — it is the honest replay for surviving
   recognizer/true nodes of this shape.
3. **Ground truth (the raw log)** — with the arm discharged, the chain
   computes literal 1 ⇒ 'NIL but `END-LITERAL :RESULT` records the
   literal UNCHANGED. `rewrite-atm` (simplify.lisp): the atom rewrote
   to *t* by type reasoning alone, and the
   `try-type-set-and-clause` heuristic ("don't let type-set remove
   facts from the goal") ABANDONED the reduction, keeping the atom —
   while the fork left the speculative derivation in the log. Same
   speculative-rollback class as the rejected lambda/fncall
   expansions. Fork fix b236e17c28: checkpoint the log tail before the
   speculative `(rewrite atm …)`, roll back when the type-reasoning
   reduction is abandoned (`tval == atm` at the non-implies
   try-type-set-and-clause site). The IMPLIES-expansion site is left
   untouched (returns the expansion — progress deliberately kept; if a
   book hits a chain mismatch there, extend then, driven off that
   record).

Next after rebuild: `just recapture-all` → provenance → full sweep →
re-test ORDERED-PERMS (literal 1 should now be a 0-step unchanged
literal; the case-branch walk proceeds to the later literals).

## ORDERED-PERMS GREEN (2026-07-31) — Class A at 3/4 (ORDEREDP-APPEND remains)

After the fork rollback fix landed (b236e17c28) and the corpus was
recaptured, the row advanced through ELEVEN further frontiers, each driven
off the real record:

1. **tlpCons pattern demand + cons-fact evidence** — the recognizer's
   type-set justification is a later `(NOT (TRUE-LISTP (CONS a w)))`
   literal; `ContextDemand.tlpCons` + the closure arm's cons-fact route
   (`logic_trueListp_ne_nil_t`).
2. **type-alist nil-closure ingredient demand** — a nil-verdict on `u`
   also demands `(NOT (TRUE-LISTP u))` (later literal 9 justified
   `B ⇒ 'NIL` with the branch's `(CONSP B)`-false segment).
3. **rewrite-equal cons-decomposition** (`replayRewritesWith`): ACL2's
   scratch components (`(car s1)`/`(car s2)` at gstack bkptr 1/2 — paths
   that are NOT literal subterms), recorded or SILENT component decisions,
   both polarities: refutation (`logic_equal_nil_of_{car,cdr}_components`)
   and the positive cons-extensionality
   (`logic_equal_t_of_components` + `conspEvidence?`).
4. **S4 lemma arm, first consumer** — the census's ORDERED-PERMS
   EQUAL-CONS clausify-expand row now demands it (per the S4 plan's own
   "as the census demands"): `dpLiftF_equal_cons_expand` (+`dpLiftF_prim2`,
   `equal_cons_decomp`) in ClausifyBridge; `runCheckedExpand` validates the
   recorded target verbatim against the registry decomposition form.
5. **elim restriction-strip transport direction** — `evtrue_of_fuel_eq`
   maps EvTrue of its RHS; the strip's false-branch needed `symm hIf`
   (latent since inc-3; first exercised now).
6. **ASSUMED:dp-fact condition threading** — the documented TODO, now
   demanded: `dpFactStmtOfClause` (shared obligation builder),
   `ReplayCtx.dpFactHyps`, harness offers per discharge leaf
   (`theoremDischargeLeaves` moved to Driver/Discharge as the single
   source), `replayDischargeNode` prove-first-then-hypothesis fallback.
   Provable leaves stay unconditional (used-filter).
7. **bare-variable branch-substitution** — remove-trivial-equivalences'
   variable-literal case with the variable a CLAUSE literal (`A2` positive,
   `A2 ⇒ 'NIL`): byCases + substitute + 'NIL-frame drop.
8. **equal-nil normalization at DEPTH** — `bridgeEqualNilNormDeep`
   (unique-difference descent) wired into the if-finish/combined joint
   alongside the swap normalizations.
9. **record-1 elim guard child** — the elim'd var's `(not (consp v))`
   literal can be ABSENT from record 1's clause too (B guarded only through
   TRUE-LISTP); the guard-child route generalized, recompute loop pushes
   record-1 guard clauses.
10. **stale-ctx in the nil-literal drop loop** — `mkConstTestCollapse` got
    ctx1 (pre-substitution pins) instead of ctx2; (RM A1 'NIL) unpinned.
    Same class as audit F8 / the checked-hoist fix.
11. **the CONSP closure kit** — `deriveConspT` (the CONSP twin of
    deriveNilFact): syntactic-cons value, `conspEvidence?` (+ new
    truthy-(CDR t) route `logic_consp_of_cdr_ne_nil`), IF-branch split
    (`logic_consp_if_branches`), (CDR u)-of-proper-list
    (`logic_consp_of_trueListp_ne_nil`), and the general
    truthy+proper-list route (`logic_ne_nil_of_if_nil_t_nil` decode);
    demands for all (CDR u) subterm ingredients. Plus the ADJACENT
    duplicate-literal collapse after in-clause equality substitution
    (`re_if_dup_adjacent` — Subgoal 2's B ⇒ A dedup).

Final row: REPLAYED ✓ cond[rule:CONS-CAR-CDR, rule:ORDEREDP-MEMB,
ASSUMED:dp-fact ×4] — the four tau/fc verdict leaves whose ∀-lift is
stronger than the clause instance (PERM/ORDEREDP semantic content) are
HONEST conditions in the statement, exactly the standalone probes' ◌ rows.
AUDIT FLAGS for the pre-merge audit: the dp-fact hypothesis offers
(soundness rests on dpFactStmtOfClause = replay-time obligation,
isDefEq-checked), the rewrite-equal decomposition's silent-refutation
route, and the S4 lemma-arm target validation.

## Sweep checkpoint (2026-07-31): 69/79 — ORDEREDP-MSORT green as a BONUS

Full sweep after the ORDERED-PERMS increment: **69/79 (30 unconditional +
39 conditional); DP leaves ✓38 ◌5 ✗0 of 43**. Two flips, zero regressions
(all other rows byte-identical):
- ORDERED-PERMS → REPLAYED ✓ (the inc-5 arc above);
- ORDEREDP-MSORT → REPLAYED ✓ cond[total:MERGE2, total:MSORT, tp:EVENS] —
  its old wall ("literal 9 chain reached 'NIL, recorded result
  (NOT (CONSP (MERGE2 …)))") was EXACTLY the rewrite-atm
  abandoned-reduction log-orphan class; the fork rollback fix cured it
  with no row-specific work. One Class C row down for free.

Remaining ARC-scoPED reds (4): ORDEREDP-APPEND (Class A —
"pathStepsFromFrames: navigated to 'GTE, expected redex
(ALL-REL 'LTE A E)"), HOW-MANY-QSORT (Class D — J6 solidify),
MSORT-IS-ISORT + QSORT-IS-ISORT (Class B — the shared
"(HOW-MANY E (ISORT X)) :PATH does not navigate" preprocess class).
BSORT-IS-ISORT stays excluded (bsort recon wall, next arc). The other
FAIL rows (CLASSIFY-POS, LEN2-APP-VIA-USE, CD2-BOUND,
ACL2-COUNT-EVENS-*) are pattern-book rows outside this arc's charter.

## Generality review (2026-07-31, prompted by MDD mid-arc guidance)

Honest classification of the inc-5 machinery, principled vs epicyclic —
"epicycle" = per-shape pattern matching where ACL2 itself runs ONE general
procedure:

PRINCIPLED (mirrors an identifiable ACL2 mechanism):
- The rewrite-equal cons-decomposition interpreter — mirrors
  rewrite-equal's own code structure (rewrite-args on the synthesized
  car/cdr components, recursive decision, cars-then-cdrs). Narrowness to
  fix when observed: silent refutation only tried at the CAR phase;
  scratch detection requires the EQUAL at the literal root.
- The S4 lemma arm — per-rule registry facts are the RATIFIED S4 Route A;
  EQUAL-CONS validated verbatim. bsort's CONS-EQUAL (flipped orientation)
  is the known next entry.
- ASSUMED:dp-fact threading — the standalone assumeFact route's ambient
  analog, shape-free.
- The fork rewrite-atm rollback — emission-side, general (proved by
  ORDEREDP-MSORT going green for free).

EPICYCLIC (per-shape instances of ACL2's ONE type-set procedure) — all
of these are hand-derived rays of `type-set-rec` + the type-alist:
- deriveNilFact's rule list (tlp∧¬consp→nil, car/cdr-of-non-cons,
  equation transport);
- deriveConspT's route list (syntactic cons, truthy-(CDR t), IF-branch
  split, (CDR u)-of-proper-list, truthy+proper-list, the (IF w 'NIL 'T)
  decode);
- the recognizer closure arms (TRUE-LISTP/CDR direct/cons-fact/equation
  routes; the CONSP arm);
- the tlpCons/ingredient DEMAND generation (per-shape guesses at which
  later literals type-set consulted).
The GENERAL rule they all approximate: a bounded VALUE-LEVEL TYPE-SET
WALKER — compute ts(term) under the in-scope facts exactly as
type-set-rec does (per-primitive ts transfer + type-alist lookup +
assume-true-false entries), with one soundness statement per primitive
transfer, as a fragment-local judgment (L1). The arc charter's Class A
"expected landing = emitted entry provenance + bounded relief registry"
pointed the same way; inc-2..5 built shape routes instead because each
row demanded one ray at a time. CONSOLIDATION CANDIDATE (end-of-arc or
next arc, MDD's call at the merge point): fold the closure kits into the
walker; the per-shape kernel lemmas become the walker's transfer lemmas
(they are the right primitives — none is wasted); the demand generation
becomes "the type-set ingredients of the verdict" computed by the same
walker run in discovery mode.
- Adjacent-ONLY duplicate collapse: ACL2's add-literal dedups against
  the WHOLE clause (member-term). General form: drop a literal equal to
  ANY earlier literal (byCases: the earlier occurrence closes / the
  frame drops); adjacent-only is an artifact of the observed instance.

## COMPLETION CRITERIA AMENDED (MDD directive, 2026-07-31)

The arc does NOT reach its merge point until, in addition to the original
goal (every sweep sorting row green):

1. **All epicycles eliminated.** The generality review's EPICYCLIC list
   above is a work list, not a note: the type-set closure kits
   (deriveNilFact / deriveConspT / the recognizer closure arms / the
   per-shape demand generation) must be consolidated into the bounded
   value-level TYPE-SET WALKER (fragment-local judgment per L1; the
   existing per-shape kernel lemmas become its transfer lemmas); the
   duplicate-literal collapse must dedup against the WHOLE clause (not
   adjacent-only); the rewrite-equal silent refutation must be
   CAR/CDR-symmetric. No merge with shape-dispatch epicycles in place.

2. **Mirrors for every reasonable example in the arc's target.** The
   arc's target = the sorting-corpus theorems. Every green sorting row
   needs a NATIVE MIRROR (Lean-idiomatic statement proved FROM its
   replayed statement) — `.pending` catalog entries do not satisfy the
   arc. Proposed reading of "reasonable" (for MDD review at the merge
   point, not silently assumed): all green sorting rows EXCEPT those
   whose mirrors require machinery the charter explicitly defers
   (equisort R6 / functional instantiation R7 / bsort-recon-walled rows),
   and helper lemmas whose statements are internal stepping stones with
   no natural native reading may share the MAIN theorem's mirror file
   rather than get one each — the enumeration to be listed explicitly
   before the merge proposal.

Sequencing (amended): remaining red rows (A: ORDEREDP-APPEND, D:
HOW-MANY-QSORT, B: MSORT-IS-ISORT/QSORT-IS-ISORT) FIRST — so the walker
consolidation sees every demanded ray — then epicycle elimination, then
the sorting mirrors (pulling the validator/lifter tranche-2 machinery
forward as needed). The pre-merge audit proposal comes only after all
three.

## ORDEREDP-APPEND diagnosis (2026-07-31) — the path-accounting CHOICE POINT

Ground truth (qsort.proof-log, Subgoal *1/2'-family literal 5): the
failing node is `definition:ALL-REL (ALL-REL 'LTE A E) => 'NIL`, a child
INSIDE nested if-finish/combined nodes. Its relativized frames
`[arg 1 IF, arg 2 IF, arg 1 ALL-REL]` navigate the RECORDED pre-collapse
structure `(IF (IF (ORDEREDP B) (IF (ALL-REL 'LTE A E) …) 'NIL) 'NIL 'T)`,
but the walk's RUNNING term has already taken a constant-test collapse the
chain recorded earlier, so the same frames land on `'GTE` (inside the
collapsed sibling). This is exactly `relativizeAndStrip`'s documented
not-handled case: a BRANCH frame interleaved between residual boundary
frames — the strip machinery only accounts collapses at specific positions
(chain root, if-finish's own steps).

TWO general fixes exist; picking one is an architecture call (per the
no-epicycles directive, patching this instance with a third ad-hoc strip
list is NOT on the table):

(a) **Lean-side, general frame accounting.** Replace the
    relativize/strip/boundary trio with ONE coordinate map maintained by
    the walk: every collapse/unfold the chain performs registers its
    gstack-frame effect, and path navigation consults the map. Retires
    three mechanisms into one; stays within the current emission format;
    the map's correctness burden lives in the replayer (each collapse
    class must register correctly — a new invariant to maintain as node
    classes grow).

(b) **Fork-side, re-architect :PATH emission.** Emit paths relative to
    the node's position in the CURRENT rewrite-entry term (what the
    replay actually walks) instead of raw gstack coordinates — the
    mapping-plan's ratified "prefer fork emission over Lean-side
    reconstruction" direction. Eliminates the whole
    relativize/strip/boundary family, but changes instrumentation
    semantics corpus-wide (full recapture; every existing path consumer
    revalidated; the fork must compute term-relative positions at emit
    time, which ACL2's rewrite does not track natively — feasibility
    needs a fork-side spike).

Status: PAUSED for MDD discussion at this choice point (goal ended per
the 2026-07-31 directive). Remaining arc work after the decision:
ORDEREDP-APPEND via the chosen mechanism, HOW-MANY-QSORT (D),
MSORT-IS-ISORT/QSORT-IS-ISORT (B), then epicycle elimination (the
type-set walker consolidation — same review found the closure kits'
general form), then the sorting mirrors per the amended criteria.
