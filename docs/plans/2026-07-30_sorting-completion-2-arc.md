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
