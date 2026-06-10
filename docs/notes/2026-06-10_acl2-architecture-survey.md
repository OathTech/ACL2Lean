# ACL2 architecture survey — the full prover, from primary sources

_Created 2026-06-10. Input to `docs/plans/2026-06-10_generality-design.md`.
Method: 8 parallel read-only surveyors over the `acl2/` sources (waterfall,
rewriter, types+arithmetic, induction+structural, ttrees+forcing, events+world,
Milawa, plus an empirical reader), each producing a structured inventory
(role / internal justification / what is recorded today / emission leverage /
replay needs / cross-goal dependence / frequency), file:line-anchored. The two
highest-stakes claims (forcing provenance completeness; Milawa's
induction-as-primitive) were spot-checked verbatim against the sources. Full
structured output preserved in the session workflow log._

_Honest limitation: the planned **measured** mechanism-frequency sweep over
community books did not materialize — the frequency labels below are
source-comment-based judgments, not counts. A grep-based book sweep remains
follow-up work before the "core" cut is finalized._

## 1. The prover in one picture

```
defthm formula
  └─ waterfall (prove.lisp) — ledge state machine over CLAUSES, ids derived
     deterministically (forcing-round, pool-lst, case-lst, primes)
       apply-top-hints-clause   :use/:by/:cases/:or/:clause-processor
       preprocess-clause        built-in-clausep | expand-abbrevs + clausify-input + tau
       simplify-clause          rewrite-clause per literal (the rewriter)
       settled-down-clause      control-flow marker (no logic)
       eliminate-destructors    :elim rules — NEW VARIABLES
       fertilize-clause         equality substitution, may DISCARD the equality
       generalize-clause        term→fresh-var — NEW VARIABLES (induction only)
       eliminate-irrelevance    drops disconnected literals (induction only)
       push-clause              → pool → INDUCTION (induct.lisp) → subgoals re-enter
  └─ forcing rounds: 'assumption ttree entries → new top-level goals (round k+1)
```

Everything is justified through **ttrees** (tag-trees): an alist of
tag → values threaded through every step ('lemma runes, 'assumption records,
'pt parent-trees, processor-specific payloads). The ttree is the native
"proof object" — append-only provenance, not a derivation.

## 2. The recording spectrum (the design-driving classification)

Every mechanism falls into one of five classes by **what exists to replay**:

**(a) Per-step recorded.** The rewriter (with our instrumentation): rune, lhs,
rhs, subst, path, geneqv-relevant context per step. Elim/generalize/fertilize
ttrees carry full payloads upstream already ('elim-sequence with
(rune rhs lhs alist restricted-vars var-to-runes-alist), 'terms/'variables/
'var-to-runes-alist, 'bullet/'target/'equiv/'cross-fert-flg) —
other-processes.lisp:1265, 2325, 1944. These replay step-for-step.

**(b) Verdict + deterministic recomputation.** clausify-input (pure 6-case
if-recursion — now checkpointed by us), clause-id derivation, subsumption
checks, expand-abbreviations' unconditional expansions, induction-formula
construction from a chosen scheme. Replayable by recompute-and-validate
against recorded outputs; divergence is loud.

**(c) Verdict-only, justification not externally reconstructible.**
- **type-set** (type-set-b.lisp:7785): records only the runes used in the
  final ttree; the lattice derivation, backchain attempts, and the
  ancestors-based cycle-breaking are not recorded. Recomputation requires
  reimplementing the lattice + tables + rule backchaining exactly.
- **tau** (tau.lisp:12030): deliberately records NOTHING but the verdict — no
  tau-alist evolution, no per-implicant firings.
- **linear arithmetic** (linear-a/b): polys carry ttrees and parents, but the
  cancellation sequence/final contradiction derivation is not recorded.
- **expand-and-or** inside clausify (induct.lisp:645): consults the enabled
  structure (ens) — not a pure function of the term.
These are the natural domain of the ratified decision-procedure carve-out, or
of future targeted emission (each has clear hook points, anchored in the
inventory).

**(d) Heuristic search, certifiable RESULT.** Induction scheme selection
(suggest/flush/merge/veto over candidates — induct.lisp:3306–5036) is a big
heuristic search, but the SELECTED scheme (measure, rel, controllers, per-case
tests + substitution alists) is a complete certificate; the search itself
never needs replay. Same for loop-stoppers, rule ordering, rw-cache: heuristic
control whose outcome is visible in what fired. Our scaffold already exploits
this: certify results, ignore searches.

**(e) Trust extensions.** :meta rules and :clause-processors (user code whose
soundness rests on a separately-proved correctness theorem about an
evaluator); skip-proofs / ttags / :bye (explicit trust holes, all flagged in
the world); include-book certificates. An importer must surface these as
explicit trust assumptions, not replay them.

## 3. Cross-goal dependence (the locality question)

The clause tree is NOT fully local, but every cross-goal mechanism records
enough to restore locality:

- **Forcing rounds** (the big one): 'assumption records carry
  `((type-alist . term) immediatep rewrittenp . assumnotes)` — the COMPLETE
  deferred statement (term under a type-alist context) plus provenance
  (assumnote = (cl-id rune . target)), linear-a.lisp:634–651 (verified
  verbatim). After the waterfall, extract-and-clausify-assumptions
  (prove.lisp:3724) turns each into an explicit CLAUSE for round k+1, with
  assumnotes preserved through subsumption merges (union-equal). So a forced
  proof is: tree for round 0 + recorded clause set for round 1 + … — each
  round locally replayable, joined by "the forced assumption's clause implies
  the use site's obligation". Caveat: subsumption merges union provenance
  (many sources → one goal), and assumnote cl-ids are filled lazily.
- **Pool/induction**: push-clause → pool → induction subgoals; already handled
  (clause-id lineage + pool-root synthesis).
- **:use/:by**: generate sibling constraint clauses recorded in the :use/:by
  ttree tags (lmi-lst, constraint-cl, k) — explicit obligations. Note the
  "rune-tracking gap": the lmi's own runes are deliberately NOT ttree'd
  (tau.lisp:755) — the constraint proof carries the justification.
- **Functional instantiation cache** ('proved-functional-instances-alist,
  history-management.lisp:3379): prunes RE-generation of constraint
  obligations, world-global. An importer must either track the cache or
  re-emit the constraints each time.
- **pt / tail-biting** (linear-a.lisp:75): intra-clause only — polys/forward
  facts record which literals they came from so they can't refute themselves.
  Replay must respect the same exclusion when recomputing class-(c) verdicts.
- **encapsulate/constraints**: world-level, see §5.

**New-variable mechanisms** (elim, generalization; elim's internal
generalization too) record the introduced variables, the term→var maps, the
type restrictions, and the per-var :generalize runes. Replay needs fresh-name
discipline and an env-extension story, but no missing data.

## 4. Milawa: the worked answer to "what core suffices"

`books/projects/milawa/ACL2/` (fully present in our tree) is Jared Davis's
self-verifying ACL2-like prover. Directly relevant findings:

- **The primitive proof core is ~12 rules** (logic/proofp.lisp): axiom,
  theorem, propositional schema, functional equality, beta-reduction,
  expansion/contraction/associativity/cut, instantiation, **induction**, and
  base-eval — over a 3-connective formula language (pequal*, pnot*, por*).
- **Induction is a PRIMITIVE** (logic/proofp.lisp:862, verified verbatim):
  measure m, case formulas qs, per-case substitution sets, with basis /
  inductive / ordinal (`ordp m`) / measure-decrease subproofs. This is
  structurally our scaffold's emitted justification (measure, case tests, IH
  alists, WF obligation) — independent confirmation that the induction
  interface we built against is the right one.
- **Trace-then-compile**: Milawa's rewriter emits TRACES (method, lhs, rhs,
  **iffp flag**, hypbox, subtraces — rewrite/traces/tracep.lisp:56) during
  search and compiles them to proofs separately. Our log→replay pipeline is
  the same architecture with the compiler in another system. The iffp flag
  baked into the core trace independently validates R-parameterized judgments
  (equal/iff) as the right shape.
- **Levels** (levels/level2..11): higher-level rules (≈ our per-rune recipes)
  compile down to lower levels; each level's checker is verified against the
  previous. This is the verified-checker endpoint of our certifying spectrum,
  demonstrated feasible for exactly this logic.
- **Costs**: appeal trees are trees, not DAGs — subproof duplication is the
  known cost (their fast-traces exist to defer proof construction). Mirrors
  our Expr-sharing bite; plan sharing early.
- **What Milawa omits**: forcing, tau, full geneqv (only equal/iff),
  defattach-style attachment, metafunctions-as-trusted (it verifies its
  tactics instead). I.e. the Milawa fragment ≈ a principled "core" cut.

## 5. Events and the logical world (the importer's obligations)

- **defun/mutual-recursion**: body + measure justification + guard split
  (guards are NOT part of logical meaning); type-prescriptions computed and
  recorded. Already largely modeled.
- **defthm/defaxiom**: theorem + rule-classes; defaxiom is an explicit axiom
  (must surface as a trust assumption).
- **encapsulate** (other-events.lisp:8452): two-pass; the logical content of a
  constrained function is its CONSTRAINT (selected pass-1 theorems). An
  importer models constrained functions as opaque + constraint hypotheses —
  structurally the same shape as our totality/TP conditional hypotheses.
- **functional instantiation**: obligations = instantiated constraints of
  every ancestor function touched; recorded via :use/:by tags + the
  world-global cache.
- **defchoose/defun-sk**: explicit choice axioms — in Lean terms,
  `Classical.choice`-shaped; representable, must be surfaced.
- **defattach**: changes the EVALUATION theory, not the logical theory
  (acyclicity + constraint discharge); for theorem import it can largely be
  ignored except where proofs used evaluation of attached fns (then it's a
  trust note).
- **include-book/certificates/ttags/skip-proofs**: trust boundaries with
  explicit world flags; importer surfaces them, never replays.

## 6. Surprises worth remembering

- Specious simplifications are reported as HITS (simplify.lisp:9135) — an
  output clause set can contain the input clause; settled-down catches the
  loop. Replay must tolerate identity-shaped hits (we already met this as
  no-op clausify records).
- elim/generalize/fertilize/eliminate-irrelevance only fire DURING induction
  (pool check) — they are induction-support processors, not general ones.
- immediatep ∈ {t, 'case-split, nil} is soundness-critical tri-state
  (prove.lisp:659 warns); case-split clauses are built from (not cl), not from
  the type-alist.
- The :by/:use lmi runes are deliberately not tracked as 'lemma — the
  constraint-clause proof carries the justification.
- Meta-rule soundness is an evaluator-level META argument (rewrite.lisp:12837
  essay), not a term-level equation — replay-by-evaluation is not available;
  it is a genuine trust extension unless we verify the metafunction in Lean.
- Free-variable hypothesis relief (:match-free) enumerates unifiers — the
  CHOSEN unifier must be emitted (or the search re-run) for faithful replay.
- Type-set's cycle-breaking ancestors heuristic is unrecorded — exact
  recomputation must reimplement it bug-for-bug; prefer emission or carve-out.

## 7. Classification summary table

| Mechanism | Class | Replay strategy (candidate) |
|---|---|---|
| rewriter steps (rules, defs, congruences) | (a) | per-step replay (current driver) |
| geneqv/iff positions | (a/b) | emit geneqv per step; R-parameterized judgment |
| clausify-input | (b) | checkpointed recompute-validate (done) |
| clause ids / waterfall structure | (b) | deterministic reconstruction (done) |
| induction scheme | (d) | certify selected scheme (done, v1 shapes) |
| induction formula | (b) | recompute-validate from scheme |
| elim / generalize / fertilize / irrelevance | (a) | replay from recorded payloads + fresh-var env story |
| type-set | (c) | carve-out leaf OR emitted derivations (decide in design) |
| tau | (c) | ratified carve-out (done) |
| linear | (c) | ratified carve-out; lean-smt for non-trivial (gated) |
| forward chaining | (c→a) | fc-derivation records exist; needs emission polish |
| forcing rounds | recorded cross-goal | per-round local replay + assumption-clause joins |
| :use/:by/:cases | (b) | recorded obligations as sibling clauses |
| functional instantiation / encapsulate | (b/e) | constraint hypotheses (the conditional-proof shape) |
| meta rules / clause processors | (e) | trust assumption or Lean-side verification |
| skip-proofs / ttags / defaxiom / :bye | (e) | surfaced trust assumptions |
| defchoose / defun-sk | (b) | choice axioms, explicit |
| BDD | (e/c) | carve-out or trust |
