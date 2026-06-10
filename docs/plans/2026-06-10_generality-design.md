# Handling ACL2 in (useful) generality — logical architectures and a proposal

_Created 2026-06-10. Companion to
`docs/notes/2026-06-10_acl2-architecture-survey.md` (the inventory this doc
reasons from). Status: DRAFT for MDD review; feature work paused until ratified._

## 0. What we are designing

A pipeline that imports ACL2 theorems as Lean-kernel-checked proofs with
genuine, faithful replay, scaled from today's corpus (17/37 driver-replayed)
to a **useful core** of real ACL2 practice, with a principled story for
everything outside the core. "Useful core" is proposed below (§5); its final
cut should be confirmed by a measured book sweep (survey's noted gap).

The survey's load-bearing facts:

1. Every ACL2 mechanism falls into five replay classes — per-step recorded
   (a), verdict+deterministic-recompute (b), verdict-only opaque (c),
   heuristic-search-with-certifiable-result (d), trust extension (e).
2. Cross-goal dependence is always *recorded*: forcing rounds carry complete
   deferred statements + provenance; :use/:by carry their constraint clauses;
   induction pools are deterministic lineage. Locality is restorable.
3. Milawa demonstrates that a ~12-primitive proof core — with induction as a
   primitive whose shape matches our emitted justification, and iff/equal
   baked into rewrite traces — suffices for ACL2-style proving, and that
   trace-then-compile (≈ our log→replay) is a sound architecture for it.

## 1. Two cross-cutting decisions (independent of architecture)

### 1.1 Statement semantics: `= some t` vs truthiness

ACL2's notion of a theorem is *the term is non-nil*; clause truth is *the
disjunction is non-nil*. Our current statements (`eval … = some t`) are
strictly stronger; they coincide on boolean-valued terms (today's corpus) but
make some true theorems unprovable (truthy-non-t last literals) or even
false-as-stated (non-boolean formulas). The iff-geneqv chain made this
concrete: preprocess rewrites under iff.

**Decision proposed**: migrate the *clause/mirror* judgments to truthiness —
`∃N∀f≥N ∃v, eval t = some v ∧ v ≠ nil` (call it `EvTrue`) — with `= some t`
retained as a derived strengthening where the value is pinned (the spine's
last-literal case, recognizers). Rationale: it is ACL2's own semantics, it
dissolves the boolean restriction *and* the iff-chain awkwardness at the
root, and the migration cost is concentrated in a small lemma layer
(`re_dp_if_split`-family gets `EvTrue` variants; the DP lift's last-literal
`= t` facts strengthen to it trivially). Interim fallback if deferred: a
fail-closed boolean-valuedness check at the statement builder.

### 1.2 Judgment parameterization: equivalence relations as a parameter

The rewriter is generic over equivalence relations (geneqv); preprocess runs
under iff; users add congruence rules (runes!). Milawa bakes iffp into the
core trace. **Decision proposed**: one rewrite judgment family parameterized
by the relation —

```
EvRel R a b  :=  ∃N∀f≥N, R-related (eval a) (eval b)
  R = equal : eval a = eval b              (today's chain)
  R = iff   : truthiness of a ↔ truthiness of b
```

with positional congruence indexed by (function, arg-position, R-in, R-out) —
exactly ACL2's congruence-rule shape, hence emittable per step (the geneqv is
in scope at every instrumented site). Ground-zero congruences (if-test,
if-branches-under-iff, not-arg, equal-args, …) are a fixed Lean lemma set;
user congruence rules become recipes keyed by their runes. This subsumes the
pending iff-chain work and prevents walker-family multiplication when the
third relation arrives.

## 2. Architectures explored

### A. Certifying walkers, hardened (the current architecture, completed)

Driver meta-functions interpret recorded/validated ACL2 structure into proofs
built from a fixed lemma toolkit; judgments layered (values → R-equalities →
truth → structure); every joint validated against the emitted artifact;
fail-closed everywhere.

- **For**: incremental, already validated on 17/37 incl. induction and the
  clausify bridge; failures are always honest (kernel or frontier error);
  each mechanism lands as a recipe; mirrors Milawa's trace-compiler in
  architecture.
- **Against**: proof terms duplicate subproofs (Milawa's appeal-tree cost,
  observed in our Exprs); the walker codebase grows with mechanisms and
  duplicates ACL2 semantics in meta-code (bounded by validation, but real
  upkeep); nothing is *proved once* — every theorem pays full elaboration.

### B. Deep-embedded derivation checker (the Milawa endpoint)

Define a Lean datatype of derivations (an appeal/trace tree: rewrite steps
with runes and R-flags, clausify checkpoints, induction nodes with the
emitted justification, DP leaves, …), write a checker function
`check : Derivation → World → Formula → Bool`, prove **one** soundness
theorem `check d w φ = true → Mirror w φ`, and have the pipeline produce
`Derivation` values; per-theorem cost becomes kernel evaluation of `check`.

- **For**: per-theorem cost collapses (no per-step `Expr` assembly; the
  Env-reducibility work makes `check`-by-reduction realistic); the semantics
  duplicated in meta-code becomes *verified* code; proof-object size is data,
  not proof terms; Milawa demonstrates feasibility for exactly this logic.
- **Against**: the soundness proof is a large induction over the derivation
  datatype — weeks of proof engineering up front, re-paid on every datatype
  extension (each new mechanism = new constructor = new soundness case);
  validation-against-record discipline must be re-encoded inside `check`;
  much harder to iterate against real-tree surprises (our whole c3 experience
  was rapid recipe iteration, which A makes cheap and B makes expensive).

### C. Hybrid: walkers as the lane, derivation-checker as progressive
   consolidation (recommended)

Keep A as the production lane and the *discovery* mechanism (new ACL2
features always land as walkers first, iterated against real trees). When a
fragment stabilizes, consolidate it into B-style verified functions
piecewise — the architecture already supports this because each walker's
output judgment is a fixed proposition:

- Tier 1 consolidations (cheap, high payoff): the value layer
  (`dpValExpr`-lift as a verified function over reified terms + one
  soundness lemma), the disjoin spine intro/elim, the clausify recursion
  (`clausifyPure` is already a Lean function — prove its bridge lemma once,
  by induction, replacing the per-leaf walkers).
- Tier 2: the rewrite-chain composer over an `EvRel`-derivation list.
- The full derivation datatype emerges bottom-up from these, with soundness
  proved per-fragment instead of one monolith. If/when complete, A's walkers
  reduce to parsers into the datatype.

This keeps A's iteration speed, caps its proof-term cost where it actually
hurts (the per-literal/per-node leaf proofs), and reaches B's trust shape
asymptotically without betting the project on a monolithic soundness proof.

## 3. Per-class replay strategy (uniform policy)

- **(a) per-step recorded** → walker recipes (existing pattern). Includes the
  structural processors: elim/generalize/fertilize payloads are already
  recorded upstream; they need the *new-variable* env story: each introduced
  variable becomes a ∀-bound value in the clause statement with its recorded
  type-restriction as a hypothesis (the same shape as our induction case
  lambdas — `withLocalDeclD` + recorded restriction facts).
- **(b) verdict + recompute** → recompute-and-validate against the record;
  hard-fail on divergence (clausify precedent).
- **(c) opaque verdicts** → the ratified carve-out (tau, linear, type-set-fc
  leaves) stays; for **type-set inside the rewriter** (assume-true-false,
  recognizer evidence) prefer *targeted emission* over recomputation —
  the survey anchors the hook points; recomputation would have to clone the
  lattice + cycle-breaking heuristics bug-for-bug. lean-smt remains the gated
  path for arithmetic the fixed tactic can't close.
- **(d) search-with-result** → certify the result, never the search (already
  the induction policy; extends to free-variable hyp relief: emit the chosen
  unifier).
- **(e) trust extensions** → conditional-proof hypotheses, exactly like
  total:/tp: today: metafunction correctness, clause-processor soundness,
  defaxioms, skip-proofs/ttags each become named, explicit hypotheses of the
  imported theorem (or import is refused). No silent trust.

## 4. Cross-goal composition

- **Forcing rounds**: treat each round as additional `Development`-level
  proof units. The emitted artifact needs one upgrade: emit the
  per-assumption `(type-alist, term, assumnotes)` and the round-(k+1) clause
  list (extract-and-clausify-assumptions is the single hook). Replay: prove
  round-(k+1) clauses locally; at each force site, the recorded assumption
  clause is a bound hypothesis discharged by the corresponding round-(k+1)
  proof — the same conditional-then-discharge shape as totality. Assumnote
  merges (many sources → one goal) are fine: one proof discharges all sites.
- **:use/:by/:cases**: sibling obligation clauses, recorded; replay as child
  clause proofs feeding the hint node (the `apply-top-hints` recipe).
- **Induction pool**: done (lineage + pool-root synthesis).
- **Functional instantiation/encapsulate**: constrained functions = opaque
  fns + constraint hypotheses (the conditional shape we already use for
  totality); :functional-instance = substitution event whose obligations are
  the recorded constraint clauses. The world-global cache is an optimization
  we ignore (re-emit obligations per use; dedupe in the importer if needed).

## 5. The proposed core (and the tiers outside it)

**CORE (target: full faithful replay)** — approximately the Milawa fragment
plus the carve-out:
waterfall structure & clause ids; preprocess (chains, clausify checkpoints,
built-in leaves); the rewriter with R ∈ {equal, iff} + congruence runes +
definitions + recorded with-lemmas + free-var unifier emission; if/case
handling; type facts via emitted TP/type-set data; tau/linear/type-set-fc
leaves via the carve-out; induction (single + mutual + multi-case + merged
schemes, via the emitted justification); elim/fertilize/generalize/
irrelevance from recorded payloads; :use/:by/:cases; forcing rounds;
defun/mutual-recursion/defthm/encapsulate-as-constraints; defchoose/defun-sk
as explicit choice axioms.

**EXTENDED (conditional import)** — user congruence relations beyond iff
(recipe-per-rune, same machinery); metafunctions & clause processors
(imported with a correctness hypothesis, or verified in Lean per-function);
functional instantiation chains; non-trivial guard reasoning.

**OUT (refuse or trust-flag)** — ttags/skip-proofs/defaxiom-dependent
theorems (imported only with explicit axiom hypotheses); BDD; defattach
evaluation-theory reasoning.

The cut should be validated by the measured book sweep (follow-up): if e.g.
:functional-instance or meta rules are far more prevalent than the
source-based guess, they move inward.

## 6. The native bridge in this picture

The product is native Lean theorems. Generalize the existing pattern
(`my_len_my_app` → `List.length_append`) into a BRIDGE LAYER: per ACL2 data
shape, an encoding `enc : τ → SExpr` with simulation lemmas for the core
operations (the `corr_*` lemmas of the hand proofs, systematized); the mirror
theorem instantiated at encoded values + simulation yields the native
statement. This layer is ordinary Lean library engineering, independent of
the replay architecture; it should grow per imported theorem family, and is
where `EvTrue` (§1.1) pays again — truthiness is what encodings naturally
produce for non-boolean ACL2 functions.

## 7. Recommendation and sequencing

**Adopt C** (walkers as the lane, progressive consolidation), with §1's two
decisions taken now. Concretely, in order:

1. **R-parameterized rewrite judgment + geneqv emission** — unblocks the
   iff chain (app-nil/rev-rev/true-listp-app), retires the pending frontier,
   and installs the parameterization discipline. (≈ the deferred iff work,
   done right.)
2. **`EvTrue` migration** of clause/mirror judgments (with the boolean
   strengthening lemmas kept). Moderate, mechanical, removes a whole class of
   future walls.
3. **Tier-1 consolidations** (clausify bridge lemma by induction; value-layer
   soundness function) — caps proof-term growth before bigger corpora.
4. **Forcing-round emission + composition** (the one genuinely new emission
   chunk; survey-anchored, single hook).
5. **Induction generality** (3-subgoal/merged schemes, multi-var measures,
   mutual-recursion flag schemes) — pure scaffold extension, corpus-driven.
6. **Measured book sweep** to confirm the core cut; revisit this doc.

Each step lands with the existing discipline: real artifact first, fail
closed, ci + coverage as the scoreboard, audits at milestones.
