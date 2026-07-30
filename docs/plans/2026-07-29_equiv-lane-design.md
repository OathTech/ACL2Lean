# The equivalence lane (L2): R-parameterized replay — design note

**Status: RATIFIED DIRECTION (MDD conversation 2026-07-29), deliberately
UNCOMMITTED on `mdd/sorting-completion` as session-failure insurance; this
file becomes the opening commit of `mdd/equiv-lane` after the sorting arc
merges.** The direction below was settled explicitly with MDD; the "open
mechanics" section is what remains to pin during the build.

## Problem

The replay's only composition relation today is evaluation equality
(`∃N ∀f≥N, evalOpt f w env lhs = evalOpt f w env rhs`), plus truthiness at
the clause boundary. ACL2's rewriter is natively RELATION-parameterized
(geneqv): at each position it rewrites under an equivalence R justified by
`:congruence` rules, and records `:EQUIV R` per step (the fork emits this
— S2b `structured-geneqv-equiv`). Real blocked rows, all one family:

- `ORDEREDP-QSORT` — `replayPreprocessNode: step under equivalence perm —
  R-parameterized recipe pending (G1 frontier)`. Consumes
  `(defcong perm equal (all-rel fn x e) 2)` + `PERM-QSORT` (recorded step:
  `:RUNE (:REWRITE PERM-QSORT) :ORIGIN ABBREVIATION-EXPANSION :EQUIV PERM`
  — 2 such steps in qsort.proof-log, 1 in ordered-perms).
- `PERM-IMPLIES-EQUAL-ALL-REL-2` (the defcong itself) —
  `branch-substitution under equivalence some PERM (frontier — equal
  only)`. Its own proof rewrites under perm using earlier perm lemmas.
- `ORDEREDP-APPEND` — iff-normalization in the preprocess chain: `iff` is
  the bottom rung of the same ladder. (Related: the p3-conj-mid-literal
  tripwire's `(IF a a b) → (IF a 'T b)` or-shape normalization is an
  iff-context normalization.)

An equality chain cannot represent "perm-equivalent": `(qsort x)` and `x`
evaluate to different values. Missing dimension, not missing recipe —
hence design invariant L2 and the pattern map's parked circle.

## Ratified core (the part that is now settled)

1. **A user equivalence is the INTERPRETED relation.** For perm:
   `R a b := EvTrue w env (PERM ⟨quote a⟩ ⟨quote b⟩)` over the world's own
   PERM defun — the `interpCount` move again: never re-model what the
   interpreter defines. Env-independence on quoted arguments must be
   stated (same subtlety interpCount had).
2. **Every property of R is CONSUMED from replayed theorems, never
   assumed**: refl/sym/trans from the replayed `:equivalence` rule's
   defthm mirrors (`PERM-IS-AN-EQUIVALENCE`, `PERM-SYMMETRIC`,
   `PERM-TRANSITIVE` — all green rows today); congruences from replayed
   defcong mirrors. In ACL2 an equivalence IS exactly (binary defun +
   proved :equivalence rule + proved :congruence rules) — the interpreted
   relation + replayed properties is that structure's faithful image;
   there is no further mathematical content to be faithful to.
3. **Scale argument** (why native models are ruled out as the lane):
   user equivalences are arbitrary defuns; per-equivalence native
   modeling (CountSim-style) is unbounded manual work with a fresh
   divergence surface each time. Native relations belong ONLY at the
   `Imported/` lift boundary (interpreted-perm ↔ `List.Perm`, once,
   kernel-checked, only for relations the final statement mentions).
4. **L1/L2 conformance**: a fragment-local judgment (own `Prop`, own
   soundness lemma — no widening of the monolith); congruence recipes
   land ADDITIVELY, indexed by (fn, position, R-in, R-out), each backed
   by a replayed theorem; R is abstract, never an enum switch.
5. **Statement layer untouched**: the mirror theorem stays
   `EvTrue w env (disjoin goal)`; R lives in proof plumbing only (like μ).

## Judgment sketch

`EvRel (R : SExpr → SExpr → Prop-source) a b` with instances:
- `equal` — today's fuel-eq, DEFINITIONALLY (the existing corpus must not
  move; `EvRel equal` unfolds to the current chain shape).
- `iff` — truthiness agreement (both-truthy-or-both-nil at the limit).
- user R — the interpreted relation (1) above.
Chain transitivity per-R from the consumed equivalence facts. The walker
threads the step-recorded `:EQUIV` and refuses (loud frontier) any R with
no in-scope equivalence-fact bundle — the D6 pattern: an undischargeable
R-fact surfaces as an honest `cond[…]` hypothesis, never an assumption.

## Bootstrap DAG — VERIFIED on the real logs (2026-07-30, perm-lane inc-0)

Probe: walk every theorem's `citedRuneNames` against creation order in
the perm and qsort books. RESULT — no circularity, no forward or self
citation anywhere:

- perm book (creation order PERM-CONS → PERM-SYMMETRIC → MEMB-RM →
  PERM-MEMB → COMM-RM → PERM-RM → PERM-TRANSITIVE →
  PERM-IS-AN-EQUIVALENCE): strictly earlier citations throughout;
  PERM-IS-AN-EQUIVALENCE cites only PERM-SYMMETRIC + PERM-TRANSITIVE.
  All 8 rows are GREEN (8/8 unconditional in the sweep) — the
  equivalence facts rung 2 consumes are replayed mirrors.
- qsort book: PERM-IMPLIES-EQUAL-ALL-REL-2 cites ZERO local theorems
  (support is cross-book: CAR/CDR-CONS + LEXORDER-REFLEXIVE/TRANSITIVE);
  ORDEREDP-QSORT cites ORDEREDP-APPEND, PERM-IMPLIES-EQUAL-ALL-REL-2,
  ALL-REL-FILTER-1/2, PERM-QSORT — all strictly earlier.
- Dependency note: ORDEREDP-QSORT cites ORDEREDP-APPEND (currently FAIL
  at the type-alist relief class) — the headline row will be conditional
  on rule:ORDEREDP-APPEND until that class lands (D6-honest).

The RECORD classes rung 2 must replay (from the same probe):

1. ORDEREDP-QSORT: exactly TWO `:EQUIV PERM` rewrite steps, both
   `(:REWRITE PERM-QSORT)` via ABBREVIATION-EXPANSION — perm-rewrites at
   congruence-licensed positions (ALL-REL arg 2, where the replayed
   defcong mirror licenses Perm-in → Eq-out: the L2 congruence-registry
   collapse row, the direct analogue of rung 1's iff collapse rows).
2. PERM-IMPLIES-EQUAL-ALL-REL-2: its own proof has NO `:EQUIV PERM`
   rewrite steps (only EQUAL/IFF) — the blocker is a
   BRANCH-SUBSTITUTION record whose `:EQUIVALENCE` is PERM
   (remove-trivial-equivalences substituting under the perm relation);
   the transport needs the interpreted-relation instance at the
   substituted positions.

## Sequencing

- **Rung 1 — iff**: validates the R-parameterization with no user
  relation (no new consumed facts beyond booleanness); targets
  `ORDEREDP-APPEND` + the or-shape normalization tripwire
  (`p3-conj-mid-literal` flips green = the conjunction composer's
  mid-literal arm gets its validation).
- **Rung 2 — perm**: the congruence registry + interpreted-relation
  instance; targets `PERM-IMPLIES-EQUAL-ALL-REL-2` then `ORDEREDP-QSORT`.
- Each rung ships with decorrelated validation books in
  `acl2_samples/pattern-tests/` pinned via `Tests/PatternPins.lean`
  (the inc-2b structure).

## Rung-1 build log (2026-07-29, mechanics as pinned during the build)

Landed (inc-1/inc-2a — see TODO for the increment detail): the IFF-unfold
emission gap (fork `expand-abbreviations/nonrec-body`), `replayIffDef`,
the or-shape collapse relabeled `:EQUIV IFF` at the fork (it was a
fidelity mislabel), `evrel_siff_if_or_shape`, and the first COLLAPSE rows
beyond if-test: IMPLIES arg-1/2 (`evrel_implies_arg1/2_siff_collapse`) —
an SIff payload lifted along a node's `:PATH` collapses to an
eval-equality at the first boolean-consumer frame, so most rewrite-side
iff steps need NO chain-type change.

REMAINING rung-1 core (inc-2b, designed, not yet built):

1. **The or-collapse bridge** (p3-conj's flip): an IFF
   `if-finish/combined` node whose then-branch is the UNREWRITTEN test's
   copy `A` (rewrite-if replaced it by `'T` with no recorded step; the
   collapse fired because `unrewritten-test == left`). The bridge fact
   `EvRel SIff (IF X A B) (IF X 'T B)` needs `eval A = eval X` — the
   test's OWN recorded chain, re-composed on the then-copy. Mechanism:
   thread a `chainPrefix : List (ProofNode × Nat × List (Option String ×
   Nat))` through `replayRewritesWith` (trailing DEFAULTED param — all 22
   call sites are in NodeCore; consume-and-continue recursions append
   `(n, depth, strip)`, re-process sites pass unchanged); in the combined
   handler, filter prefix nodes whose relativized path descends the TEST
   position (`.arg 1` after this node's `rel`) and re-replay them on the
   then-copy `A` via the EXISTING strip mechanism — exactly the branch-
   children pattern (`replayRewritesWith … A testNodes depth (strip' ++
   [(myKind, 1)])`), requiring the result to be `c` (fail-closed). Bridge
   lemma `evrel_siff_if_or_bridge (hAX : ∃N∀f≥N, eval A = eval X) …`.
2. **Literal-chain R-threading**: the bridged combined node sits at the
   literal ROOT, so its composite is IFF at the literal boundary — change
   `replayRewritesWith`/`NodeRec.rewrites`/`replayLiteralChain` to return
   `Option (Expr × Bool)` (isIff flag). Wave plan: (a) type change with
   eq-only behavior — a `chainReqEq` shim (named frontier on iff) at the
   ~20 eq-composition sites (`chainWith`-idiom sites get a `chainWithR`
   with the mid-term's `ctxValProof` for SIff injection, mirroring
   `replayPreprocessChainCore`'s mixed compose); golden byte-identical;
   (b) real iff handling ONLY on the spine path that consumes the literal
   chain: an iff literal chain COLLAPSES to an eval-equality of the
   clause disjunction at the literal's if-test position
   (`evrel_if_test_siff_collapse` — the disjoin spine treats each literal
   as a test), so `composeSplit`/the trivial continuation transport
   truthiness with no further spread.
3. **ORDEREDP-APPEND's other frontier**: `LEXORDER-TRANSITIVE`
   marker-relieved hyp `(LEXORDER A3 (CAR A4))` with `:TA-RUNES
   [LEXORDER]` — a type-alist relief class (the fact lives in `*1.1`'s
   own spine/branch context; investigate the record before building).

## Rung-2 build log (2026-07-30, mechanics as pinned during the build)

BOTH targets GREEN (sweep 65/79): PERM-IMPLIES-EQUAL-ALL-REL-2
unconditional; ORDEREDP-QSORT conditional only on pre-existing debt
(rule:ORDEREDP-APPEND at the type-alist relief frontier + the standard
totality/TP/arithmetic-rule classes) — its perm reasoning is
self-contained (both new hypothesis classes DISCHARGED from replayed
mirrors). Decorrelated validation: `p7-cong-collapse` 4/4
(fresh SAME-LN relation, arity-1 congruence position; PatternPins).

Mechanics as BUILT (vs the sketch above — two simplifications, both
faithful to the observed records):

1. **No chain-threaded user-R payload was needed.** In both observed
   classes the R-fact collapses IMMEDIATELY:
   - The branch-substitution class (the defcong's own proof) has the
     substituted variable ONLY in the justifying `(not (R var val))`
     literal — the mirror is pure clause structure (byCases on the
     literal; falsity collapses its if-frame out), consuming NO R-facts
     at all. Occurrences outside the justifying literal remain a loud
     congruence-transport frontier.
   - The rewrite class (ORDEREDP-QSORT) records the R-step's :PATH with
     the congruence frame INNERMOST, so the payload lives for exactly
     one frame: `replayCongCollapse` converts it to an eval-equality of
     the parent applications on the spot, and everything outward lifts
     as ordinary equality. `EvRel` never needed a user-R instance.
2. **The interpreted relation appears as HYPOTHESIS SHAPES, not a
   judgment.** A user-equivalence stored rule is offered as
   `∀ env', EvTrue w env' (R lhs rhs)` (mkRuleHypType's R-route, gated
   on R naming a world-defined binary fn; discharge decode: the defthm
   conclusion must BE the R-application — routeRel). A defcong is
   offered as its WHOLE-FORMULA mirror `∀ env', EvTrue w env' formula`
   (`cong:<thm>`, CongSpec shape-parsed from the formula with
   recompute-and-check at the use site; discharged from the replayed
   mirror with NO decode). The collapse is value-level MP
   (`implies_value_mp`) + the two-valued EQUAL decode — the L2
   congruence registry is the (fn, pos, R)-indexed CongSpec list.
3. En route (surfaced by the validation book): the multi-clause
   clausify bridge's TAUT-DROPPED split (recorded :CLAUSE ('T);
   ACL2's type-set sees the COMMUTED-EQUAL pair) — landed as the
   multi-bridge taut arm + `tautClauseClose`'s commuted-equal pair.
   Plus the inc-1 spine relief: if-test falsity demands (recorded
   lhs/rhs + world-side unfolded definition bodies) feeding the
   later-literal hoist, the silent-tautology close at spine
   exhaustion, and segFacts/litFacts extensions to the unemitted-test
   resolver.

## Open mechanics (to pin during the build, none philosophical)

- Exact `EvRel` statement shape (fuel-quantification placement; the
  equal-instance definitional-compatibility proof obligation).
- The congruence-registry data format and its offer/discharge plumbing
  (mirror-application like `rule:` hypotheses vs telescope-fvar offers).
- How the iff rung interacts with the existing `EvTrue`-boundary lemmas
  (several are iff-shaped already: `evtrue_and_*`, two-valued decodes).
- Whether the geneqv POLARITY context (rewriting inside a NOT flips the
  usable relation set) needs explicit threading or falls out of the
  recorded per-step `:EQUIV` (suspected: falls out — verify on records).
- Perf: interpreted-R facts add per-step conv obligations; measure before
  optimizing.
