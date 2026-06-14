# Multi-case induction schemes (G5 core, sorting R1a) — design

**Driving artifact:** perm's 7 blocked theorems (`sorting/perm` rows of the
golden table, all at `replayInduction: no step case with tests [(consp x)]`).
The real emitted schemes (from `dump-proof-tree` on the fresh log):

```
INDUCTION on (perm x y)  (3 subgoals)
  measure (acl2-count x) decreases under o-p/o<; on: x
  case [(consp x) ∧ (memb (car x) y)]:       IH: x := (cdr x), y := (rm (car x) y)
  case [(consp x) ∧ (not (memb (car x) y))]: base (no IH)
  case [(not (consp x))]:                    base (no IH)
```

(memb's scheme is the same shape with tests on `(equal a (car x))`; every
perm-book scheme is single-controller, controller substitution `(cdr x)`.)

## What generalizes vs the v1 scaffold

v1 (`replayInduction`): exactly 2 cases `[(consp v)]` (one IH `v:=(cdr v)`,
identity elsewhere) / `[(not (consp v))]`; single pushed literal; fixed
principle `acl2_induction_consp`.

v2 adds, measured from perm:
1. **N cases with COMPOUND ruling tests** — each case is a test LIST
   (a conjunction). ACL2's induction machine derives cases from the scheme
   function's if-structure, so the test lists form a DECISION TREE; v2
   recovers that tree syntactically (split on the shared head test, recurse;
   malformed structure hard-fails).
2. **Multiple base cases** (perm has two).
3. **IH alists substituting NON-CONTROLLER variables by computed terms**
   (`y := (rm (car x) y)`) — simultaneous substitution; the env bridge
   becomes N-variable (values computed in the ORIGINAL env, then inserted —
   sequential insert of precomputed values = simultaneous semantics).
4. **Multiple IHs per case** (perm needs 1, but the per-IH loop is uniform —
   the v1 "exactly 1" restriction lifts for free; true-listp-flatten's 2-IH
   scheme becomes reachable).

## Kept as named frontiers (perm does not need them)

- Controller substitution other than `(cdr controller)`, and step cases whose
  tests do not include `(consp controller)` — the measure-decrease story
  stays `acl2Count_cdr_lt_of_consp`. (msort/qsort move this wall later;
  that is when the emitted measure-justification clauses get consumed.)
- Multiple controllers / multi-var measures (len-zip2, len-interleave).
- Multi-literal pushed clauses (the separate existing frontier, unchanged).

## The principle: strong induction on `acl2Count`

v1's `acl2_induction_consp` bakes the case split AND the decrease into one
fixed lemma. v2 separates them:

```
theorem acl2_strong_induction_count (P : SExpr → Prop)
    (step : ∀ v, (∀ u, u.acl2Count < v.acl2Count → P u) → P v) : ∀ v, P v
```

(plain well-founded recursion on `Nat`). The case DISPATCH then happens
inside `step` at the ENV level, mirroring the emitted decision tree; each IH
application supplies a measure-decrease fact (`acl2Count (cdr xv) < acl2Count
xv` from the in-scope `consp` hypothesis — the Count library).

`P` is unchanged from v1 (the G2 form):
`P xv := ∀ e, (∃N∀f≥N, eval f w e cvar = some xv) → EvTrue w e pushed`.
Non-controller scheme variables are generalized by the inner `∀ e`, exactly
as in v1 — nothing new is needed for `y`.

## Case dispatch needs TEST CONVERGENCE

Splitting on a ruling test's value (nil vs non-nil) at the env level requires
the test to CONVERGE — for primitive tests (`consp x`) that is the existing
value walk; for user-fn tests (`(memb (car x) y)`) it is TOTALITY: the
admission-data machinery (#37, `proveTotality` + `totWalk`) discharges
exactly these facts. The split lemma is classical case analysis:

```
conv t → (eval t ↦ nil → goal) → (∀ v ≠ nil, eval t ↦ v → goal) → goal
```

A ruling test whose convergence cannot be established (no admission data, no
walkable shape) HARD-FAILS with a named frontier — never assumed.

## Child-clause linking (recompute-and-validate, as v1)

For a case with tests `T₁…Tₖ` and IH alists `A₁…Aₘ`, the expected child
clause is `(map negate T) ++ (map (fun A => (not (subst A pushed))) alists)
++ [pushed]` — recomputed from the emitted scheme and matched EXACTLY against
`cn.children`'s input clauses (a mismatch hard-fails; the children are
additionally required to be a permutation-free 1:1 cover of the cases).
`negate (not x) = x`, `negate x = (not x)` (ACL2's dumb-negate-lit shape, as
already mirrored in ClausifyBridge).

At each decision-tree leaf, the replay peels: ruling literals (their values
are pinned by the path hypotheses), then each IH literal — IH instance from
the strong-induction hypothesis at the substituted controller value
(decrease by Count), bridged to the case env by the N-var substitution lemma
(`evalOpt_substTerm_substN`, generalizing `evalOpt_substTerm_subst1`), made
nil by truthiness (`conv_not_nil_of_evtrue`, G2) — then the pushed literal
remains (`evtrue_extract_else` chain, as v1).

## Steps (each gated on `just ci`, golden eyeballed)

1. `acl2_strong_induction_count` (Count/EvalLemmas; trivial WF recursion) +
   the env-level value-split lemma.
2. `evalOpt_substTerm_substN` — the N-variable simultaneous substitution
   bridge (statement read off the v1 1-var lemma; induction over the alist).
3. The decision-tree builder from case test lists (pure, hard-failing) +
   child-clause recompute/validate (replaces v1's fixed matching).
4. The scaffold rebuild in `replayInduction` (the big step): strong
   induction + per-leaf dispatch with test-convergence facts + per-IH
   bridge/peel loop. v1's behavior must be SUBSUMED (the existing corpus's
   two-case schemes are the trivial decision tree) — golden stays
   byte-identical for all current rows.
5. Gate: perm rows move (REPLAYED or the next named wall — solidify
   `.segment` / `.branchTest` are expected for some); update golden
   deliberately; record as-built here.

## As-built (2026-06-12, branch mdd/sorting-r0)

Steps 1–4 landed (commits aa871ca, ef9dfd0): the principle + split lemma +
substN bridge (axioms clean; the induction principle axiom-FREE), the
decision-tree builder, the scheme/children recompute-validation, and the
full scaffold rebuild. `just ci` green; ALL 17 previously-REPLAYED rows
byte-identical through the new generic scaffold (v1 subsumed exactly).

**Result on perm: the scheme wall fell.** All 7 blocked theorems advanced
past induction into deeper machinery. The measured next walls:

1. **Multi-literal pushed clauses** (perm-symmetric, memb-rm, perm-memb,
   perm-rm). Measured shape (perm-symmetric): pushed = `[(not (perm x y)),
   (perm y x)]`; the step case emits ONE SCHEME CLAUSE PER (alist × pushed
   literal) — ACL2 clausifies the disjunctive IH hypothesis by splitting,
   each clause carrying `dumbNegateLit` of one substituted pushed literal.
   Replay design: `P` over `disjoinTerm pushedLits`; at a step leaf the IH
   gives a truthy DISJUNCTION, eliminated literal-by-literal (per-literal
   convergence via totality pins; the ClausifyBridge `evtrue_disjoin_*`
   characterizations), each branch consuming the matching child clause.
2. **Clausify on multi-literal clauses inside case children** (perm-cons,
   perm-transitive at Subgoal *1/3) — the preprocess/clausify composition
   currently requires a single-literal clause; case children carry ruling
   literals alongside.
3. **`executable-counterpart` terminal** (comm-rm) — DONE 2026-06-14
   (commit 7fe4d38, branch mdd/perm-exec-counterpart): exec-counterpart as
   chain step AND closing-literal terminal, faithful ground re-execution
   (`replayExecGround`). comm-rm then revealed a SECOND wall behind it —
   `sublis-var` display-folding of if-simp branches (logging-only; not a
   missing-reasoning gap) — **DEFERRED** pending data on live-branch-fold
   frequency. Mechanism + A/B/C options + keep/throwaway rationale:
   docs/notes/2026-06-14_exec-counterpart-and-folding-wall.md.
4. **`.segment` / `.branchTest` solidify consumers** (perm-is-an-equivalence
   and inside others) — the conditional-congruence machinery (R1's second
   wall, unchanged).
5. true-listp-flatten: now precisely `controller maps to (car x)` — the
   car-decrease variant (cheap Count extension + per-IH decrease selection).
   len-zip2/3: merged multi-controller test shape (`(not (if (atom x) …))`)
   — the G5 multi-controller continuation.
