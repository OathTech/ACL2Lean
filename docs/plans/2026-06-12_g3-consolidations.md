# G3 — tier-1 consolidations: design + decision log

_Created 2026-06-12, branch `mdd/g3-consolidations`. Step 3 of the ratified
generality plan (§2C tier 1, §8.3). Status: DESIGN for MDD review before
deep implementation._

## 0. What and why

Two stable walker fragments consolidate into VERIFIED FUNCTIONS with
once-proved soundness lemmas — architecture C's progressive-consolidation
move. Today these walkers re-construct structurally identical proof terms
per leaf × per literal (`mkAppM` chains); after G3 the driver COMPUTES a
pure function (kernel-reducible — the Layer-1 Env-as-assoc-list change was
made for exactly this) and instantiates ONE lemma. Payoffs: proof-term size
capped before bigger corpora; the meta-code that duplicates evaluator
semantics becomes verified code; per-theorem elaboration shrinks.

Binding invariants: **fragment-local per L1** (own function, own soundness
lemma, composing at the judgment layer — `EvTrue`, convergence Props; NO
shared derivation datatype); **L3 world-parametric** (lemmas over arbitrary
`w`).

## 1. Fragment A — the value-layer lift (first; B consumes it)

Today: `dpValExpr` (meta) computes the lifted VALUE Expr of a clause term
over env-vars + pinned opaques; `dpValProof` (meta) builds the convergence
proof per node. Consolidated:

```lean
/-- The DP lift as a PURE function: variable values from the env, opaque
    values from an assoc list keyed by the opaque application term. -/
def dpLift (env : Env) (opq : List (SExpr × SExpr)) : SExpr → Option SExpr
```

with one soundness lemma (by induction over the term, mirroring today's
`dpUnary`/`dpBinary` primitive tables as a fixed match):

```lean
theorem dpLift_sound :
    dpLift env opq t = some v →
    (∀ (o, ov) ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env o = some ov) →
    [no-shadow side conditions for the primitive heads] →
    ∃ N, ∀ f ≥ N, evalOpt f w env t = some v
```

Driver: compute `dpLift` (decide/reduction for the `= some v` fact),
instantiate `dpLift_sound` once per term. `dpValExpr`/`dpValProof` retire
where the lift is total; walker fallback stays for shapes outside the
primitive table (hard-fail messages unchanged — frontiers preserved).

Decisions to settle:
- D-A1: opaque lookup by syntactic `==` on the application term (mirrors
  today's `opq.find?`); the function is deterministic, no search.
- D-A2: the no-shadow premises — per-head facts (as today, carried in
  `ReplayConfig.noShadow`) vs one world-level premise. Lean side wants the
  latter; fidelity is unaffected either way.
- D-A3: `dpLift` value-equality facts proved by `decide` over the reflected
  world vs `Eq.refl` by reduction — measure both (the perf lesson: profile
  before choosing).

## 2. Fragment B — the clausify bridge lemma

Today: `bridgeClausify` validates the RECORD against `clausifyPure`
(recompute-and-validate stays — that is stage-(b) policy, untouched), then
`peelClause` + `walkPosT`/`val*` rebuild `EvTrue input` from the proved
output clause by per-leaf proof construction. Consolidated: ONE lemma by
induction mirroring `clausifyPure`'s 6-case if-recursion:

```lean
theorem clausifyPure_sound :
    (∀ cl ∈ clausifyPure t pos, EvTrue w env (disjoinTerm cl)) →
    [per-subterm convergence premises, supplied via Fragment A] →
    (if pos = true : EvTrue w env t; the neg case states the dual)
```

The mutual structure (pos/neg, the `dumbNegateLit` wrapping) suggests a
paired statement proved by one structural induction. The driver's
`bridgeClausify` then: validate record (unchanged) → prove the output
clause (unchanged) → ONE `clausifyPure_sound` instantiation.
`peelClause`/`walkPosT`/`valNeg*`/`valPos*` and their lemma kit
(`evtrue_if_fact_elim` etc.) retire if consumer-free afterward.

Decisions settled at implementation (2026-06-12):
- D-B1: the convergence premise IS Fragment A's — `dpLiftF vars opq t =
  some v` plus the bundle premises; every clausify literal is a lift of a
  `t`-subterm (or its `not`-wrap, and `not` is in the table), so one
  premise covers the whole structure.
- D-B2 CORRECTED: `clausifyPure t pos` returns ONE clause's LITERAL LIST
  (this section originally said "∀ cl ∈ clausifyPure" — wrong reading).
  The invariant: `disjoinTerm (clausifyPure t true)` is iff-equivalent to
  `t`'s truth; the `false` mode to `t`'s falsity. The paired statement:
  `EvTrue (disjoin (clausifyPure t true)) → EvTrue t` and
  `EvTrue (disjoin (clausifyPure t false)) → eval t ⇒ some nil`,
  proved by ONE mutual structural induction mirroring the 6-case
  recursion, with a helper `EvTrue (disjoin (xs ++ ys)) →
  EvTrue (disjoin xs) ∨ EvTrue (disjoin ys)` (needs xs's literal
  convergences — supplied by the lift premise) and `dumbNegateLit`
  value lemmas.
- D-B3: `clausifyPure` (and the proof surface) must be TOTAL — it is
  `partial` today, which has no induction principle and no equation
  lemmas; its recursion is structural, so dropping `partial` is
  behavior-identical. Fragment B lives in its own file
  (`Replay/ClausifyBridge.lean`, importing DpLift) per L1.

### Fragment B helper decomposition (sketched 2026-06-12)

1. `not_evtrue_disjoin_nil : ¬ EvTrue w env (disjoinTerm [])` — disjoin of
   the empty clause is `(quote nil)`, whose value is pinned nil.
2. `evtrue_disjoin_cons (hconv : conv l vl) :
   EvTrue (disjoinTerm (l :: rest)) ↔ vl ≠ nil ∨ EvTrue (disjoinTerm rest)`
   — UNIFORM across `rest = []` (LHS is `EvTrue l`, RHS's right disjunct
   refuted by (1)) and `rest = _::_` (the spine if-split). This dissolves
   `disjoinTerm`'s singleton special case.
3. `evtrue_disjoin_append_elim` by list induction on xs over (2), premised
   on each xs-literal's convergence.
4. The `dumbNegateLit` arm lemmas: `(not X)`-shaped literals via
   `conv_not_nil_of_evtrue` (exists, G2); the wrap arm needs the dual
   (`EvTrue (not t)` + `conv t vt` → `eval t ⇒ some nil` via
   `arg_nil_of_not_truthy`).
5. `clausifyPure_sound` via `clausifyPure.induct`, motive
   `(t, pos) ↦ EvTrue (disjoin (clausifyPure t pos)) →
   (pos: EvTrue t | neg: eval t ⇒ some nil)`, lift-fact premise threaded
   to subterms through the bind extraction.

## 3. Sequencing

1. Fragment A: function + soundness lemma, wired into ONE consumer
   (the DP fact's value characterization), gate green, commit.
2. Fragment A: remaining consumers (discharge spine, TP instantiation),
   retire dead walker paths, gate, commit.
3. Fragment B: the paired lemma, wire into `bridgeClausify`, retire the
   peel/walk kit, gate, commit.
4. Measure (the harness timings ride along free); update this doc as-built;
   audit per milestone discipline.

The golden coverage gate is the scoreboard throughout: outcomes must stay
byte-identical (this is a refactor of HOW proofs are built, never of what
is proved — any status drift is a defect by definition).
