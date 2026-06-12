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

### Fragment B main-proof case plan (as worked out, 2026-06-12)

- **D-B4 refined:** `dpOpqKeyOk` bans by NAME (quote/if/table names,
  any package) — matching `collectOpaques`' name-based collection. Then
  wrong-package special-named heads (CL::IF, CL::NOT…) can be neither
  keys nor structural lifts, so `dpLiftF t = some v` REFUTES those cases
  (the name-only checks in `clausifyPure`/`dumbNegateLit` still fire for
  them, but the lemma's cases discharge vacuously).
- **The value route:** in every if-split case, the lift premise itself
  gives `v = cond (toBool cv) tv ev` (`dpLiftF_if_inv`) and `conv t v`
  (`dpLiftF_sound` on t directly — no `re_val_if` needed); the els/thn
  quote values compute by `dpLiftF_quote`. The IHs supply only
  nil/truthiness of cv/tv/ev (via `val_unique` against the IH's
  conclusion), and the goal is pure `cond`-algebra: e.g. neg-(if t1 t2
  'nil): left IH → cv=nil → v=nil; right IH → tv=nil → v=cond b nil nil
  = nil.
- **Hypothesis splitting:** `evtrue_disjoin_append_elim` with literal
  convergences from `clausifyPure_lifts` (a preliminary induction: every
  clause literal lifts when t does, via if_inv/not_intro/not_inv) +
  `dpLiftF_sound`.
- **dumbNegate arms:** strip-arm (t = (not x)): EvTrue x + conv → xv ≠
  nil → `not_nil_of_truthy` → conv t nil. Wrap-arm: EvTrue (not t) +
  conv → `arg_nil_of_not_truthy` → v = nil → conv t nil.
- **Empty-clause cases** (t = 'nil pos / 't neg): hypothesis refuted by
  `not_evtrue_disjoin_nil` (vacuous, honest — the empty clause is
  unprovable).
- Pieces still to write: name-based `dpOpqKeyOk` + generalized find-none
  lemma + `dpLiftF_quote` + lift-none-for-wrong-package lemma (DpLift);
  `clausifyPure_lifts`, `ClausifyGoal`, `clausifyPure_sound`
  (ClausifyBridge); then the bridgeClausify rewire + walker retirement.

## 4. As-built record (2026-06-12)

Both fragments landed on `mdd/g3-consolidations`; golden coverage gate
byte-identical at every step (REPLAYED 17/37; DP-discharge leaves
9/9/0 of 18 throughout — outcomes never moved, only HOW).

### Fragment A — as built (`ACL2Lean/Replay/DpLift.lean`)

- `dpLiftF (vars : List (Symbol × SExpr)) (opq : List (SExpr × SExpr))
  (t : SExpr) : Option SExpr` — opaque-table lookup first, then
  quote / strict if / primitive table (`callBuiltin`, guarded by
  `dpLiftHeads` + ACL2 package, D-A4); variable values via the explicit
  `vars` assoc list (D-A5 — adopted at wiring time when the original
  `env : Env` parameterization proved undischargeable: `env` is a
  quantified fvar, so `env.get?` is symbolically stuck, while concrete
  list keys reduce and the lift fact discharges by `Eq.refl`/defeq).
- `dpLiftF_sound` — the once-proved soundness lemma (12-case
  `dpLiftF.induct`), premises: per-entry convergence proofs for `vars`
  (`hvars`) and `opq` (`hopq`), plus `dpNoShadow w` (no world def
  shadows a lift primitive; discharged by `mkDecideProof`).
- Driver consumers: `DpLiftBundle` (varsE/hvars/opqE/hopq/hns built by
  `mkDpLiftBundle`; per-entry proofs assembled by `mkForallMemProof`'s
  `List.forall_mem_cons` chain), `dpLiftProof` (defeq lift-fact +
  ONE `dpLiftF_sound` instantiation). Wired into `dischargeSpine` /
  `dischargeClose` (both DP discharge paths).
- `dpValProof`'s per-node `mkAppM` chain is DEAD on the discharge path;
  it retains non-discharge consumers (totality walk, TP-corollary
  instantiation, congruence-arg values) — retire when consumer-free
  (follow-up).

### Fragment B — as built (`ACL2Lean/Replay/ClausifyBridge.lean`)

- `clausifyPure` moved in and made TOTAL (D-B3); returns ONE clause's
  literal list (D-B2 corrected).
- Helper ladder: `not_evtrue_disjoin_nil`, `evtrue_quoteT`,
  `evtrue_disjoin_cons` (uniform cons characterization),
  `evtrue_disjoin_append_elim`; `dumbNegateLit_eq` (shape-driven);
  `lifts_leaf_pos/neg`; `sound_neg_leaf`.
- Extraction layer (D-B4 refined): `dpOpqKeyOk` bans special heads by
  NAME in any package (matching `collectOpaques`); `dpOpqWF`;
  `dpLiftF_quote` / `dpLiftF_if_inv` / `dpLiftF_not_intro/inv` /
  `dpLiftF_app_none_of_banned_name` (the wrong-package refuter — those
  cases of the lemma discharge vacuously because the lift premise is
  refuted).
- `clausifyPure_lifts` — every clause literal lifts when the input does
  (11-case `clausifyPure.induct`).
- `clausifyPure_sound` — THE bridge lemma (11 cases): lift premise +
  `EvTrue (disjoinTerm (clausifyPure t pos))` ⇒ `ClausifyGoal t pos`
  (pos ⇒ `EvTrue t`; neg ⇒ t converges to nil). Value route is pure
  cond-algebra off `dpLiftF_if_inv`; IHs supply only nil/truthiness
  (G2/D9 honored — no exact-`t` anywhere).
- `bridgeClausify` rewired to ONE `clausifyPure_sound` instantiation
  (record validation unchanged); the peel/walk kit DELETED (~318 lines:
  `LeafFact`, `leafFiring`, `peelClause`, `walkPosT(Lit)`, the eight
  `val*` walkers). Dead walker-era lemmas cut from `EvalLemmas.lean`
  (`evtrue_if_fact_elim`, `toBool_false_of_nil`,
  `arg_truthy_of_not_nil`, `not_t_of_nil`, `cond_val_true/false`).

### Deviations from plan

- Step 2 of the sequencing (Fragment A "remaining consumers": TP
  instantiation) intentionally NOT migrated: the TP-corollary path
  consumes `dpValExpr` values inside an `Eq` statement, not a
  convergence fact — it is not a lift-fact consumer. Discharge spine +
  close were the real consumers; both migrated.
- `ClausifyGoal` carries the neg case as raw nil-convergence (not
  `EvTrue (not t)`). The neg case exists to make the mutual
  `clausifyPure` induction go through — the only driver instantiation
  is `bridgeClausify` at `pos = true` (the `EvTrue` case).

### Evidence

- Gate: `just ci` green, golden byte-identical, zero warnings.
- Axioms: `dpLiftF_sound`, `clausifyPure_lifts`, `clausifyPure_sound`
  all `[propext, Classical.choice, Quot.sound]`.

### Audit disposition (2026-06-12)

Single Fable agent, read-only, full surface (statement fidelity /
totalization fidelity vs the ACL2 sources / validation+frontier parity /
invariants+carve-out), per the audit-plan sign-off rule (MDD approved the
single-agent shape). **Zero critical, zero major.** Four minors, all
documentation accuracy, all fixed in the follow-up commit:

- A1 (minor): the D-A4 header claimed the old walker also rejected
  wrong-package PRIMITIVE heads — false (`conv_builtin1/2` dispatch by
  name); the new behavior is a deliberate fail-closed frontier
  narrowing. Comment corrected (`DpLift.lean`).
- A2 (minor): `dumbNegateLit` docstring overstated "the pure fragment"
  — ACL2's quote-fold and equal-nil arms are pure too, just unmirrored
  (divergence hard-fails at record validation). Docstring corrected.
- A3 (minor): `clausifyPure` joins sub-clauses with `++` where ACL2's
  `disjoin-clauses`/`add-literal` may dedupe or detect complements — a
  second divergence class beyond `expand-and-or`, previously
  undocumented and mislabeled "(expansion divergence?)" in two error
  texts. Docstring + both error messages corrected.
- A4 (minor): the as-built record mis-attributed `ClausifyGoal`'s neg
  case to `dischargeSpine` (it serves the induction only). Corrected
  above.

Affirmative verifications (auditor, anchored): validation parity — all
eight pre-existing `bridgeClausify` checks retained verbatim plus three
new gates; walker errors impossible-by-construction; `ClausifyGoal w env
t true` literally defeq `EvTrue w env t`; the D-B4 name/symbol matrix
closed (no non-vacuous mismatched lemma case); both `isDefEq` gates
fail-closed with the `mkEqRefl`+`mkExpectedTypeHint` kernel backstop;
all new `decide`/`mkDecideProof` uses are encoding side conditions
(carve-out intact); L1/L3 clean (grep: no concrete-world constants).
Noted parity deltas (accepted, fail-closed or sound-vacuous): the
wrong-package-primitive frontier narrowing (A1) and the empty-clause
input now discharged vacuously by `not_evtrue_disjoin_nil` instead of
the old `peelClause` hard error (degenerate input no corpus log
produces).
