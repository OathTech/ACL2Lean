# Driver design: type, soundness, and sequencing

**Date:** 2026-06-07
**Status:** design conclusions from two independent theory reviews (one minimal-
context / first-principles, one grounded in the real artifacts; they converged).
Companion to `2026-06-07_schematic-replay-rule.md` (the per-node discipline) — this
note fixes the driver's *type* and the *soundness claim*.

## The plan (restated precisely)

1. Reconstruct a **proof tree** from the instrumented ACL2 proof log (clause
   waterfall + per-literal rewrite chains; runes, before/after terms, subst, IH
   links, type facts).
2. Define a **proof-producing driver**: a recursive function that, per node,
   emits a Lean `Expr` proving that node's claim — the driver *is* ACL2's proof
   rules reified as Lean proof-constructors (LCF-style derived rules). This is the
   standard proof-*reconstruction* architecture (cf. SMT-proof replay,
   Sledgehammer/metis), not proof translation and not an oracle.

## What it establishes (soundness claim — corrected)

A kernel-checked driver output establishes **exactly**: *the mirror proposition,
stated in `evalOpt` terms, is true* — **per theorem**. It is NOT a meta-theorem
("the encoding is sound"). Precise phrasing to use:

> A driver built only from kernel-checked per-rune lemmas emits only kernel-valid
> proofs of the mirror statement.

**Residual trust** (unchanged from CLAUDE.md's trust note): `evalOpt`-faithfulness
to ACL2, the mirror statement-builder, and instrumentation/reconstruction fidelity.
**Circularity to keep in mind:** `evalOpt` and the per-rune lemmas are *co-designed*
— they can be consistently wrong together, and **the driver succeeding does not
validate `evalOpt`.** Only two things break that circle: (a) the **native-theorem
bridge** (state the wanted fact in Lean's own semantics, kernel-prove it follows
from the mirror), and (b) **differential-testing `evalOpt`** against real ACL2 on
ground terms. Neither exists yet; until (a), "sound" is conditional on stages 5–6.

## The driver's type (the central decision)

**Two mutually-recursive layers**, matching the reconstruction's two layers
(`ClauseProof`/`ClauseNode` ↔ `ProofNode`/`LiteralProof`):

```
-- Γ : the proof context in scope at the node — an explicit structure, not just
-- the Lean local context, so the driver can LOCATE facts deterministically
-- (no search) and hard-fail when a needed fact is absent.
structure ReplayCtx where
  caseHyps   : List Hyp        -- case-split assumptions + negated sibling literals
  ih         : Option IHLink   -- the induction hypothesis (addressed by the tree's solidify→IH edge)
  typeFacts  : List TypeFact   -- type-prescription / type-alist (consumed from ACL2, not inferred)
  envBindings : List Binding   -- the induction value / variable bindings being threaded
-- (env is universally quantified INSIDE the claim, not stored in Γ)

-- Rewrite-detail node → a proof of an eval-equality:
replayNode  : World → (env) → ReplayCtx → ProofNode
            → Proof of  (∃ N, ∀ f ≥ N, evalOpt f w env before = evalOpt f w env after)

-- Clause/waterfall node → a proof of clause validity:
replayClause : World → (env) → ReplayCtx → ClauseNode
            → Proof of  (∃ N, ∀ f ≥ N, evalOpt f w env clauseFormula = some t)
```

**Node goal Props.** Rewrite node: a *fuel-robust, env-quantified* eval-equality
`∃ N, ∀ f ≥ N, evalOpt f before = evalOpt f after` (the `∃N ∀f≥N` form is required
so definition-unfold and transitivity compose despite fuel shifts). Clause/literal
root: `… = some t` (the equal-self wrapper turns the former into the latter).
*Eventually parameterize by the congruence relation* (`equal` vs `iff`/`equiv`);
the tree so far only uses `equal`, but leave room.

**Context flow — the answer to "does it return an updated context": NO.**
- Γ flows **DOWN** only, via **continuation-passing** at the structural nodes:
  induction builds the step-child's Γ (adds the IH + the `consp` case assumption);
  case-split adds the branch assumption. `acl2_induction_consp`'s
  `(base) → (step with IH) → ∀v, P v` shape already *is* this model.
- A rewrite node returns **only its proof**; it never extends Γ.
- Left-to-right *sibling* fact-accumulation (a later literal seeing an earlier
  one's result, the type-alist growing) is resolved during **tree reconstruction**
  — each node-record already names its full hypothesis set — so the driver stays a
  clean fold-down. (We already do this for the IH link.) Add an up-flowing return
  only if a genuine sequential dependency can't be pre-resolved; needing it is a
  smell that reconstruction is underpowered.

**The no-shortcut invariant (enforce the schematic rule at the type level).** The
*only inhabitants* of the rewrite-node claim must be the per-rune lemmas — do NOT
export any computational/`decide`/`rfl` proof of `∃N ∀f≥N, evalOpt f s = evalOpt f s'`
for symbolic `s`. Then "shortcut to the goal by computing values" is **not
expressible**, enforcing "mirror the tree, never shortcut" structurally instead of
by review. (This is the precise structural guard against the failure mode that has
recurred: computing-and-matching values / functionality.) Pair with per-node
type-ascription so a stuck node fails *locally*.

## Risks (and status)

- **Fuel-monotonicity of `evalOpt`** is a precondition for the whole substrate —
  already satisfied (`evalOpt_fuel_mono` / `evalOpt_ge_fuel`). ✓
- **Symbolic vs value substrate**: a value `evalOpt` replaying symbolic rewriting
  works *iff* claims are env-quantified fuel-robust eval-statements (not value
  computations). Compound-arg definition unfold — the one genuinely doubtful case
  — is now proven expressible (`evalOpt_substTerm_conv` + `evalOpt_unfold1_conv`).
- **"Driver stuck"** (missing rune handler, absent fact, exotic induction scheme,
  unlinkable IH) is **incompleteness, not unsoundness** — *provided it hard-fails*
  and never falls back to an eval-shortcut (which would be infidelity).
- **`Expr` blowup** on shared subproofs → `let`-bind in the emitted proof.
- **Undischarged trust hole (must close):** the functionality facts
  `h_mylen_fn`/`h_myapp_fn` are hypotheses the driver could never emit. Delete them
  (task #27); a green hand proof that still uses them is NOT evidence the plan works.

## Sequencing (what both reviews imply)

**Finish the schematic rework of the hand proof first; the driver is then "write
down the dispatch table that the reworked proof instantiates."** Per CLAUDE.md's
"there is no later where it gets validated," do NOT build the driver ahead of a
hand proof that is genuinely an instance of the schematic discipline. Concretely:
wire `evalOpt_unfold1_conv` into `node2a`; redo `node4c` as the IH-as-Γ-fact
(substitution lemma + `eval_equal_t_implies_eq`, no integer arithmetic); delete the
functionality facts; discharge #23 (type-prescription) and #24 (`fix` as a defined
function, which also de-collapses base `node3`). Then re-audit with the
driver-schematic dimension.
