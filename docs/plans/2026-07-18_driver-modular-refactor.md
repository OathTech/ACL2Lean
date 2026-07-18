# Driver modular refactor (perf-OODA WP2, aggressive) — plan

STATUS: DRAFT, awaiting MDD ratification. Branch `mdd/perf-ooda`.

Goal: `ACL2Lean/Replay/Driver.lean` (6,868 lines, three `mutual` blocks) →
per-recipe modules with an explicit recursion interface, so the most-edited
code (recipes, decrease fragments, the coming #37 rework) rebuilds in
seconds and new recipes land as additive FILES, not mutual-block insertions
(the L1-shaped open surface at the meta level).

Invariant for every stage: ZERO behavior change — coverage golden
byte-identical + `just ci` + diff-test 389/0 after each stage; each stage
is its own commit. No stage starts until the previous is gate-green.

## Stage 0 — knot audit (DONE 2026-07-17; read-only, no code change)

Method: mechanical intra-block call graph over the three mutuals with
comments AND string literals stripped (raw grep is misleading — e.g.
`replayRecognizer`'s apparent self/`replayRewrites` edges were all
`throwError` message strings and one doc comment). Every surviving edge
spot-checked as a real invocation.

### Call graph (real edges only; line = call site)

| mutual | member | in-block callees |
|---|---|---|
| #1 (1190–2423) | `replayRecognizer` | **NONE** (downward only; not even self-recursive) |
| | `replayDefinition` | `replayRewrites` (1385) |
| | `replayNode` | self, `replayRecognizer` (1695), `replayDefinition` (1689), `replayRewrites` (×6) |
| | `replayRewrites` | self, `replayNode` (2399) |
| #2 (3064–3106) | `dischargeSpine` | self, `dischargeClose` |
| | `dischargeClose` | **NONE** (downward only) |
| #3 (4175–5938) | `replayClauseSpine` | self, `composeSplit` (4487), `replayClause` (4532) |
| | `composeSplit` | self, `replayClauseSpine` (4865), `replayClause` (×2) |
| | `replayClause` | self, spine (5021) + all five processors |
| | `replayElim` / `replayGeneralize` / `replaySubsumed` / `replayEliminateIrrelevance` / `replayInduction` | `replayClause` (one site each; no self, no cross-processor edges) |

### SCCs (the true knots)

- **Mutual #1 SCC = {`replayDefinition`, `replayNode`, `replayRewrites`}**
  (cycle: node→definition→rewrites→node, plus node↔rewrites directly).
  **Freeable: `replayRecognizer`** (~123 lines) — moves above the mutual as
  a standalone def in Stage 1.
- **Mutual #2 has NO knot — it dissolves entirely in Stage 1**:
  `dischargeClose` becomes a plain def placed first; `dischargeSpine` is
  then a standalone self-recursive `partial def`.
- **Mutual #3 SCC = all 8 members** (every processor is called by
  `replayClause` and calls it back). Nothing freeable in Stage 1; this knot
  unties only via the Stage 2 callback interface. Minimal recursion surface:
  the five processors need ONLY a `clause` callback; `composeSplit` needs
  `clause` + `spine`; the residual tie is `replayClauseSpine ↔ replayClause`.
- The two knots are **independent layers** (file order: #1 strictly below
  #3; no upward reference is possible), so they can be untied separately.
- `dischargeRuleHyp` (6501), `replayProofConditional` (6653), `replayProof`
  (5942), `buildTotalEnv` (6108) are already top-level plain defs after the
  mutuals — no knot involvement, contrary to the pre-audit guess.

### Stage 2 `ReplayRec` fields (exact signatures, read off the source)

```
node        : ReplayConfig → ReplayCtx → ProofNode → Nat → MetaM Expr
rewrites    : ReplayConfig → ReplayCtx → SExpr → List ProofNode → Nat →
              List Nat → MetaM (Option Expr × SExpr)
clause      : ReplayConfig → ReplayCtx → ClauseNode → MetaM Expr
clauseSpine : ReplayConfig → ReplayCtx → String → List (Nat × SExpr) →
              List ClauseItem → List SExpr → List ClauseNode → MetaM Expr
-- composeSplit stays in the tie (called from one site, calls spine+clause)
```

### Section map → Stage 1 file split (line-boundary split is dependency-safe
by declaration order; the 5-way guess becomes 6 files + re-export root)

| lines | content | target module |
|---|---|---|
| 1–403 | reflection kit, goal builders, G2 congruence emitter | `Driver/Reflect.lean` |
| 404–2778 | ReplayCtx/Config, registries, value characterization, **mutual #1**, literal machinery | `Driver/NodeCore.lean` |
| 2779–3107 | DP discharge leaves, G3 fragment wiring, **mutual #2** (dissolved) | `Driver/Discharge.lean` |
| 3108–3515 | totality from admission (#37) | `Driver/Totality.lean` |
| 3516–3916 | preprocess replay + clausify bridge | `Driver/Preprocess.lean` |
| 3917–6802 | c3 induction scaffold, **mutual #3**, conditional-mirror harness, `dischargeRuleHyp` | `Driver/Core.lean` |
| 6803–6868 | importer front-end (`derive_world`, `findThm`) | root `Driver.lean` (with re-export imports) |

### `private` decls needing de-privatizing at the split (13 total, 6 cross-boundary)

Cross-boundary (drop `private`, keep in a `Congr`-style namespace):
`PathStep`, `asApp`, `navigateFrames`, `rebuild`, `applyStep` (Reflect kit,
used file-wide), `mkForallMemProof` (NodeCore → Discharge/Preprocess/Core).
Local-only (keep `private`): `pathStepsFromFrames`, `mkDefsGet`,
`mkValConvPropE`, `CaseTree`, `buildCaseTree`, `TestFact`,
`theoremsWithRulesGo`.

## Stage 1 — free the non-knot members
Move every non-knotted member out of its mutual (same file first — mutual
shrink only), then split the FILE at the existing linear section
boundaries: Reflect / ValueCore / Totality / Preprocess / Core (the 5-way
split), with `private` re-scoping as needed. Mechanical; golden-gated.

## Stage 2 — recursion interface
Define in a new `Driver/Recurse.lean`:
  structure ReplayRec where
    node   : ReplayCtx → ProofNode → Nat → MetaM Expr
    clause : ... (the replayClause entry)          -- exact fields from Stage 0
Each recipe becomes a top-level def taking `(rec : ReplayRec)`; the knot is
tied once in a thin `Driver/Tie.lean` (`partial def`s that instantiate the
structure). All meta-code is `partial`/MetaM — no termination obligations.

## Stage 3 — per-recipe modules
One file per recipe family: Definition, Recognizer (incl. two-valued
registry), RuleApplication, IfSimplification, Induction (+ a
`Induction/Fragments.lean` for decrease fragments — the #37 rework's home),
DischargeLeaves, Telescopes. Root `Driver.lean` becomes re-exports so all
existing imports keep working.

## Predicted loop after Stage 3
Fragment/recipe edit: its module (~200-600 lines, ~5s) + Tie (~1s) +
Runner (4s) + link (11s) ≈ ~20s; vs 55s today. Structural benefit: #37
rework and future fragments are additive files.

## Risks / mitigations
- Signature churn (every recipe + call sites): staged, golden-gated.
- `private` cross-boundary breakage: surfaced by the compiler; re-scope
  minimally, prefer namespacing over exposure.
- Elaborator commands (`derive_world`, `driver_mirror%`) reference driver
  internals: keep them in Core/Tie until Stage 3 proves stable.
- Perf regression from indirection: none expected (compiled closures), but
  the golden + a timed qsort focused run guard it per stage.

## Out of scope
EvalLemmas/Count (already separate), Runner/CLI (WP1), any behavior or
frontier change whatsoever.
