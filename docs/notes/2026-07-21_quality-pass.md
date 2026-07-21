# Quality / de-dup / optimization pass (2026-07-21)

Branch `mdd/quality-pass` off main a84fb31 (post qsort-frontiers arc).
Bar for every de-dup increment: behavior-preserving, golden BYTE-IDENTICAL,
ci green. Perf increments: measured before/after on the runtime focused
replay (`just replay` per-theorem ms — Lake-cache-proof).

## Survey (clone census, 2026-07-21)

| # | Pattern | Sites | Disposition |
|---|---------|-------|-------------|
| C1 | chain-continuation idiom: `match rest?/chain? with \| none => x \| some p => fuel_chain_eq/evtrue_of_fuel_eq` | ~35 across Driver/ | EXTRACT (Q1): `chainWith`, `chainOptWith`, `evtrueWith` |
| C2 | lift-and-continue tail in replayRewritesWith arms (emitCongruence → recurse → chain) | 5 | EXTRACT (Q2): `liftAndContinue` |
| C3 | nil-cast plumbing `re_val_cast [t, v(t), nil, p(t), hf]` | ~8 of 27 re_val_cast sites share the exact shape | EXTRACT (Q2): `castConvToNil` |
| C4 | quote-term SExpr spellings in EvalLemmas statements | dozens | REJECTED: lemma statements must stay syntactically stable for mkAppM unification; churn risk ≫ benefit |
| C5 | litFacts/segFacts transport loop | 1 (already unified in arc inc-7) | none needed |
| C6 | falsity/vacuous/const-collapse/closer helpers | done in arc inc-8 | — |

## Perf baseline (runtime focused replay, qsort book)

HOW-MANY-APPEND 18539 ms; ALL-REL-FILTER-1 16995 ms; ALL-REL-RM-2
12813 ms; TRUE-LISTP-QSORT 10694 ms; HOW-MANY-FILTER-1 9160 ms;
buildTotalEnv (lazy) 8930 ms; ALL-REL-RM-1 6329 ms; PERM-QSORT 5713 ms.

Optimization candidates to investigate (measure before touching):
- P1: `proveByDecide` on the concrete reflected world (`proveNoShadow`,
  `quoteTFact`, no-shadow facts) — kernel-decides a 200+-entry DefMap
  lookup PER CALL; candidate for a per-run cache in ReplayConfig.
- P2: `replayExecGround`'s `isDefEq` kernel reduction of `evalOpt F w e t`
  at large F on the reflected world.
- P3: repeated `pinTermOpaques` sweeps (34 call sites; idempotent but
  each walks the term).

## Increment log

- **Q1** (f48266a): chainWith/chainAfter/chainOptWith/evtrueWith — the
  optional-chain threading idiom, ~20 hand-rolled copies replaced.
  Golden byte-identical. Rider: check-push-ready guard (the fork-push
  incident).
- **Q2** (51430c4): castConvToNil + peelToLast — nil-cast plumbing and
  residual peel loop (3 copies + vacuousResidualClose rebased). Golden
  byte-identical, zero warnings.
- **P1**: proveByDecide memo cache (IO.Ref, keyed by the whole Prop
  Expr — pointer-eq fast path keeps world-embedding keys cheap; only
  successes cached; different worlds → different keys, no cross-book
  leakage). MEASURED (quiet machine, runtime focused replay, qsort
  book): instrumented baseline showed 3869 calls / ~3.4 s inside
  HOW-MANY-APPEND alone and ~8.4 s cumulative by ALL-REL-FILTER-1.
  After: ALL-REL-FILTER-1 16995→14897 ms (−12%), TRUE-LISTP-QSORT
  10694→8794 (−18%), ALL-REL-RM-2 12813→11445 (−11%),
  HOW-MANY-FILTER-1 9160→7812 (−15%); HOW-MANY-APPEND unchanged (first
  theorem = cold cache, fills it for the rest).

## Deeper profiling breadcrumbs (for a future perf arc)

One instrumented run (contended, treat shapes not absolutes):
HOW-MANY-APPEND ≈ 22-40 s total, of which Meta.check ≈ 2.8 s and
proveByDecide ≈ 3.4-4.7 s — i.e. the DOMINANT cost is MetaM proof
CONSTRUCTION (mkAppM elaboration, dischargeSpine/dpLift defeq,
replayExecGround isDefEq at large fuel), not kernel checking. P2/P3
(replayExecGround reduction, pinTermOpaques sweeps) remain unmeasured.
