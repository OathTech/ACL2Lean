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

(appended as they land)
