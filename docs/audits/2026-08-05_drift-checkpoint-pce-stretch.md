# MDD CHECKPOINT — stop-early condition 2 (drift test) on the PCE stretch

**Declared 2026-08-05, plainly, per the arc plan's stop-early clause.**
Corroborating signal: the user's mid-run drift question ("we want to make
sure we're not drifting").

## What fired

The carve-out drift test (MDD-ratified 2026-08-02; agent memory + TODO):
"if we find ourselves writing custom proofs or checkers for each case …
we are not mirroring ACL2, but building custom search."

The stretch `e5eeab9..053e131` (this session's tail, all gated
TRUE_EXIT=0) added, while advancing ONE row
(PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS) through ~9
successive frontier classes:

- the literal-boundary IFF-normalization tower bridge (`bridgeIffBoolNorm`,
  moves A/B/C, 5 conv lemmas);
- the tlp-cdr demand emitter + `logic_trueListp_cdr` closure feeding
  move B;
- the single-summand positive-sum cell
  (`logic_equal_nil_of_plus1_nonneg1`) + a latent match-capture fix;
- the call-stack fold, L-orientation (`re_equal_t_fold_l`);
- the boolean-TP fold (`logic_equal_t_self_of_boolean_tp`) + wiring
  `bridgeEqualNilNormDeep` at the literal chain end;
- the last-position nil-drop with FOUR two-valued sources (EQUAL/NOT
  values, the emitted boolean TP, the literal 'T);
- the term-vs-sum disjointness cell
  (`logic_equal_nil_of_plus1_self_r/_l`);
- the type-set-equality orientation normalization (`logic_equal_comm`
  re-orientation).

Also flipped honestly green en route: TRUE-LISTP-BNEXT (the
complement-tautology close — 86/116). The PCE row currently sits at the
`replayElim` reorder-lift class — another distinct composition family.

## The honest assessment (both sides)

- FOR the additions: every one is keyed to RECORDED or EMITTED content
  (recompute-and-check toward the recorded result — the ratified
  `bridgeEqualNilNorm` precedent; TP facts consumed at pinned values;
  the demand-hoist reuses the existing fail-closed mechanism). Nothing
  infers what ACL2 did not record. Each mirrors a real unrecorded
  normalization ACL2 performs silently (add-literal, if-interp folds,
  cons-term folding, type-set disjointness).
- AGAINST: the per-class count grew by ~8 in one session chasing one
  row — the same TREND the consumer-queue audit's D8 measured and the
  July-31 consolidation was mandated to stop. Whether these classes
  CONVERGE on ACL2's bounded set of silent normalizations (rewrite.lisp
  3791/18089-93, add-literal, cons-term) or diverge per-example is the
  drift test's exact question, and the executing agent cannot
  self-certify it. The structural pressure (an exit condition
  unreachable without user decisions, plus an automatic continue signal)
  is precisely the condition under which per-case accretion happens.

## The decision (the user's, not the agent's)

1. **Scrutinize**: point the pre-merge audit's outside lane at
   `e5eeab9..053e131` specifically, with the drift test as its lens
   (the recommended default — the machinery is gated, byte-reviewed,
   and honestly recorded either way).
2. **Ratify**: accept the chain-end-bridge family as a named, bounded
   mirror class (ACL2's silent-normalization set), recording its
   closure criteria.
3. **Revert**: roll back part or all of the stretch pending the audit
   (each increment is an isolated gated commit; the TRUE-LISTP-BNEXT
   green at e5eeab9 stands independently of the later PCE-only pieces).

Work on the PCE row is STOPPED at this checkpoint. The arc's other exit
items (the fork batch review, the rung-3 checkpoint, the pre-merge audit
sign-off, the merge) are as recorded in the close report.
