# tpthm-consumer sub-arc — audit (2026-08-04)

Branch `mdd/tpthm-consumer` (b770de1..58a8212), close-out Phase 3's
tail. One adversarial Opus reviewer. Verdict **READY-WITH-FIXES**;
required fixes F1/F5/F6/F7 + recommended F9/F10 applied in-arc (this
file records both).

## Ground truth the reviewer established

- Build/test/sweep green; golden byte-identical at 84/100; the target
  row's FAIL-message advance reproduced (the failure now throws
  DOWNSTREAM of the literal chain with both recorded nodes' effects in
  the reached term — "the recognizer wall falls" is supported).
- MATCHER sound under 11 adversarial probes: function-position symbols
  can never bind; QUOTE opaque; inconsistent bindings rejected; the
  duplicate-variable first-vs-last divergence is structurally
  impossible (σ.find? guards before prepending — σ never holds a
  duplicate key, so substTerm's first-match cannot diverge).
- BOTH anchoring gates hold under tamper (scratch copies): the cited
  rune removed → route does not fire; `:CLASSES` flipped to
  `(:REWRITE)` → offer refused. Independent, load-bearing.
- Telescope alignment verified by position (tpthm 9th in all four
  sites); no `tp:`/`tpthm:` prefix collision.
- Drift test PASSES (general arm; the only hardcoded names are the
  pre-existing trusted-core two-valued registry).
- Fidelity better than claimed: the hyp instance's relief consumes a
  REAL clause literal ((NOT (TRUE-LISTP Y)) is literal 5 of the input
  clause) — mirroring type-set backchaining, not a DP shortcut.

## Findings → resolution

- **F5 MEDIUM (fixed).** `tpThmSpecs` lacked the self-exclusion +
  strictly-earlier topological guard its `useSpecs` sibling got from
  the R7a audit (a theorem was offered its own statement; the sole
  defense was untrusted fork emission — the BUG-023 class). Guards
  added, and the fold's binder shadowing of the outer `cp` removed.
- **F7 MEDIUM (fixed — diagnosis corrected).** The 58a8212 wall
  diagnosis mis-aimed: the IF-collapse is a CONSUMER gap (the fork
  already emits `:IF-TEST-TRUE :ORIGIN IF-FINISH/IF-TEST` with its own
  justification runes; ProofTree discards IF-test markers), and only
  the `((equalityp rhs))` boolean case-restructuring arm
  (rewrite.lisp:18434-18440, untagged while its four neighbours emit)
  is a genuine emission-batch item. TODO corrected.
- **F6 MEDIUM (fixed — overclaim restated).** "The machinery is
  validated" was unsupported: the row FAILs, so nothing tpthm-built is
  kernel-checked and the discharge side is corpus-unexercised. The
  record now states exactly that; a green consumer row is the
  validation gate.
- **F1 MEDIUM (fixed).** The route's unchecked segFacts fallback was
  dead (litFactByTermChecked? already scans segFacts WITH the type
  check) and re-opened at source level the cross-env hole that helper
  closes. Deleted.
- **F9 MEDIUM (fixed).** The context-demand arm fired on all 26
  recognizer/true nodes; now gated on the node citing a
  :TYPE-PRESCRIPTION rune (26 → the citing nodes, zero behavior loss).
- **F8 MEDIUM (accepted, record).** The "unmatched demands are skipped
  harmlessly" claim was wrong AS A MECHANISM (the hoist consumer
  value-constructs demands with no try/catch); today's safety is that
  demands failing value construction never arise in-corpus. The F9
  gate bounds the surface; noted for the hoist-site hardening backlog.
- **F10 LOW (fixed).** QUOTE guard on the demand arm's inner
  application match.
- F2/F3/F4/F11/F12/F13 (LOW/nits) recorded in TODO as follow-ups:
  flattenAnd for conjunctive TP hyps; first-cited-only candidate
  selection; hard-fail :COROLLARY-bearing TP specs; the trusted-core
  registry's three diverged copies (extract); the tautological
  same-source formula assert; a docstring nit.

## Reviewer's could-not-verify

The dead-arm liveness under non-default transparency (argued, not
instrumented); the shared substN bridge (pre-existing); whether the
outer-IF fork site is absent vs suppressed; no axiom check for a
tpthm-carrying constant (none exists yet — F6).

## Fold-back gates

Fixes applied; behavior unchanged (10/13, same frontier — guards
only); claim-gate TRUE_EXIT recorded in the fold-back commit.
