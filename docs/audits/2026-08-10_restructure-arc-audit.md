# Equal-descent restructure arc — audit synthesis (2 Opus, inside + outside)

Charter-ratified exit audit of db44b96..227fbd3 (the recursive descent
+ the bsort cascade, 106→110/116). Both reviewers adversarial against
primary sources; the outside reviewer ran a decisive guard experiment.
Dispositions follow each finding; the fix round landed in this commit.

## Convergent DEFECT 1 — HOW-MANY-BAD-PAIRS-BNEXT was conditional on
## its OWN :linear rule (vacuity class, third instance)

The linear offer surface (`linearSpecs`, Harness) had no self-gate —
unlike its tpthm:/use: neighbours ("ACL2 cannot cite a not-yet-admitted
rule") — and the end-of-book snapshot offers a theorem's own rule to
its own replay. `mkLinearHypType` of that rule IS the theorem
(env-schematic), so the row's registered statement was
`… → (∀ env', ⟦thm⟧) → ⟦thm⟧`-class. The outside reviewer RAN the
decisive experiment: with a one-line self-gate the row replays GREEN
with the circular condition GONE (the premise was never load-bearing —
the leaves close from the clause's own IH literal), every other row
byte-identical. **FIX (landed): the self-gate at the linearSpecs fold**
— the row now ships `cond[total:BNEXT, tp:HOW-MANY-SMALLER,
tp:BNEXT-SIZE]`, strictly stronger; the four consumer rows keep
`linear:HOW-MANY-BAD-PAIRS-BNEXT` as an honest D6 condition now
justified by a NON-vacuous row. The inside reviewer's arithmetic
independently confirmed the premise was gratuitous at both leaves.
This is the vacuity family's third instance (assumedDpFactCond,
ASSUMED:fi-self, now the linear self-offer) — the class note is
carried to the leftovers: any NEW offer class must ship with
self/chronology gates from day one.

## Convergent DEFECT 2 — the DP linear-premise supply is RUNE-BLIND

`replayDischargeNode`'s linear pass injects premises by max-term match
against obligation opaques, never consulting the leaf's recorded
`:RUNES` — it supplied the rule at two leaves whose recorded rune sets
do not (and could not) cite it, and the property that makes the
mechanism faithful held by accident at the one legitimate site (the
BSORT admission, which does cite the rune and records the hyp-relief).
NOT fixed this round: the honest fix (gate injection on cited runes)
hits the admission-path gap — verdict-only emitted termination clauses
carry NO rune channel — so this is folded into the standing DP-scan
RATIFICATION QUESTION for Mike (TODO), now with the concrete
direction: leaf-rune gating where a rune channel exists; emit the
rune channel for admission clauses in a future fork batch.

## Other findings and dispositions

- **identityLiteralItem's third disjunct was shape-only** (both
  reviewers): FIXED — provenance-gated to the verdict-class origins
  the descent's own dec? consumes (`equal/self`,
  `equal/type-alist-nil`).
- **prefixDischargeExtend accepted any syntactic prefix** (outside
  C5.1): FIXED — every dropped literal must be the trivially-nil
  `(NOT (EQUAL t t))` class (today's sole witness class); anything
  else hard-fails rather than being absorbed as monotone weakening.
- **applyPreparedUseFi's linear key was first-match** (inside N6):
  FIXED — exactly-one-or-refuse, the depMirrorProofAt discipline.
- **The claim-gate artifact recipe leaned on pipefail placement**
  (inside N7): FIXED — `${PIPESTATUS[0]}`.
- **Statement pins missing for the four new greens** (outside C3):
  QUEUED (needs linear-hyp pin helpers); the audit's own hand-check
  verified all four goal terms are the FULL ACL2 theorems, no
  weakening — recorded here as the interim anchor.
- **The cons-cons registry arm has no green consumer** (inside D2):
  ACCEPTED as-is with this note: the arm is on the direct path of the
  2e continuation (it executed during the failing row's wall
  progression — the row advanced THROUGH it before stopping at the
  detail-chain wall), i.e. consumer-directed, not speculative; it
  greens with 2e.
- **Descent scratch keying + positioned-arm position** (inside N9):
  logged as hardening candidates; mis-fires hard-fail rather than
  misprove.
- **TODO staleness on 0cbfe35's gate line** (inside N10): fixed in
  the TODO update.
- **Arc-tip full-gate gap** (inside C5): remedied structurally — this
  fix round's claim-gate is the arc's exit gate and the FIRST to
  produce a .gate-runs artifact.

## Verified solid (both reviewers, credit)

The recursive descent's outcome table is rewrite.lisp's cons-cons cond
verbatim (including the negative-side *t* discard, checked against
upstream and the artifact); the probe no-op provably drops only work
ACL2 itself discarded; the nested arm is exercised by the newly-green
row; assertDpEqualNilComm is anchored on upstream assoc-equiv; the
μ-route induction is the recorded scheme with the decrease decoded
from the replayed admission, never assumed; axioms on all five new
registered statements are the classical trio (verified by running);
golden tally arithmetic reproduces; bsort rows byte-match a live
replay.

## Reviewer could-not-verify (carried)

Full-corpus re-execution at tip (this round's gate covers it);
the 46ac66b/0cbfe35 gate claims (pre-artifact era — the .gate-runs
mechanism now closes this class going forward); instrumented
green-row-vs-red-row usage traces for the new spine closers.
