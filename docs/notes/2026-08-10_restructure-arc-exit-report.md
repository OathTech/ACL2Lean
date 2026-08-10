# Equal-descent restructure arc — EXIT REPORT + merge proposal

Charter: `docs/plans/2026-08-10_equal-descent-restructure-charter.md`
(scope ruled by Mike: restructure + leftovers). Branch
`mdd/equal-descent-restructure` off main @ db44b96. The charter's exit
criterion is met: items 1–3 landed or honestly logged at named walls,
item 4 review-logged (the pending ruling is success by the exit
terms), item 5 done or logged, the audit run/verified/synthesized,
the fix round applied, the exit gate TRUE_EXIT=0 with the arc's first
in-repo gate artifact.

## Scoreboard

**110/116 corpus (45 unconditional + 65 conditional); sorting 74/78;
bsort 7/8 (+ termination:BSORT ✓).** Arc start: 106/116, sorting
69/78. Five bsort rows flipped red→green; after the audit fix round,
HOW-MANY-BAD-PAIRS-BNEXT's row is UNCONDITIONAL of its own rule
(`cond[total:BNEXT, tp:HOW-MANY-SMALLER, tp:BNEXT-SIZE]`) — the
audit's convergent defect made the arc's headline row STRONGER.

## Queue disposition

1. **Extract — DONE** (46ac66b): `replayEqualDescent`,
   behavior-preserving, byte-identical sweep, full gate.
2. **Recursive extension — DONE** (0cbfe35): per-phase outcomes,
   the four decision arms, nested descents with enclosing-record
   cross-checks, the rewrite.lisp outcome table verbatim including
   the negative-side *t* discard (the prior audit's C3 asymmetry,
   now reachable and mirrored). Both exit auditors verified the
   table against upstream and the artifact; the nested arm is
   exercised by the newly-green row. HOW-MANY-BAD-PAIRS-BNEXT ✓.
3. **Cascade — DONE at two named walls.** termination:BSORT ✓
   (the `<`-headed linear premise + the comm goal-prep) → the three
   μ-route rows ✓ (recorded scheme, decrease decoded from the
   replayed admission — audit-verified never-assumed).
   ORDEREDP-WHEN-BNEXT-CONSTANT burned five walls and is LOGGED at
   the named 2e wall (expansion detail chains carry an IFF-class
   step; the composition needs nil-equivalence weakening at
   BOOL-tolerant positions — its own sub-project; gates nothing).
   BSORT-IS-ISORT stays ASSUMED (fi-self) — its bridge advanced one
   wall (linear: threading landed; the W3 one-hyp premise lift is
   the named ✓ path).
4. **Leftovers fork batch — REVIEW-LOGGED (the carried user gate):**
   `docs/notes/2026-08-10_leftovers-fork-batch-review.md` — item E
   (emit/dedup-drop), item F (entry-derivation provenance), item G
   deferred. PLUS, from the exit audit: the admission-clause rune
   channel (DEFECT 2's emission half) is a natural additional item
   for the same review.
5. **Small leftovers**: the claim-gate artifact landed
   (.gate-runs/<sha>-<utc>.log; this arc's exit gate is the first
   recorded one); navigateFrames validation and the DP-scan breadth
   stay logged — the latter now a SHARPENED ratification question
   (the audit's rune-blind finding, with the leaf-rune-gating +
   emission direction).
6. **Exit audit — DONE** (2 Opus, inside + outside; synthesis:
   `docs/audits/2026-08-10_restructure-arc-audit.md`). Convergent
   DEFECT 1 (the linear self-offer vacuity — the family's third
   instance) FIXED by the self-gate, verified equivalent to the
   outside reviewer's own guard experiment; identityLiteralItem
   provenance-gated; the prefix discharge's dropped-tail class
   check added; applyPreparedUseFi's linear key made
   exactly-one-or-refuse; the gate recipe hardened. Statement pins
   for the four new greens QUEUED (the audit hand-verified all four
   goal terms against the ACL2 source meanwhile).

## Open user gates carried out

1. The leftovers fork batch (items E, F, + the rune-channel emission)
   — item-by-item review.
2. The DP-scan ratification question (sharpened).
3. (Standing, from earlier arcs): the R-lane rung-3 Lean lane; the
   tau middle-path charter's scout.

## Named continuations (no gate)

The 2e detail-chain composition (ORDEREDP-WHEN-BNEXT-CONSTANT — the
last bsort row); the W3 one-hyp premise lift (BSORT-IS-ISORT's ✓);
the statement pins with linear-hyp helpers; HOW-MANY-RM-GENERAL's
tau leaf (rides the tau charter).

## Merge proposal

The branch is ready to propose: charter executed end-to-end, every
claim point full-gated (this exit gate with an in-repo artifact),
goldens reviewed row-by-row at each re-pin (the only cond-set change
in the fix round was the STRENGTHENING of HOW-MANY-BAD-PAIRS-BNEXT),
the audit synthesized with every DEFECT dispositioned in-arc. Per the
standing rule I am NOT merging — this is the report-and-ask. If
approved: fast-forward local main; pushes remain yours outside the
sandbox (fork remote unchanged this arc — no fork edits were made).
