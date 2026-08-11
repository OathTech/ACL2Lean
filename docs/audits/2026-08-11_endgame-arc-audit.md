# Sorting-endgame arc — exit audit synthesis (2026-08-11)

Two Opus reviewers (inside: faithful to our own sources/process;
outside: right thing at all, judged independently), decorrelated,
adversarial persona, primary-source-anchored. Both pre-approved at
goal-set per the charter. Findings verified/spot-checked by the
orchestrator before acting; dispositions below.

## Convergent positives (both reviewers, independently verified)

- **The three newly-green rows are CLEAN and NON-VACUOUS.** The
  outside reviewer independently hand-transcribed HOW-MANY-RM-GENERAL
  from the `.lisp` source and wrote its statement pin from scratch —
  it typechecked against the sweep's registered constant, axioms-clean
  (the strongest possible external check: the registered statement IS
  the ACL2 theorem under the standard translation, with exactly the
  one tp:HOW-MANY hypothesis, which is source-true). BSORT-IS-ISORT's
  15 premises each checked against sources: none is the goal, none
  false, no circularity (the goal `bsort=isort` appears in no
  premise); the old vacuous `usefi + fi-self` pair is GONE from row
  and pin. ORDEREDP-WHEN-BNEXT-CONSTANT character-exact vs source.
- **Two inference rungs genuinely retired** (the LEXORDER-ORDER
  kernel-order-axiom rung; the dedup inferred-from-shape trigger);
  scout F's refutation checks out against the artifact.
- **The fork edits are faithfully sited and rollback-safe**; the
  emitted `:TAU-BASIS` decodes correctly against ACL2's own defrec
  layouts (both reviewers decoded the real record independently);
  the golden's three re-pins verified diff-by-diff — no unreviewed
  row changed; the recapture provenance clean (91/91 at the pointer).
- **The new kernel lemmas say what their docstrings claim**; the
  liftability side condition on `dpLiftF_equal_self` is FORCED
  (kernel-checked decide, not optional); `clausifyPure_sound_sub`
  uses membership in the safe direction; the recorded-drop clausify
  relaxation cannot accept a wrong clause (single-split enforced
  before the drop logic; the kernel independently re-checks
  membership).

## DEFECT (convergent-style; fixed in the round)

- **D1 (inside 1): `ctx.dedupDrops` was not clause-scoped** — child
  descents reset `litFacts` but not `dedupDrops`, so an ancestor's
  recorded drop could license a skip in a descendant clause.
  Fidelity-only (the skip proof is a sound byCases regardless), but
  it defeated item E's per-clause read-off contract. FIXED: all 30
  child-descent reset sites now clear `dedupDrops` with `litFacts`.

## CONCERNs and dispositions

- **C1 (outside 4.1): the HOW-MANY-BSORT pin docstring was FALSE**
  (claimed the golden row shows rule:NOT-MEMB-…; it does not — the
  residual belongs to a different row in a different run config).
  FIXED: docstring corrected; the pin itself was verified correct.
- **C2 (outside 4.2): HOW-MANY-RM-GENERAL had NO pin** despite the
  arc plan covering it. FIXED: the pin added
  (Tests/SortingPinsEndgame), transcription per the outside
  reviewer's independently-verified shape.
- **C3 (outside 3.1): `consumeExpandDetail` locates the detail
  step's position (the emitters carry no `:PATH`) and silently
  tie-broke a both-branches match.** FIXED: the ambiguous case now
  hard-fails naming the `:PATH` emission follow-up (tracked in
  TODO); the position-location residual stands until that fork item.
- **C4 (inside 11 / outside 3.2): the positioned probe dropped the
  first `:PATH` frame on an unchecked convention.** FIXED: the
  dropped frame's fn must now name the literal atom's head.
- **C5 (inside 2 / outside 2a): the gz-trim deviation note's
  justification ("gz tau data is world-constant") is false in
  general**, and there is no Lean-side gz tau database standing in.
  FIXED: note reworded to the honest fail-closed statement (no
  corpus leaf needs gz implicants; a needing leaf falls to ASSUMED).
- **C6 (inside 9): the review doc promised a thrown frontier for a
  non-matching `:TA-ENTRY` that is not implemented** (the demand is
  skipped like every unresolvable demand, fail-closed). FIXED: doc
  corrected to describe the actual (sound) behavior.
- **C7 (inside 10): `allowRune` matches only :REWRITE/:LINEAR
  classes** — over-filtering, fail-closed. Comment added at the
  gate; tracked in TODO.
- **C8 (inside 15): no negative/tamper tests for the four new
  acceptance gates.** ATTEMPTED in the round: a p8-based dedup-gate
  tamper — found UNTESTABLE there (p8's drop rides the tautology
  path; the gate never fires on the only tracked log). Honest
  disposition: tracked follow-up — a dedicated pattern book whose
  clausify keeps a commuted duplicate without a complement close
  (the synthetic-books amendment's vehicle). The p8 pin and the
  golden remain the standing regression nets.

## Items for Mike (report-and-ask; NOT self-resolved)

- **M1 (inside 12 / outside 2b): the 2e implementation is not the
  ruled design.** The approved design was the nilEquiv weakening +
  the generalized walk lemma; what shipped consumes the recorded
  IFF collapse as a VALUE equality over EQUAL-headed carriers
  (strictly stronger as a relation, strictly narrower in coverage),
  with nilEquiv held as an unbuilt fallback behind a loud frontier.
  Both reviewers judge it sound and recorded-data-driven (the
  EQUAL-headedness is read off the step's lhs); the ask is explicit
  ratification of the substitution rather than inferred approval.
- **M2 (outside residual 4): the tau leaf-rune gate is FN-granular,
  not rune-granular** — the slice does not record which rules FIRED
  (exact-fired threading is the ruling's own named later
  tightening). Exit language states this plainly.

## Could-not-verify (carried honestly, both reviewers)

The corpus logs are gitignored (only p8 tracked) — stamps verified,
byte-level recapture equivalence not; the "ablation-verified" claim
for the tau premise has no artifact (it was a live experiment in the
session); pre-existing lemmas (`clausifyPure_sound`, `dpLiftF_sound`,
`evtrue_fnfree_agree_iff`, …) were read at call sites, not
re-audited; `evalOpt` fidelity and the `gen-world` wiring gap bound
everything and are unchanged by this arc.
