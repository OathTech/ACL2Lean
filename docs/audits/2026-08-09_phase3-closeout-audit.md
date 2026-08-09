# Phase 3 close-out audit — branch mdd/phase3-r7b (a1f0e07..e7c59fb)

Run 2026-08-09 per the close-out charter's PRE-APPROVED plan
(`docs/plans/2026-08-08_phase3-closeout-charter.md` §4): two Opus
reviewers, the proven inside/outside pattern, decorrelated skeptical
briefs, over the whole branch. Ground truth first (claim-gate
TRUE_EXIT=0 at e7c59fb; both reviewers ran builds/greps themselves).
Findings verified by the coordinating agent before the fix round
(the two MAJORs re-checked verbatim at the cited lines).

## Reviewer verdicts (summary)

- **Inside** (fidelity to sources/process): ~20 independent
  verbatim comparisons of D5 constants, gz_def bodies, witness kits
  vs the emitted artifacts — ZERO transcription drift. The golden
  re-pin verified row-by-row as a pure-removal delta with the
  mechanism confirmed from first principles (no offer-derivation
  change in the branch diff, so a cond could not have vanished by an
  offer disappearing). The FI offer derivation's verbatim
  `substFnCalls σ f == hypI` check and the exactly-one match on
  `(name, subst, formula)` judged "the correct fix for the cache-key
  class". All 11 static ci gates re-run green.
- **Outside** (right-thing-at-all): "The work is the right thing.
  The alias-world composition is a genuine object-level rendering of
  ACL2's functional-instantiation step, it is route (a1) as ratified,
  the substitution and instance are checked verbatim against the
  emission, the constrained-scope statements carry no witness
  vocabulary, the boot-rule re-pin is clean and correctly grounded in
  axioms.lisp, and the two capstone statements are the real theorems.
  Nothing found weakens a statement or fakes a result."

## Findings and dispositions (fix round applied 2026-08-09)

CONVERGENT MAJOR — **M1 (inside) / O-4 (outside)**: the AtCanonical
docstrings (`EquisortParametric.lean` section header + both constant
docs) claimed "every premise discharged" / telescope satisfiability
while the live elaboration keeps TWO premises; the `Macro.lean`
dispatch doc claimed undischargeable premises hard-fail while the
implementation keeps them (D6). **FIXED**: docstrings corrected to
name the two KEPT hypotheses and state that full satisfiability is
NOT yet established; the dispatch doc now describes the keep
discipline.

**M2 (inside)**: two stale comments in `Tests/Coverage/Harness.lean`
described the usefi callback and the pre-pass as DISABLED while both
are live (they documented the reverted 265139c/3072bd2 state); an
inert `if false` guard survived. **FIXED**: comments corrected, dead
guard removed.

**O-1 / m1 (convergent, MAJOR-adjacent framing)**: the recorded
`:CONSTRAINT-CL` chain is VALIDATED (endpoint must be 'T) but its
proof term is discarded (`Core.lean` useHint arm); the obligations
enter premise-wise via the parametric telescope. Not unsound, not the
banned shortcut (strictly more replayed content, not less), but a
route difference from the a1 bullet's wording. **FIXED (disclosure)**:
route note at the discard site; erratum appended to the Phase 3 exit
report; flagged as an open question for the compositional-replay
ratification.

**O-2 (minor)**: Class-2 consumer-rule lookup was first-match with no
uniqueness check. **FIXED** (with an honest incident): the first fix
refused ANY multiple match and broke both capstone rows in the gate —
the rule pool legitimately carries byte-identical copies of one rule
via the own/cross channels (the audit's "not live" call was right for
distinct rules, wrong for duplicates). Refined to `eraseDups` first,
refusing only ≥2 DISTINCT same-shaped rules; the capstone book then
rebuilt byte-identical to the golden.

**O-3 (minor, disclosure)**: `QSORT-IS-ISORT` assumes
`rule:HOW-MANY-QSORT` — one of its own FI constraint obligations,
green as a row in the same sweep (the known green-as-row /
assumed-as-dependency gap, `Provers.lean` D1-registry note);
`MSORT-IS-ISORT` has no analogue, so the capstones are not of equal
strength. **DISPOSED**: disclosed here and in TODO; the
mirror-registry application is the tracked fix.

**O-5 / m6 (minor)**: the D5 justification prose over-claimed —
FOLD-CONSTS-IN-+ is a certified-book theorem (not boot/skip-proofs),
and the LEXORDER flag cited the LexorderOrder theorems as the
fidelity anchor when they are internal properties (agreement is the
differential corpus's job). **FIXED**: D5 admission criterion
restated as two classes (boot-skip; owning-book-outside-corpus, with
the capture as FOLD-CONSTS-IN-+'s retirement path); flag text
corrected in the gate script and GzRules header.

**m5 (minor)**: `check-gz-agreement.sh`'s name character class
silently dropped `$`-names (PAIRLIS$ exists in the corpus; not
builtin-named, so no live miss). **FIXED**: extraction now matches
any non-space token.

**O-6 (minor)**: the gz-agreement gate is name-level; the ten new
lemmas are consumed nowhere, so a mis-transcription would pass ci
(the inside reviewer independently verified all ten bodies verbatim).
**DISPOSED**: gate limitation documented in the script and the
deferral log; content-level pin tracked as follow-up.

**m2 (minor)**: `ParametricInstantiate.lean` swallows attempt
failures broadly instead of the N1 `isFrontierErr` discipline. Every
swallow degrades only to an honestly-KEPT premise (both reviewers
checked no wrong proof can result); blanket adoption of N1 here would
turn legitimate cost-bound failures (heartbeat/rec-depth) into hard
build failures. **DISPOSED**: documented as a deliberate trade-off at
the dispatch site; the deferral log's blocker attribution annotated
as coming from an instrumented run.

**m3 (note)**: the "must inhabit the binder type" isDefEq guard is
vacuous on bridge paths (mkExpectedTypeHint makes it true by
construction); the real gate is the kernel at addDecl, which runs.
No change.

**m4 (minor)**: cache-key relatives hunt — three findings, all
fail-closed today (collisions surface as row FAILs at Meta.check/
addDecl, never silent wrong proofs): (a) the prepare cache's 64-bit
formula hash (σ-dropping verified safe), (b) three sanitize-based
addDecl name keys without the Macro-style collision guard,
(c) runeKey-based row-parameter resolution with asymmetric dedup
order between prepare and row sides (not live in the current corpus).
**DISPOSED**: (b) tracked as follow-up hardening; (a)/(c) noted.

**m7 (minor)**: TODO/deferral-log said "ALL EIGHT" constraint
premises; the emitted `(:CONSTRAINTS …)` events carry SIX per scope.
**FIXED**: wording corrected ("all six per constant").

**n1 (note)**: nothing pins the AtCanonical KEPT inventory (a silent
regression from 2 to more kept premises would pass ci). Tracked with
the capstone-row statement-pin follow-up. **n2 (note)**: dead code at
the totality-conv argument list. **FIXED** (removed). **n3**:
budgets/tstack judged cost sizing, not correctness masking — no
finding.

## What the reviewers could not verify (carried forward honestly)

Neither re-captured from ACL2 (all "emitted" claims are against the
committed corpus; provenance gates green). Neither audited the
FnAlias proof BODIES (~1400 lines of structural induction) — the
statements and all use sites were checked, the kernel accepts them,
and they are sorry-free; a dedicated proof-level review of
`aliasArgsSimple`'s sufficiency remains open. The inside reviewer
could not verify the KEPT-premise blocker attribution from the build
(see m2 disposition). `evalOpt`'s fidelity to ACL2 (the standing
trust note) is assumed throughout and remains policed differentially.
