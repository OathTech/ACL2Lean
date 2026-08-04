# equisort-r6 sub-arc — audit (2026-08-04)

Branch `mdd/equisort-r6` (d102d72..ba11422), close-out Phase 4. One
adversarial Opus reviewer. Verdict **NOT-READY** — the second NOT-READY
of the close-out arc (stop-early condition 6 class), with a SOUNDNESS-
ADJACENT finding. Remediation applied same-day (recorded below); the
DESIGN CHECKPOINT (F3) is stopped for MDD.

## The two critical findings (both verified mechanically)

- **F1 CRITICAL.** The BUG-019 pin book cov-encapsulate was GREEN AGAIN
  at HEAD (2/2, `cond[total:CF, ASSUMED:dp-fact]`) — the telescope
  commit (6540192) re-opened the false-green class and was never re-run
  against the pin book, which sat OUTSIDE the sweep (gate-invisible).
  docs/BUGS.md's BUG-019 evidence was false as written at HEAD.
- **F2 CRITICAL (machine-checked).** The constrained-fn totality
  hypotheses are stated at the CONCRETE world where those fns have no
  definition — `evalOpt` diverges, so the hypothesis is UNSATISFIABLE
  (the reviewer proved `totalHyp → False` in a scratch Lean file).
  Every row green through such a hypothesis is VACUOUSLY true — the
  BUG-019 failure mode one level up (statement vacuity). The same holds
  for `rule:` hypotheses about constrained fns at the concrete world.
- **F3 HIGH (design deviation).** The telescope was a CONCRETE-WORLD
  PROXY for ratified option (a) (`∀ w, ConstraintsHold w → …` over an
  ABSTRACT w with the EMITTED constraint formulas as the premise
  surface). The commit reframed the watch item instead of stopping:
  λ-abstracting an unsatisfiable premise at a fixed world is not the
  parametric statement, and the emitted `:CONSTRAINTS` formulas were
  consumed by nothing. Condition-1 discipline called for a checkpoint.

## Other findings

- F4 MEDIUM: 3 of the +5 sweep DP-leaf greens were conditional on the
  unsatisfiable witness-fn convergence hypotheses (printed, but blended
  into the ✓ tally). Resolved by the revert.
- F5 MEDIUM (fixed): the ba11422 diagnosis named the WRONG fork arms —
  the unrecorded `(EQUAL s1 s2) ⇒ 'NIL` collapse is the
  ASSOC-TYPE-ALIST arms at rewrite.lisp:18348-18354 (silent
  *ts-t*/*ts-nil* returns), not the equalityp arms at 18428/18434;
  tagging only the latter would not unblock the rows. TODO corrected;
  the fork-batch item now covers both.
- F6 LOW-MEDIUM (recorded): `Development.scopes` silently drops
  nested-scope sigs and lacks a depth gate on `.constraints` —
  fail-closed today (no corpus artifact nests), but a hard-fail at
  depth>1 is owed per never-silently-skip.
- F7 LOW (recorded): witness TPs now flow into `cfg.gzTps`, inert only
  via the builtinIntTps whitelist — exclude explicitly.
- F8 LOW: two commit-message overstatements (10/12 not 12/12 rows fail
  at witness-unfolding; the watch-item evidence was weaker than stated
  because the walk ran under contradictory premises).

## Verified-good (the increments that survive)

- `Development.toWorld` excludes witnesses by construction; witness
  admission data never reaches the totality prover; no cross-book leak
  (sorts-equivalent/qsort carry the sigs but no witnesses).
- Bracket balance + witness-outside-bracket hard-fails.
- The `equisort_scope_pins%` pin is truthful (3 scopes; the first is
  ordered-perms' own trivial encapsulate arriving via include-book).
- Drift test clean; no equisort-specific identifiers in the machinery.
- The narrow watch-item sub-claim holds: WEAK's recorded chain uses
  only constraint rules + CONVERT-PERM-TO-HOW-MANY + exec-counterparts
  — no `definition:SORTFN*` step (though see F8's weakening).
- The strong/weak wall diagnosis mechanism is verbatim-correct (the
  collapse is absent from the RAW emission, not dropped by recon).

## Remediation (same-day, this branch)

1. **6540192 REVERTED** — constrained fns get no concrete-world
   hypotheses; cov-encapsulate back to honest red (0/2, opaque CF);
   goldens and behavior restored consistently.
2. **cov-encapsulate ADDED TO THE SWEEP** (84/116) — the pin book's two
   honestly-red rows are now gate-visible; any green there is a
   statement-vacuity alarm.
3. **F5's fork-batch pointer corrected** in TODO.
4. **STOPPED for the MDD design checkpoint (F3)**: the parametric
   statement needs the genuinely abstract-world driver surface (or an
   MDD-ratified alternative); not built unilaterally.

Surviving increments (witness scoping, sweep entry, scope surface,
the wall diagnoses) remain on the branch; fold-back deferred to the
checkpoint's outcome.
