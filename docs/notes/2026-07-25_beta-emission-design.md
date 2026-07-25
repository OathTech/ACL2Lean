# S2b design: completing the beta emission (sites 2–4) and the `:EQUIV` fix

Status: DRAFT — for MDD ratification before any fork edit.
Inputs: the S2 audit's four-site table (pattern map, S2 section); the three
S2b pin books (`p2-beta-quoted-actuals`, `p2-beta-preprocess`,
`p2-beta-equiv-iff`); `acl2/rewrite.lisp` + `acl2/induct.lisp` read
2026-07-25.

## Ground facts (read from the source, this checkout)

- **geneqv's runtime shape.** `nil` = pure equality. `*geneqv-iff*`
  (`rewrite.lisp:815`) = a singleton congruence-rule record with `:equiv
  'iff` and the anonymous fake rune. The general case = a LIST of
  congruence-rule records, each carrying `:equiv` (a symbol) and `:rune`.
  The relation a geneqv-maintaining rewrite establishes is the generated
  equivalence of the SET — for a multi-element geneqv no single symbol
  names it without computing a coarsest-common relation.
- **All four beta sites rewrite the body under the AMBIENT geneqv**,
  unchanged: `rewrite-fncall`'s lambda branch (`rewrite.lisp` ~20378), the
  all-quoteps fast path (~17337), and both `expand-abbreviations` lambda
  arms (`induct.lisp:384-389`, `:429-435` — `geneqv` passed through
  verbatim).
- **Existing `:EQUIV` emissions are single symbols** and the parser
  REQUIRES a symbol (`ProofLog.lean:475-479`; a non-symbol `:EQUIV`
  hard-fails as malformed — a list shape is a named parse failure today,
  fail-closed by construction).
- **The driver already fail-closes on non-EQUAL step equivs**: the G1 gate
  (`NodeCore.lean:1581`) throws "R-parameterized recipe pending (G1
  frontier)" for any `prov.equiv ≠ equal`. So an emitted `IFF` beta step
  turns the row into a NAMED frontier — no Lean-side work is required for
  correctness, only (later, S3) for coverage.
- **The twin defect**: `fncall/non-recursive` (`rewrite.lisp:20595`) also
  hardcodes `:equiv 'equal` over a geneqv-maintained body rewrite —
  identical class, pre-S2.

## The `:EQUIV` question — options

**A. Serialize the full geneqv** (new field, e.g. `:GENEQV ((IFF .
rune) …)`, on every body-rewrite step).
- For: maximal fidelity; exactly "emit what ACL2 has"; the S3 L2 lane will
  eventually want geneqv-shaped data.
- Against: a new parser field + provenance plumbing built AHEAD of any
  consumer (the banned build-now-wire-later pattern applies to our own
  layers even when the emission side is cheap); every one of the 65
  existing push sites would arguably want the same field for uniformity —
  scope explosion; and the single-symbol `:EQUIV` would coexist with it,
  two sources of truth.

**B. Emit the honest single symbol where one exists; the raw list where
not** (RECOMMENDED):
- `geneqv = nil` → `:equiv 'equal` (identity read, no computation);
- `geneqv = *geneqv-iff*` (structural `equal` against the constant) →
  `:equiv 'iff`;
- anything else → emit the equiv-name list verbatim, e.g. `:equiv (iff
  same-len2)` — which the parser REJECTS as malformed today, i.e. a loud,
  named frontier at exactly the inputs we cannot yet describe honestly.
  (If/when S3 wants these, THAT arc upgrades the parser; until then a
  user-equivalence beta context hard-fails at parse instead of being
  mislabeled.)
- For: no ACL2-side computation (two structural reads); single-symbol
  format preserved for the two cases that cover the whole current corpus;
  information is never wrong and never silently lost; the false-claim
  defect is gone.
- Against: the multi-element case produces a log the parser refuses — a
  capture-time-visible frontier rather than a graceful one. (Accepted:
  that is what hard-fail-at-frontiers means.)
- Rejected refinement: using `geneqv-refinementp` to classify. It answers
  "is X a refinement of G" (rule-applicability), not "what is G's
  generated relation"; using it to summarize would be computing a judgment
  the log doesn't record.

**C. Emit nothing; let the replay derive the required relation from the
congruence position.** Rejected outright: that is geneqv reasoning
re-derived in Lean — the checker-does-no-inference rule exists precisely
to forbid this.

**D. Keep `'equal` but suppress the beta step when geneqv ≠ nil.**
Rejected: suppression re-orphans the LAMBDA-BODY block under IFF contexts
— the exact mis-parenting defect S2 fixed.

Option B applies uniformly to: the S2 beta step (site 1), the new site-2/3/4
emissions, AND `fncall/non-recursive` (same helper, same batch). The two
existing 'iff-labeled push sites are already honest and untouched.

## Site-by-site emission plan (all reuse the `(:LAMBDA-BODY NIL)` rune)

1. **Site 2 — `rewrite`'s all-quoteps lambda case (~17337).** Same shape
   as site 1: the beta step after the body rewrite, `:origin
   'rewrite/lambda-body-quoted` (distinct origin, round-trip rule), plus
   the same saved-log-tail speculative-rollback pattern if this path has a
   rejection arm (to check while implementing; if none, no checkpoint).
   Flips the `p2-beta-quoted-actuals` nosig pin → update to a sig pin.
2. **Site 3 — `expand-abbreviations` lambda arms (`induct.lisp:384`,
   `:429`).** Emission at the point the lambda application is REPLACED by
   its expanded body: `:origin 'expand-abbreviations/lambda-body`, `:lhs`
   the application (args already expanded), `:rhs` the expanded body.
   NOTE the third arm (`:436-441`) KEEPS the lambda but swaps the
   rewritten body INTO it — that is not a beta; it needs either its own
   step (lhs/rhs both lambda applications) or a documented no-emit with
   the tree builder unable to mis-parent (to settle while implementing —
   the preprocess chain replay consumes these linearly, so a silent swap
   would break the chain's term threading loudly at the next step's
   navigate). Flips `p2-beta-preprocess`'s nosig pin.
3. **Site 4 — `:expand … :lambdas` (~12835 → rewrite-with-lemmas).** Same
   beta-step shape, `:origin 'expand-hint/lambda-body`. No corpus book
   reaches it; author a `p2-beta-expand-hint` book in the batch so the
   emission lands with its pin.
4. **`:EQUIV` fix** per option B on all of the above + site 1 +
   `fncall/non-recursive`. Flips the `p2-beta-equiv-iff` sig pin (its
   book's beta context is iff, so the fixed log reads `:EQUIV IFF` and the
   row becomes a G1-frontier FAIL instead of carrying a false claim).

## Replay impact (this batch — minimal by design)

- Site-1/2/4 steps under `equal`: already replay (`replayLambdaBody`).
- Site-3 steps: the preprocess-chain machinery needs a `lambda-body` arm
  mirroring the simplify-side recipe (bounded; the chain is linear).
- Non-equal betas: G1 frontier via the existing gate — correct and named.
- Golden: expect message-only churn plus possibly new-frontier rows on
  the defevaluator books (they contain iff-context betas); review via
  `just golden-review` as usual.

## Out of scope (unchanged queue)

MV-NTH DP-lift; SYMBOLP recognizer cells; SYNP preprocess shape; binder
arity > 2; the S3 L2 lane (which will consume `:equiv iff` steps and
retire the G1 frontier).

## Verification plan

Per fork edit: `just check-acl2-tags` → build → recapture-all → the three
S2b pins flip as predicted (update each to pin the FIXED state) → golden
review → `just ci`. Then the batch re-audit (new emission, per the S2
precedent).
