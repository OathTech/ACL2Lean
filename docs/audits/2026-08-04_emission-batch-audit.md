# emission-batch sub-arc — audit (2026-08-04)

Branch `mdd/emission-batch` (054aecd..e020437; fork 24e6dbc138), the
MDD-approved fork batch (items 1/3/4) + its two Lean-side consumers.
One adversarial Opus reviewer. Verdict **READY-WITH-FIXES**; F5/F6/F7
fixed in-arc, F1/F2/F3/F4/F9/F11/F13 recorded in TODO (this file +
that record are the durable residue).

## Ground truth the reviewer re-ran

- `just claim-gate` → TRUE_EXIT=0 independently; the pre→HEAD golden
  diff is EXACTLY 4 lines (header 84→85, two message advances,
  HOW-MANY-BNEXT green); **the 5 recovered rows and every dependent
  cond set are byte-identical to pre-batch** — verified verbatim.
- All four emission classes verified as genuine READ-OFFS against
  upstream semantics — including that `find-rewriting-equivalence`'s
  geneqv-refinement + lambda guards make `(ffn-symb eterm)` the
  licensing relation and always a symbol; `geneqv` is the in-scope
  ambient parameter at the with-lemma site; `tterm0` is the translated
  statement `:FORMULA` untranslates.
- **HOW-MANY-BNEXT's green consumes the NEW emission** (the
  equal/type-alist-nil node at the exact if-test the pre-batch message
  named, followed by :IF-TEST-FALSE) — not a coincidental green.
- The case-split orientation re-derived (truth table) and traced on
  both real corpus instances (the lhs-variant's comm order correct);
  two-valuedness unspoofable (SExpr- and value-level checks).
- No cross-env hole in the equation-closure arm (the disequality goes
  through the type-checked lookup; wrong-context edges fail
  elaboration, never compose silently); loop termination bounded.
- **The process disclosure verified via reflog**: 08befc1 → 8298966
  was a MESSAGE-ONLY amend (identical trees) correcting a false
  TRUE_EXIT=0 claim to the honest RED record — the disclosure sentence
  in the commit is true.

## Findings → resolution

- **F5 (fixed).** `logic_equal_two_valued` was a verbatim clone of the
  pre-existing `logic_equal_t_or_nil` (identical statement AND proof)
  — the F11-class registry-drift recurrence. Deleted; the consumer
  uses the original.
- **F6 (fixed).** `logic_equal_nil_of_ne` was dead (advertised in the
  commit, used nowhere). Deleted.
- **F7 (fixed — comment).** The equation-closure arm is BOUNDED
  DETERMINISTIC SEARCH and its comment now says so (the target is
  never chosen by the search — the node's emitted verdict pins it;
  the search only finds a justification).
- F1/F2/F3/F4/F9/F11/F13 recorded in TODO (emission-only landings
  with named pending consumers; the corpus-unexercised
  equal/type-alist-t path; the stale emit/defthm tag text QUEUED for
  the next fork round; the fcons-vs-cons-term modelling brittleness;
  the rune-sharing dispatch note).
- F8 (accepted): 8298966's regression-class naming ("truthy arm") was
  imprecise — the actual class was the NIL verdict needing the
  disequality source; 6e23a10 built exactly that. Recorded here.
- F10 (accepted): exceptions escape the candidate loop (fail-closed
  but over-eager); revisit if a real artifact trips it.
- F12 (fixed by the TODO record itself).

## Reviewer's could-not-verify

The progn$-mv translation on ACL2's :logic reader path (empirically
fine — the idiom matches the pre-existing sites; all 91 logs
recaptured); an exhaustive rewrite.lisp sweep for silent
geneqv-weakening arms; the pre-amend BUILD state of 08befc1 (reflog
shows message-only); remote CI.

## Fold-back gates

Fix set applied; golden must remain byte-identical; claim-gate
TRUE_EXIT recorded in the fold-back commit.
