# Emission-cluster sub-arc audit (2026-08-03) — NOT-READY + the ratified fix round

Branch `mdd/emission-cluster` (657f6b2..3c3255d), the close-out arc's
Phase 1. One adversarial Opus reviewer; verdict **NOT-READY**; the
findings survived verification (mechanically demonstrated). The remedy
below was ratified by MDD the same day (Option A + the bundle). THIS
FILE is the durable record — a future iteration executes the fix round
from here, and a FRESH verifier re-audits against this list (the
original reviewer's context is gone).

## Findings (numbered as in the review)

- **F1 BLOCKING — `just ci` exit 1 at the "COMPLETE" commit.**
  `Tests/TamperTests.lean:45-50` (`mapItem`) lacks arms for the new
  `ClauseItem.fcDerivations` and narrows `.useHint` to 3 args (a
  3-arg pattern is NOT a wildcard over the optional 4th — Lean fills
  the default IN PATTERNS). The fidelity negative-guards were dark;
  `test`/`driver-coverage` never ran in ci. PROCESS FAILURE: the
  completion commit claimed "GOLDEN BYTE-IDENTICAL" against a red
  build (the golden claim itself was separately verified TRUE by a
  forced rebuild — but it was not ci-gated when claimed).
- **F2 HIGH — brackets NOT balanced; my three "always balanced"
  comments are false.** The `(:ENCAPSULATE-END)` at
  `other-events.lisp:9039-9046` sits in the INCLUDE-BOOK cond branch
  (`:8977`), mutually exclusive with the BEGIN's branch (`:8654`) —
  every include-book'd encapsulate emits END with no BEGIN (corpus:
  sorts-equivalent 0/13, qsort 0/11, isort/bsort/msort 0/1,
  equisort 2/3, cov-defun-sk 4/7). Also `:empty-encapsulate` is a
  SUCCESS exit (`:8786` → `:8162`) that skips END, and error exits
  leave open BEGINs.
- **F3 HIGH — the builder is fail-open on balance**
  (`ClauseTree.lean:808-822` rejects brackets only inside open
  theorem blocks; stray END/unclosed BEGIN accepted silently; a
  stray END even runs `closeBlock` and can mis-attribute an
  admission block — currently benign by luck).
- **F4 MEDIUM — nesting is real** (cov-defun-sk nests 3 deep, also
  unbalanced) and its pinned frontier message changed silently
  (pattern-map `2026-07-22_pattern-map.md:99-103` stale; the new
  bracket error also MISDIAGNOSES — the true cause is the pass-2
  :DEFTHM without :QED).
- **F5 MEDIUM — pass-1/pass-2 :DEFTHM duplication real and undeduped**;
  two present-tense "the parser dedups" claims are false
  (`ProofLog.lean:358-362`, `other-events.lisp:8685`). Dedup is
  Phase-4 work and must be recorded as such.
- **F6 MEDIUM — `:CLASSES NIL` indistinguishable from absent**
  (`ProofLog.lean` `.getD .nil`): `:rule-classes nil` is pervasive,
  so the ratified absence-vs-presence gating is unimplementable —
  needs `Option SExpr`, threaded into `Development` (today `classes`
  is discarded at `ClauseTree.lean:757,769,787`).
- **F7 MEDIUM — the literal-window fcDerivations branch is dead code**
  (probe: removing the filter arm leaves the sweep green; all 375
  corpus occurrences are clause-level) and its emission order is
  wrong if it ever fired.
- **F8 MEDIUM — provenance gate can't detect a stale image**: all 89
  banners name a DIFFERENT commit than the meta stamp (the image was
  saved 33s before the stamped commit); the gate never cross-checks
  the banner it has in-file.
- **F9 LOW — `:PARENTS` should use `collect-parents`** (pt TREES
  flatten; raw `tagged-objects 'pt` can hand a cons) and the emission
  drops `:fc-round`.
- **F10 LOW — `:FC-DERIVATIONS` silently absent when no log is open**
  (forward-chain-top also runs from induct/built-in-clausep/bdd) —
  the Phase-6 join-by-:CONCL consumer must HARD-FAIL on a missing
  join, never read absence as "no forward chaining".
- **F11 LOW — zero docs in the sub-arc** (this file remedies it).
- **F12 cosmetic — misplaced comment** (`ProofTree.lean:513-518`).

Verified CORRECT (keep): all four emissions are genuine read-offs
(lmi-lst alignment proven against the producer; constraint-lst
verbatim; fcd accessors per the defrec; raw rule-classes); golden
byte-identity real (forced rebuild); tag convention green; parity
registrations correct; the clause-level fcDerivations fix covered.

## The RATIFIED fix round (MDD 2026-08-03, "Option A + bundle")

One fork round-trip (rebuild + full `just recapture-all` + row-by-row
golden review), then a FRESH verifier re-audits against this list:

1. **Brackets structural (F2/F3/F4)**: add the missing BEGIN on the
   include-book path (mirror the END's branch); add END on the
   `:empty-encapsulate` exit; DELETE the three false "always
   balanced" comments and state the real invariant (balanced in any
   SUCCESSFUL capture; error exits abort the capture, and the parser
   enforces at EOF). Lean: `buildDevelopment` keeps a bracket DEPTH
   counter — hard-fail on stray END (depth 0) and unclosed BEGIN at
   EOF; nesting supported by the counter (pairing semantics still
   Phase 4). Fix the cov-defun-sk misdiagnosis ordering (the
   open-theorem check must fire for the :DEFTHM-without-:QED cause,
   not the bracket) + update the pattern map entry.
2. **TamperTests (F1)**: add the missing arms; then `just claim-gate`
   (see 7) must show TRUE_EXIT=0 before any completion claim.
3. **Dedup claims (F5)**: fix both false comments; record Phase-4
   dedup as an explicit open item in TODO.
4. **`:CLASSES` → `Option SExpr` (F6)**, threaded into
   `Development`/`WorldEvent` so the equivalence/congruence gates can
   consume it (consumption itself lands with its user).
5. **F9 in the same round-trip**: `collect-parents` for `:PARENTS`;
   emit `:fc-round`.
6. **F8**: `check-log-provenance` cross-checks the in-file banner
   commit against the meta stamp (script-only; would have caught the
   33-second skew). Also fix the `image-mtime` BSD-stat noise.
7. **`just claim-gate` (process)**: pipefail-honest full `just ci`
   printing `TRUE_EXIT=$?`; the standing rule (goal text + plan doc):
   no commit claims complete/green without its output.
8. **F7**: DROP the dead literal-window branch (keep the clause-level
   path); if a literal-window occurrence ever appears, it hard-fails
   loudly at the chain boundary instead — honest and covered.
9. **F10/F12**: pin the join-must-hard-fail rule in the Phase-6 TODO
   item; move the comment.

Fold-back only after: fresh verifier confirms each numbered fix,
claim-gate TRUE_EXIT=0, golden reviewed row-by-row post-recapture.
