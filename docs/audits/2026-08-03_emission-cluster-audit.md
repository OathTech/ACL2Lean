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

## Fresh verification (2026-08-03) — verdict: FOLD-BACK-WITH-FIXES

One fresh adversarial Opus verifier (no prior context), against the
nine-item list above, at repo 07e5616 / fork c93f8d5938. Six items
VERIFIED clean; three PARTIAL. It independently re-ran the full claim
gate with forced re-elaboration of all 17 include_str consumers
(TRUE_EXIT=0), confirmed golden byte-identity, confirmed corpus
bracket balance (12/12 bracket-carrying logs), and tamper-probed the
new enforcement (deleted END → unclosed-BEGIN hard-fail; deleted
BEGIN → stray-END hard-fail; both on scratch copies).

New findings:

- **N1 HIGH (item 1 incomplete).** The INCLUDE-BOOK path's
  `:empty-encapsulate` success exit (`other-events.lisp:9047`) emits
  no END — the newly-added include-path BEGIN is left unclosed, and
  the new invariant comment ("three success exits") is false: there
  are FOUR. Demonstrated empirically: an include-book'd
  `(encapsulate () (local (defthm …)))` captures BEGIN=1 END=0 on a
  clean ACL2 exit, and `dump-proof-tree` then hard-fails a LEGITIMATE
  pattern with the misdiagnosis "the encapsulate failed mid-capture".
  Same defect class the round was convened to close.
- **N2 MEDIUM (item 1 tail missed).** `pattern-map.md:99-103` still
  pins the OLD cov-defun-sk frontier message; the fix round never
  touched the file, and `check-pattern-map.sh` cannot catch prose
  pins going stale.
- **N3 MEDIUM (item 4 half-delivered).** `:CLASSES` is threaded only
  through the in-book arm; the include-book arm
  (`ClauseTree.lean:778`, `WorldEvent.includedTheorem`) drops it —
  and that is where the target consumers' data arrives
  (`PERM-IS-AN-EQUIVALENCE` is `:SOURCE :INCLUDE-BOOK` in qsort and
  equisort; all 542 include-book :DEFTHMs in qsort carry `:CLASSES`).
- **N4 LOW (item 6 second clause not done).** The `image-mtime`
  BSD-stat noise in `capture-proof-log.sh` was never fixed — all 89
  `.meta` sidecars carry a 6-line filesystem dump as the value
  (harmless to the line-anchored commit check, but malformed).
- **N5 LOW.** The banner cross-check is fail-open when a log has no
  banner line (currently all 89 have one).
- **N6 LOW.** A stale "ALWAYS balanced" / "the parser dedups" copy
  survives in TODO.md's historical worklist block (~:473-478),
  contradicting the corrected entry above it.

### Ratified remedy (this verdict's fix set — one more fork round-trip)

- a. END on the include-book `:empty-encapsulate` exit; invariant
  comment corrected to four success exits. Pin the pattern with a
  synthetic pattern BOOK (include-book'd local-only encapsulate) so
  the corpus exercises it permanently.
- b. Update the pattern-map cov-defun-sk pin to the current message.
- c. Thread `classes` through `WorldEvent.includedTheorem`.
- d. Fix the `image-mtime` stat call (falls out of the same
  recapture); make the banner check fail-closed (require a banner).
- e. Fix the stale TODO.md historical block.

Fold-back after: fix set applied, one rebuild + recapture +
row-by-row golden review, claim-gate TRUE_EXIT=0, and a targeted
mechanical re-check of each of a-e (narrow, file:line-checkable —
no fresh full audit needed for a fold-back-with-fixes verdict, per
the cross-rules precedent).
