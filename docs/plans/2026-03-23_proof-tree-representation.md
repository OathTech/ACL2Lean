# Proof Tree Representation for ACL2 Trace Output

Created: 2026-03-23

## Context

We instrument ACL2's rewriter to emit a structured proof trace. A Lean
rewriter replays the trace to produce kernel-checked proofs. The current
trace is a flat sequence of REWRITE-STEP events with structural markers
(BEGIN-LITERAL, BEGIN-BRANCH, etc.). A Lean rewriter applies steps via
`replaceFirst` in a sequential fold.

This works for 96% of cases (357/371 across the sorting corpus) but
fails for 14 cases. The failures reveal that the flat model is an
inadequate representation of what ACL2's rewriter actually computes.

## What ACL2's Rewriter Actually Does

ACL2's rewriter builds a **proof tree**, not a flat sequence. At each
node, it makes a logical step (definition expansion, rule application,
type-alist resolution, IF branch selection) that is justified by a
specific mechanism (a rune, a type-prescription, a clause assumption).

Key structural patterns:

### IF branch processing is tree-shaped
When processing `(IF test left right)`:
1. Determine test's truth value (type-alist, assume-true-false)
2. If UNKNOWN: rewrite BOTH branches under different assumptions
   - TRUE branch: rewrite `left` with test assumed true
   - FALSE branch: rewrite `right` with test assumed false
3. Combine results via `rewrite-if1`

This is a tree with two sub-proofs under different assumptions.

### Definition expansion creates sub-proofs
When expanding `(f args)`:
1. Look up the definition body
2. Substitute actuals for formals
3. Rewrite the body (recursive sub-proof)
4. Return the fully simplified result

The body rewriting is a complete sub-proof. The outer step's result
incorporates all inner simplifications.

### Branch assumptions create scoped contexts
When a case split produces branches:
1. Each branch carries assumptions (e.g., `(EQUAL A X1)` holds)
2. The rewriter works under these assumptions (type-alist extended)
3. Variable substitutions from assumptions (via `find-rewriting-equivalence`)
   are scoped to the branch

### The fnstack prevents recursive expansion
When a function is being expanded, recursive calls to the same function
are blocked by the fnstack. Instead, `rewrite-solidify` is called,
which may find equivalences in the type-alist. This creates a situation
where the inner simplification path differs from normal expansion.

## Why the Flat Model Fails

The flat REWRITE-STEP model serializes the proof tree into a sequence.
This serialization is lossy in three specific ways:

### 1. Scope loss (14 → 11 cases fixed, 3 remaining)
Branch assumptions (e.g., `X1 = A`) are scoped to the branch. The
flat trace either doesn't record the assumption at all, or records it
at the wrong level. We added `find-rewriting-equivalence` logging
which fixed most cases by recording equivalence substitutions at
depth 0. But some equivalences fire at depth > 0 (inside definition
expansion) and are suppressed by the depth counter.

**Concrete example:** bsort `(bnext (cdr x)) = (cdr x)` from a branch
assumption. The equivalence is found by `rewrite-solidify-rec` at
depth 1 (inside bnext expansion). The depth counter suppresses it.
The outer definition step's RHS shows `(bnext (cdr x))` instead of
`(cdr x)` because the fnstack prevented recursive expansion, and
the solidification result isn't propagated.

### 2. Inner step leakage (6 cases)
Steps from inside definition expansions reference subterms that only
exist in the expansion intermediate, not in the literal. The depth
counter suppresses most of these, but some leak through because they
fire at the same depth level (e.g., from `rewrite-equal`'s internal
decomposition, or from IF branch processing which is lateral, not
deeper).

**Concrete example:** qsort `x-equiv` cases where `(memb x1 x-equiv)`
appears in logged steps but is NOT a subterm of the literal. These
steps come from inside the expansion of `rm` or `all-rel`.

### 3. Branch combination loss (7 cases)
When both IF branches are rewritten (the UNKNOWN case), the inner
steps from each branch are now suppressed (we added depth increment
for IF branches). But the combined result from `rewrite-if1` sometimes
requires additional simplification that isn't captured. The literal
ends up as `(IF 'NIL 'NIL 'T)` — a form ACL2 never explicitly
constructs — because the branch simplification steps were applied to
the wrong structural level by `replaceFirst`.

## Observations About the Right Representation

### The proof IS a tree
ACL2's rewriter computes a tree-structured proof. The English-language
output mode (`set-raw-proof-format nil`) describes this tree in prose:
"By opening up BNEXT and simplifying using CAR-CONS and CDR-CONS,
and using the hypothesis that..." Each sentence corresponds to a
justified logical step with sub-steps.

### Individual rewrites may only be justified in combination
Some transformations are only valid in context. A variable substitution
`X1 → A` is only justified within the scope of the branch assumption
`(EQUAL A X1)`. A `find-rewriting-equivalence` substitution is only
justified given the type-alist entries from the current proof context.
The granularity of logical justification doesn't always match the
granularity of individual term rewrites.

### ACL2's designers have reasons for each step
Every transformation ACL2 performs is justified by a specific mechanism:
runes (named rules), type-prescription (type-set inference),
executable-counterparts (ground evaluation), or clause context
(assumptions from other literals). Understanding WHY each step is
justified — at the level ACL2's designers intended — is key to
building a faithful extractor.

### The existing trace has tree skeleton
The structural markers already define tree structure:
- BEGIN-LITERAL / END-LITERAL — per-literal processing
- BEGIN-BRANCH / END-BRANCH — case-split branches
- IF-TEST-TRUE / FALSE / UNKNOWN — branch decisions
- CASE-SPLIT — branching points

The REWRITE-STEP events are leaves in this tree. What's missing is:
- **Scope information** — which assumptions are active at each point
- **Sub-proof boundaries** — where a definition expansion or rule
  application's sub-proof begins and ends
- **Assumption bindings** — which variable substitutions are in effect

## Current Implementation Status

### What works (357/371 = 96%)
- Depth counter suppresses inner steps (definition body, rule RHS,
  lambda body, abbreviation expansion, IF branches)
- Outer steps incorporate inner simplifications in their RHS
- `find-rewriting-equivalence` logged for variable substitutions
- Executable counterpart, type-set equality, recognizer, IF
  simplification, equal-self all logged
- IF branch processing suppressed with combined result logged

### What fails (14/371 = 4%)
- bsort: 1 case — fnstack + depth interaction
- qsort: 7 cases — IF branch combination loss
- qsort: 6 cases — inner definition expansion step leakage

### ACL2 code modifications
All modifications are in the `acl2/` submodule (branch `acl2-lean-output`):
- `rewrite.lisp` — ~20 logging points added, depth counter in
  `rewrite-entry` macro, `*structured-rewrite-depth*` variable
- `simplify.lisp` — ~10 logging points for literal/branch/clause events
- `axioms.lisp` — function registrations for `#-acl2-loop-only` code

### ACL2 code patterns discovered
- **rewrite-entry macro** (rewrite.lisp ~7038): central dispatch for
  all rewrite family calls. Manages `*deep-gstack*` restoration and
  `*structured-rewrite-depth*` increment/decrement. Detects inner
  rewrites by checking bkptr argument.
- **rewrite-solidify-rec** (rewrite.lisp ~4750): solidification path
  with two branches — `find-rewriting-equivalence` (equivalence
  substitution) and `obj-table` (type-set coercion). Both now logged.
- **rewrite-if-finish** (rewrite.lisp ~17277): IF processing with
  three cases — must-be-true, must-be-false, unknown. Each now logs
  and increments depth for branch rewriting.
- **rewrite-fncall** (rewrite.lisp ~19766): definition expansion with
  fnstack gate. When `being-openedp` is true, short-circuits to
  `rewrite-solidify` instead of expanding the body.
- **scons-term** (rewrite.lisp ~1499): term construction with special
  cases for IF evaluation, executable counterpart, and equal-self.
- **rewrite-equal** (rewrite.lisp ~17592): equality processing with
  type-set-based resolution.

## Possible Next Steps

### Option A: Proof tree events
Extend the trace with explicit sub-proof boundaries:
```
(:BEGIN-SUBPROOF :REASON :definition-expansion :FUNCTION bnext)
  ... inner steps ...
(:END-SUBPROOF :RESULT (cons (car x) (cdr x)))
```
The Lean rewriter would process the tree recursively, applying the
sub-proof's result at the parent level.

### Option B: Enriched flat sequence
Keep the flat sequence but add enough metadata to reconstruct the tree:
- Each REWRITE-STEP carries a `depth` or `scope-id` field
- CONTEXT-SUBST events carry the branch they apply to
- A `COMBINED-RESULT` event after sub-proof sequences captures the
  net effect
The Lean rewriter remains a fold but uses scope metadata to decide
which steps apply.

### Option C: Reconciliation pass
Post-process the flat trace in ACL2 (raw Lisp) to verify composability.
Simulate `replaceFirst` and emit bridging steps where the flat sequence
doesn't compose. This is a pragmatic fix that achieves 100% coverage
without redesigning the trace format.

### Option D: Hybrid
Use the depth counter and accurate logging (current approach) for the
96% that works. For the 4% that fails, emit enriched events that
capture the sub-proof structure needed. This avoids a full redesign
while handling the edge cases.

### Considerations for any approach
- The Lean rewriter should remain as simple as possible — ideally a
  fold or tree traversal, not a search or backtracking procedure
- Every step/node must have a single justification (rune or mechanism)
  that the Lean soundness proof can verify
- The ACL2 side should emit accurate, complete information — the Lean
  side should replay mechanically, not make decisions
- The trace should be technique-independent on the ACL2 side — emit
  what happened, not how Lean should process it
- ACL2's English output mode may provide insight into the logical
  structure ACL2's designers intended
- The existing structural markers (BEGIN-BRANCH, IF-TEST, etc.) are
  the skeleton of the proof tree and should be preserved/extended
