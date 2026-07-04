# The branch-split spine (R1 W3) — design note

*2026-07-03. Status: DESIGN — the last structural wall before perm-cons's `*1/2`
subtree replays. Written after the node-family walls fell on
`mdd/perm-r1-frontiers` (commits 12038b0, 7de8af5).*

## Ground truth (the real artifact)

ACL2's `rewrite-clause` scans a clause literal-by-literal; after rewriting
literal `k` to `L'`, it **clausifies `L'`** into segments and recurses per
segment (`rewrite-clause-lst`, instrumented at
`acl2/simplify.lisp:7822` — `emit/clause-lst/begin-branch`):

- `:END-LITERAL … :RESULT L' :BRANCHES m` — the literal's net result and its
  segment count.
- Per segment: `:BEGIN-BRANCH :SEGMENT (lit…)` — the segment's literals JOIN
  the continuation clause, each **assumed false** while scanning the remaining
  literals (clause semantics).
- `:CONTEXT-SUBST` — for a segment literal `(not (equal l r))` (assumed false ⇒
  the equality holds), the substitution ACL2 applies in that branch. Consumed
  by solidify nodes with `equivSource = .segment`.
- A branch with an **empty continuation** at the end of the clause is the
  residual: `new-clause ++ segment` is pushed as the node's CHILD subgoal
  (`crunch-clause-segments`), where `new-clause` = the surviving (post-rewrite,
  non-false) literals so far.

Verified against `perm.proof-log` for `Subgoal *1/2''` (events 592–1786):

```
l1 (not (consp (cons x1 x2))) ⇒ 'NIL          BRANCHES 1, SEGMENT NIL
l2 (memb x1 y) unchanged                      BRANCHES 1, SEGMENT ((memb x1 y))
l3 (not (memb a (cons x1 x2)))
   ⇒ (not (if (equal a x1) 't (memb a x2)))   BRANCHES 2:
   b₁ SEGMENT ((not (memb a x2))):
      l4 (equal (perm …) (perm (rm …) …))
         ⇒ (equal (if (equal x1 a) (perm x2 y) 'NIL)
                  (perm (if (equal a x1) x2 (cons x1 (rm a x2))) y))
         BRANCHES 1, SEGMENT ((equal x1 a)
                              (equal 'NIL (perm (cons x1 (rm a x2)) y)))
         — EMPTY continuation ⇒ residual pushed as *1/2''' =
           [(memb x1 y), (not (memb a x2)), (equal x1 a), (equal 'NIL …)]  ✓ matches
   b₂ SEGMENT ((not (equal a x1))) + CONTEXT-SUBST x1⇒a:
      l4 re-scanned ⇒ 't (5-step chain; solidify .segment consumes the
      (equal a x1)-true hypothesis) — closes inline.
```

**The key fidelity fact:** the emitted segments are NOT pure if-lifting
output. *(Corrected 2026-07-03 after the clausify-instrumentation
investigation — an earlier revision wrongly said "type-alist".)* `clausify`
is deliberately "dumb" (its own comment, `acl2/rewrite.lisp:4611-4617`): NO
type-alist is passed. `rewrite-clause` calls
`(clausify val (convert-clause-to-assumptions (cdr tail) (… new-clause nil)) nil sr-limit)`
(`acl2/simplify.lisp:7543-7550`) — the assumptions are the negations of the
OTHER clause literals, and both reasoning steps are performed by `if-interp`'s
purely SYNTACTIC assumptions machinery while lifting `L₄'`'s two ifs:
- test `(equal x1 a)` TRUE ⇒ the tautologous case
  `(equal (perm x2 y) (perm x2 y))` was **dropped**: `call-stack`'s
  equal-reflexivity fold (`rewrite.lisp:3707-3710`) made the leaf `*t*`,
  dropped at `if-interp`'s leaf case (`rewrite.lisp:4000-4011`);
- under `(equal x1 a)` FALSE, the second test `(equal a x1)` resolved FALSE by
  `if-interp-assumed-value2`'s COMMUTATIVE equal/iff match
  (`rewrite.lisp:3332-3368`) — no second split.

So a pure `clausifyPure` recomputation cannot reproduce the segments, and
there is no emitted per-branch clausify record. The closed syntactic rule set
`if-interp` can apply is small and enumerable: commutative EQUAL/IFF matching
(3332-3368), equal-to-distinct-constants (3282-3330), INTEGERP↔RATIONALP
(3370-3400), and `call-stack`'s folds — equal-reflexivity/two-quoteps
(3707-3723), `not` (3684-3706), `iff` (3740-3766), `<` (3728-3739), `mv-nth`
(3767-3777). Three FURTHER mechanisms can reshape the segment set after
if-interp: the Satriani subsumption step (`rewrite.lisp:3969-3986`),
`subsumption-replacement-loop` (`4625-4631`, only ≤ sr-limit), and the
conjoin dedup (`simplify.lisp:502-519`).

## The replay obligation

At literal `k` (chain `lk ≡ L'` already replayed), under the accumulated
spine facts, prove `EvTrue (disjoin (lk :: rest))` from the branch proofs:

- inline branch `i`: continuation proof of
  `EvTrue (disjoin (rest'))` under facts ∪ {segᵢ literals false}, where the
  continuation re-scans the remaining literals (possibly with fresh chains
  under CONTEXT-SUBST facts);
- residual branch: the CHILD node's `EvTrue (disjoin (newClause ++ seg))`,
  peeled by `evtrue_extract_else` with the in-scope falsity facts down to the
  surviving disjunct.

## The design fork

**Option A — semantic byCases composition (no new instrumentation).**
Compose by `Classical.byCases` over the VALUES of the segment-literal atoms
(equivalently the tests ACL2 split on): in each leaf, either a branch's
continuation applies (its segment literals are false there) or the literal
`L'` itself evaluates true (the leaf ACL2's clausify dropped as a tautology —
re-derived by if-true collapse + equal-self at the value level) or a test
resolves by value-level equal-symmetry (`Logic.equal a b = nil ↔ ≠`,
symmetric). Everything is driven by the emitted segments (deterministic — the
case structure IS the segment list), but the driver must re-derive the two
clausify-internal facts (tautology, symmetry) semantically. Analogous in
spirit to how the elim replay re-derives `(cons (car v) (cdr v)) = v`: the
value-level content of the rule ACL2 applied, at the granularity ACL2 records.

**Option B — emit more instrumentation.** Log, per branch, clausify's
assume-true-false derivation (which tests resolved, which cases dropped and
why), and replay those records. Keeps the checker free of any re-derivation,
at the cost of instrumenting `clausify`/`if-interp` (a deep, hot ACL2 code
path — the current instrumentation deliberately avoids it) and a log-format
extension.

**RESOLUTION (2026-07-03, ratified after the instrumentation investigation):
Option A with PARTIAL LOGGING.** The investigation found the *decisions* have
clean single choice-points but the *justifications* are diffused (the
`call-stack` folds, an 8-function signature change to name the resolving
assumption, three set-reshaping mechanisms) — and even full Option B would
still leave the replay re-deriving leaf values. The adopted middle path logs
the DECISION SKELETON so the replay's byCases tree comes from the record, and
re-derives only the value-level facts against it (fail-closed on the closed
rule set above), without committing to zero-inference clausify replay:

- `infra/clausify-trace`: a raw special bound `t` ONLY around
  `rewrite-clause`'s main clausify call (`simplify.lisp:7543`) — the
  `if-tautologyp` / preprocess / guard / corollary clausifies never emit.
- `:if-test` events at `if-interp`'s test case (`rewrite.lisp:4056-4125`):
  test, verdict (`split | true | false`), how (`constant | assumed`), plus
  the assumption path above the `:ignore-when-converting-to-clause` marker
  (self-locating — immune to the else-first evaluation order).
- `:leaf` events at the leaf case (`4000-4011`): leaf value, outcome
  (`dropped | segment`), path.
- FIRED-MARKERS at the Satriani step (`3984`) and
  `subsumption-replacement-loop` (`4627`) so the replay hard-fails when the
  segment set was reshaped downstream rather than mis-attributing it.
- Deliberately NOT logged: which assumption resolved an `assumed` verdict,
  why a leaf value folded to a constant (`call-stack`), per-clause
  subsumption records — the replay re-derives these value-level facts from
  the enumerated rule set, fail-closed.

**Ratification extension (MDD, 2026-07-04, post-audit).** The adversarial
audit of the perm-cons replay (finding 2) asked whether this ratification
covers the two further RECORD-DIRECTED reconstructions the drive required:
the hidden definitional `implies` unfold (applied only when the recorded
`:RESULT` demands it) and unemitted type-alist test resolutions (an in-scope
clause/segment fact, possibly through `equal`'s commutativity, mirrored as an
explicit test-position rewrite). RATIFIED: deterministic, fail-closed,
record-validated reconstruction of this kind is within the partial-logging
decision. The line that must not be crossed is INTRODUCING SEARCH — SMT-like
proof search, heuristic rule selection, or any step not pinned by the record
and the enumerated closed rule set. Extensions to the rule set must remain
enumerable, each justified by a specific if-interp/rewriter code path.

## Implementation sketch (Option A)

1. `replayClauseSpine` v3: items walked STRUCTURALLY (`.branch seg items`
   consumed, not flattened) — the current flat walk + index check stays for
   the single-branch case; multi-branch literals enter the split composer.
2. The split composer at literal `k` with branches `(segᵢ, itemsᵢ)`:
   recompute ACL2's split semantically — byCases over the distinct atoms in
   the segments' literals (value-level); at each leaf, select the branch whose
   segment literals are all false, peel/close as above; leaves with no branch
   must be discharged by the tautology/symmetry rules only (else hard-fail).
3. Residual branches: identify the child by clause match
   (`newClause ++ seg == child.inputClause` — recompute `newClause` from the
   surviving results; hard-fail on mismatch), recurse `replayClause`, peel.
4. `segmentFacts` ctx channel (mirroring `branchFacts`) feeding solidify
   `.segment` (+ CONTEXT-SUBST validation: the substitution must match the
   segment literal's equality).
5. `*1/1'` reuses the same machine (its solidify sources are `.literal` (IH),
   already supported).
