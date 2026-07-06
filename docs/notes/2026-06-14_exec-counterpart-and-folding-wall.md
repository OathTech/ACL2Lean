# executable-counterpart replay + the abbreviation-expansion folding wall

*2026-06-14, MDD. Branch `mdd/perm-exec-counterpart` (off `main`).*

Context: first R1 wall taken under the post-Fable capability situation
(buffer against mistakes, smaller steps). comm-rm (`sorting/perm`) was picked
as the smallest remaining perm frontier. It turned out to be **two** walls;
the golden frontier message only ever shows **one wall deep**, so wall 2 was
invisible until wall 1 fell. (Process lesson: "smallest visible frontier" ≠
"smallest actual work" — re-measure after each wall.)

## Wall 1 — executable-counterpart steps + closer (DONE, commit 7fe4d38)

ACL2 closes ground subterms by running their executable counterpart, recording
only a verdict + the `executable-counterpart:<fn>` rune (the ratified
decision-procedure carve-out). The replay now mirrors this faithfully in two
positions:

- **chain step** (`replayNode`, Driver.lean): e.g. `(consp 'nil) => 'nil`
  inside a rewrite chain → node-equality `eval lhs = eval rhs`.
- **closing-literal terminal** (`replayLiteral`): e.g. `(equal 'nil 'nil) =>
  (quote t)` → `eval literal = some t`.

Both re-run the SAME closed computation via `evalOpt` at a concrete fuel,
verify it matches ACL2's recorded value (divergence hard-fail), and lift by
fuel monotonicity. Shared `replayExecGround` helper (placed before the `mutual`
block) deduplicates the evaluator logic with the existing preprocess-chain
exec-counterpart case. Hard-fails on open lhs, evaluator divergence, or a
closer that does not reduce to `t`.

This capability is **orthogonal to wall 2** and is kept regardless of how wall 2
is resolved: exec-counterpart appears across the corpus, not just in comm-rm.
It currently closes no whole theorem on its own (comm-rm needs wall 2 too) — a
wiring gap, not throwaway work.

## Wall 2 — `sublis-var` display-folding mismatch (DEFERRED)

### Mechanism (precise)

comm-rm's `rm` abbreviation expansion runs inside `simplify-clause` (the
rewriter). When an if-test rewrites to a constant, `rewrite-if`'s constant-test
branch (rewrite.lisp:17587–17592) logs its display term as:

```lisp
:lhs (mcons-term* 'if test (sublis-var alist left) (sublis-var alist right))
:rhs (if (cadr test) (sublis-var alist left) (sublis-var alist right))
```

`sublis-var` constant-folds via `cons-term` (basis-b.lisp:2698, 809), so
`(car 'nil)→'nil` / `(cdr 'nil)→'nil` in the branches. ACL2's own comment
(17578–82) states this is **"logging-only and does not affect rewriting"** —
the actual rewrite takes only the live branch (`(rewrite right alist 3)`).

The replay reconstructs the same term via `substTerm` (Driver.lean:925), which
does NOT fold. So the replay's running term carries the branches unfolded while
ACL2's logged redex has them folded → `pathStepsFromFrames: navigated to … ,
expected redex …` (the diff is exactly the folded car/cdr).

**This is NOT a missing-reasoning log gap.** Everything needed to replay the
if-simplification (rule, test value, taken branch) is logged. The discrepancy
is a logging-*format* choice (fold-for-display) ACL2 made deliberately. So the
default "log from ACL2 > reconstruct" preference (which targets missing
*reasoning*) doesn't cleanly apply.

### The broader phenomenon

The same `sublis-var` display-instantiation is used by other logged step kinds
(if branches here; the recognizer steps at rewrite.lisp:5282 — "consistent with
the sibling recognizer/cdr-cons steps"). So the fold/no-fold mismatch is a
*family*, not unique to if-simp.

### Options and difficulty

- **A — replay relaxes the dead-branch match** for a constant-test
  if-simplification (require only test + taken branch; the discarded branch may
  differ). Low risk, localized, faithful (`(if 'nil A B)=B` is independent of
  `A`). No re-capture. **Limit:** only handles DEAD-branch folds; a *live*
  branch carrying a ground fold is a distinct future wall. Mild fidelity-net
  cost: a substitution bug in the dead branch would go uncaught (mitigate:
  still match test + taken strictly, require dead branch well-formed).
- **B — ACL2 logs the branches unfolded** (non-folding subst in the fork).
  Honors "log from ACL2" literally but only *reformats* an existing log (adds
  no missing reasoning); needs a non-folding subst + re-capture + full-corpus
  golden revalidation. Broad blast radius.
- **C — replay's `substTerm` folds like `cons-term`** so logged and
  reconstructed terms agree everywhere `sublis-var` is used (dead + live + all
  step kinds). Most general; touches foundational `substTerm` + its semantic
  lemma (`evalOpt_substTerm`). Highest proof risk for the current capability
  situation.

### Why deferred, and the keep/throwaway answer

- **A is reversible and subsumable:** if C is adopted later, the dead branch
  matches exactly and A's relaxation becomes a removable no-op. So A does not
  box us in architecturally — it is a stepping stone, not load-bearing.
- **Generality cannot be measured yet:** most corpus theorems fail at *earlier*
  walls (multi-literal induction, clausify) before reaching if-simp folding, so
  we cannot yet bound how often live-branch folds occur downstream. Any A/B/C
  choice now is partly a guess.
- **Decision:** defer wall 2. Keep wall 1 (committed; orthogonal). Decide A vs C
  with data, as earlier walls fall and the phenomenon's frequency becomes
  measurable. If live-branch folds prove rare → A; if pervasive → C.

comm-rm therefore stands at the wall-2 frontier (a clean named hard-fail), 1-of-2
done. Next R1 work moves to clausify-on-multi-literal (perm-cons,
perm-transitive).

## Update 2026-07-05 — perm-transitive is NOT this wall: the hyp-relief leak

Re-measured after the R1 composer landed (perm-cons replaying). perm-transitive's
`pathStepsFromFrames: navigated to x, expected redex (perm y x)` looked like the
folding family but has a DIFFERENT mechanism, found by reading the raw event
sequence for `*1/3'` literal 2:

`perm-symmetric` is a CONDITIONAL rewrite rule (`(implies (perm x y) (perm y x))`
→ lhs `(perm y x)`, hyp `(perm x y)`). Trying it on the literal's atom
`(perm x y)` unifies with subst `{y↦x, x↦y}`; `relieve-hyps` then REWRITES the
instantiated hypothesis `(perm y x)` (gstack frame `(1 . PERM)` = hyp 1) — a
full definition-unfold subtree — the hyp does not relieve to `'t`, the rule
FAILS, and the hyp-relief events were never rolled back: the def-perm node
leaked into the literal's top-level chain. On SUCCESS (literal 4's
perm-symmetric) the hyp events leaked too, as unbracketed SIBLINGS preceding
the with-lemma node. Never exercised before: the 18 replaying theorems use
only unconditional with-lemmas.

**Fix (this branch, `infra/hyp-log-tail` + `emit/with-lemma/begin-hyps`/
`end-hyps`):** checkpoint the log tail before `relieve-hyps`; bracket the
relief's events as an inner block `:KIND HYP` (on success they become the
with-lemma node's CHILDREN — its justification, mirroring BODY/RHS blocks);
on failure roll back to the checkpoint (abandoned backchaining leaves no
trace). Tagged checkpoint (`cons t tail`) so an empty tail restores.

The ORIGINAL wall-2 mechanism (sublis-var display-folding) still stands for
comm-rm — unchanged by this fix; options A/C above still apply. And behind the
hyp fix, perm-transitive's next expected wall is the USER-RULE with-lemma
replay: instantiating a previously-proven theorem (perm-symmetric) by the
node's `:SUBST`, with its mirror entering the conditional telescope as a
theorem-dependency hypothesis (rule:<name>, the c2 pattern extended) and the
HYP children discharging the instantiated hypotheses.

## Update 2026-07-06 — wall 2 RESOLVED: option A adopted (data-ratified)

The earlier walls fell (multi-literal induction et al.) and the phenomenon
became measurable: every observed fold in the corpus sits in the DISCARDED
branch of a constant-test if-simplification — exactly the shape option A
covers. Adopted as designed (commit 81d4f37): when the recorded lhs differs
from the running term, require the SAME test and SAME taken branch (strict)
and replay the collapse on the RUNNING term; anything else falls THROUGH to
the normal machinery (a first draft that threw instead of falling through
broke the if-finish family — caught by the golden gate within minutes).
Audit #2 (2026-07-06) verified the relaxation cannot change which branch is
taken. comm-rm advanced past this family to the multi-literal preprocess
chain (*1/1.2); a LIVE-branch fold has still never been observed — if one
appears, option C (folding substTerm) remains the escalation path and A
becomes a removable no-op, as analyzed above.
