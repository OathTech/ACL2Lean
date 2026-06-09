# Measure-emission track — plan

_Created 2026-06-09. Branch `mdd/measure-emission`._

## Decision (already taken)
Replay induction the **faithful** way: emit ACL2's induction-scheme **measure + justification**
and (eventually) build a `WellFounded.fix` from it — NOT a library of pre-justified
principles, and NOT re-deriving well-foundedness in Lean (that would be inference). So the
induction's *justification* must travel from ACL2 → proof log → proof tree.

## First milestone (this track, pre-driver)
**`dump-proof-tree` correctly reflects the intended induction reasoning** — the measure, the
well-founded relation, the measured variables, and per-case (governing tests + the IH
substitutions) — instead of only the generated `:SCHEME` clauses. Replaying it in the driver
is a later step; the goal here is that the reconstructed tree *says the right thing*.

## What information we need (and why)
ACL2 justifies an induction by a function's recursion: a **measure** that **decreases** under a
**well-founded relation** in each recursive case. The current emit
`(:INDUCTION :TERM … :SUBGOALS n :SCHEME (clauses…))` gives only the generated case clauses —
the measure/relation/IH-substitutions are implicit (recoverable only by diffing clauses against
the conjecture). We want them explicit:
- **measure term** (e.g. `(acl2-count x)`) — what decreases.
- **well-founded relation** `rel` (e.g. `o<`) and its **domain predicate** `mp` (e.g. `o-p`).
- **subset** — the measured formals.
- **per case**: the governing **tests** and, for each induction hypothesis, the **substitution
  alist** σ (var → term) — the exact IHs, not reverse-engineered from clause literals.

## Where it is in the source
`acl2/induct.lisp` — at the induction-choice emit point (~L6818, the `emit/induction` `fms`,
where `winning-candidate` is in scope). The `candidate` defrec (L1554) carries:
- `:justification` → `justification` defrec (L1686): `(subset . ((subversive-p . (mp . rel)) (measure . ruler-extenders)))` — gives **measure, rel, mp, subset**.
- `:tests-and-alists-lst` → list of `tests-and-alists` (defrec `(tests alists)`, L~1700): per case,
  `:tests` (instantiated governing tests) and `:alists` (a list of substitution alists, one per
  recursive call / IH).
- `:xinduction-term` — the user-level induction term (we currently emit `:induction-term`, an alias).

All accessible at the emit point via `(access candidate winning-candidate :justification)` /
`:tests-and-alists-lst`.

## Plan

### M1 — ACL2 emit (induct.lisp)
Enrich the `(:INDUCTION …)` event (keep `:TERM`/`:SUBGOALS`/`:SCHEME` for back-compat + cross-check):
```
(:INDUCTION :TERM t :XTERM xt :SUBGOALS n
            :MEASURE m :REL rel :MP mp :SUBSET (v…)
            :CASES ((:TESTS (test…) :ALISTS ((( v . term )…) …)) …)
            :SCHEME (clauses…))
```
Tag is already `emit/induction`; run `just check-acl2-tags` after. Comment-and-payload change to
one `fms`. (Measure/rel/mp/subset/cases are pure reads of `winning-candidate`.)

### M2 — regenerate inductive sample logs
Rebuild ACL2 (`just build-acl2`) and regenerate the inductive corpus
(`simple`, `02-rev`, `03-linear`, `04-multi-case-induction`, `06-measure`, …) via
`just capture-all-logs`. (Slow — ACL2 build. Required before the Lean side sees the new fields.)

### M3 — parser + reconstruction (Lean)
- `ProofLog.lean`: extend `InductionStep` with `measure : SExpr`, `rel : Symbol`, `mp : Symbol`,
  `subset : List Symbol`, `cases : List InductionCase` where
  `InductionCase := { tests : List SExpr, alists : List (List (Symbol × SExpr)) }`.
  Extend `parseInduction?` to read `:MEASURE/:REL/:MP/:SUBSET/:CASES` (keep `:SCHEME` parse).
  Old logs without the new fields must still parse (defaults), so the corpus doesn't all need M2 at once.
- `ClauseTree.lean`: the synthesized pool-root already carries `induction : Option InductionStep`;
  the new fields ride along (no new linking needed for the dump). **Reconstruction logic to add
  (validation):** check `cases.length = subgoalCount`, and link each `:CASES` case to its `*1/k`
  child subgoal by matching the case tests against the child's input clause (hard-fail on mismatch
  — the no-silent-skip rule). This is the genuinely new reconstruction step.

### M4 — dump-proof-tree (Main.lean)
Render, e.g.:
```
╫ INDUCTION on (my-app x y)   measure (acl2-count x) under O< (mp O-P), measured {x}   (2 subgoals)
    case *1/2: tests [(not (consp x))]            IH: (none)
    case *1/1: tests [(consp x)]                  IH σ: [x := (cdr x)]
```
Verify on `simple.proof-log`: the measure is `(acl2-count x)` (my-app recurses on `x`), rel `O<`,
two cases with the cdr-x IH — cross-checked against ACL2's actual `my-app` measure.

### Deferred (driver / later milestones)
- **Termination-proof emission**: the admission's measure-conjecture clause-tree (per case,
  `tests ⇒ (rel (measure σ) (measure))`) — needed for the driver to BUILD `WellFounded.fix`
  with a kernel proof of decrease. Slot exists (`WorldEvent.defun.termination`, currently `none`).
  Not needed for the dump milestone.
- **Driver**: `replayClause` recurses push→pool-root→children, emits WF induction from
  (measure, rel, cases), threads case-hyps + IH per `:ALISTS`. (Track A induction scaffold.)

## STATUS (2026-06-09): M1–M4 done — milestone reached

- **M1 ✓** `induct.lisp`: `(:INDUCTION …)` now emits `:MEASURE :REL :MP :SUBSET :CASES` (+`:XTERM`),
  via `structured-induction-cases` (infra/induction-cases). ACL2 rebuilt (compiles); `check-acl2-tags` green.
- **M2 ✓** Rebuilt ACL2 + regenerated the corpus (`simple` + all `recon-tests`).
- **M3 ✓** `ProofLog`: `InductionStep` + `InductionCase`; `parseInduction?`/`parseCase`/`parseAlist`
  read the new fields (optional → legacy logs still parse). Fields ride through `buildDevelopment`
  on the synthesized pool-root.
- **M4 ✓** `dump-proof-tree` renders the measure justification + per-case tests + IH substitutions.
  Verified: `my-len-my-app` → `measure (acl2-count x) decreases under o-p/o<; measured: x`, step
  `[(consp x)]` IH `x:=(cdr x)`, base `[(not (consp x))]` no IH. `02-rev`'s 6 inductions render
  across controllers. `just ci` green; coverage harness parses+reconstructs the whole (new-format)
  corpus; tag check OK.

### Verified against the inducting corpus (after the instantiation fix)
Checking other examples caught a real bug: the justification's measure/subset are in the
inducting FUNCTION's formals, so the first cut emitted e.g. `(app a b)` → `:MEASURE
(acl2-count x) :SUBSET (x)` while `:CASES` were about `a` (only `my-len-my-app` looked right,
reusing `app`'s formal `x`). **Fixed:** instantiate the measure via the term's formals→actuals
alist; emit `:CONTROLLERS` (the candidate's already-instantiated controllers). Verified:
- `simple` `(my-app x y)`: measure `(acl2-count x)`, on `x`, IH `x:=(cdr x)`.
- `02-rev` (6 inductions): `(app a b)`→`(acl2-count a)` on `a`; `(rev x)`→on `x`;
  `(app rv (cons x1 'nil))`→`(acl2-count rv)` on `rv`. Varied controllers all instantiated.
- 2- and 3-subgoal inductions both render (cases = scheme cases, NOT = subgoalCount — a
  3-subgoal induction still has 2 scheme cases; do NOT assert cases.length = subgoalCount).
- `01`, `05` (app on `x`).

**Unverified (no corpus example exercises them):** a step case with MULTIPLE IHs (2+ recursive
calls → 2+ `:ALISTS`; the parser maps over alists so it *should* handle it); a custom
non-`acl2-count` measure inside a *proof* induction (`06-measure` declares custom measures but
proves by simplification, 0 inductions — that's the admission-time/defun-measure path, deferred).

### Next (not yet done)
- **Case↔child linking (reconstruction):** correlate each `:CASES` case with its `*1/k` child
  subgoal **by tests** (NOT by order — ACL2 emits cases consp-first while subgoals are *1/2 base-first),
  so the driver knows which child gets which case-hyp + IH. A real design step (how to match the
  case's tests against the child's input clause); did NOT add a `cases.length = subgoalCount`
  hard-fail since merge/split may break that invariant on other theorems — verify before asserting.
- **Termination-proof emission** (deferred, for the driver's WF-fix decrease proof).
- **Driver** WF-induction replay (Track A scaffold).

## Sequencing
M1 → M2 (rebuild+regen) → M3 → M4, then verify the dump. M1 is the ACL2-side core; M3/M4 are the
Lean reconstruction+display. The dump milestone is reached at M4. Keep `just check-acl2-tags` green
(M1 enriches an `emit/` payload) and the existing `just ci` green (M3 parser changes must keep the
non-inductive corpus parsing). Commit per milestone on `mdd/measure-emission`; **no merge without
explicit sign-off.**
