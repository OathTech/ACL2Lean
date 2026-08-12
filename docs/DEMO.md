# The demo — a reader path through ACL2Lean

**For a Lean user who does not speak ACL2.** ACL2Lean takes theorems that
[ACL2](https://www.cs.utexas.edu/users/moore/acl2/) proved, replays ACL2's own
recorded proof inside Lean, and hands you an ordinary kernel-checked Lean
theorem about ordinary Lean functions. ACL2 is an *untrusted oracle*: it
proposes proofs, the Lean kernel checks them.

This page is a four-stop tour. Stops 1–3 are the whole story in about twenty
minutes; stop 4 is optional and goes downward, into the machinery.

---

## Stop 1 — What is proved, and what you must trust (5 minutes)

**Read: [`ACL2Lean/Imported/Mirrors/Showcase.lean`](../ACL2Lean/Imported/Mirrors/Showcase.lean)**

The front door. Its header is the **trust map** in three tiers — what you must
read and believe (the kernel; the statements themselves; and that the Lean
definitions they mention — `isortL`, `qsortL`, … — are the sorting functions
*you* mean, which you check by reading them, exactly as in any Lean
development), what is untrusted-but-kernel-checked (all of ACL2, our
instrumentation, the parser, the tree reconstruction, the replay driver, the
semantic core, and the encoders), and what is assumed (exactly 20 `sorry`s,
enumerated by class with each class's unlock).

The point the page is careful about: **you do not need to trust — or care —
what ACL2 does.** ACL2 is the untrusted proof-search oracle; a bug anywhere in
the import pipeline, including our transcriptions of ACL2's functions simply
being the wrong functions, can only make a proof *fail to exist* — it cannot
make a statement on the page false. "Imported" is *attribution* (how the proof
was found), not a premise; the provenance hashes, statement pins, and
differential harness keep the import route healthy and honestly attributed,
not the theorems true — the kernel alone does that.

Then the headline results, each a one-line restatement of an already-proved
constant, each followed by a `#guard_msgs`-pinned axiom receipt so its exact
axiom set is checked by the build and printed on the page:

| result | Lean statement |
| --- | --- |
| insertion sort sorts | `LexSorted (isortL xs)` |
| insertion sort preserves multiplicity | `(isortL xs).count e = xs.count e` |
| merge sort sorts / preserves multiplicity | `LexSorted (msortL xs)`, … |
| quicksort sorts / preserves multiplicity / permutes | `LexSorted (qsortL xs)`, …, `(qsortL xs).Perm xs` |
| the counterexample witness is complete | `xs.isPerm ys = (xs.count (pceL xs ys) == ys.count (pceL xs ys))` |
| the abstract sorts-equivalence capstone | a *conditional* — see below |

Two things to notice, because they are where honesty lives on this page:

* Most receipts read `[propext, sorryAx, Classical.choice, Quot.sound]`. The
  `sorryAx` is not decoration: it is the visible debt, and the header says
  exactly which class of assumption it comes from. A result whose receipt is
  the clean trio has *no* assumptions beyond Lean's.
* The sorts-equivalence capstone is presented as the **conditional it is**.
  ACL2 proves it in a constrained theory, so the artifact is the
  world-parametric constant with the scope's constraints as explicit premises;
  the concrete-world instantiation keeps two named hypotheses. No
  unconditional version is claimed.

## Stop 2 — The objects of study (plain Lean, no ACL2)

**Read: [`ACL2Lean/Imported/Sorting/Sims.lean`](../ACL2Lean/Imported/Sorting/Sims.lean)**

Everything the Showcase talks about is defined here as plain recursive Lean
over the `SExpr` value type: `isortL`, `msortL`, `qsortL`, `lexorderB`,
`orderedpRec`, `filterL`, `merge2L`. These are the *subjects* of the imported
theorems, and they are readable on their own terms — there is no evaluator, no
world, no proof log in this layer.

`SExpr` (`ACL2Lean/Syntax.lean`) is ACL2's value universe: `nil`, an atom, or a
`cons`. `lexorderB` is ACL2's built-in total order on that universe as a
`Bool`; `LexSorted` (in `Mirrors/IsChain.lean`) is Mathlib's `List.IsChain`
over it. So "sorted" and "permutation" mean what they mean in Mathlib.

The directory around it *is* the trust story — the module layering answers
"what do I have to trust?" with `import` lines. Four layers, six modules
(`Iso` and `Decode` are each split in two purely to respect the 1500-line
module norm):

| layer | module | contents |
| --- | --- | --- |
| 1 | `Sorting/Sims.lean` | the definitions above + the ACL2 body constants they simulate |
| 2 | `Sorting/Iso.lean`, `Sorting/IsoAdmission.lean` | the correspondence layer: each ACL2 program computes its Lean reading on encoded inputs (the second module covers the ordinal / `acl2-count` admission substrate) |
| 3 | `Sorting/Decode.lean`, `Sorting/DecodeSorts.lean` | the *only* layer that touches replayed statements — transports each into its native form |
| 4 | `Sorting/Debt.lean` | the quarantined assumptions: 12 sorried dischargers, each with its named unlock. Auditing "what is assumed?" means reading this one file |

`ACL2Lean/Imported/Sorting.lean` is now a facade re-exporting all six, so
existing imports are unchanged.

Notice layer 4's import line: `Debt.lean` imports `Sims.lean` **only**. The
twelve assumed statements are therefore stated over the definitions alone —
none of them depends on the correspondence or decode layers.

`scripts/check-trust-imports.sh` (in `just ci`) pins each layer's direct
imports and checks that `Sims.lean` and `Debt.lean` never reach the proof-log,
clause-tree, development or driver modules, so the layering cannot rot
silently. Read its header for the limit of that claim, stated plainly: the
closure *does* reach `Replay.EvalLemmas` through `Imported/Lifting.lean`,
because the encoders and the evaluation lemmas still share one module. The
enforced claim is "no proof-log/clause-tree/driver machinery", not "no
`Replay` module at all".

## Stop 3 — The scoreboard, and the gates that keep it honest

**Read: [`ACL2Lean/Imported/Mirrors/Catalog.lean`](../ACL2Lean/Imported/Mirrors/Catalog.lean)**

`liftCatalog` carries **one decision per green row** of the corpus-wide replay
sweep: a native mirror (with the constant), an explicit `pending` (naming the
blocking work), or `replayedOnly` (no non-vacuous native content). A newly
green row with no decision fails the build, so "replayed but never lifted"
cannot accumulate silently. The sweep it is checked against is
`Tests/driver-coverage.golden` (`just ci`).

The same file states the **mirror criterion** and mechanizes it. One sentence
each:

* **Lift-coverage gate** — every green golden row has a catalog decision, and
  every named constant exists.
* **Seam gate** — each native's proof term must transitively consume its own
  `driver_replayed%` constant, so a "mirror" cannot be detached from the ACL2
  proof it claims to import.
* **Axiom gate** — every mirror theorem's axiom set is checked exactly: the
  classical trio, plus `sorryAx` only where a catalog entry declares the debt
  — and an entry that *stops* carrying `sorryAx` also fails, forcing a
  promotion review rather than letting debt retire unnoticed.
* **Criterion-1 gate** — a mirror's *statement* may not mention the evaluator
  layer (`evalOpt`, `EvTrue`, `World`, `boolEnc`) or any `*Exec` function: no
  mixed vocabulary, so the statement is readable without knowing ACL2.
* **Provenance gate** — no Lean-side content discharger may exist in the mirror
  layer outside the registered debt set; a registered entry whose `sorry` is
  replaced by a hand proof fails the build. ACL2 must do the reasoning.
* **`hreplayed`-usage gate** — a decode that *takes* a replayed statement must
  actually *use* it, not prove its content beside it.

These gates are **speedbumps, not barriers** — deliberately. Each is
documented with its own threat model: they catch the honest mistake and stay
simple enough to be obviously right. The load-bearing trust is the design (the
kernel plus small, exact axiom checks), not gate cleverness.

## Stop 4 — One worked replay (optional, downward)

What actually happens between "ACL2 proved it" and the theorem in stop 1. Take
insertion sort.

**(a) The ACL2 source** — `acl2/books/sorting/isort.lisp`, upstream ACL2's own
sorting book:

```lisp
(defun insert (e x)
  (if (endp x) (cons e x)
    (if (lexorder e (car x)) (cons e x)
      (cons (car x) (insert e (cdr x))))))

(defun isort (x)
  (if (endp x) nil (insert (car x) (isort (cdr x)))))

(defthm orderedp-isort (orderedp (isort x)))
```

**(b) The proof log** — our instrumented ACL2 fork (the `acl2/` submodule)
records the waterfall as it runs: runes, rewrite steps with their
substitutions, induction schemes, type-prescription corollaries. The result is
`acl2_samples/sorting/isort.proof-log` (a generated artifact — see the README's
capture instructions).

**(c) The proof tree** — the log is parsed and reconstructed into the clause
tree ACL2's waterfall actually walked (not a flat list):

```sh
lake exe acl2lean dump-proof-tree acl2_samples/sorting/isort.proof-log
```

**(d) The replay** — the driver recurses that tree and emits a Lean `Expr`,
node by node. It does **no inference**: if the tree lacks the information for a
step, it hard-fails at a named frontier rather than guessing.

```sh
just replay acl2_samples/sorting/isort.proof-log orderedp-isort
```

```
• isort  (world: 27 defun(s), 3 theorem(s))
    ORDEREDP-ISORT → REPLAYED ✓ cond[tp:INSERT]
    TRUE-LISTP-ISORT → REPLAYED ✓ cond[tp:INSERT]
    HOW-MANY-ISORT → REPLAYED ✓ cond[tp:HOW-MANY, rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0]
```

`cond[tp:INSERT]` is the *kept condition*: the replayed statement is
conditional on ACL2's emitted type-prescription corollary for `insert`. That
condition is exactly the debt you saw as `sorryAx` in stop 1 — the same fact,
tracked in three places that must agree.

**(e) The replayed statement** — what the driver produces is a deep-embedded
proposition: "under the world derived from this log, the goal formula
evaluates to something non-`nil`". True, kernel-checked, and unreadable.

**(f) The decode** — `Sorting/Decode.lean` transports it into the native
statement, using the correspondence lemmas of `Sorting/Iso.lean` (each ACL2
program computes its Lean reading on encoded inputs). Out the other end comes
`orderedpRec (isortL xs) = true`, and then stop 1's `LexSorted (isortL xs)`.

**Where the remaining trust sits.** Steps (b)–(f) are all untrusted: a bug in
any of them makes the Lean proof fail to typecheck. What the kernel does *not*
check is that the replayed statement in (e) faithfully restates the ACL2
theorem in (a), nor that our interpreter faithfully models ACL2 — those are
separately enforced (source-hash provenance on every log, hand statement pins
per book in `Tests/SortingPins.lean`, differential testing of the interpreter
against real ACL2, and adversarial audits). The README's *Trust model* section
spells the three properties out.
