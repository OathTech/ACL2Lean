# Part 1 — What's the TCB?

**For a Lean user who does not speak ACL2.** ACL2Lean takes theorems that
[ACL2](https://www.cs.utexas.edu/users/moore/acl2/) proved, replays ACL2's own
recorded proof inside Lean, and hands you an ordinary kernel-checked Lean
theorem about ordinary Lean functions. ACL2 is an *untrusted oracle*: it
proposes proofs, the Lean kernel checks them.

The first question a reader should ask is **what do I have to trust?** The
answer is one folder, and it is small:

```
ACL2Lean/Demo/Sorting/
  TCB.lean          the definitions        ~200 lines
  AclSource.lean    the ACL2 transcripts   ~670 lines (pure data)
  Assumptions.lean  the 18 assumed facts   ~440 lines
  Statements.lean   the theorems           ~290 lines
```

Read those four files and you have read the whole trust base. Everything else
in the repository — some tens of thousands of lines of parser, proof-tree
reconstruction, replay driver, correspondence lemmas, gates and tests — is
*untrusted*: a bug in any of it can only make a proof fail to typecheck.

---

## The tour

### `Statements.lean` — start here

The front door. Its header is the **trust map** in three tiers, and then come
the headline results, each a one-line restatement of an already-proved
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

The page adds **zero proof content**: every proof on it is a bare application
of a catalog constant. It is the one demo file that imports machinery, and it
imports it for statements only.

### `TCB.lean` — the definitions

`isortL`, `msortL`, `qsortL`, `merge2L`, `evensL`, `insertL`, `bnextL`, `pceL`,
`orderedpRec`, `LexSorted`, `lexorderB` — plain recursive Lean over `SExpr`
(ACL2's value universe: `nil`, an atom, or a `cons`, defined in
`ACL2Lean/Syntax.lean`). `lexorderB` is ACL2's built-in total order on that
universe as a `Bool`; `LexSorted` is Batteries' `List.IsChain` over it. So
"sorted" and "permutation" mean what they mean in ordinary Lean.

Your whole obligation here is the one you would have in any Lean development:
**read the definitions and satisfy yourself they are the functions you mean.**

There is no evaluator in this file, no `World`, no proof log, no replay — its
imports are the value core alone.

### `AclSource.lean` — the ACL2 transcripts

Pure data: the macroexpanded `defun` bodies of the ACL2 sorting books as
`SExpr` terms (`insertBody`, `msortBody`, `qsortBody`, …), the symbols that
name them, and the term builders they are spelled in. Nothing here computes or
asserts anything.

You need this file only if you care about the **attribution** — that the
theorems really came from ACL2's proofs of *these* functions. It is not a
premise of any theorem: a wrong transcription can only make a replay fail to
exist. Its imports are the syntax core alone.

### `Assumptions.lean` — what is assumed

Exactly **20** `sorry`s exist in the whole library, and **18 of them — every
one this demo touches — are here. This file IS the list.** (The other two
belong to other books: `drv_tp_len` in `Imported/Lifting.lean`, `drv_tp_mylen`
in `Imported/SimpleWorld.lean`.)

Each is a fact ACL2 itself discharged, for which the replay route does not
exist yet, held as a visible `sorryAx` rather than re-proved in Lean:

| class | count | what it is | unlock |
| --- | --- | --- | --- |
| `tp:` type-prescription | 14 | ACL2-emitted type corollaries of a defun ("`(insert e x)` is a `consp`") | a TP-replay discharge route |
| `total:` termination | 5 | a defun's admission (`MERGE2`, `MSORT`, `O<`, `PERM-COUNTER-EXAMPLE`, `BNEXT`) | `with_termination` admission coverage |
| `rule:` previously-proved | 1 | `CONVERT-PERM-TO-HOW-MANY` used as a rewrite rule | the R-lane arc (PERM-TLFIX replay) |

Its imports are the value core, the semantic model (`evalOpt`), `TCB.lean` and
`AclSource.lean` — nothing else.

---

## What you need *not* trust

**You do not need to trust — or care — what ACL2 does.** ACL2 is the untrusted
proof-search oracle; a bug anywhere in the import pipeline, including our
transcriptions in `AclSource.lean` simply being the wrong functions, can only
make a proof *fail to exist* — it cannot make a statement on the page false.
"Imported" is *attribution* (how the proof was found), not a premise. The
provenance hashes, statement pins and differential harness keep the import
route healthy and honestly attributed, not the theorems true — the kernel alone
does that.

Concretely, all of this is untrusted-but-kernel-checked: ACL2's proof search,
our ACL2 instrumentation (the `acl2/` fork's proof-log emission), the proof-log
parser, the proof-tree reconstruction, the replay driver, the semantic core
(`SExpr`, `Logic`, `evalOpt`), the encoders (`enc`/`boolEnc`/`intRep`), and the
whole correspondence/decode layer.

Two things to notice on the page, because they are where honesty lives:

* Most receipts read `[propext, sorryAx, Classical.choice, Quot.sound]`. The
  `sorryAx` is not decoration: it is the visible debt, and it points at
  `Assumptions.lean`. A result whose receipt is the clean trio has *no*
  assumptions beyond Lean's — and for those, the trust base is `TCB.lean` plus
  the statement, full stop.
* The sorts-equivalence capstone is presented as the **conditional it is**.
  ACL2 proves it in a constrained theory, so the artifact is the
  world-parametric constant with the scope's constraints as explicit premises;
  the concrete-world instantiation keeps two named hypotheses. No
  unconditional version is claimed.

## The arrow

The demo folder never imports the machinery (`Statements.lean` is the single
exception, and it imports the catalog for statements only). The machinery
imports the demo folder. `scripts/check-trust-imports.sh` (in `just ci`) pins
every one of these import sets and checks that the closure of `TCB.lean`,
`AclSource.lean` and `Assumptions.lean` contains **nothing but the value and
semantic core** — no `Replay` module, no proof log, no driver. Read that
script's header for its threat model: it is a speedbump against forgetting the
boundary, not a barrier against a motivated construction.

---

Next: **[Part 2 — what you do to replay a book](2-replay.md)**, or
**[Part 3 — how it works](3-internals.md)**.
