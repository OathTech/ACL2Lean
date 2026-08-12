# Part 1 — What's the TCB?

**For a Lean user who does not speak ACL2.** ACL2Lean takes theorems that
[ACL2](https://www.cs.utexas.edu/users/moore/acl2/) proved, replays ACL2's own
recorded proof inside Lean, and hands you an ordinary kernel-checked Lean
theorem about ordinary Lean functions. ACL2 is an *untrusted oracle*: it
proposes proofs, the Lean kernel checks them.

The first question a reader should ask is **what do I have to trust?** The
answer is one folder plus a little, and it comes in **two tiers** — pick the
one that matches what you want to do with the assumptions.

### Tier A — you ACCEPT the assumed facts as stated

```
ACL2Lean/Demo/Sorting/
  TCB.lean          the definitions        204 lines
  Statements.lean   the theorems           405 lines
  Assumptions.lean  the 18 assumed facts   566 lines  (only for a
                                                       sorryAx receipt)
  AclSource.lean    the ACL2 transcripts   670 lines  (pure data; only
                                                       for attribution)
ACL2Lean/Lexorder.lean                     104 lines
```

`Lexorder.lean` is in the tier because `TCB.lean`'s `LexSorted` bottoms out in
`lexorderB`, ACL2's built-in total order. You may instead take that function on
its kernel-checked order properties — `lexorder_refl` / `_antisymm` / `_trans`
/ `_total` in `ACL2Lean/LexorderOrder.lean` — and not read the implementation.

**~710 lines** of definitions + statements; **~1280** with the assumptions,
**~1950** if you also want the ACL2 attribution.

### Tier B — you want to VALIDATE the assumptions rather than accept them

The 18 assumed statements are written over the semantic core, so reading them
*for content* means adding the modules that give their vocabulary meaning:

```
ACL2Lean/EvalOpt.lean   824   the fuel-bounded interpreter
ACL2Lean/Logic.lean     764   the ACL2 primitives
ACL2Lean/Syntax.lean    886   SExpr, symbols, worlds
ACL2Lean/Parser.lean    745   rides into the import closure via EvalOpt
```

**~3200 further lines.** `Parser.lean` is a reader, not part of the semantics,
but it *is* in the closure, so it is named here rather than quietly excluded.
Add to it the `AclSource.lean` bodies each assumption mentions.

One convention to know before you read them: `evalOpt` is fuel-bounded, and
every assumption states convergence as `∃ N, ∀ f ≥ N, evalOpt f … = some v`.
That form is well-defined because evaluation is fuel-*monotone*
(`evalOpt_fuel_mono` / `evalOpt_ge_fuel` in `ACL2Lean/EvalOpt.lean`) — a
pointer for reading the statements, machinery-side context, not part of either
tier's trust base.

Everything else in the repository — some tens of thousands of lines of
proof-log parsing, proof-tree reconstruction, replay driver, correspondence
lemmas, gates and tests — is *untrusted*: a bug in any of it can only make a
proof fail to typecheck.

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

At the bottom of the page is the **attribution receipt**: for each headline,
the exact set of `Assumptions.lean` statements its proof transitively consumes,
written out in the source and recomputed from the proof terms by a
build-failing check. So "18 assumptions" is never the per-theorem story —
`isort_sorts` consumes exactly one of them (`dis_insert_tp`), and the two
parametric capstones consume none.

One scoping note, because the page states it too: the ban on evaluator
vocabulary (`evalOpt`, `EvTrue`, `World`, `boolEnc`, `*Exec`) — mechanized by
the catalog's criterion-1 gate — covers the **native** entries in §§1–4. The
four §5 capstone entries are deep-embedded conditionals over `EvTrue`/`evalOpt`
at an abstract or canonical `World`, labelled as such where they appear, and
outside that gate's scope by design.

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
exist yet, held as a visible `sorryAx` rather than re-proved in Lean. Each
docstring carries an **EVIDENCE** line naming the ACL2 artifact it transcribes
(the book plus the emitted `:TYPE-PRESCRIPTION` corollary, `:DEFUN` admission
or `:DEFTHM`, quoted from the captured proof log) — evidence for believing
them, not a proof of them:

| class | count | what it is | unlock |
| --- | --- | --- | --- |
| `tp:` type-prescription | 12 | ACL2-emitted type corollaries of a defun ("`(insert e x)` is a `consp`") | a TP-replay discharge route |
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

The one place the semantic core comes back is tier B above: the 18 assumed
statements are *written in* `evalOpt` vocabulary, so judging whether they are
TRUE means reading it. It is untrusted for what the page PROVES, and it is what
you read if you want to check what the page ASSUMES.

Two things to notice on the page, because they are where honesty lives:

* Most receipts read `[propext, sorryAx, Classical.choice, Quot.sound]`. The
  `sorryAx` is not decoration: it is the visible debt, and it points at
  `Assumptions.lean`. A result whose receipt is the clean trio has *no*
  assumptions beyond Lean's — and for those, the trust base is `TCB.lean`
  (with `Lexorder.lean` under it) plus the statement, full stop. Which
  assumptions a `sorryAx` result actually uses is on the page, per theorem, in
  the attribution receipt.
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
