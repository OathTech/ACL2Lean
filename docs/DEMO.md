# The demo — a reader path through ACL2Lean

**For a Lean user who does not speak ACL2.** ACL2Lean takes theorems that
[ACL2](https://www.cs.utexas.edu/users/moore/acl2/) proved, replays ACL2's own
recorded proof inside Lean, and hands you an ordinary kernel-checked Lean
theorem about ordinary Lean functions. ACL2 is an *untrusted oracle*: it
proposes proofs, the Lean kernel checks them.

The demo is in three parts. Read them in order, or stop after part 1.

| | | |
| --- | --- | --- |
| **[Part 1 — What's the TCB?](demo/1-tcb.md)** | ~10 min | What is proved and what you must trust. A tour of `ACL2Lean/Demo/Sorting/` — four files, and that is the whole trust base — plus what you need *not* trust. |
| **[Part 2 — What you do to replay a book](demo/2-replay.md)** | ~15 min | The user manual: book → `capture-proof-log` → `load_development%` → `derive_world` → `driver_replayed%` → your native definition → `derive_sim%` → decode → catalog entry, worked end to end on insertion sort. |
| **[Part 3 — How it works](demo/3-internals.md)** | optional | Downward, into the machinery: the seven pipeline stages, the four layers from replayed statement to native theorem, the generators, the catalog and its gates, the census and metrics. |

**Start here:** `ACL2Lean/Demo/Sorting/Statements.lean` — the front door. Its
header is the trust map; below it are the headline results, each a one-line
restatement of an already-proved constant, each followed by a
`#guard_msgs`-pinned axiom receipt so its exact axiom set is checked by the
build and printed on the page.

| result | Lean statement |
| --- | --- |
| insertion sort sorts | `LexSorted (isortL xs)` |
| insertion sort preserves multiplicity | `(isortL xs).count e = xs.count e` |
| merge sort sorts / preserves multiplicity | `LexSorted (msortL xs)`, … |
| quicksort sorts / preserves multiplicity / permutes | `LexSorted (qsortL xs)`, …, `(qsortL xs).Perm xs` |
| the counterexample witness is complete | `xs.isPerm ys = (xs.count (pceL xs ys) == ys.count (pceL xs ys))` |
| the abstract sorts-equivalence capstone | a *conditional* — see part 1 |
