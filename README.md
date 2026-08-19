# ACL2Lean

**ACL2 proofs, replayed into Lean 4 — kernel-checked, trusting nothing but Lean.**

ACL2Lean turns theorems proved by the [ACL2](https://www.cs.utexas.edu/users/moore/acl2/)
theorem prover into ordinary [Lean 4](https://lean-lang.org/) theorems. It does not translate proofs
approximately, and it never trusts ACL2's word for anything: it replays ACL2's
actual proof — the clause tree its waterfall produced — step by step inside
Lean, until Lean's kernel has checked every step. A bug anywhere in the
import pipeline makes the result fail to compile; it can never make Lean
prove something false.

## The result

The classic J Moore **sorting corpus** — insertion sort, merge sort,
quicksort, bubble sort, and the theory that they all agree — is imported
end to end. Open [`ACL2Lean/Mirrors/Sorting.lean`](ACL2Lean/Mirrors/Sorting.lean)
and you'll find fifteen ordinary Lean statements, for example:

    ∀ (xs : List α), Ordered (qsort xs)
    ∀ (a : α) (xs : List α), howMany a (msort xs) = howMany a xs
    ∀ (xs ys : List α), Ordered xs → Ordered ys → (xs = ys ↔ Permuted xs ys)

Every one is a proved theorem, and every proof was produced by replaying
the ACL2 book's own proof of the corresponding `defthm`.

**What you have to trust:** Lean's kernel, your own reading of that one
file (it imports nothing — not even Mathlib — and elaborates from Lean's
prelude alone), and the one seven-line order instance those theorems are
applied at (`TotalOrder Int` — `Int` under its own `≤`). That's the whole
list. The other ~70,000 lines — the instrumented ACL2 fork, the
proof-log parser, the clause-tree reconstruction, the ACL2 interpreter,
the replay driver — are **untrusted by construction**: they can fail to
produce a proof, but they cannot produce a false one.

Every theorem's axiom footprint is exactly
`{propext, Classical.choice, Quot.sound}` — no `sorry`, no `native_decide`,
anywhere. (Two lemmas in the file are proved natively rather than by
replay: the termination facts Lean's kernel itself demands before `bsort`
may exist as a definition — the same obligations ACL2 discharges to admit
it. The file says so where they appear.)

## Try it

    git submodule update --init   # the instrumented ACL2 fork (pinned)
    lake build                    # type-check everything
    just test                     # run the test suite

One caveat for a fresh clone: the captured ACL2 proof logs are build
inputs and are *not* in git, so they must be generated once before
`lake build` will succeed — see
[`docs/OVERVIEW.md`](docs/OVERVIEW.md) § *Getting started*.

## Learn more

- [`docs/OVERVIEW.md`](docs/OVERVIEW.md) — the architecture and the
  seven-stage pipeline, in full technical detail
- [`docs/LEXICON.md`](docs/LEXICON.md) — the project vocabulary
  (replayed statement / waypoint / mirror)
- [`docs/notes/2026-08-18_project-history.md`](docs/notes/2026-08-18_project-history.md)
  — how it was built, including everything that went wrong along the way
