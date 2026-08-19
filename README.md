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

Every one is a proved theorem — fourteen at `Int`, one at `Option Int`
— and every proof was produced by replaying the ACL2 book's own proof of
the corresponding theorem (one product bundles three: the
equivalence-relation conjuncts).

**What you have to trust:** Lean's kernel, your own reading of that one
file (it imports nothing — not even Mathlib — and elaborates from Lean's
prelude alone), and the one seven-line order instance those theorems are
applied at (`TotalOrder Int` — `Int` under its own `≤`). That's the whole
list. The other ~70,000 lines — the instrumented ACL2 fork, the
proof-log parser, the clause-tree reconstruction, the ACL2 interpreter,
the replay driver — are **untrusted by construction**: they can fail to
produce a proof, but they cannot produce a false one. What the kernel
certifies is the theorems themselves. That each proof faithfully
retraces ACL2's recorded reasoning is enforced one level down —
generated proof templates, provenance hashes, and seam gates: strong
engineering evidence, deliberately distinguished from the kernel's
guarantee.

Every theorem's axiom footprint is exactly
`{propext, Classical.choice, Quot.sound}` — no `sorry`, no `native_decide`,
in anything checked. (A handful of termination lemmas in the file are
proved natively rather than by replay — Lean's kernel demands them
before `bsort` may exist as a definition; two are themselves named ACL2
book theorems. The file says so where they appear.)

## Try it

One caveat for a fresh clone: the captured ACL2 proof logs are build
inputs and are *not* in git, so they must be generated once before
`lake build` will succeed — see
[`docs/OVERVIEW.md`](docs/OVERVIEW.md) § *Getting started*.

    git submodule update --init   # the instrumented ACL2 fork (pinned)
    lake build                    # type-check everything
    just test                     # run the test suite

## Learn more

- [`docs/OVERVIEW.md`](docs/OVERVIEW.md) — the architecture and the
  nine-stage pipeline, in full technical detail
- [`docs/LEXICON.md`](docs/LEXICON.md) — the project vocabulary
  (replayed statement / waypoint / mirror)
- [`docs/notes/2026-08-18_project-history.md`](docs/notes/2026-08-18_project-history.md)
  — how it was built, including everything that went wrong along the way
