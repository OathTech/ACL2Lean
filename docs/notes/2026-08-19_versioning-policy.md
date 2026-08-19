# Release and versioning policy (ratified 2026-08-19)

> Ruled by Mike on 2026-08-19, verbatim: **"Great, let's do it that way"**.
> This note is the record of the scheme; where a later ruling changes it,
> amend here rather than scattering the change.

## The scheme

**[Semantic Versioning](https://semver.org/) with an honest `0.x`.** The
project is a research prototype and the version says so: while the major
version is `0`, the public surface — the mirror specs, the CLI, the log
format, the catalog shape — may change between MINOR releases, and the
version number does not promise otherwise.

Three things stay in sync at every release:

- **the git tag** — annotated, `vMAJOR.MINOR.PATCH`;
- **`lakefile.toml`'s `version` field** — kept equal to the tag it will be
  released under (it currently reads `0.1.0`);
- **the release notes** — which **name the pinned Lean toolchain** for that
  release (the pin lives in `lean-toolchain`). A toolchain bump is a
  first-class, visible part of a release: everything in this repository is
  kernel-checked against exactly one toolchain, and a reader reproducing a
  release needs to know which.

## What the numbers mean for THIS project

| bump | means |
| --- | --- |
| **MINOR** (`0.N.0`) | a **capability or corpus milestone**: a second (third, …) mirrored book family, a named broadening of what the pipeline handles, workflow ergonomics for user-authored statements, or `gen-world` automation landing. |
| **PATCH** (`0.N.P`) | fixes and documentation. No new capability claimed. |
| **MAJOR** | **reserved** — see the 1.0.0 bar below. |

### The ratified 1.0.0 bar

**`1.0.0` = the importer demonstrated at full ACL2 scale — EITHER coverage of
essentially all reasonable community books, OR end-to-end replay-and-mirror of
one vast industrial development (e.g. an ISA semantics model such as
`x86isa`).**

Mike, 2026-08-19, verbatim:

> I think 1.0.0 would be *complete coverage* of ACL2 - all reasonable books.
> Or maybe replaying some vast book, one of the ISA semantics books.

Either disjunct suffices; both are scale demonstrations rather than
architectural checkboxes. Everything short of that is a `0.x` MINOR — a second
mirrored corpus, user-authored-statement workflow ergonomics, named
broadenings of what the pipeline handles, `gen-world` automation.

### The withdrawn bar, and why (2026-08-19)

An earlier draft of this note set the bar at *the independent statement
frontend (`gen-world`/`Translator`) wired into the certified pipeline, plus at
least one mirrored corpus beyond sorting*. **That bar is WITHDRAWN.** It rests
on treating statement derivation as a trust surface, and Mike re-ruled that
framing on 2026-08-19, verbatim:

> I actually think the aim for the statement to come from the ACL2 book isn't
> quite right - If we think about what the user wants here, it seems reasonable
> they would write some somewhat idiomatic Lean themselves. This isn't really a
> trust surface, it's just automation convenience.

**The analysis this rests on.** On the PRODUCT path the user authors the
idiomatic Lean `Prop` and the kernel covers it end to end. If statement
derivation produced something divergent, one of two things happens, and
neither is a false user-facing theorem: the transport either **fails to
close** — loud incompleteness, the honest outcome — or it **closes**, in which
case the replayed statement still entails the user's own `Prop`, which is the
theorem the kernel then certifies. A wrong statement cannot make the user's
`Prop` true. So the risk statement derivation carries is not soundness.

What the caveat does still cover is narrower, and stays on the books:

- **Attribution** — that a product is the ACL2 theorem it is named for. This
  is review-checked (the bijection reading of spec against book, plus the hand
  statement pins as honest-mistake tripwires, not trust anchors), exactly as
  `docs/OVERVIEW.md` § *Trust model* property 2 says.
- **The METRIC layer** — un-mirrored replayed statements and waypoints, where
  no user-authored `Prop` sits downstream to catch a divergence. There the
  caveat has full force; it is also why the lexicon forbids presenting those as
  results.

`gen-world` therefore moves to the **convenience backlog**: automation that
saves the user writing the statement, not a trust prerequisite.

## v0.1.0 — the first release

**Content:** the sorting corpus close-out — J Moore's sorting books imported
end to end, fifteen sorting `Prop`s with fifteen products proved via replay,
21 mirror products in all with the `Basics` books, each carrying the pinned
`{propext, Classical.choice, Quot.sound}` receipt and each consuming a
replayed statement through the build-failing mirror seam gate. Externally
audited on 2026-08-19
(`docs/audits/2026-08-19_top-level-claims-audit.md`).

**When it is tagged:** on the **gated commit after** two in-flight pieces of
work land — the **v4.33.0 toolchain bump** and the **documentation polish**.
Deliberately *not* tagged on the `v4.28.0` tree: that tree emits the known,
cosmetic `Lean.LibrarySuggestions.SymbolFrequency` panic during the heaviest
coverage modules (post-elaboration, no artifact or gate reads it — classified
in `docs/OVERVIEW.md` § *Known limitations*, measured in
`docs/archive/2026-08-19_symbolfrequency-panic-measurement.md`). A first
release should not ship with a panic in its build transcript that the release
notes then have to explain away, when a bump is already queued that is
expected to remove it.

**Gate:** the tag goes on a commit with a full `just claim-gate` recorded
(`TRUE_EXIT=0`), per the two-tier gating rule in `CLAUDE.md` — a release is a
claim point, never a fast-gate.

**The tag:** annotated (`git tag -a`), never lightweight, so the release
message is stored in the object.

**The release notes headline three things, in this order:**

1. the **sorting result** — what was imported, and that the products are Lean
   theorems with zero ACL2 notions proved via replay;
2. the **toolchain pin** for the release;
3. a **scope statement** — the honest boundary: this is a research prototype;
   the kernel certifies the truth of the Lean theorems, while statement
   authenticity and replay fidelity are engineering evidence (provenance
   hashes, statement pins, generated transport templates, seam gates, review)
   and not kernel guarantees; breadth beyond the demonstrated corpus is future
   work.

**GitHub Release:** wraps the tag at the next networked push. Pushes happen
outside the sandbox and keep their full gate (`just check-push-ready` — the
submodule pointer must be reachable from the fork remote, so push the fork
FIRST), per `CLAUDE.md`.

## Notes for whoever cuts it

- There are no tags in the repository yet; `v0.1.0` is the first.
- `lakefile.toml` already reads `version = "0.1.0"`. Confirm it matches the
  tag at the moment of tagging, and bump it as part of the release commit for
  every release after this one.
- The proof logs are gitignored build inputs, so a release tag alone does not
  give a downstream reader a buildable tree — the release notes should point
  at `docs/OVERVIEW.md` § *Getting started* for the capture step.
