# docs/ — index

An index, not a document. Start at the root [`README.md`](../README.md); the
technical entry point is [`OVERVIEW.md`](OVERVIEW.md).

## The reading rule (live vs dated)

**A file with a DATE in its name is a RECORD of that date** — true when
written, never current state. The canonical documents below win wherever a
dated file disagrees with them; in particular, dated files written before
2026-08-12 use "mirror" for what is now called a WAYPOINT, so read
[`LEXICON.md`](LEXICON.md) first.

## Canonical / live

| doc | what it is |
| --- | --- |
| [`OVERVIEW.md`](OVERVIEW.md) | The technical overview: the nine-stage pipeline, the trust model, the product layer, how to build and reproduce, known limitations. |
| [`LEXICON.md`](LEXICON.md) | The canonical glossary — *replayed statement* / *waypoint* / *mirror* name three different things. **Wins all terminology conflicts.** |
| [`BUGS.md`](BUGS.md) | The single index of known fidelity bugs (`BUG-NNN`), cross-checked against the differential corpus by `scripts/check-bugs.sh`. |
| [`notes/2026-08-19_versioning-policy.md`](notes/2026-08-19_versioning-policy.md) | Release and versioning policy: SemVer with an honest `0.x`, what MINOR/PATCH mean here, the 1.0.0 bar, and the v0.1.0 plan. |

Two dated documents are **governing** rather than merely historical, and say
so at their heads:

| doc | governs |
| --- | --- |
| [`plans/2026-09-05_master-plan.md`](plans/2026-09-05_master-plan.md) | The governing post-sorting goal sequence: word-library mirrors, reusable imports, and x86 program correctness. Retains METRIC/PRODUCT and Track FREE / Track REAL; supersedes the sorting plan's sequencing. |
| [`notes/2026-07-22_pattern-map.md`](notes/2026-07-22_pattern-map.md) | The COVERAGE source of truth (ci-gated by `just check-pattern-map`): the frame over ACL2's situation space and the pinned frontiers per layer. Consult before building new support. |

Also binding, but outside `docs/`: [`../CLAUDE.md`](../CLAUDE.md) (the working
rules — fidelity requirements, gating tiers, audit practices) and
[`../TODO.md`](../TODO.md) (the live backlog).

## Dated categories

| directory | what lands there |
| --- | --- |
| [`plans/`](plans/) | **Arc charters and design plans** — one per arc, usually carrying that arc's log and exit. The record of how a piece of work was scoped and what it actually did. |
| [`notes/`](notes/) | **Dated findings**: investigations, surveys, measurements, design briefs, close-out notes. `2026-08-18_project-history.md` is the narrative history of the project, including what went wrong. |
| [`audits/`](audits/) | **Review records**, adversarial and otherwise. The most recent top-level review is [`audits/2026-08-19_top-level-claims-audit.md`](audits/2026-08-19_top-level-claims-audit.md). |
| [`archive/`](archive/README.md) | **Moved history**: passages retired from live documents, kept verbatim, with an index. Includes the pre-2026-08-19 `TODO.md` arc journal. |
| [`comms/`](comms/) | Correspondence and hand-offs. |
| [`reference/`](reference/) | Parked material that is **not built and not trusted** — currently one file, whose own header says so. Do not cite, import, or build on it. |

Recent assessment: [After sorting: the next north-star target](notes/2026-09-05_next-north-star-assessment.md)
compares machinery broadening with candidate books, records fresh probes, and
recommends a bounded bitvector-library arc leading toward x86 program proofs.
Its direction was accepted; the [new master plan](plans/2026-09-05_master-plan.md)
sets the goal sequence. The [NS1 charter](plans/2026-09-05_bvchop-foundation-charter.md)
specifies the first three BVCHOP mirrors, completion receipts, and the
agreed scope and review allocation for the long run.

Active slice: [NS1-R — reusable type-query and clause-edit replay](plans/2026-09-07_ns1-replay-mechanisms-plan.md)
sets the focused probe, consolidation, whole-dependency replay and reuse
acceptance plan from the 2026-09-07 check-in. It builds on the existing NS1
worktree and has its own bounded completion condition; it does not close NS1
or change the three native targets.

Its [frozen supported scope](notes/2026-09-07_ns1-r-supported-scope.md) and
[execution record](notes/2026-09-07_ns1-r-execution.md) separate implemented
cases, whole-proof receipts and remaining acceptance work. The execution
record links the capture/image provenance manifests.
