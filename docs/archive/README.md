# docs/archive — retired passages, kept verbatim

This directory holds text that was **removed from a live document** but is
worth keeping: dated audit quotations, correction trails, incident asides,
and superseded instructions that were retained as annotations until the
document they lived in was restructured.

Nothing here is current state. Read it as a record of what a live document
used to say and why it changed. Where a passage merely duplicated an
existing dated doc under `docs/audits/` or `docs/notes/`, the entry here is
a POINTER to that doc rather than a copy.

The live documents are:

- [`../OVERVIEW.md`](../OVERVIEW.md) — the technical overview.
- [`../LEXICON.md`](../LEXICON.md) — the canonical glossary.
- [`../BUGS.md`](../BUGS.md) — the single index of known fidelity bugs.
- [`../plans/2026-08-12_master-plan.md`](../plans/2026-08-12_master-plan.md)
  — the governing plan.

## Contents

| File | What it holds |
| --- | --- |
| [`2026-08-19_overview-historical-notes.md`](2026-08-19_overview-historical-notes.md) | The historical passages removed from `docs/OVERVIEW.md` when it was restructured from the inherited README text into a reader-facing overview (2026-08-19): the quoted 2026-08-16 TCB-audit trust paragraph and its current-disposition note, the correction trails from the 2026-08-19 external claims audit, the perf-arc timing history, and the document's own provenance note. |
| [`todo-history-2026.md`](todo-history-2026.md) | Everything `TODO.md` accumulated up to 2026-08-19, moved out when the live file became a backlog an outsider can read: **Part 1** the per-arc journal (narrative entries, newest first), **Part 2** the old section structure with its prose and every completed item. Verbatim; the only thing not reproduced is the open items, which ARE the live `TODO.md`. Carries an arc → charter pointer table. |
| [`2026-08-19_symbolfrequency-panic-measurement.md`](2026-08-19_symbolfrequency-panic-measurement.md) | The full measurement record behind the accepted `Lean.LibrarySuggestions.SymbolFrequency` panic: why no project-local switch exists, why a module split cannot work, the deny-list surface that was measured and not taken, and how the panic reads in a gate artifact. `docs/OVERVIEW.md` keeps a compact statement of the disposition and points here. |
