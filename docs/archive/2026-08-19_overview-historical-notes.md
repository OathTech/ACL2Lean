# Historical passages removed from `docs/OVERVIEW.md` (2026-08-19)

> Dated record. Nothing here is current state; where it conflicts with
> [`docs/OVERVIEW.md`](../OVERVIEW.md), [`docs/LEXICON.md`](../LEXICON.md) or
> `CLAUDE.md`, those win.

`docs/OVERVIEW.md` inherited the repository `README.md` wholesale on
2026-08-19 and with it that file's accretion: dated audit quotations,
incident asides, correction trails, and instructions that were superseded
and then kept as annotations. The restructure into a reader-facing overview
removed those passages from the live document. They are reproduced below
**verbatim**, each with the reason it was written and where the same
information now lives.

---

## A. The document's own provenance note

Removed from the top of the file. AGENTS.md already records the move
(`docs/OVERVIEW.md` — "this was `README.md` until 2026-08-19; the root
`README.md` is now a short front page").

> *This document was the repository's `README.md` until 2026-08-19, when the
> README was rewritten as a short front page and the technical detail moved
> here. Paths in prose are repo-root-relative; markdown links are relative to
> this file's location in `docs/`.*

---

## B. The quoted 2026-08-16 TCB-audit trust paragraph

This was OVERVIEW's "two-sentence version" of the trust model. The quotation
itself is not original to OVERVIEW — it reproduces
[`docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md`](../audits/2026-08-16_eob-audit-a1-tcb-trust.md)
§Q4, which is the primary source and remains in place. The live OVERVIEW now
states the same three-property distinction in current terms rather than
quoting a dated paragraph and annotating it.

The framing sentence and the quotation as they stood:

> **The two-sentence version** (adopted 2026-08-16 from the end-of-branch
> TCB audit, `docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md` §Q4, whose
> wording this reproduces):
>
> > Every mirror theorem is a self-contained statement over its own
> > zero-import definitions, kernel-checked from exactly
> > propext/Classical.choice/Quot.sound — so nothing in the ACL2 pipeline,
> > however wrong, can make one false; you need only read that one spec
> > file and trust Lean's kernel. The further claim that these theorems
> > were proved *via ACL2 replay* rather than by a Lean-side shortcut is
> > not kernel-certified: it rests on generated proof templates,
> > build-failing seam/axiom gates at the waypoint layer (whose per-book
> > granularity and absence at the mirror level are known), and review —
> > that audit verified it holds today for all nine live artifacts by
> > direct proof-term inspection, and also demonstrated that a deliberate
> > author could evade the template gate, so treat "via replay" as
> > strongly-evidenced engineering, not mathematics.

### B2. The 2026-08-19 disposition note attached to it

Original to OVERVIEW, written when the external claims audit found the quote
stale (finding P1, "Binding status documents contradict the live product
claim"). Its content is now folded into the live trust-model section.

> *Current disposition (2026-08-19) — the quote above is DATED and stays as
> historical record.* Two of its particulars have moved: the mirror-level seam
> gate it records as ABSENT now exists (`ACL2Lean/MirrorProofs/SeamGate.lean`,
> build-failing) and mechanically finds **21** mirror products, each with a
> replayed-statement witness — not nine artifacts checked by hand. Its
> CONCLUSION is unchanged and still governs: "via replay" remains
> strongly-evidenced engineering, not mathematics — the gate catches detachment,
> not mis-pairing, and nothing in it makes attribution kernel-certified (see
> `docs/audits/2026-08-19_top-level-claims-audit.md`).

---

## C. The rewrite trail on the three-property trust model

A parenthetical recording that the section had been rewritten. The three
properties themselves are live and stay in OVERVIEW; only the trail is
archived. The audit it refers to is
[`docs/audits/2026-08-06_overall-project-audit.md`](../audits/2026-08-06_overall-project-audit.md).

> The long form — three DISTINCT properties, separately enforced (rewritten
> 2026-08-06 after the overall-project audit — the earlier text conflated
> them):

---

## D. The fresh-clone capture correction trail

The *substance* of this passage — why the whole log surface must be
captured — is live in OVERVIEW's build section. What is archived is the
correction trail: the record that the instruction used to be wrong, and how
it was found.

> **Why the whole surface** *(corrected 2026-08-19 — the instruction here used to
> capture only `simple.lisp` + `recon-tests/*.lisp` and call the rest optional,
> which cannot build the default targets; found by the external claims audit,
> `docs/audits/2026-08-19_top-level-claims-audit.md`)*

The finding is
[`docs/audits/2026-08-19_top-level-claims-audit.md`](../audits/2026-08-19_top-level-claims-audit.md)
§ *P1 — The documented fresh-clone build sequence cannot build the default
targets*, which carries the full build-graph argument.

---

## E. The perf-arc timing history

Attached to the cold-build row of the fresh-clone reproduction inventory.
OVERVIEW keeps the current measured per-module figures and the honest note
that no whole-build figure has been re-measured; the before/after history is
here.

> *These were ~50 min and ~8 min before the 2026-08-18 perf arc, which is what
> the ~2 h cold-build figure measured 2026-08-16 was dominated by; the
> whole-build figure has not been re-measured since.*

The perf arc itself is recorded in `docs/plans/` and `TODO.md`; the
end-of-branch claims audit that produced the ~2 h figure is
[`docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md`](../audits/2026-08-16_eob-audit-a1-tcb-trust.md)
and its sibling reports.

---

## F. The `WaypointCatalog.lean` header caveat, stated twice

OVERVIEW carried the same caveat in two places (the pipeline's waypoint stage
and the status section). It is live and true — the module facade's narrative
header covers only the first 18 catalog entries — so OVERVIEW keeps it, once.
The duplicate wording is recorded here only so the deduplication is visible:

> `Imported/WaypointCatalog.lean` is the module facade, and its header
> narrative covers only the first 18 entries (historical).

> the narrative header on `Imported/WaypointCatalog.lean`
> is historical and covers only the first 18 entries, so do not read status
> off it
