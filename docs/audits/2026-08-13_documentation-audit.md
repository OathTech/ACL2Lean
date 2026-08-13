<!-- Recovered verbatim from the session transcript (agent final report,
     2026-08-13) and persisted 2026-08-13. Basis commit: main @ 4a600c8.
     Documentation normalization audit: 138 markdown files + module headers + Justfile + scripts, release-checkpoint triage.
     Findings feed the R-arc roadmap: docs/plans/2026-08-13_r-arcs-roadmap.md.
     Dated record — where terminology conflicts with docs/LEXICON.md, the
     lexicon wins. -->

All four sweeps are complete and I've verified the high-stakes claims myself. Here is the audit.

# DOCUMENTATION AUDIT — ACL2Lean @ main 4a600c8

**Surface inventoried: 138 markdown files** (55 `docs/plans/`, 50 `docs/notes/`, 24 `docs/audits/`, 1 `docs/comms/`, `LEXICON.md`, `BUGS.md`, 4 root, 2 nested READMEs) **+ ~20 Lean module headers, 33 Justfile recipes, 21 scripts.**

---

## 1. INVENTORY BY CLASSIFICATION

### (a) LIVE-CANONICAL — 9 docs + the code headers

| Doc | Verdict |
|---|---|
| `docs/LEXICON.md` | **CLEAN.** I mechanically verified every term it names against code (`derive_exec%`, `_of_replayed`, `driver_replayed%`, `parametric_replayed%`, FORBIDDEN-DEBT, `Imported/Waypoints/`, `check-mirrors-pure`) — all resolve. The one genuinely trustworthy doc. |
| `docs/BUGS.md` | **CLEAN.** Lexicon header at :7-9, machine-parseable, `check-bugs.sh` in ci, all 27 numbers present. Two nits: entries are in non-monotonic order (…027, 022, 020, 019, 018, 017, 012, 011); newest entry is 2026-08-02 — the entire Aug 3–13 arc logged no bugs. |
| `README.md` | **6 defects** (below) — the worst is a self-contradiction. |
| `CLAUDE.md` | **7 defects** (below), incl. two dead command/file references in binding rules. |
| `TODO.md` | **Structurally broken as a backlog** (below). |
| `docs/plans/2026-08-12_master-plan.md` | Correct lexicon usage; **"14 Props" wrong ×4**. |
| `docs/plans/2026-08-12_two-track-charter.md` | The doc that *fixed* the vocabulary; **"14 target properties" whose own enumeration sums to 13**. |
| `docs/notes/2026-07-22_pattern-map.md` | CI-gated, but the gate covers only books↔map bidirectionality, log presence, and ~50 grep pin-signatures — **not one word of the narrative**. Headline "26 REPLAY / 23 FAIL" is from 2026-07-23, never updated (reality moved 26/50 → 113/116). No terminology header. |
| `docs/plans/2026-06-10_generality-design.md` | Cited as "**the governing plan**" by README ×2 + CLAUDE + a TODO heading — **its own header says `Status: DRAFT for MDD review; feature work paused until ratified`**, its §0 says "17/37 driver-replayed", and its §6 uses pre-lexicon "mirror". Never given the terminology header the sweep gave TODO.md. |
| Code headers (`Mirrors/*`, `MirrorProofs/*`, `Waypoints/*`, `SimGen`, `ExecGen`, `IsoGen`, `WaypointCatalog`, `BranchFacts`) | **All clean.** Zero pre-lexicon vocabulary anywhere in Lean source. `SimGen.lean` even carries an in-place correction of its own earlier over-claim. Best-maintained layer in the repo. |

### (b) DATED-HISTORICAL — well-behaved: ~95 files
All 24 audits, ~48 of 50 notes, ~40 plans, `docs/comms/`. This project's append-a-correction habit is genuinely strong (`exec-counterpart`, `fail-closed-audit`, `mapping-plan-impact`, `consumer-queue-audit`, `phase3-exit-report` all carry dated errata). `docs/notes/2026-08-11_thin-lean-boundary.md` is the **exemplar**: ruling header + 2026-08-12 terminology header + explicit supersession pointer.

### (c) STALE-LIVE — the dangerous class: 6 items
1. **`AGENTS.md`** — last touched **2025-12-17**, 8 months before anything else in the repo. Pure Lake template: *"`Basic.lean` exposes `hello`"*, *"With no history yet"*, *"consider a `Tests/` namespace"*, and — directly contradicting CLAUDE.md — *"rely on sorry placeholders while sketching proofs."* Read by non-Claude agents. Highest-severity single file.
2. **`docs/plans/2026-08-11_demo-design.md`** — ends `## RULED (Mike, 2026-08-11): APPROVED as a first pass — build it.` It describes `docs/DEMO.md`, `Imported/Mirrors/Showcase.lean`, `Imported/Mirrors/Catalog.lean`. **None exist**; the build is archived to `archive/demo-2026-08` and is not an ancestor of main. Zero rollback note.
3. **`docs/plans/2026-08-13_basics-closeout-charter.md`** — baseline "mirrors proved 2/6", queue A–F open. HEAD (`4a600c8`) is that charter's **completed exit**. No ARC LOG appended.
4. **`docs/notes/2026-07-31_mirror-industrialization.md`** — "mirror" = waypoint throughout, no terminology header, and **actively cited as a live source** by `2026-08-01_sorting-absolute-arc.md` and TODO.md.
5. **`docs/notes/2026-07-23_mapping-plan-impact.md`** — CLAUDE.md cites its S1–S4 sequencing in the present tense; S1 and S2 verifiably landed 2026-07-23/25.
6. **`Justfile:62-64`** — `check-mirrors-pure` comment says Mirrors "may import only **Mathlib**/Std/Batteries". The script it calls excludes Mathlib (removed 2026-08-12; re-admitting it is a ruling). A reader trusting the comment believes a Mathlib import passes a gate it actually fails.

### (d) SUPERSEDED-UNMARKED
- **53 of 55 plans carry no closure marker of any kind.** Only `2026-08-12_pathfinder-charter.md` and `2026-08-12_tp-replay-charter.md` append an `## ARC LOG` / `## ARC COMPLETION`. Everywhere else, completion exists only in git.
- `docs/plans/2026-07-06_long-term-roadmap.md` — wholly superseded by the master plan, no pointer.
- **`docs/plans/2026-07-30_validator-lifter-arc.md:12-15`** — the single most damaging survivor. It states with maximum rhetorical weight: *"**Terminology + ground truth (MDD, 2026-07-30).** A *mirror* is only and exclusively the Lean-idiomatic native theorem proved FROM a replayed statement (`Imported/`, `NativeMirrors`)"* — a competing "ground truth" definition, pointing at a dead path, that the lexicon exists to retire.
- `docs/plans/2026-08-11_mirror-closeout-charter.md` — item 4 produced the rolled-back demo; unmarked.

---

## 2. SPECIFIC CHECKS — RESULTS

**"14 Props vs 13" — RESOLVED, and worse than framed.** It is not a disagreement *between* the two docs. Both say 14: master plan `:7`, `:134` ("PHASE D — sorting close-out (all 14 Props become theorems)"), `:145`, `:170`; two-track `:23`. **The file has 13** (I counted `def … : Prop` directly: `isort_ordered`, `isort_perm`, `msort_*`, `qsort_*`, `bsort_*`, `ordered_perm_unique`, `sorts_agree`, `sorter_unique`, `perm_iff_howMany`, `permWitness_complete`) — and the two-track charter's *own* parenthetical enumerates 13. The error originated in commit `449c6fd`'s message and propagated. **The definition of the release checkpoint is off by one in every doc that states it.**

**Release-checkpoint distance:** `Mirrors/Sorting.lean` = **0 of 13 Props are theorems**. The only 2 theorems in the file are kernel-demanded termination measures. Zero `sorry` — the file is honest. `Mirrors/Basics.lean` is 3 of 6.

**Pre-lexicon vocabulary in LIVE docs:** none in code, none in BUGS.md, none in LEXICON. Survives in: `validator-lifter-arc` (as "ground truth"), `generality-design` §6, `mirror-industrialization` (title + throughout), `pattern-map` (×2), `demo-design` + `mirror-closeout-charter` (`Imported/Mirrors/` namespace), `2026-08-06_overall-project-audit` (`Imported/NativeMirrors.lean`, `ACL2.Imported.Mirrors` — both dead paths, in a file with live open findings). TODO.md's occurrences are governed by its `:3` terminology header.

**README vs current architecture — 6 defects:**
- **Self-contradiction:** `:74-75` says the WaypointCatalog header "covers only the first 18 entries (historical)"; `:211-213` then sends the reader there for **"Live status"**. (This was P2-11's fix in the capstone-demo arc — "regenerate the header from `liftCatalog`" — later abandoned when the header was frozen as history; the README pointer never followed.)
- **The product layer is absent.** No `Mirrors/` or `MirrorProofs/` row in the layout table; the pipeline's stage 8 is "**Native bridge**" describing the waypoint layer in pre-lexicon framing. A newcomer reading README learns the metric and never learns the product exists.
- `:176`, `:209` governing-plan claim (above).
- `:94` cites `Tests/SortingPins.lean`; CLAUDE cites `Tests/DriverTests.lean`; there are actually four pin files.
- No two-category model, no 113/116, no mirror counts.
- Positive: **no demo/DEMO.md/Showcase reference anywhere** — the rollback was clean in README.

**CLAUDE.md status paragraph vs reality — 7 defects:**
- `:129-132` "the PRODUCT layer … **is the north star being built toward**" — three mirrors are shipped and `MirrorProofs/` exists.
- `:130` waypoints "exist as validated **HAND** proofs" — now generated (`mirror_iso%`, `mirror_transport%`, SimGen/IsoGen/ExecGen).
- **`:72` `Replay/ProofProducer.lean` does not exist** (it's `Replay/Driver.lean` + `Replay/Driver/`).
- **`:304` the binding two-tier fast-gate requires "focused `just replay` of the books the diff touches" — there is no `replay` recipe.** It existed at `84a6a47` (2026-07-17) and was removed; the binding rule was written 2026-08-07 against a dead command.
- `:143` "46 authored pattern books" — **actual 61** (gate output: `OK (61 books…)`).
- `:20` instrumentation "in `rewrite.lisp` / `simplify.lisp` / `axioms.lisp`" — actually **12 files, 225 tags**.
- `:421-433` the architecture block is still 3 layers; the waypoint and mirror layers do not appear.

**TODO.md coherence — this is the worst structural problem.** 4,526 lines / 300KB. Lines 4–3,387 are an unstructured reverse-chronological blockquote narrative with **zero headings and zero checkboxes**. All 49 open checkboxes live in the June/July tail, under headings like `### c3 — COMPOSITION (current focus; first end-to-end inductive proof)` and `## CURRENT PRIORITIES (confirmed with MDD 2026-07-06)`. I sampled 6 "open" items: `Totality from admission`, `Preprocess-chain replay`, `Discharge-leaf composition`, `recognizer + if-simplification nodes` — **all four shipped** (Totality.lean, replayPreprocessChain, replayDischargeLeaf, re_if_true). Only `gen-world` frontend replacement is genuinely open. It also carries `## THE GOVERNING PLAN — 2026-06-10_generality-design` (duplicating the stale claim) and `GOVERNS THE CURRENT ARC` for the 2026-07-26 audit, six arcs later. Mitigation that works: the `:3` terminology header.

**BUGS.md currency:** good. Open: 009, 010, 011, 013, 015, 016, 017, 018, 027, plus partial 022/023. BUG-027's "open until that emission lands" and BUG-026's "tracked in TODO.md" are the only forward pointers that need checking at release.

**Duplicate rulings / lexicon supremacy:** three rulings are stated normatively in 3+ places — the **tagging convention** (survey → CLAUDE.md verbatim → proof-tree-representation), the **DP carve-out** (CLAUDE.md → totality-from-admission → direct-proof-emission, worded slightly differently each time, and it is safety-critical), and the **two-standard rule** (CLAUDE.md normative + 3 citations). **No case of inconsistent content was found** — the risk is maintenance, not live disagreement. The inverse problem is sharper: **Mike's 2026-08-13 vocabulary-practice ruling exists only in `Mirrors/Sorting.lean`'s header and the TODO narrative — it is in neither CLAUDE.md nor LEXICON.md.**

**Findings I REFUTED (reported honestly, since a sub-agent raised them):**
- The 2026-08-06 audit's **two P0s are NOT open.** I verified the fix directly: sidecars now carry `source-path` + `source-sha256` + include-closure hashes + `log-sha256`, and `check-log-provenance.sh` recomputes them fail-closed inside `just ci`; `capture-proof-log.sh` is fatal on every incomplete branch and additionally requires an `(:CAPTURE-END … :STATUS :COMPLETE)` end record. Remediation is recorded in `2026-08-06_capstone-demo-arc.md` Phase 0. **The real finding is documentary: the audit file carries no closure marker, so it reads as two live P0s to anyone who opens it.**
- The one apparently-dangling doc reference (`2026-06-05_producer-triage.md`) self-discloses "**on that branch**". Not a defect.
- **My full cross-reference sweep over every `docs/{plans,notes,audits,comms}/*.md` path mentioned anywhere in the repo found zero genuine dangling links.** Likewise zero live references to `Demo/`, `DEMO.md`, `Showcase`, `Sims.lean`, `Debt.lean`, `TCB.lean`, `check-trust-imports`, `NativeMirrors`, `Imported/Mirrors`, `mirror-metrics` in any live doc, header, recipe, or script.

**WaypointCatalog historical scoreboard:** marking is *sufficient for a top-down reader* — the disclaimer is in caps immediately above the block ("it is HISTORY, not status. Count entries there, not here."). It is fragile against non-linear reading: inside the block the prose reverts to bare `PROVED` / `PENDING` with no inline date. Given README currently points *at* it for live status, fix the README pointer first.

---

## 3. RELEASE-NORMALIZATION WORKLIST (ranked by reader impact at the checkpoint)

**Tier 1 — a newcomer is actively misled (do before release)**
| # | Action | Scope |
|---|---|---|
| 1 | **Rewrite `AGENTS.md`** or reduce it to a pointer at CLAUDE.md | 1 file, ~20 lines; it currently authorizes `sorry` |
| 2 | **Fix the "14 Props" count → 13** in master plan (×4) and two-track charter (×1) | 5 line edits — but it is the definition of done |
| 3 | **Fix README's live-status pointer** (`:211-213`) to `liftCatalog` / `just driver-coverage`, resolving the self-contradiction with `:74-75` | ~4 lines |
| 4 | **Add the product layer to README** — `Mirrors/` + `MirrorProofs/` rows in the layout table; reframe stage 8 as waypoint→mirror per the lexicon | ~15 lines |
| 5 | **Adjudicate the governing plan.** Either mark generality-design as architecture-only + point README/CLAUDE/TODO at the master plan, or ratify it (its header still says DRAFT) | 4 edits across 3 files + 1 header |
| 6 | **CLAUDE.md dead references:** `ProofProducer.lean` → `Replay/Driver.lean`; `just replay` → a real recipe (or restore the recipe) | 2 lines, one in a binding gate rule |
| 7 | **Mark `2026-08-11_demo-design.md` ROLLED BACK** (+ the mirror-closeout charter's item 4) | 2 header blocks |
| 8 | **Fix `Justfile:62-64`** Mathlib comment | 1 line |

**Tier 2 — stale but not misleading-on-contact**
| # | Action | Scope |
|---|---|---|
| 9 | **CLAUDE.md status paragraph rewrite** — mirrors exist (3 shipped), waypoints are generated not hand-written, 61 not 46 books, 12 instrumented files not 3, correct pin files, 4-layer architecture block | ~25 lines |
| 10 | **TODO.md restructure** — split the 3,387-line narrative into `docs/notes/2026-08_arc-log.md` (dated record) and reduce TODO.md to a real backlog; re-verify the 49 checkboxes (≥4 sampled are shipped) | The largest single job; ~2h |
| 11 | **Terminology headers** on the 4 unmarked pre-lexicon docs still cited live: `generality-design`, `mirror-industrialization`, `pattern-map`, `validator-lifter-arc` (the last needs its "ground truth" clause explicitly retracted) | 4 × 3 lines |
| 12 | **Closure markers on plans** — at minimum the 6 most recent (`basics-closeout` has none despite being HEAD's exit); adopt the pathfinder/tp-replay `## ARC LOG` pattern | 6 × ~5 lines |
| 13 | **Close-out marker on `2026-08-06_overall-project-audit.md`** noting P0-1/P0-2 remediated in capstone-demo Phase 0 | 3 lines — prevents a future auditor re-raising them (mine did) |
| 14 | **Record the 2026-08-13 vocabulary practice** in CLAUDE.md + LEXICON.md | ~8 lines |
| 15 | Update `pattern-map`'s stale 26/23 headline; add "as of" to its narrative sections | ~5 lines |
| 16 | `mapping-plan-impact`: mark S1/S2 DONE | 2 lines |

**Tier 3 — hygiene**
17. Reorder BUGS.md numerically (~15 min). 18. Document `coverage-repin` in the Justfile (1 line). 19. Add an in-body date to `2026-08-10_restructure-arc-audit.md`. 20. Fix the dead paths in `2026-08-06_overall-project-audit.md` or header-note them. 21. `acl2_samples/recon-tests/README.md` lists 8 books; there are 18 (last touched 2026-06-06). 22. Mark `2026-07-06_long-term-roadmap.md` superseded. 23. Residual co-opted noun "mirror" at `Runner.lean:82`, `Provers.lean:1394`.

**Consolidate (decide, don't just edit):** the DP carve-out is stated at length in 3 places with drifting wording — pick one normative home (CLAUDE.md) and make the others cite it. Same for the tagging convention.

**Delete:** nothing. Every dated record is worth keeping; the problem is markers, not volume.

---

## 4. MISSING — what a release checkpoint needs and doesn't have

| Missing | Why it bites at the checkpoint |
|---|---|
| **A current architecture overview reflecting the two-category end-state** | The only end-to-end narrative is README's pipeline, which stops at the waypoint layer. When 13/13 Props land, there is **no document that explains what was achieved** in the vocabulary the lexicon fixed. Highest-value new doc. |
| **`docs/README.md` — a doc index / "how to read this repo"** | 132 files, no index, no reading order, no live-vs-record signal. A newcomer cannot tell that `LEXICON.md` should be read first and `demo-design.md` is dead. |
| **Release notes / CHANGELOG seed** | None exists. The material is all in commit messages and exit reports. |
| **A live-status doc (or a fixed pointer)** | README defers to "the repo", and the pointer it gives is a frozen historical block. There is no single place showing 113/116, 3 mirrors, 13 Props, open debt. |
| **A standard "DATED RECORD" header convention** | Only 5 of 132 files carry any supersession marker, and each is ad hoc. Define one string, apply it. |
| **A backlog that is a backlog** | Covered above; TODO.md cannot currently answer "what is left". |
| **Lexicon additions** | `mirror_iso%` / `mirror_transport%` (the transfer kit's actual entry points) and the vocabulary-practice ruling are absent. |

---

## 5. PROPOSED CANONICAL-DOC HIERARCHY

**Load-bearing and current (6 — everything else is a dated record):**
1. **`docs/LEXICON.md`** — vocabulary. Supremacy clause already stated; it is the only doc I verified end-to-end against code with zero defects.
2. **`README.md`** — the outside view: what this is, the pipeline through *mirror*, the trust model, how to build.
3. **`CLAUDE.md`** — the working rules: fidelity invariants, gates, audit practice. *Not* a status doc — move its status paragraph out (see #5).
4. **`docs/plans/2026-08-12_master-plan.md`** — the governing plan, explicitly superseding `2026-06-10_generality-design.md` (which is retained as the **architecture reference**, correctly labelled).
5. **`docs/STATUS.md` (new)** — the single live scoreboard: replay metric, mirror count, Props proved, open debt, expiry-held mechanisms. This is what README `:211` should point at.
6. **`docs/BUGS.md`** — fidelity divergences. Already canonical and gated.

**Second tier — current but domain-scoped:** `docs/notes/2026-07-22_pattern-map.md` (coverage, CI-gated), `TODO.md` (backlog, post-restructure), `docs/notes/2026-08-11_thin-lean-boundary.md` (mirror-layer boundary ruling).

**Everything else — dated record**, carrying one standard header. The rule to state in `docs/README.md`: *any file with a date in its name is a record of that date and is never current state; where it conflicts with the six above, the six win; where it uses "mirror" for a waypoint, read `LEXICON.md` first.*

**The one systemic fix behind most of this worklist:** completion is recorded in git and in *other* documents, never written back into the document that made the claim. Adopting the `## ARC LOG` closure pattern (already proven twice) as a merge requirement would prevent the recurrence of items 7, 12, and 13.
---

## CORRECTIONS (R0 execution, 2026-08-13 — appended, record above unchanged)

- **The CLAUDE.md `just replay` finding is REFUTED.** The recipe exists
  and works (Justfile:110, wired to the real `acl2lean-replay` exe;
  added at 84a6a47 and never removed — verified by `git log -S`).
  CLAUDE.md :304 needed no change; the audit's "removed recipe" claim
  was wrong.
- **The "14 Props" site list was wrong both ways**: master-plan :145
  and :170 carry no count; two-track-charter :68 (missed by the audit)
  does. Real total fixed: 4 sites (master-plan :7, :134; two-track
  :23, :68).

Everything else in the Tier-1 list executed as written (see the R0
commit on `mdd/r0-records`).
