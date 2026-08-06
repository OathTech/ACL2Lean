# The capstone-demo arc — sorts-equivalent by PURE REPLAY (+ audit remediation)

Status: DRAFT — awaiting MDD ratification.
Branch: `mdd/capstone-demo-arc` (opened at main c85d2be).

## Goal

Land the three `sorts-equivalent` capstones as native mirrors whose ENTIRE
mathematical content comes from replayed ACL2 reasoning:

- `msortL xs = isortL xs`, `qsortL xs = isortL xs`, and (under `true-listp`)
  `bsortL xs = isortL xs` — each decoded from the faithfully replayed
  ACL2 theorem, which ACL2 proves by FUNCTIONAL INSTANTIATION of the
  equisort book's abstract uniqueness argument
  (`strong-ssortfn1-is-ssortfn2` / `weak-sortfn1-is-sortfn2` over
  constrained sort functions).

The demo statement (ratified framing, 2026-08-06): *"ACL2 proved three
sorting algorithms equivalent via an abstract uniqueness argument with
functional instantiation; every step was replayed and kernel-checked in
Lean; here is `qsortL = isortL` as a native theorem, and Lean never saw
a proof of it — only ACL2's."*

**Binding negative constraint (the 2026-08-06 lesson).** A bridge that
supplies mathematical content from Lean/Mathlib — e.g. deriving the
equivalence via `eq_of_perm_of_sorted` from the sortedness+permutation
mirrors — is BANNED for the capstones. It solves the Lean problem with
Lean, demonstrating the opposite of the mission. Decode lemmas may
ELIMINATE REPRESENTATION (evaluator structure, `enc` transport,
order-embeddings, map-commutation sims); they may never prove a fact
ACL2 did not prove. This line joins the mirror criterion at Phase 4.

Simultaneously, this arc REMEDIATES the two 2026-08-06 external reviews
(`docs/audits/2026-08-06_overall-project-audit.md`,
`docs/audits/2026-08-06_full-acl2-forward-design-review.md`, both
verified finding-by-finding in-session): every finding gets a phase or
an explicit recorded deferral below — none is silently dropped.

## Escape hatch (binding, per CLAUDE.md Goal design)

The agent stops and reports, without further grinding, when remaining
work all gates on: (a) a user decision or MDD ratification, (b) the fork
batch review or any fork round-trip, (c) a ratified design boundary
(e.g. the rung-3 checkpoint scope), or (d) a frontier whose honest fix
is a NEW emission not in the ratified batch. Progress metric per phase
is its named exit criterion — not "rows advanced."

## Phases

### Phase 0 — artifact authenticity + doc truth (BEFORE any recapture)

Review-1 P0s and the cheap P1/P2s, landed first so the Phase-1 recapture
produces artifacts born complete:

- **P0-2 fatal capture**: every INCOMPLETE branch in
  `capture-proof-log.sh` becomes fatal; atomic write (tmp + rename on
  success only); no sidecar on failure.
- **P0-1 source provenance**: sidecar gains canonical source path +
  SHA-256 of the source `.lisp` + the include-closure identities;
  `check-log-provenance.sh` recomputes and compares (fail-closed).
  The fuller ACL2-emitted post-`ld` manifest is Phase-1 fork work
  (rides the batch as item 8).
- **P0-3 + P2-11 doc truth**: README trust model rewritten around the
  three properties (Lean soundness / statement authenticity / replay
  fidelity), aligned with CLAUDE.md's trust note; README stage 5
  corrected to the wired proof-log path (F5b); "no inference" text
  amended to name the expiry-held deviations; NativeMirrors header
  scoreboard regenerated from `liftCatalog` (also fixes P2-12's manual
  axiom-list drift risk: derive the gate list from the catalog).
- **P2-10**: `include_proof_log%` elaborator replacing the 33
  `.getD .done` sites (compile-time parse/reconstruction errors); static
  check banning the pattern in production modules.
- **P1-9 scoreboard separation**: assumed DP probes rendered in a
  separate section of the golden, never intermixed with replay counts.

Exit: `just claim-gate` TRUE_EXIT=0 with the hardened scripts; a
deliberately truncated log and a source-edited book both FAIL the local
gate (negative tests committed).

### Phase 1 — the fork batch round-trip (ONE rebuild + recapture)

The accumulated batch (close report, now 8 items) — **requires the
user's item-by-item review before the rebuild** (standing rule):

1. local `:LINEAR` snapshot; 2. `:FALSETS` + recognizer-tuple snapshot;
3. fc/type-alist provenance; 4. emit/defthm tag refresh; 5.
literal-boundary normalization steps; 6. include-book EDGE emission;
7. add-literal complement-close emission (PRIORITY — B1 expiry);
8. (NEW, review-1 P0-1) post-`ld` capture manifest: source identity +
include closure + explicit successful-completion record, ACL2-emitted.

On landing: retire ALL FOUR expiry-held mechanisms (R1→3, R2→2,
ground-hyp→2, complement-close→7) by replacing each with a direct read
of the emitted record; wire the include DAG (review-1 P1-8: offers
restricted to transitive includes); golden reviewed row-by-row.
Expected unlocks: termination:BSORT + 3 μ-registry bsort rows,
HOW-MANY-SMALLER-BNEXT, PCE, HOW-MANY-BAD-PAIRS-BNEXT's class.

Exit: gate green, four expiry markers GONE from the tree, bsort book
green or its residue honestly classified.

### Phase 2 — the abstract-world arc (equisort = the parametric encapsulate)

The 14 equisort rows ARE the abstract uniqueness theorem. Build per the
ratified r6-encapsulate design note: constrained functions as
world-parameters (never witness bodies — BUG-019 doctrine), scope
identity from `Development.scopes` (its consumer finally wires),
constraint clauses as the theorems' hypotheses. This is review-2's
Priority E / Stage-3 centerpiece — the strategic machinery, not
sorting-local work. `cov-encapsulate`'s 2 rows green here too.

Exit: equisort 14/14 replayed (or classified against a NEW ratified
boundary), `WEAK-SORTFN1-IS-SORTFN2` / `STRONG-SSORTFN1-IS-SSORTFN2`
green with world-parametric statements (L3 checked).

### Phase 3 — R7b functional instantiation

The `:CONSTRAINT-CL` composition: a functional-instance `:use` payload
discharges by (i) the abstract theorem's replayed statement under the
functional substitution, (ii) each constraint clause proved for the
concrete instances — all from emitted content (the R7a plain-`:use`
pattern extended; the R7 soundness design note governs). PERM-TLFIX's
rung-3 R-lane checkpoint sits here iff the capstone conds require it
(scope per the ratified equiv-lane design; a rung-3 build is its own
MDD checkpoint before construction).

Exit: the 3 sorts-equivalent rows replayed.

### Phase 4 — capstone mirrors + the demo artifact

- Native mirrors for the three capstones (decode-only bridges; the
  banned-content line above enforced in review).
- Review-1 P1-6: MUTATION TESTS land with these mirrors (swap the
  consumed replay theorem for a same-book neighbor / a tautology → the
  bridge must fail to build).
- Review-1 P1-5 tier split (`ACL2Semantic` / `DecodedValue` /
  `NativeLean`) ratified and applied to the catalog — an MDD item, since
  it amends the 2026-07-30 terminology and re-opens the flatten
  exemption's classification.
- The demo write-up: statements, axiom prints, and the honest trust
  story (what is kernel-checked, what is expiry-held, what is emitted).
- OPTIONAL (decode-only, post-capstone): the `List Int` restatement via
  order-embedding + map-commutation kits.

Exit: three capstone mirrors axiom-clean; mutation tests red-team the
seam; demo doc committed.

## Recorded deferrals (explicit, so nothing is "forgotten")

- **Review-1 P1-4 full statement-identity gate** (source translation vs
  log manifest): Phase-1 item 8 lands the artifact side; the Lean-side
  comparison gate is the FOLLOW-ON arc (it subsumes wiring `gen-world`,
  a tracked TODO). Not silently dropped — it is the first item of the
  next arc's charter.
- **Review-1 P1-7 typed conditions**: adopted in principle; lands with
  the include-DAG wiring where the condition sources become typed IDs
  (Phase 1/2 boundary); full typed-obligation structure is follow-on.
- **Review-1 P2-13 adversarial import tests**: one per open BUG lands
  opportunistically; the centralized ingestion preflight is follow-on.
- **Review-2 census (Stage 0)**: runs AFTER this arc (or as an idle
  side-task) — the user's demo ruling (2026-08-06) sets this arc's
  scope; the census then governs what comes next.
- **Review-2 certificate consolidation pace, apply$ isolation,
  coverage-contract matrix**: each needs its own MDD; queued for the
  post-arc planning session with the census in hand.
- **Review-1 N4/N6/N7 hardening**: N6 lands in Phase 0 (catalog-derived
  gate list); N4 (red-cond rendering) with Phase 1's golden re-pin; N7
  stays a recorded robustness note.

## Standing rules (unchanged, restated as binding here)

Claim-gate TRUE_EXIT=0 before any commit claiming green; golden re-pins
reviewed row-by-row; fork changes in ONE reviewed round-trip; merges
only on explicit sign-off at the moment of merge; audits committed to
docs/audits/ before fold-back; the carve-out drift test and the
replay-vs-infra test govern every new mechanism; no new name-keyed
registries where emission can express the fact (review-2 pause list,
consistent with the ratified expiries).
