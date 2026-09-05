# NS1 charter — three word-truncation mirrors and their semantic foundation

Dated 2026-09-05. First goal of the
[post-sorting master plan](2026-09-05_master-plan.md).
**Status: C0 checked 2026-09-05; C1 semantic migration next. NS1 incomplete.**
The strategic direction and preflight choices are agreed. On 2026-09-05 the
user explicitly authorized ownership of the complex migration and the
subagents proposed below. Those authorizations persist throughout this goal;
do not ask for them again.

## The goal

From the pinned, unmodified `kestrel/bv/bvchop.lisp`, deliver **three complete
native Lean mirrors**: truncation is bounded, truncating twice is the same
as truncating once, and truncation preserves values already in range.
Their proofs must come through faithful ACL2 replay, with every required
dependency discharged. Include the semantic and generator repairs necessary
to make that import work, and preserve all existing sorting/Basics products.

This deliberately combines the assessment's feasibility work and first
product increment into one ambitious goal. Its end state is not a report,
parser support, a successful capture, or one isolated generic lemma. Internal
checkpoints make the prerequisite work reviewable without converting each
one into another user interaction.

**Early exit:** stop incomplete if every remaining route requires an
unapproved semantic scope, a new fidelity/trust ruling, an excluded proof
mechanism, a change to the three native specifications, or unavailable
external state. Name the actual artifact/node, remaining conditions, and
smallest decision that would reopen progress. A newly encountered replay
frontier within the agreed scope is work to do, not a reason to stop.

## Exact result contract

The source theorem names and formulas are in
[`bvchop.lisp`](../../acl2/books/kestrel/bv/bvchop.lisp). Its operation is
defined in [`bvchop-def.lisp`](../../acl2/books/kestrel/bv/bvchop-def.lisp) by
`(mod (ifix x) (expt 2 (nfix size)))` on the logical path.

The native specification uses **all natural widths and all integer
inputs**, including width zero and negative inputs. The following declarations
are implemented in [`Mirrors/WordOps.lean`](../../ACL2Lean/Mirrors/WordOps.lean);
their proofs remain the goal of NS1:

```lean
namespace ACL2Lean.WordOps

def wordClip (width : Nat) (value : Int) : Int :=
  value % (2 : Int) ^ width

def wordClipBound : Prop :=
  ∀ (width : Nat) (value : Int),
    wordClip width value < (2 : Int) ^ width

def wordClipIdempotent : Prop :=
  ∀ (width : Nat) (value : Int),
    wordClip width (wordClip width value) = wordClip width value

def wordClipIdentity : Prop :=
  ∀ (width : Nat) (value : Int),
    0 ≤ value → value < (2 : Int) ^ width → wordClip width value = value

end ACL2Lean.WordOps
```

| Native proposition | ACL2 theorem consumed |
| --- | --- |
| `wordClipBound` | `bvchop-upper-bound` |
| `wordClipIdempotent` | `bvchop-of-bvchop-same` |
| `wordClipIdentity` | `bvchop-identity`, with the generic correspondence between `unsigned-byte-p` and the stated integer bounds |

The names passed the existing collision linter at C0. The mathematical
formulas are the contract. The bound does not
silently add a separate nonnegativity theorem; additional useful results
belong to their own replayed source facts.

The `%`/power definition must be connected to the ACL2 logical operation by
a kernel-checked generic correspondence. Proving idempotence directly with
a Lean modulo lemma is not that correspondence and does not count as the
target proof. Generic representation/core-logic proofs are allowed; book
theorem content always enters through replay. The underlying replayed
statements retain their actual untyped ACL2 formulas. The native results
are explicitly typed restrictions, not claims of unrestricted equivalence
between the Lean and ACL2 value universes.

**Shop-window limitation (2026-09-05):** these are elementary modular laws,
so they offer limited protection against accidentally proving the result
through existing Lean arithmetic lemmas. They remain the agreed NS1 targets
because they exercise the semantic migration and the complete mirror path.
The master's target-selection preference favors more substantial proofs in
later goals. NS1 must establish faithful use of replay through the actual
proof route; the difficulty of its native propositions supplies little
independent evidence of that attribution.

## Starting evidence and the main risk

The [assessment](../notes/2026-09-05_next-north-star-assessment.md) records
the baseline at ACL2Lean `06ccb8e` / `v0.1.0`, Lean 4.33.0, and fork
`e8d78e513d6867d04002f0df644da1723cc96e89`. A fresh capture of `bvchop`
completed with 116 QEDs for 116 local theorem events, but the complete log
fails parsing on `#C(0 1)` in an included arithmetic theorem. No `bvchop`
proof tree or downstream replay frontier has yet been measured.

The agreed remedy is a proper repair of **BUG-009**, not a parser token
that represents complex values incorrectly or discards the offending event.
Adding values to `SExpr` changes the domain quantified over by existing
proofs. The migration must account for all of the following:

- Canonical exact complex-rational values: rational components, normalization
  to an existing rational when the imaginary component is zero, and no
  duplicate or nested-complex representations. Preserve the canonical
  rational guarantees established for BUG-012.
- Reader, printer, equality, reflection, and primitive evaluation on the
  enlarged numeric domain. This includes arithmetic, recognizers,
  real/imaginary parts, and ACL2's actual completion behavior outside guards;
  measure the behavior against the pinned ACL2 implementation.
- The distinction between `RATIONALP` and `ACL2-NUMBERP`, and all proofs or
  DP registrations that currently exploit their coincidence.
- `ACL2-COUNT`, numeric/order semantics and order proofs, and the totality
  and induction branches currently closed because `COMPLEX-RATIONALP` is
  constantly false. Those branches need real proofs on the enlarged domain.
- Type-set index 6 becoming inhabited. Remove the complex-bit discount in
  `TsFacts.tsAcl2MaskOk` in the same coherent migration; retaining it is not
  an acceptable transitional completed state.
- Existing native embeddings, correspondence lemmas, stored rule proofs,
  differential classifications, and all generated consumers affected by the
  type change. Finish with BUG-009 closed under its actual semantic scope.

These are known impact areas, not a claim that the complete repair is already
designed. The first internal checkpoint must inspect all relevant source
sites and produce the concrete numeric representation/design before changing
the value model. It must not infer ACL2's complex arithmetic from Lean's
ordinary ordered-field intuitions.

## Work included in the agreed autonomous scope

The run owns the following without repeated permission requests:

1. The coherent numeric migration above and repairs required to preserve
   existing semantics, proofs, and products. Choose the concrete canonical
   representation and module decomposition against the stated invariants.
2. Capture and provenance of the selected book and its actual dependency
   proofs, including the necessary certification/package setup for those
   dependencies. Establish the exact selected proof closure as real trees
   become available; do not assume inclusion captured their proofs.
3. Source-compatible fork instrumentation fixes needed to replay recorded
   rewrite, induction, admission, or existing DP-leaf shapes on that closure.
   Tag changes, rebuild the image, recapture affected inputs, and keep the
   source book's statements, definitions, and proof hints unchanged.
4. General primitive/definition correspondence, execution generation,
   hypothesis discharge, and decode/transport extensions required by the
   three results. Add new core semantics only for justified ACL2 core
   operations; an ordinary library function does not become a trusted
   primitive merely to shorten its proof. Reuse existing world transport.
5. Removal of special cases encountered on this route, extraction from real
   repeated implementations, focused tests, bug-index updates, and measured
   decomposition of expensive terms. No unrelated cleanup campaign.
6. Integration of the three mirrors with the existing statement, seam,
   purity, naming, axiom, provenance, and independent-validation machinery.
   Prepare local commits and a merge candidate under the existing gate tiers.

The generator work must pay off inside NS1: the second and third results use
the first result's operation/representation kit and common decode machinery.
Do not write three bespoke Lean proofs and defer the shared route to NS3.
A fully general import frontend or a separate external-user acceptance
experiment is not required until NS3/NS4.

## Boundaries fixed before launch

| Topic | Agreed disposition |
| --- | --- |
| Numeric-domain migration | **Include the full BUG-009 repair and its regression consequences in NS1. Explicitly authorized 2026-09-05.** Choose and validate its concrete canonical representation at C0. |
| Native representation | Use the Nat-width / Int-input / Int-result specification above. Preserve negative inputs and width zero. `BitVec` ergonomics can follow when a consumer requires them. |
| Targets | All three named source theorems. Choose their implementation order from actual proof dependencies; no substitution of easier targets. |
| Capture and fork | Local instrumentation/capture changes within the existing fidelity contract are in scope. No modification of upstream book content or hints; no log surgery. |
| Additional proof mechanisms | General GL, arbitrary metafunction/clause-processor replay, a new SMT backend, forcing-round composition, and guard-proof replay are excluded from NS1. If one becomes unavoidable, present its actual obligation and stop for a scope decision. Do not skip the record. |
| Trust and glue | Existing kernel/trust/fidelity rules remain. No new axioms, solver verdict trust, or hand proofs of ordinary book dependencies. |
| Resource use | Use normal focused development and full claim points. Optimize measured bottlenecks; do not solve the run by permanent heartbeat/recursion-budget inflation. No wall-time or token estimate is asserted before the unknown proof closure is visible. |
| Parallel agents | Four review-only tasks are authorized, as specified below. No implementation delegation or extra review campaign is implied. |
| Integration | Finish with verified local work and a reviewable candidate. Merge, push, and publication still require their explicit point-of-action authorization. |
| Fallback | `misc/records.lisp` remains a proposed alternative only after reporting why NS1 stopped. Switching does not make this goal complete. |

## Internal checkpoints and completion receipts

Checkpoints are evidence and review points, not separate goals or automatic
requests for user approval. Continue after resolving findings within the
agreed scope. Preserve a coherent checked commit before a broad migration;
temporary WIP is labeled and never presented as a completed product.

| Checkpoint | Required artifact |
| --- | --- |
| **C0 — Establish the contract and numeric design** | Fresh baseline checks; capture reproduction; pure native spec; source-based numeric behavior/impact inventory; concrete canonical representation; scoped test plan. Review the design before building downstream proofs on it. |
| **C1 — Semantic migration closes the ingestion boundary** | BUG-009 repaired across the model and its affected proofs; relevant differential tests pass; real `bvchop` capture passes the complex-number boundary; existing coverage/products restored. Record any next parse/reconstruction frontier rather than claim replay success. This checkpoint alone does not complete NS1. |
| **C2 — First complete mirror** | Complete reconstruction of the selected capture and the needed dependency trees; one of the three named targets replayed and transported, conditions discharged, axiom receipt and exact source/spec pairing checked. Record the shared kit now used by the next target. |
| **C3 — All three results** | Three checked native mirrors; replayed dependency closure complete; common operation and decode routes used across the results; unselected book frontiers separately reported. No all-book coverage claim. |
| **C4 — Verified candidate** | All acceptance checks below pass; final independent review findings resolved; fresh full claim-gate artifact and independent product-validation evidence; concise change/risk summary ready for merge review. |

**Completion is the conjunction of these requirements:**

- The three native propositions have complete proofs, each consuming the
  corresponding source theorem through replay; no theorem-specific content
  proved by an alternative Lean route.
- All required proof, totality, type, and dependency obligations are closed.
  Native mathematical hypotheses such as the identity theorem's bounds are
  exactly those of the contract, not hidden replay conditions.
- Full complex-rational semantics in scope are implemented and
  differentially checked; BUG-009 and its documented domain-restriction
  adaptations are retired. Existing supported behaviors are preserved or
  corrected with explicit source evidence and regression pins.
- The baseline 116 theorem rows remain unconditional and all 21 existing
  native products retain their statements and accepted axiom receipts.
  Any representation-induced golden/proof movement is explained under the
  normal protocol; no failing result is removed. The three new products
  also pass the relevant purity/naming/seam/axiom checks.
- A fresh full `just claim-gate` records `TRUE_EXIT=0`. Extend and run the
  existing comparator/nanoda validation for the new native propositions.
  Missing external validation is reported honestly; it is not a passed gate.
- The charter records commands/artifact locations, source/fork/toolchain
  identities, the actual dependency closure, before/after timings at the
  measured granularity, and remaining unselected frontiers. TODO contains
  only surviving work from this arc; detailed history stays here or in its
  linked notes.

## Authorized review allocation

**Authorized by the user on 2026-09-05:** two reviewers at C0, and two at C4,
using the current session model. Total: four planned reviewer tasks plus
the primary agent's independent verification of findings. C0 reviewers
cover (a) numeric semantics/canonicity against ACL2 and (b) migration effects
on type sets, replay, and existing products. C4 reviewers cover (a) implemented
semantics/regressions and (b) source/statement attribution, replay fidelity,
conditions, and final axiom receipts. They read primary sources and run the
relevant checks; they do not simply endorse this charter.

The user selected this over the cheaper solo-review option. It bounds review
to two specific checkpoints instead of a standing agent team. No model change,
extra audit wave, or implementation delegation is implied by approval of
these four tasks. Review findings must be verified before changing code;
gates themselves retain the simpler honest-mistake standard.

The authorization is explicit because [CLAUDE.md](../../CLAUDE.md) says:
“Seek sign-off on the audit plan BEFORE triggering any subagent.” No
subagents were launched during planning. This requirement is satisfied for
the allocation above. Both C0 reviews have now run; the two C4 tasks remain
authorized for their concrete checkpoint artifacts, without requesting the
same approval again.

## C0 execution evidence

- **Fresh baseline:** invalidated coverage and ran `TMPDIR="$PWD/.tmp" just
  claim-gate` before changing proof code. Receipt
  `.gate-runs/b452b70-20260905T221458Z.log`, `TRUE_EXIT=0`; 116/116 rows
  unconditional and golden byte-identical. All existing product checks passed.
- **Fresh ACL2 image and capture:** the image's system-books directory points
  inside this worktree. The unchanged BVCHOP source produced 436,039 log lines
  and 116/116 QED/local-theorem events. Parsing still rejects `#C`. Source and
  log hashes, commands and probe transcripts are recorded in the
  [numeric design](../notes/2026-09-05_ns1-numeric-design.md).
- **Native specifications:** the four WordOps declarations build, and the
  existing naming linter reports 59 names with no collisions. No new mirror
  proof or product is claimed.
- **Reviews:** [numeric semantics](../audits/2026-09-05_ns1-c0-numeric-review.md)
  and [migration consequences](../audits/2026-09-05_ns1-c0-migration-review.md)
  completed. The primary independently checked the substantive findings;
  the design note records the adopted repairs. Newly reproduced BUG-028
  (zero-denominator reader) and BUG-029 (numeric term-weight saturation)
  are included in C1, alongside BUG-009.
- **Design:** canonical core `Rat` components, nonzero imaginary part,
  existing rational constructors preserved; exact ACL2-value count for
  replay count measures, separate from structural `consCount`; coherent
  type-set, ordering and completion changes. No additional scope ruling
  or review task is needed before implementation.
- **C0 gate after adding specs:** `TMPDIR="$PWD/.tmp" just claim-gate`,
  `.gate-runs/b452b70-20260905T223811Z.log`, `TRUE_EXIT=0`. This run reused
  the freshly checked baseline coverage artifacts; WordOps and its naming
  consumer were newly built. All existing products remain unchanged.

## Resume record

- **Current artifact:** approved planning docs committed on `main` at `b452b70`;
  execution worktree `/home/dev/projects/ACL2Lean/.claude/worktrees/ns1-bvchop`,
  branch `mdd/ns1-bvchop`. C0 baseline, specifications, numeric design and
  both authorized reviews are checked. Proof/model code remains at the
  assessed release baseline; WordOps contains unproved specifications only.
- **Last observed blocker:** full `bvchop` log parsing rejects `#C` before
  reconstruction. Reproduction is in the assessment.
- **Settled preflight choices:** the run owns the numeric-model migration;
  the two pairs of review-only subagents are authorized. No preflight
  questions remain pending.
- **Next action:** implement C1 using the
  [adopted numeric design](../notes/2026-09-05_ns1-numeric-design.md), then
  inspect the real BVCHOP proof tree at its next ingestion/replay boundary.
  Do not restart candidate-book selection or implement an unrelated backlog.
- **Execution outcome:** C0 checked; C1–C4 and all three new mirror proofs
  remain open. NS1 is in progress.
