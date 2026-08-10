# Sorting endgame arc — charter

Branch `mdd/sorting-endgame` off main @ c9e1570. Baseline: 110/116
corpus (45 + 65); sorting 74/78. The arc executes the 2026-08-10
rulings: the consolidated fork batch (E/F/H/I, one round-trip), its
consumers, the 2e composition (design ruled before build), and the W3
one-hyp lift. Plausible landing: sorting 77/78, leaving only
PERM-TLFIX for the R-lane arc. ("Endgame", not another "completion" —
the last arc of consumer machinery before the R-lane finisher.)

## Queue

1. **SCOUTS (read-only, find-outs back to Mike before any fork
   edit).** Three sites need pinning: (F) where the type-alist binds
   an order-derived disequality entry (assume-true-false /
   type-set-rec path); (H) where the admission machinery's rune set
   for a termination clause is in hand (the measure-conjecture path);
   (I) whether the tau verdict site can cheaply report its fired rule
   set (upstream tau is deliberately ttree-free — the ruling's one
   open implementation question). Item E's site is already pinned
   (simplify.lisp:154). The scouts' exact site+shape proposals
   complete the item-by-item review; a diffuse or expensive site
   comes back as a find-out, possibly dropping that item from the
   batch honestly.
2. **THE FORK BATCH — ONE round-trip** (user-approved composition
   E+F+H+I; content review completed by item 1): tag per the
   round-trip rule, `check-acl2-tags`, commit-fork → build-acl2 →
   recapture-all (the provenance discipline), goldens row-by-row.
   Expected row changes: NONE from E/F/H (consumers become
   read-offs); item I's records enable the tau-leaf consumer (item
   3). Any other drift is a mandatory stop.
3. **CONSUMERS, row by row**: (a) `dedupSkipClose` trigger → the
   recorded drop (expiry retires); (b) the LEXORDER-ORDER rung →
   the recorded entry derivation (expiry retires); (c) the DP
   premise passes gain LEAF-RUNE GATING where the channel exists
   (the ruled DP-scan direction — narrowing, watched for behavior
   changes via the sweep); (d) the tau rule-set-basis consumer:
   HOW-MANY-RM-GENERAL's *1/3.2 leaf discharges from exactly the
   recorded runes' instances → the row's ✓.
4. **THE 2e COMPOSITION — DESIGN FIRST.** Present the short design
   (weakening the expansion-walk composition to nil-equivalence at
   BOOL-tolerant positions; the recorded detail chain consumed
   step-by-step) for Mike's ruling BEFORE building. On approval:
   build, landing ORDEREDP-WHEN-BNEXT-CONSTANT (and discharging
   ORDEREDP-BSORT's rule: cond).
5. **THE W3 ONE-HYP LIFT**: extend the class-2 constraint-premise
   bridge to one-hypothesis rules (TRUE-LISTP-SORTFN1/2) —
   BSORT-IS-ISORT's usefi discharges and the fi-self marker lifts;
   its statement pin + catalog entry land here. Also: the queued
   statement pins for the four restructure-arc greens (the
   linear-hyp pin helpers).
6. **Exit audit** — proposed for pre-approval at goal-set, the
   established shape (two Opus, inside: the new consumers vs the
   recorded payloads + the recapture provenance + re-pins; outside:
   statement strength of the newly-green rows + the drift test on
   the rune-gating narrowing) — then the fix round (TRUE_EXIT=0,
   gate artifact) and the exit report with the merge proposal.

## Discipline

Two-tier gating (full claim-gate + .gate-runs artifact at re-pins
and claim points; labeled fast-gates for intermediates). Inert files
only while gates/sweeps run; fork sequencing commit → build →
recapture. Every new offer class ships with self/chronology gates
from day one (the vacuity family's standing lesson).

## Exit criterion + escape hatch

Done = items 1–5 landed or honestly logged at named walls (a scout
find-out that drops a batch item, a pending user ruling on the 2e
design, or a fork round-trip surprise are all honest exits for their
items), the audit run/verified/synthesized, the fix round gated
TRUE_EXIT=0, and the exit report with the merge proposal.
ESCAPE HATCH (binding): the agent may declare an early exit at any
time, for any reason or none — an honest interim report is a success
outcome; fidelity rules and drift tests override completion
pressure. MANDATORY-EXIT triggers: any green-row flip without a
diagnosis in hand; recapture drift outside the expected surface;
any fix that would weaken a statement or infer an unrecorded step;
the 2e build proceeding without the design ruling.
