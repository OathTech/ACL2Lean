# Mirror closeout arc — charter

Branch `mdd/thin-lean-boundary` off main @ 90412ff (the thin-Lean
purge + audit fix round merged; rulings recorded @ 93a1c49 —
`docs/notes/2026-08-11_thin-lean-boundary.md` is the binding boundary
text). Baseline: corpus 110/116 (45 + 65); sorting 74/78 (the three
capstone rows ASSUMED ◌ on named replay debt + PERM-TLFIX open);
catalog 113 entries (24 native / 20 nativeSorried / 30 pending / 39
replayedOnly); 18 FORBIDDEN-DEBT sorries; ~145 hand lines per catalog
native.

The arc cues up the FINAL sorting-book closeout by resolving every
MIRROR-SIDE issue: after it, each sorting row has a settled, gated
catalog disposition, the iso/decode layers are generated rather than
hand-written, and the capstone area reads as a demo — a visitor can
see exactly what they must trust and what is untrusted-but-checked.
NOT in scope: the replay-side debt unlocks (R-lane, TP-replay
discharge, with_termination admission coverage) — those are the
closeout arcs this one clears the ground for. The three capstone rows
STAY honestly conditional here; the demo presents that conditionality,
never papers over it.

## Queue

1. **OPENING RULED INCREMENTS** (each independent, own fast-gated
   commit; all four ruled 2026-08-11):
   (a) delete `prepareUseFi`'s `totsNames` parameter
   (ParametricInstantiate.lean; sole call site passes `[]`; golden
   unchanged);
   (b) the `hreplayed`-USAGE CHECK — every catalog DECODE proof must
   actually consume its replayed binder;
   (c) the SHAPE GATE — every mirror-layer theorem classifies as
   SIM / ISO-corr / ISO-enc / DECODE / registered SUPPORT (enumerated
   allowlist with one-line justifications, `d5Allowed` style);
   unclassifiable fails the build. The initial SUPPORT census (~21
   Sorting lemmas) is reviewed line-by-line at registration — a
   member the audits did not class clean is a mandatory stop;
   (d) F6: bring `Mirrors/P8ClausifyDetail.lean`'s native under the
   catalog (row/entry/seam/axiom gates), plus the metric record —
   `usefi:` added to the debt registry; the kept-condition census +
   hand-lines-per-native counter scripted so the numbers are
   measured, not asserted.
2. **INDUSTRIALIZATION WAVE — `derive_sim%`** (MUST precede any
   accumulator book; landing it here satisfies that sequencing rule).
   Build the generator: user supplies only the native def; the macro
   emits `fooExec`, `foo_exec_corr`, AND `fooExec_enc` via the T1
   (aligned structural recursion) / T2 (measure-change) templates.
   TEMPLATE FAILURE IS A HARD ERROR — never a hand-proof fallback
   (the ruled anti-smuggling gate); named hard frontiers: mutual
   recursion, non-`enc`/`boolEnc`/`intRep` readings, non-computable
   subjects. VALIDATION = regenerate the 11 existing `_enc` proofs
   through it (behavior-preserving: same statements, coverage golden
   unchanged, axiom sets unchanged); an existing iso the templates
   cannot regenerate is a design surprise → mandatory stop, back to
   Mike. Follow-on in the same wave IF it falls out cleanly: the
   DECODE-ASSEMBLY generator (all 36 decodes are a six-step fold over
   the `Formula` with the four enders in `Lifting.lean`) — otherwise
   log it as the next industrialization item with what blocked it.
   Measure hand-lines-per-native before/after.
3. **MIRROR WAVE — settle every sorting `.pending` row.** Enumerate
   the sorting-book `.pending` entries from the live catalog; each
   either (i) gains its native via the NEW machinery under the win
   states (discharge via replay or stay honestly conditional /
   `.nativeSorried`; NEVER a new discharger, never a hand `_enc`), or
   (ii) is re-dispositioned `.replayedOnly` with a doctrine-quality
   justification, or (iii) stays `.pending` ONLY with a named
   blocking frontier. Exit state: zero sorting entries whose
   disposition is "backlog"/unexplained. Non-sorting `.pending`
   entries (accumulator/zip/interleave) are OUT of scope — they wait
   for their book-family arc (and now have `derive_sim%` waiting for
   them).
4. **THE DEMO — DESIGN FIRST.** Present a short design for Mike's
   ruling BEFORE restructuring (this is a taste question, per the 2e
   precedent). Contents to design: (a) the TRUST-LEGIBLE FACTORING —
   split the per-book ball of mud (Sorting.lean 4575) into layered
   modules whose import discipline mirrors the trust boundary
   (sims/defs import no replay machinery; iso; decode as the only
   layer touching replayed statements), each under the module-size
   norm, behavior-preserving (statements/axioms byte-identical, one
   verifiable step per extraction); (b) the CAPSTONE SHOWCASE — an
   entry-point module + doc presenting the sorting capstones with
   their full trust story: TRUSTED = the Lean kernel + the semantic
   core (Logic/evalOpt/SExpr) + the enc/Rep layer, UNTRUSTED-BUT-
   KERNEL-CHECKED = the entire ACL2 pipeline and driver, VISIBLE DEBT
   = the sorryAx-carrying premises with their named unlocks; the
   `#guard_msgs` axiom pins as the on-page receipts; (c) the READER
   PATH — what a Lean-speaking visitor reads first, second, third.
   Execute on approval; goldens/pins byte-identical throughout.
5. **EXIT AUDIT** — pre-approved at charter-set, the established
   shape (two Opus + verification): INSIDE — generated-vs-hand proof
   equivalence, shape-gate/SUPPORT-census honesty, catalog
   dispositions vs the win states; OUTSIDE — a fresh-eyes
   Lean-speaking persona reads ONLY the demo path and reports whether
   the trust story is actually legible (what it thought it had to
   trust vs the true boundary). Then the fix round, full claim-gate
   TRUE_EXIT=0 + artifact, exit report with the merge proposal.

## Discipline

Two-tier gating (full claim-gate at claim points/re-pins; labeled
fast-gates for intermediates; batch within a fix round). Inert files
only while gates/sweeps run. Goldens row-by-row; any row flip without
a diagnosis in hand is a mandatory stop. Module-size ratchet on every
new file. The win states govern all new mirror content; the provenance
+ shape + axiom gates are the enforcement, and weakening a gate to
land an item is forbidden.
THE TWO-STANDARD RULE (adopted mid-arc, 2026-08-11 — now in
CLAUDE.md's audit section): adversarial review is reserved for
semantics/claims/records; gates are reviewed to the deterrent
standard (honest mistake / simple enough / deletable) and are NEVER
hardened against motivated evasion. The exit audit's gate dimension
is a DELETION review under that standard (the gate-cruft first
pass), not an attack round; speedbump gates gain threat-model
comments before the arc exits.

## Exit criterion + escape hatch

Done = items 1–4 landed or honestly logged at named walls (a template
surprise on an existing iso, a SUPPORT-census member the audits
didn't clear, a demo-design ruling still pending, or a decode-gen
blocker are all honest exits for their items), the audit
run/verified/synthesized, the fix round gated TRUE_EXIT=0, and the
exit report with the merge proposal. ESCAPE HATCH (binding): the
agent may declare an early exit at any time, for any reason or none —
an honest interim report is a success outcome; fidelity rules and
drift tests override completion pressure. MANDATORY-EXIT triggers:
any golden row flip without a diagnosis; the shape gate flagging a
survivor the audits classed clean; any restructure step that changes
a statement, an axiom set, or a pin; hand-writing an `_enc` or a
decode the generator claims to cover; the demo build proceeding
without the design ruling.
