# Sorting-endgame arc — exit report (2026-08-11)

Charter: `docs/plans/2026-08-10_sorting-endgame-charter.md`, branch
`mdd/sorting-endgame` off main @ c9e1570. Baseline 110/116 (sorting
74/78) → **landing 113/116 (45 unconditional + 68 conditional),
sorting 77/78** — the charter's plausible landing, exactly. Every
claim point full-gated (`TRUE_EXIT=0`, artifacts in `.gate-runs/`).

## Queue disposition (all six items)

1. **Scouts — DONE, with a refutation.** Scout F REFUTED the
   order-derived-entry theory: both rung-serving witnesses'
   `:TA-ENTRY` is a verbatim TAIL clause literal
   (`rewrite-clause-type-alist` item (a), simplify.lisp:5065). Item F
   dropped from the fork batch (the charter's pre-authorized drop
   class, with a stronger reason than anticipated: the artifact
   already carried the derivation; the gap was the consumer's scope).
2. **Fork batch E+H+I — DONE** (submodule → 56de33b5a1, one
   round-trip + two fix commits, provenance discipline throughout;
   91/91 logs stamped). E: `emit/dedup-drop` at BOTH member-term drop
   sites (add-literal + add-literal-and-pt — the second site found
   when the *1/4.5 witness's drop bypassed the reviewed site). H:
   `:TERMINATION-RUNES` (per-admission as ruled; boxed so set-but-
   empty ≠ absent; never on the include-book recompute path). I:
   `:TAU-BASIS` (the fn-restricted slice as ruled) — with one
   MANDATORY STOP honored and fixed: the first recapture ballooned
   every slice-carrying world ~+90 defuns (the slice's gz implicant
   universe poisoned the cited-symbol closure); diagnosed, fixed by
   the gz-trim (predefined fns emit tau-pair identity only —
   deviation documented and reworded per the exit audit), re-swept to
   BYTE-IDENTICAL goldens.
3. **Consumers — DONE** (each claim-gated): dedup read-off (the
   expiry retired; an unrecorded skipped duplicate now hard-fails);
   the scout-F consumer (the recorded `:TA-ENTRY` hoisted as a
   demand — ACL2's own justification — and the LEXORDER-ORDER rung
   RETIRED); leaf-rune gating (tau half: the slice gates rule
   premises, FN-granular — exact-fired stays the ruled tightening;
   admission half: `:TERMINATION-RUNES` gates the recorded-
   termination bundle's offers); the tau EVG premise
   (`rule_premise_fact_evg`) → **HOW-MANY-RM-GENERAL ✓
   cond[tp:HOW-MANY]** (ablation-verified load-bearing in-session;
   the NOT-MEMB rule's content discharged by its own earlier replay)
   + two rows STRENGTHENED (the discharged dependency leaves their
   cond sets).
4. **2e — DONE, exceeding the wall.** Three walls burned:
   `consumeExpandDetail` (the recorded detail chain consumed
   stepwise — equal-self + the IFF collapse as a VALUE equality over
   the EQUAL-headed carrier read off the record); the recorded-drop
   clausify relaxation (`clausifyPure_sound_sub`, membership-only);
   the positioned unresolved probe (path-validated no-op) →
   **ORDEREDP-WHEN-BNEXT-CONSTANT ✓ cond[total:BNEXT]**, bsort 8/8,
   ORDEREDP-BSORT's rule: cond discharged. The p8 pattern book
   honored its MDD completion criterion: GREEN ROW + NATIVE MIRROR
   (`cons_neq_detail_native_driver`, decoded FROM the replayed
   statement, axioms-clean) + the pin flipped to assert the green.
   **RULING ASK (M1)**: the implementation substitutes value
   equality for the approved nilEquiv weakening (stronger relation,
   narrower coverage; nilEquiv held as a loud-frontier fallback) —
   please ratify or amend (docs/audits/2026-08-11 audit, M1).
5. **W3 one-hyp lift + pins — DONE**: the class-2 bridge admits one
   fn-free-hypothesis constraints (world-crossing by fn-freeness),
   and a hyp-free consumer twin may discharge a conditional
   constraint (strictly stronger) → **BSORT-IS-ISORT ✓** (the usefi
   DISCHARGED; the fi-self vacuity GONE — the D1 refusal note in the
   catalog retired). EIGHT statement pins in
   `Tests/SortingPinsEndgame.lean` (the seven planned + HOW-MANY-
   RM-GENERAL added in the audit fix round), all against the SWEEP'S
   OWN registered constants (no duplicate replay; pins and sweep
   cannot drift), all axioms-clean.
6. **Exit audit — DONE** (2 Opus inside/outside, pre-approved;
   synthesis: `docs/audits/2026-08-11_endgame-arc-audit.md`). Both
   reviewers verified the three headline rows CLEAN and NON-VACUOUS
   (the outside reviewer re-derived HOW-MANY-RM-GENERAL's pin from
   the `.lisp` source independently). One DEFECT (dedupDrops
   clause-scoping — fidelity-only) fixed with six CONCERNs in the
   round; two items to Mike (M1 above; M2: the tau gate is
   fn-granular). Follow-ups tracked in TODO.

## Open user gates carried out of the arc

1. **M1** — ratify/amend the 2e value-equality substitution.
2. **M2** — acknowledge the fn-granular tau gating (the ruling's
   own "exact-fired later tightening" remains the path).
3. (Standing): the R-lane rung-3 arc (PERM-TLFIX → sorting 78/78 —
   the last row; design pinned, emission prerequisites landed).

## Merge proposal

The branch is ready to propose: charter executed end-to-end (six of
six items, no deferrals), one mandatory stop honored with a
diagnosed fix, every claim point full-gated with in-repo artifacts,
goldens re-pinned row-by-row (audit-verified diff-by-diff — no
unreviewed change), the audit synthesized with every finding
dispositioned or tracked. Per the standing rule I am NOT merging —
this is the report-and-ask. If approved: fast-forward local main;
pushes remain yours outside the sandbox (fork FIRST:
acl2 @ 56de33b5a1, then main, then `just check-push-ready`).
