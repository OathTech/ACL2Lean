# R2 charter — the fork batch (2026-08-14)

Branch `mdd/r4-wave0-refinement` continues (wave 0 committed at
fc06b33); R2 work lands on this branch (rename-at-merge if wanted).
Basis: the persisted fork-emission audit
(`docs/audits/2026-08-13_fork-emission-audit.md` — GAP-1 prototyped
in-image and WORKING; GAP-2 re-framed to per-leaf subterm verdicts;
item 3 = the fork deliberately discards the strong stored rule) and
the D-A ruling (reflect ACL2's type-set reasoning). Aim (the quest):
retire the `tp:` condition class so the corpus moves toward
unconditional — the demo's "no qualifications" bill.

## Scope

1. **GAP-1 — context-refined `:LEAVES`**: the ~15-line collector
   mirroring `type-set-rec` (acl2/defuns.lisp:12022) + the
   ld.lisp:5668 caller, per the audit's working prototype.
2. **GAP-2 — per-leaf subterm verdicts** (same collector; primitives
   store no TPs — emit the 7/32 subterm verdicts).
3. **`:ALL-TPS`** — stop discarding the stored strong rules
   (ld.lisp:5601 `gz-definitional-tp`); new field in both emitters.
4. **Parser** (ProofLog.lean:1134) + consumers (Provers.lean tp-arm:
   consume the new emissions; the D-A ts-algebra only as far as the
   emissions demand — no speculative library).
5. **Fold-in scouts (same round-trip):** the recognizer-under-IF
   termination trio (COUNT-DOWN/MY-EVENP/CD2: `CONSP` of an IF-valued
   term, no TP hypothesis — determine whether GAP-1/2 emissions cover
   it; if an additional emission is needed, add it NOW) and
   CLASSIFY-POS (the type-set-equality consp-evidence cell — same
   question).

## Protocol (binding)

- **Fork sequencing:** ALL fork edits committed in the submodule
  FIRST → build the image → recapture-all → only then Lean-side
  consumption. No artifact overwrites while any gate/sweep runs.
- **TRACE-LOG tagging**: every inserted region tagged, round-trip
  rule for emit/ origins; `just check-acl2-tags` before the image
  build.
- Recapture is ALL books (never partial); goldens then move —
  expected movement is condition retirement ONLY (rows flipping
  cond→unconditional, DISCHARGE tags gaining leaves); any OTHER
  movement: STOP, diagnose row-by-row before repin
  (golden-review discipline).
- Standalone coverage-book runs need `--tstack=524288`.

## Escape hatch

Stop and report if: a fork edit doesn't reproduce the audit's
prototype behavior (contradicts a persisted probe — report, don't
improvise); the recapture moves rows outside the condition-retirement
class; the trio/CLASSIFY-POS turn out to need type-set machinery
beyond D-A's scope (a design fork); or image build/recapture fails
irrecoverably in-sandbox.

## Exit

`tp:` census materially reduced (report the exact before/after
counts); the trio + CLASSIFY-POS adjudicated (fixed or
frontier-with-cause); goldens repinned row-by-row-diagnosed; full
claim-gate; ARC LOG here.
