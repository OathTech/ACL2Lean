# Phase 3 close-out — final report and merge proposal

Charter: `docs/plans/2026-08-08_phase3-closeout-charter.md` (ratified
at goal-set). Branch: `mdd/phase3-r7b`, HEAD 2b18fed, 63 commits over
`main` (a1f0e07). Every claim below is gated: three full
`just claim-gate` runs recorded TRUE_EXIT=0 on this close-out
(e7c59fb's re-pin, and the audit fix round at 2b18fed).

## Scoreboard (mechanical)

- Coverage sweep: **104/116 replayed — 45 unconditional + 59
  conditional** (was 33 + 71 at charter start; TWELVE rows became
  fully unconditional in the boot-rule re-pin). DP probes ✓62 ◌9 ✗0
  of 71, unchanged.
- Capstones: MSORT-IS-ISORT and QSORT-IS-ISORT replay with the FI
  step discharged in-sweep; conds are their genuine theorem-rule/
  tp/total residue (no usefi:, no gz boot rules). Disclosed asymmetry
  (audit O-3): QSORT's conds include rule:HOW-MANY-QSORT — one of its
  own FI obligations, green as a row in the same sweep; the
  mirror-registry application is the tracked fix.
- AtCanonical witnesses: all six constraint `rule:` premises per
  constant discharge; KEPT = 2 premises each
  (hrule_CONVERT-PERM-TO-HOW-MANY — the PCE-chain/R-lane deferral;
  husethm_ORDERED-PERMS — its dep tree's tau dp-facts), so these are
  PARTIAL non-vacuity witnesses, now labeled as exactly that.

## Queue disposition

1. **D1 in-scope half — DONE.** Witness-TP kits
   (`Imported/EquisortWitness.lean`, bodies verbatim vs the emitted
   `:DEFUN` events — audit-confirmed); the inner-ctx augmentation +
   demand-driven iterated rule pre-discharge in
   `instantiateParametricAt`; FOUR new D5 prelude constants
   (DEFAULT-CAR, DEFAULT-CDR, CONS-CAR-CDR, FOLD-CONSTS-IN-+) with
   the registry generalized to multi-no-shadow and WP3-pinned against
   emitted specs across three source books. Side effect taken as an
   engineering opportunity: the Imported/Sorting hand kits for those
   rules retired (registry = single home), five consumer wirings
   simplified, and a second gz pass added for totality-pulled rule
   fvars — net, the corpus-wide boot-rule strengthening above.
   Residue logged in the deferral log's D1 close-out update.
2. **D4 — DONE (gz half).** TEN new `gz_def_*` agreement lemmas
   (zero sorries) + the fail-closed `check-gz-agreement` ci gate with
   flag-rot detection; LEXORDER/EXPT flagged with corrected
   justifications. Scope-in-force refinement stays deferred (no
   driving book; refining would be speculative generalization).
3. **D3 (bounded) — LOG-AND-MOVE-ON**, per the charter's explicit
   clause. The BSORT node's exact anatomy is dumped and recorded in
   the deferral log (FI lmi tautology-dropped + 5-conjunct
   constraint-cl + chain to a clausify record closed by a tau
   verdict); the needed composition (teaching the FI arm's chain to
   traverse clausify + verdict tails) is its own Core.lean arm,
   judged past the bounded budget. Ceiling unchanged: ◌ at best until
   the bsort emission-family lands.
4. **Close-out audit — RUN, VERIFIED, SYNTHESIZED.** Two Opus
   reviewers (inside/outside, decorrelated skeptical briefs) per the
   pre-approved plan; both MAJORs verified at the cited lines before
   fixing. Record: `docs/audits/2026-08-09_phase3-closeout-audit.md`.
   Outside verdict: the alias-world composition IS ACL2's FI step,
   route a1 as ratified; nothing weakens a statement or fakes a
   result. Inside: ~20 verbatim artifact comparisons, zero
   transcription drift; the re-pin verified row-by-row from first
   principles.
5. **Fix round — APPLIED and gated TRUE_EXIT=0** (2b18fed): both
   MAJORs (docstring/comment honesty), the O-1 route disclosure, the
   O-2 ambiguity refusal (with its own regression-and-refinement
   incident honestly recorded), the gate-extraction and D5-criterion
   corrections, wording fixes. Follow-ups tracked in TODO, not
   silently dropped: capstone statement pins, content-level gz_def
   pin, HOW-MANY-QSORT mirror application, addDecl name-key
   hardening, AtCanonical KEPT-inventory pin.
6. **This report.**

## Deferral-log state

- D1 — done-except-R-lane-and-PCE-chain-and-tau (the R-lane leg is
  Mike's pre-ratified checkpoint; blocker attribution annotated as
  instrumented-run evidence).
- D2 — RESOLVED (pre-charter; the capstone FI discharge).
- D3 — bounded attempt closed with the composition plan on record.
- D4 — done except scope-in-force (no driving book).

## Open questions for Mike (none block the merge candidate)

- The compositional-replay note's ratification questions (unchanged).
- New from the audit (O-1): should the FI arm CONSUME the recorded
  constraint chain's proof instead of validating it and discharging
  the obligations premise-wise? Both are faithful at different
  granularities; the current route is sound and strictly
  more-replayed, but the chain-consuming route is closer to the a1
  bullet's wording. Natural to decide inside the compositional-replay
  ratification.
- The PERM-TLFIX R-lane checkpoint (pre-ratified, unchanged).

## Merge proposal

`mdd/phase3-r7b` at 2b18fed is the merge candidate: the whole R7b arc
(FnAlias semantic layer, the usefi discharge with the shallow-stack
pre-pass, the capstone FI rows, the equisort witnesses and
AtCanonical partial non-vacuity, the D5 boot-rule registry with its
corpus-wide strengthening, the D4 agreement-lemma gate), fully
audited with the fix round applied, local `just ci` green
(TRUE_EXIT=0 recorded in the head commit). Per the sandbox protocol,
merge gates on this local ci + sign-off at the moment of merge —
requested but NOT assumed. Prefer a fast-forward of main to 2b18fed.
After merge, the natural next charter is the full-sorting follow-on
arc (bsort fork batch + convert machinery + the R-lane checkpoint) —
scoped in the close-out charter's boundary section.
