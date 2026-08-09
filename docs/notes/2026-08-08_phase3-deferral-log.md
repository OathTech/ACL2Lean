# Phase 3 deferral log (running, append-only)

The binding mechanism of the Phase 3 charter
(`docs/plans/2026-08-08_phase3-r7b-charter.md`): any item whose honest
resolution needs a user decision, a fork-emission change, a TCB /
statement-derivation change, a ratified-boundary amendment, or a
merge/push is DEFERRED here — a dated entry (what / why deferred /
what it would unblock) COVERS the item. A deferral is a success
outcome, equal in standing to a green row.

Format:

    ## D<N> — <short title> (YYYY-MM-DD)
    - What: …
    - Why deferred: <the decision/change it needs, and whose it is>
    - Unblocks: <rows/items that become addressable once resolved>

---

> **D1 close-out update (2026-08-08, queue item 1 RESOLUTION — the
> in-scope half is DONE).** The witness-TP `dis_*` kits landed
> (`Imported/EquisortWitness.lean`: exec kits + `derive_exec_tp%`
> dischargers for SORTFN1-INSERT/SORTFN1/SSORTFN1-INSERT/SSORTFN1,
> bodies transcribed from the emitted `:DEFUN` events), and ALL SIX
> constraint `rule:` premises PER CONSTANT now DISCHARGE at both
> AtCanonical constants (wording per audit m7) — via the inner-ctx augmentation in
> `instantiateParametricAt` (tp/totality/equivrefl proof-term entries +
> the demand-driven iterated rule pre-discharge) and FOUR NEW D5
> prelude constants (`gz_rule_default_car`, `gz_rule_default_cdr`,
> `gz_rule_cons_car_cdr`, `gz_rule_fold_consts_in_plus` in
> `Replay/GzRules.lean`, registered in `d5GzRules`, WP3-pinned against
> emitted snapshots; the old Imported/Sorting hand kits + their
> consumer applications are retired — the registry is the single home).
> KEPT residue (2 premises, each with a named out-of-scope blocker):
> - `hrule_CONVERT-PERM-TO-HOW-MANY` — the PCE-IS-COUNTEREXAMPLE
>   recognizer frontier + PERM-TLFIX R-lane chain, exactly as deferred
>   below (the R-lane leg is Mike's pre-ratified checkpoint).
> - `husethm_ORDERED-PERMS` — ORDERED-PERMS's own tree carries tau /
>   fc-contradiction DP leaves that even its green sweep row holds as
>   `◌ assumed` dp-facts; the inner re-replay has no assumed-hypothesis
>   telescope to fall back to (tried: owning-book cfg retry — the
>   usefi-bridge pattern — still unprovable). Closing it needs either
>   the tau-frontier machinery or cross-WORLD mirror application
>   (registry constant at `orderedPermsWorldD` + world-agreement
>   crossing) — both outside this charter.
> (Attribution note, audit m2: the two blockers' reasons were read
> from an INSTRUMENTED run during the close-out session — the shipped
> code deliberately swallows attempt failures into KEPT premises, so
> the attribution is not preserved by the build.)
> D1 therefore ends as **done-except-R-lane-and-PCE-chain-and-tau**,
> the charter's anticipated form.

## D1 — full non-vacuity of the capstone telescopes (2026-08-08)

- What: `weak/strongSsortfn1IsSsortfn2AtCanonical` landed as PARTIAL
  witnesses — every no-shadow/totality/TP premise kernel-discharged
  (41/49 weak, 13/21 strong; PCE totality via `dis_pce_total`,
  HOW-MANY's TP via `dis_how_many_tp` through the new generic `totals`
  registered-discharger route); the 6 constraint `rule:` premises +
  `rule:CONVERT-PERM-TO-HOW-MANY` + `use:ORDERED-PERMS` remain KEPT
  hypotheses.
- Why deferred (the residual's chain): (i) the constraint rows' own
  conds are witness TPs (`tp:SORTFN1-INSERT` class) that `proveTp`
  frontiers on (return-path CONS) — ADDRESSABLE in-scope by `dis_*`
  hand lemmas (queued as item 1b, NOT a user decision); (ii)
  `rule:CONVERT-PERM-TO-HOW-MANY`'s chain runs through
  PCE-IS-COUNTEREXAMPLE's recognizer frontier (machinery/emission
  class) and PERM-TLFIX's rung-3 R-lane build — the R-lane is a
  PRE-RATIFIED USER CHECKPOINT (equiv-lane design), so that leg is
  deferred to Mike regardless of other progress.
- Unblocks: unconditional AtCanonical constants (the full O6 closure);
  also narrows the sorts-equivalent capstones' eventual cond sets.

## D2 — item 2 residual: the usefi discharge's in-sweep enablement (2026-08-08, EARLY-EXIT residual)

- What: the R7b usefi: discharge composition is COMPLETE and COMMITTED
  (the full semantic layer A/B′/B″/lifts/transports — all kernel-checked,
  zero sorries — plus `mkUseFiDischarger` with both premise-bridging
  classes, wired through runBook and the coverage harness) but DISABLED:
  in-sweep runs SIGABRT on proof-term depth. Three remediations landed
  (kernel-route decides — fixed the first crash class; the D1-pattern
  constant declaration with consumer-fvar abstraction; hint-only gates
  with constructed types) without clearing the in-sweep crash. The
  isolation probe (.tmp/pinscratch/usefi_probe.lean) runs the whole
  composition up to the consumer-discharge step (which needs the real
  sweep telescope).
- Why residual: NOT decision-blocked — an in-scope debugging campaign
  (symbolized stack traces, bisecting which Expr walk overflows,
  possibly chunking the parametric rebuild into its own pre-declared
  constant) that this session could no longer execute reliably
  (three consecutive fix cycles at ~10 min build each without landing).
- Unblocks: MSORT-IS-ISORT/QSORT-IS-ISORT usefi: conds flip to
  discharged (queue items 3/4's full closure).

> **Close-out bounded attempt (2026-08-08, queue item 3 — ANALYZED,
> not landed; the charter's log-and-move-on clause).** The node's
> anatomy is now exact (dump: sorts-equivalent BSORT-IS-ISORT Goal,
> apply-top-hints-clause): ONE FI lmi whose `:HYPS` instance IS the
> goal (tautology-dropped, `application clauses: []`), a non-trivial
> 5-conjunct `:CONSTRAINT-CL`, and a recorded chain that rewrites the
> constraint clause down to `(IF (TRUE-LISTP X) (TRUE-LISTP (BSORT X))
> 'T)`, then a CLAUSIFY record (out:
> `[(NOT (TRUE-LISTP X)), (TRUE-LISTP (BSORT X))]`) closed by an
> executable-counterpart verdict (`⇒ 'T` — the tau/exec class, ◌
> `ASSUMED:dp-fact` in the discharge probe). The pure-FI arm
> (`Core.lean` useHint arm) requires the chain to reach `'T` directly
> and hard-fails on `useHs ≠ []` in the clausify arm; the needed
> composition extends the CONSTRAINT-CHAIN VALIDATION (not the
> conclusion — the instance's truth still comes from the `usefi:`
> hypothesis, which the WEAK prepare keeps because ORDEREDP-BSORT is
> genuinely red) to walk chain → clausify checkpoint → verdict
> closure. Landing it means teaching the FI arm's chain to traverse
> the clausify record + a discharge-verdict tail — a Core.lean arm of
> its own, judged past the bounded-attempt budget with the close-out
> audit still ahead. Ceiling unchanged: ◌ at best (the row would keep
> `usefi:` + `ASSUMED:dp-fact` conds) until the bsort book's
> emission-family frontiers land.

## D3 — item 5: BSORT-IS-ISORT's useHint+clausify composition (2026-08-08, EARLY-EXIT residual)

- What: the composition (constraint chain on CONSTRAINT-CL, clausify
  the residual, tau leaf, FI hypothesis peel) in Core's clausify
  branch — sized in TODO with its emission read-out.
- Why residual: in-scope engineering, ceiling ASSUMED ◌ regardless
  until the bsort book's Phase-1 frontier family lands (that leg IS
  emission-adjacent — partially deferral class (b)).
- Unblocks: BSORT-IS-ISORT from FAIL to ◌ (never ✓ without the bsort
  frontiers).

## D4 — item 6: touched-if-relevant Phase 2 audit deferrals (2026-08-08, EARLY-EXIT residual)

> **Close-out update (2026-08-08, queue item 2 DONE — the gz
> agreement-lemma half).** TEN new `gz_def_*` agreement lemmas landed
> in `Replay/Lemmas/Derived.lean` (IMPLIES, IFF, EQL, FORCE, HIDE,
> IFIX, NATP, POSP, ZP, EVENP — each stating the `callBuiltin`
> primitive agrees pointwise with the EMITTED ground-zero defun body's
> value composition; zero sorries), and the fail-closed ci gate
> `scripts/check-gz-agreement.sh` (in `just ci` as
> `check-gz-agreement`) enforces that every builtin-named ground-zero
> snapshot across the corpus has an agreement lemma or an explicit
> justified flag, with flag-rot detection (the gate is NAME-level —
> audit O-6; content fidelity is by review plus, for the
> d4DefFacts-registered subset, the use-site recompute; a
> content-level pin is a tracked follow-up). FLAGGED: LEXORDER (body
> cites ALPHORDER, a World fn — fidelity rests on the LexorderOrder
> theorems + differential corpus) and EXPT (body cites ZIP —
> differential corpus, BUG-021 pin). The SCOPE-IN-FORCE refinement
> stays DEFERRED: no book demands it (the over-abstraction hard-fails
> honestly at the witness-deref guard today), and refining without a
> driving book would be speculative generalization.

- What: gz agreement-lemma ci check; scope-in-force refinement.
- Why residual: untouched — the phase's work never reached them
  (charter: "cover or defer IF touched"; they were not touched).
- Unblocks: hardening only; nothing gates on them.

