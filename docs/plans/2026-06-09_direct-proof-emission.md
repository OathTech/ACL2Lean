# Direct-proof emission gap — plan (Track B-adjacent)

_Created 2026-06-09. Branch `mdd/measure-emission`._

## The gap (what 00-direct actually witnesses)

ACL2's waterfall discharges some clauses **without the rewriter** — by evaluation
(executable-counterpart), type-set reasoning, or linear arithmetic — inside
`PREPROCESS-CLAUSE` (and sometimes a terminal `SIMPLIFY` via type-set). For these,
our instrumentation emits only the processor verdict:

```
(:STEP :CLAUSEID "Goal" :PROCESSOR PREPROCESS-CLAUSE :RESULT :PROVED :RUNES NIL
       :INPUTCLAUSE ((EQUAL (BINARY-+ '1 (BINARY-+ '2 '3)) '6)))
(:QED)
```

That is a **black-box "PROVED" leaf**: ACL2 really proved it by *evaluating*
`(+ 1 2 3) → 6` and `(equal 6 6) → t`, but the proof STRUCTURE (which counterparts
fired, which type facts were used) is **not emitted**. The reconstruction faithfully
renders the coarse leaf, but there is **nothing to replay** — the driver has no
structure to mirror. This is an EMISSION gap (stage 2), not a reconstruction bug, and
not a failed proof.

This is the long-standing Track B item ("instrument ACL2's `preprocess-clause` /
type-set path to emit the … facts"); 00-direct is its concrete witness.

## Where it occurs in the corpus (scope)

A black-box leaf in the reconstructed tree = a `ClauseNode` that is PROVED but has no
`children`, no `induction`, and no step with `items` (rewriter detail). The
`blackBoxLeafIds` detector in `Tests/DriverCoverage.lean` finds them on the PARSED tree
(authoritative — a raw `grep` undercounts, since `:RESULT` often wraps to the next line).

True scope (per the detector): **19 theorems across 11 logs** — 00, 01, 02, 03, 04, 06,
07, 08, 11, 12, 16. It is far more pervasive than "direct proofs": most commonly it is
the **residual-clause TIP** — after `simplify-clause` does the real work, the leftover
subgoal (e.g. 12's `Subgoal *1/2'`, `{… ∨ (not (< …))}`) is closed by
`preprocess-clause` / `tau-system` / evaluation, which emits no structure. Sub-classes:
- **Whole-theorem black boxes** (NO instrumented structure at all): `00-direct`
  (ground-arith, sq-of-3), `03-linear`, `08-equality-reasoning`, `06`/`07` constants.
- **Residual tips** alongside real `simplify` structure: 01, 02, 04, 11, 12, 16.

Clean (no black-box leaf, fully rewriter-instrumented end-to-end): **`simple`, 05, 09,
10, 13, 14, 15** — notably the flagship `simple`.

This is wider than "Track B decision procedures": a `tau-system` / evaluation tip closes
the residual of even ordinary rewrite proofs, so closing the gap matters broadly, not
just for the three direct-proof tests.

## What ACL2 does on these paths (to instrument)

- **Executable-counterpart / evaluation**: `(equal (+ 1 2 3) 6)`, `(sq 3) = 9` — ground
  terms reduced by `*1*` exec functions. Need: which counterpart runes fired, on which
  subterms, producing which values. (Runes are partly present already: sq-of-3's step
  lists `executable-counterpart:equal/:sq`.)
- **Type-set reasoning**: a literal forced true/false by type-set (we already emit a
  `:TYPE-SET-REASONING` event in the rewriter path with `:JUSTIFICATION` runes; the
  preprocess/standalone type-set discharge is NOT yet emitted).
- **Linear arithmetic** (`03-linear`): the linear pot / `add-poly` decision procedure.
  Heaviest to instrument; emit the linear lemmas + the contradiction.

## Approach (emit → parse → reconstruct → eventually replay)

1. **Locate the discharge points in ACL2** (`acl2/`): `preprocess-clause`
   (`preprocess.lisp`/`prove.lisp`), the type-set engine (`type-set-b` etc.), the
   executable-counterpart evaluator, and the linear procedure. Find where each
   *concludes a clause* and add a tagged `emit/<...>` event mirroring the existing
   rewriter-step pattern (round-trip `:origin`).
2. **Emit a structured sub-proof** under the preprocess/type step instead of a bare
   `:RESULT :PROVED` — minimally: the sequence of (term → value, rune) reductions for
   evaluation; the type-set fact + supporting runes for type discharge; the linear
   lemmas + pot for arithmetic.
3. **Parse** the new events (`ProofLog`/`ProofTree`) into the `WaterfallStep.items`
   (or a new detail slot) so the black-box leaf gains replayable structure.
4. **Reconstruct**: the leaf is no longer "PROVED with nothing" — it carries the
   evaluation/type chain; `dump-proof-tree` shows it; the driver can later replay it
   (evaluation via `evalOpt`, type facts via the emitted `:TYPE-PRESCRIPTION`/type-set).
5. **Validate** on 00 (eval), 08 (equality/type), 03 (linear) — dumps show real
   structure; the black-box-leaf detector (below) finds none.

## Sequencing

- Start with **evaluation/executable-counterpart** (00-direct: ground-arith, sq-of-3) —
  the simplest, and `evalOpt` already models evaluation, so replay is within reach.
- Then **type-set discharge** (08) — reuse the existing type-fact emission machinery.
- **Linear arithmetic** (03) last — its own decision procedure, largest effort.

## Interim: make the gap VISIBLE (fail, don't fake-green) — DECIDED 2026-06-09

Until the emission exists, a black-box leaf must NOT look handled. `blackBoxLeafIds`
(`Tests/DriverCoverage.lean`) flags every PROVED leaf with no children/induction/`items`.

**Chosen mechanism (with the user): BROAD HARD-RED.** The `#driver_coverage` command
`throwError`s on ANY black-box leaf, so `lake build Tests.DriverCoverage` — and hence
`just ci` — is **deliberately RED** across all 19 affected theorems (11 tests) until the
preprocess/tau/eval emission lands. This is intentional, not a regression: a black-box
PROVED leaf has no structure to replay, so reporting it as handled would be a fidelity
lie. The flagship `simple` and 05/09/10/13/14/15 stay green (fully rewriter-instrumented).

Consequence acknowledged: `just ci` is not a green gate again until this gap closes —
that pressure is the point. When the emission is built, the affected leaves gain `items`
(or an eval/type sub-proof), `blackBoxLeafIds` returns empty for them, and the gate goes
green incrementally as each path is instrumented.
