# R7a plain-`:use` composition — sub-arc audit (2026-08-04)

Branch `mdd/r7a` (894ec1d..4c1e37f), the close-out arc's Phase 2. One
adversarial Opus reviewer (scale per the goal's "agent-defined" clause —
a ~250-line single-commit increment). Verdict **READY-WITH-FIXES**;
fixes F1–F4 applied in-arc before fold-back (this file records both).

## Ground truth the reviewer established itself

- Build green; all four changed golden rows reproduced BYTE-IDENTICALLY
  by direct `acl2lean-replay` runs (05-hints, convert-perm-to-how-many
  with deps, sorts-equivalent).
- `REPLAYED ✓` is kernel-checked and axiom-clean: `Runner.lean` runs
  `Meta.check` + `collectProofAxioms` (classical trio only) + `addDecl`.
- Three fail-closed tamper probes on scratch copies: σ tamper → the
  verbatim :HYPS mismatch error; self-citation lmi → no-offer error;
  `:FUNCTIONAL-INSTANCE` lmi → lmi-parse hard-fail. All live.
- Soundness: no hole found. The peel targets `disjoinTerm
  cn.inputClause` exactly (appCl shape-checked as `negs ++ inputClause`
  verbatim; child linked by clause equality; peel order = hyps order =
  negs order; `evtrue_extract_else` per head). `evalOpt_substTerm_substN`
  has no distinctness/freeness side conditions (duplicate σ formals:
  first-match on both sides; unbound frees fall through env).
- Fidelity vs `apply-use-hint-clauses` (acl2/prove.lisp:704-838):
  ACL2 really builds ONE application clause (negated hyps prefixed) on a
  singleton clause list, constraint clauses genuinely separate; the
  single-app-clause restriction and `constraintCl == ('T)` gate are
  honestly scoped (MSORT/QSORT really carry `:FUNCTIONAL-INSTANCE`).
- Telescope alignment: all four ordering sites (condsAll, the
  withLocalDecls nesting, both fvar concatenations) verified BY POSITION
  to agree; registry label formats match.

## Findings → resolution

- **F1 MEDIUM (fixed).** The `equivRefls` fallback offered RAW
  untranslated formulas (`(+ …)`, `(AND …)`), which can never pass the
  verbatim :HYPS cross-check — mislabeling the failure as "emission
  divergence" and making the documented include-book D6 path
  statement-shape-dependent. Fail-closed for soundness (a consumed
  offer must have passed the check) but dishonest diagnostics.
  FIX: fallback dropped — offers come from depProofs Goal clauses
  (translated) only; a cited theorem without one is not offered and the
  arm hard-fails honestly. Include-book translated-statement emission
  recorded as the follow-up (TODO).
- **F2 MEDIUM (fixed).** No topological guard: a same-book citation of
  a LATER theorem (ACL2-impossible) was accepted and silently
  re-replayed — demonstrated with a tampered 05-hints; also the latent
  mutual-citation discharge-cycle vector. FIX: same-book citations must
  name a strictly-earlier theorem (`takeWhile` over the creation-order
  list); cross-book entries are earlier by construction.
- **F3 LOW-MEDIUM (fixed).** ≥2 `:USE-HINT` payloads fell through
  SILENTLY to the ordinary arms (the F12 class); literal items alongside
  the payload had no consumer and no guard. FIX: both hard-fail.
- **F4 LOW (fixed).** `:USE-HINT` payloads were silently dropped on
  nodes routed to induction/push/pool-subsumed/elim/fertilize/
  generalize/eliminate-irrelevance. FIX: `guardNoUseHint` on all seven
  arms.
- **F5 LOW (follow-up, TODO).** `negs` re-derives dumb-negate-lit as a
  naive `(NOT h)` wrap; `ClausifyBridge.dumbNegateLit` exists. All
  divergences hard-fail at the shape check (soundness intact) but the
  supported class is narrowed; unifying needs per-arm falsity
  derivations in the peel.
- **F6 LOW (follow-up, TODO).** The R7b frontier label is inferred from
  constraint-clause shape, not the lmi; `:use (:theorem …)` would be
  mislabeled.
- **F7 INFO (documented).** `dischargeUseHyp`'s formula equality is a
  same-source assert, not an independent cross-check — docstring now
  says so.
- **F8 INFO (follow-up, TODO).** The `depMirrorProofAt` `use:` registry
  arm is corpus-unexercised (no row keeps a `use:` condition yet).

## Reviewer's could-not-verify

Full ci aggregate (verified per-row instead); the `use:` registry
roundtrip (no corpus instance); the equivRefls-fallback branch (no
corpus citation outside depProofs — since removed); multi-hyp `:use`
peel (only single-lmi rows exist in the corpus).

## Fix-round gates (recorded at commit time)

Fix commit re-verified: LEN2-APP-VIA-USE still `REPLAYED ✓
cond[tp:LEN2]`; full claim-gate TRUE_EXIT in the fold-back commit.
