# The two-stage lift (design note)

Date: 2026-07-06 (branch `mdd/r2-isort`). Status: DESIGN SETTLED; hand
validation on the perm book in progress. Context: TODO priority 3(a) —
per-function corr lemmas (`corr_memb_enc` ~100 lines each) are the scaling
bottleneck of the native-import layer.

## The split

For each world function `foo`, replace the single fuel-laden hand corr proof
with two pieces:

1. **Stage 1 (to be automated — the exec corr).** A total Lean function
   `fooExec : SExpr → … → SExpr` mirroring the ACL2 body EXACTLY, plus the
   kernel-checked corr theorem, world-parametric (L3):

   `∀ env a… av…, ConvTo w env aᵢ avᵢ → ConvTo w env (fooT a…) (fooExec av…)`

   proved over ALL SExpr argument values by strong induction on
   `acl2Count` of the measured formal — no `enc`, no list induction.

2. **Stage 2 (stays human).** The pure-Lean simulation equation, e.g.
   `membExec a (enc xs) = bif xs.contains a then t else nil` — ordinary
   structural induction, no `evalOpt`, no fuel.

The existing `corr_*_enc` statements are re-derived as corollaries
(stage 1 ∘ stage 2), byte-identical, so every downstream consumer
(`dis_*`, native entries) is untouched. That re-derivation IS the
validation that the split is real.

## Decisions

- **D1 — the corr is the VALUE-DETERMINED `ConvTo` form, not `ConvToP`.**
  `ConvTo w env (fooT a…) (fooExec av…)` has the same interface shape as
  `conv_builtin2`: an exec'd user fn composes into a caller's walk exactly
  like a builtin (perm's walk cites `memb_exec_corr` the way it cites
  `callBuiltin_consp`). The predicate form doesn't compose functionally —
  each caller would need a bespoke predicate. `ConvToP`/tpWalk remain for
  the TP prover, where the target genuinely is a predicate.
- **D2 — `fooExec` mirrors the body shape exactly.** ite with conditions
  `Logic.toBool (…) = true`, `Logic.*` primitives at builtin calls,
  recursive calls at self-call sites, calls to other exec functions at
  user-fn call sites. `termination_by (measured formal).acl2Count`;
  the decrease is discharged by the Count library from the ruling ite
  conditions — the same math as the totality prover's admission discharge.
  Exact mirroring is load-bearing: the walk folds its ite value tree into
  `fooExec` via the compiler equation lemma (`fooExec.eq_def`; WF defs do
  not unfold by `rfl`), so a def that doesn't match the body shape fails
  loudly there (fail-closed).
- **D3 — hand-validate the whole shape BEFORE mechanizing.** memb → rm →
  perm (perm validates cross-function composition: its body tests a `memb`
  call and passes an `rm` call — the registry seam). Each hand proof uses
  ONLY the intended kit moves (`re_val_var_get`, `conv_builtin1/2`,
  `conv_if_lift`, IH + `conv_defn_2`, `eq_def` fold), so mechanization is a
  transcription of a validated proof, not new design. Banned-anti-pattern
  note: every piece lands in the real `corr_*_enc` consumers immediately.
- **D4 — mechanization surface (follow-up): an elab command**
  (certifying walker, the tpWalk/proveTp precedent) generating the
  world-parametric theorem; a registry `fn ↦ (execConst, corrThm,
  hypothesis specs)` for composition — the hypothesis telescope (h_def +
  per-builtin no-shadow facts) grows transitively through callees. Def
  GENERATION (SExpr body → Lean source/decl) is separable and mechanical.
- **D5 — driving examples.** The perm book now (real consumers exist:
  the corr_*_enc corollaries feed the native entries). isort/insert —
  the R2 target that motivated this — follows once `Logic.lexorder`
  lands (its exec body needs the primitive; TODO priority 3 spec).

## Fidelity

Stage 1 is proved from the world semantics alone — it consumes only the
defun bodies already in the World, constructs proof objects ACL2 never had,
and sits in the import-support layer, not the replay path. Same ratified
class as the TP prover (#37 precedent): not banned inference. The replay's
no-inference rule is untouched.

## Validation result (2026-07-06, same day)

D3 is COMPLETE: `membExec`/`rmExec`/`permExec` + their stage-1 corrs +
stage-2 simulations landed in `Imported/Perm.lean`; the three `corr_*_enc`
lemmas are now 4-line corollaries (statements byte-identical — ~325 lines
of fuel-laden list-induction proof deleted); `just ci` exit 0 including the
build-failing native axiom gate (the corollaries' consumers). `perm`
validated the composition move: its walk cites `memb_exec_corr` /
`rm_exec_corr` at the callee call sites exactly like `callBuiltin` lemmas.
Per-function hand cost is now: the exec def (~8 lines, mechanical), the
walk-shaped corr (~50 lines, MECHANIZABLE — every step is a kit move), and
the stage-2 simulation (~12 lines, pure Lean — the part that stays human).

## Seams found during validation

- WF-def unfolding is by `eq_def` (`rw [fooExec.eq_def]`), never `rfl`.
- Plain `ite` (not `dite`) in WF defs: the branch condition IS available in
  `decreasing_by` goals (verified on lean4 v4.28.0; `by assumption` finds
  it). No dite noise in stage 2.
- `conv_if_lift` internals: `cases hb : Logic.toBool vc` substitutes the
  verdict into the ite value, so the branches reduce with `if_pos rfl` /
  `if_neg Bool.false_ne_true` — not `if_pos hb`.
- Stage-2 simp hygiene: rewrite `enc (hd :: tl) = .cons hd (enc tl)` (a
  `show … from rfl`) BEFORE the BEq case split (the split's substitution
  otherwise strands the `enc` redex), and convert BEq case hypotheses to
  propositional form for simp's normal forms (`eq_of_beq`,
  `Ne.symm (beq_eq_false_iff_ne.mp …)`, `hd ∈ ys` via `simpa`).

## Next (mechanization, hand-offable)

An elab command (certifying walker, the `proveTp` precedent) that takes
(fn, formals, body const, exec const, measured-formal position, callee
registry) and emits the stage-1 theorem: telescope = h_def's + no-shadow
facts (transitively through callees), `acl2Count_strong_induction` spine
(measured position picks the `tp_2_rec`/`tp_2_rec_snd` analogue), walk arms
= exactly the moves in the three hand proofs, `eq_def` fold at the root,
`conv_defn_2` assembly. Registry entry recorded per fn for callers.
Def GENERATION from the World body is separable (mechanical text/decl gen);
until it lands, exec defs are hand-written against the body (D2 shape
errors fail loudly at the `eq_def` fold).
