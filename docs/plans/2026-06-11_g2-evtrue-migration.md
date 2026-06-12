# G2 — the `EvTrue` (truthiness) migration: design + decision log

_Created 2026-06-11. Branch `mdd/g2-evtrue` (on top of the golden coverage
snapshot). Implements step 2 of the ratified generality plan
(`docs/plans/2026-06-10_generality-design.md` §1.1, §8.2). Status: DESIGN for
MDD review before deep implementation._

## 0. What and why

ACL2's notion of a theorem is *the term is non-nil*; clause truth is *the
disjunction is non-nil*. Our clause/mirror judgments currently state the
strictly stronger `∃N∀f≥N, eval … = some t`. The two coincide exactly on
boolean-valued terms (all of today's corpus), but the exact-t form:

- makes some true ACL2 theorems unprovable (truthy-non-t last literals),
- is **false-as-stated** for non-boolean formulas — a *fidelity* defect: the
  mirror would not be ACL2's claim,
- forces the iff-chain's awkward end-game: G1 left `formulaBooleanFact`, a
  per-formula-head boolean-valuedness side condition (today only `implies`
  heads pass — any other head on an iff chain is a hard frontier).

G2 migrates the CLAUSE and MIRROR judgments to truthiness and keeps exact-t
as a derived strengthening where the value is genuinely pinned. Honest
expectation recorded up front: **no new REPLAYED theorems from G2 alone**
(the live blockers are at the G5 induction frontier); the wins are statement
fidelity, the removal of the `formulaBooleanFact` frontier class, and not
having to migrate G5's machinery later.

## 1. The judgment (D1)

```lean
/-- ACL2's clause/theorem truth: the term eventually converges to a
    NON-NIL value. -/
def EvTrue (w : World) (env : Env) (t : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, ∃ v, evalOpt f w env t = some v ∧ v ≠ SExpr.nil
```

- Quantifier shape matches G1's `EvRel` (`∃N∀f∃v…`), so the two compose
  without reshaping.
- **Rejected alternative**: *defining* `EvTrue` as `EvRel SIff w env t
  (quote t)`. Equivalent, but drags a quoted constant into every statement
  and obscures intent. Instead both directions are bridge lemmas
  (`evtrue_iff_evrel_siff_qt`), so the G1 layer remains the composition
  mechanism (iff chains end in `EvTrue` directly — `truthy_of_evrel_siff`
  becomes `evtrue_of_evrel_siff` with no boolean side condition).
- Judgment-layer `Prop` per invariant L1; world-parametric per L3.

## 2. What migrates and what does not (D2)

**Migrates to `EvTrue`** (the clause/mirror layer — inventory of 2026-06-11,
agent-mapped, anchored to the current tree):

| Surface | Today | After |
|---|---|---|
| `replayClause` / `replayClauseSpine` / `replayDischargeLeaf` / `replayDischargeNode` results | `…(disjoin cl) = some t` | `EvTrue w env (disjoin cl)` |
| `replayProof` / `replayProofConditional` conclusion | `…formula = some t` | `EvTrue w env formula` |
| clausify-bridge composition (`conv_if_clauses` / `re_cond_clauses` consumers) | exact-t per output clause | `EvTrue` per output clause |
| induction motive `P` (pushed clause inside `replayInduction`) | exact-t | `EvTrue` |
| iff-chain end (`strengthenIffChain` + `formulaBooleanFact`) | truthy → boolean-head → exact-t | **deleted** — chain ends in `EvTrue` natively |
| mirror statement surface (`driver_mirror%`, WorldGen stub text, DriverTests pinned statements) | exact-t | `EvTrue` (unfolded form — see D6) |

**Does NOT migrate** (the value layer): `re_val_*`, `conv_*`,
value-characterized convergence, TP corollary facts, totality
(`mkTotalityHypType`), the DP lift's value characterization, `EvRel` itself.
A literal whose chain pins value `t` keeps its exact-t fact locally and
injects via the adapter (D3).

## 3. Exact-t as a derived strengthening (D3)

One universal injection lemma:

```lean
theorem evtrue_of_eq_t : (∃ N, ∀ f ≥ N, evalOpt f w env a = some SExpr.t) →
    EvTrue w env a
```

Every existing exact-t producer (closers, `re_equal_self`, recognizers,
executable-counterpart, discharge-node rhs-'t) stays as is and is wrapped at
the clause boundary. This makes the migration mechanical and reviewable:
value-pinned facts are never weakened *internally*, only at the judgment
boundary. Where consumers need the value back (IH-as-equivalence, decode),
per-primitive two-valuedness lemmas recover it (D5) — never a generic
"boolean-valuedness of the formula" side condition (that class dies with G2).

## 4. The spine under EvTrue (D4)

`disjoinTerm` is unchanged (`(if l₁ 't (if l₂ 't … lₖ))`). The spine split
(`re_dp_if_split`) gets an `EvTrue` variant:

- non-final literal truthy → the `if` returns exactly `'t` → `EvTrue` by
  `evtrue_of_eq_t` (unchanged content);
- non-final literal nil → descend with the falsity fact (unchanged);
- **the closer**: today requires `lp.result == quoteT` exactly. Under
  `EvTrue` the closing condition is the literal's truthiness. We KEEP the
  exact-t path for `result = 't` (the only shape ACL2's recorded chains
  produce today) and the frontier message for anything else now states the
  honest condition (truthy result without a recorded truthy-fact is an
  emission gap, not a boolean-valuedness failure).

## 5. Consumers: recovering values from truthiness (D5)

The decode layer consumes the mirror via head-specific facts. Replacement
pattern, one lemma per Logic primitive (all two-valued by definition):

- `Logic.equal` / `Logic.implies` / recognizers return `t` or `nil`; so
  `EvTrue (equal a b)`-style facts recover `Logic.equal va vb = t` (then
  `va = vb`) with NO formula-level side condition.
- `Lifting.native_of_mirror_equal` migrates to consume `EvTrue` (using
  equal's two-valuedness internally); the catalog entries and the
  hand-proof assembly lemmas (`*_native_of_mirror`) take the `EvTrue`
  mirror and strengthen INSIDE their proofs.
- The IH/solidify bridge (`eval_equal_t_implies_eq` consumers): same
  pattern — `EvTrue (equal a b) → eval a = eval b` via equal's
  two-valuedness.

## 6. Statement form on the trust surface (D6)

The mirror statement is the trust-bearing artifact; we do not want a
project-defined `def` standing between the reader and what is claimed.
**Decision**: driver-built STATEMENTS use the unfolded Prop
(`∃ N, ∀ f ≥ N, ∃ v, evalOpt … = some v ∧ v ≠ SExpr.nil`); the lemma layer
uses `EvTrue` internally (definitionally transparent — proofs cast across
the boundary by defeq, no reshaping). WorldGen's stub text emits the
unfolded form likewise.

## 7. Sequencing (D7)

Bottom-up, one commit per phase, golden coverage gate + `just ci` after each:

1. **Lemma core** (EvalLemmas): `EvTrue`, `evtrue_of_eq_t`,
   `evtrue_iff_evrel_siff_qt`, the `EvTrue` spine/split/clausify variants,
   per-primitive two-valuedness recovery lemmas. Additive only.
2. **Driver migration**, leaf-to-root: spine → discharge leaf/node →
   clausify bridge → preprocess chain end (DELETE `strengthenIffChain` /
   `formulaBooleanFact`) → induction motive + IH bridge →
   `replayProof(Conditional)`.
3. **Statement surface**: `driver_mirror%` docstring/shape, WorldGen stub,
   DriverTests pinned statements (each pin change is a deliberate,
   reviewed strengthening-direction check).
4. **Imported layer**: Lifting ender variants; NativeMirrors entries; the
   world-parametric assembly lemmas. `#print axioms` re-verified per entry.
5. **Cleanup**: delete every exact-t clause-level lemma with no remaining
   consumer (no dead layer left); golden table updated if any status text
   moved (expected: none); decision-doc updated with what actually happened.

## 7a. Discovered during implementation: `.exactT` collapses (D9)

Reading the clausify-bridge leaf machinery before migrating it
(`walkPosT`/`walkPosTLit`/`peelClause`, Driver.lean ~2150–2475): the
`LeafFact.exactT` constructor exists ONLY because the old judgment had to
pin value `t` at the spine-last literal, and `walkPosTLit` hard-fails on a
positive literal firing mid-spine ("cannot pin value t") — the
boolean-valuedness wall surfacing inside the bridge. Under `EvTrue`:

- a positive literal needs only truthiness anywhere in the spine, so
  `.exactT` is DELETED and the last literal emits `.truthy` like the rest
  (recovered from the clause fact + the pinned value via
  `ne_nil_of_evtrue_conv`);
- the mid-spine frontier message is deleted with it (the restriction is
  gone, not relocated);
- ONE spine lemma `evtrue_dp_if_split` (both branch hypotheses in `EvTrue`
  form; exact-t branches inject via `evtrue_of_eq_t` inside the lambda)
  serves `replayClauseSpine`, `walkPosT`, and `dischargeSpine` uniformly,
  replacing the per-shape `re_dp_if_split` instantiations;
- `peelClause`'s eliminator gets the matching `evtrue_if_fact_elim`.

Also noted: `Driver.lean` is MetaM-typed, so shape errors surface at the
COVERAGE RUN, not at compile time — except the pinned statements in
DriverTests and the catalog entries, which are statically elaborated. The
migration loop is therefore edit → build → coverage sweep per batch, with
the golden gate as the checker.

## 7b. Phase-2 working checklist (line anchors at branch time; tick as done)

- [x] `LeafFact`: `.exactT` deleted; consumers `walkPosTLit`,
      `valNegNilLit`, `valNegNilWrapped`, `valPosTruthyLit` collapsed to
      `.truthy`. `walkPosTLit` now takes cfg/ctx (`evtrue_of_conv_ne_nil`).
      `quoteTFact` moved up next to `disjoinTerm` (forward ref).
- [x] `replayClauseSpine`: closer → `evtrue_of_eq_t` (singleton AND
      with-rest `conv_if_true` cases); split → `evtrue_dp_if_split`;
      hthen simplifies to `evtrue_of_eq_t (quoteTFact)`
- [x] `walkPosT`: both if-shapes → `evtrue_dp_if_split`; `quoteTFact`
      branches inject
- [x] `peelClause`: `evtrue_if_fact_elim`; last literal →
      `.truthy (ne_nil_of_evtrue_conv pFact pl)`; `thnTy` binder gone,
      `restTy` is now the `EvTrue` Prop
- [ ] `bridgeClausify` (~2448): target `EvTrue info.input`
- [x] `dischargeSpine` / `dischargeClose`: `evtrue_dp_if_split` + boundary
      injection; DP fact stays value-level (`concVal = SExpr.t`)
- [x] `replayDischargeLeaf` / `replayDischargeNode`: conclusions are now
      `EvTrue (disjoin clause)` automatically (they end via the spine);
      docstrings updated with the wrap below
- [x] **D10 — discharge nodes compose as SIff chain steps** (DONE as
      designed): `evrel_siff_qt_of_evtrue`; `replayPreprocessNode`'s
      discharge case is a named hard-fail; the chain core's iff lane keys
      on the discharge origins. `replayDischargeNode`'s only other
      consumer path is the chain core itself (verified by grep);
      Driver.lean:~1068 (`fake-rune` recognizer) is value-level, stays.
- [x] chain end: both branches end in `EvTrue`; `strengthenIffChain` +
      `formulaBooleanFact` DELETED
- [x] `replayClause` clausify composition: `evtrue_of_fuel_eq` /
      `evtrue_of_evrel_siff`
- [x] `replayInduction`: motive `P` is `EvTrue` of the pushed clause
      (mkAppM ``EvTrue — no separate builder needed); case peels via
      `evtrue_extract_else` (one lemma serves base + both step peels);
      the IH literal's `(not ihInst) ⇒ nil` derives from TRUTHINESS alone
      (`conv_not_nil_of_evtrue` — the old `conv_builtin1`-at-`t` block,
      which consumed the IH's exact `t`, is gone). NOTE: the solidify/IH
      bridge inside literal chains (`equivSource`) consumes litFacts —
      value-level, unchanged; only the pushed-clause motive moved.
- [x] `replayProof` / `replayProofConditional`: migrated by construction
      (conclusion = `replayClause`'s judgment; hypothesis telescope is
      value-level, unchanged); docstrings updated
- [x] Phase 3: all 7 DriverTests pins in the unfolded truthiness form
      (hypothesis sides untouched); WorldGen stub; `native_nat_refl`
      decodes via `Logic.eq_of_equal_ne_nil` (NOTE: `rw`'s implicit `rfl`
      silently closed the `n = n` goal, bypassing the mirror — replaced by
      explicit `Eq` composition; axioms confirm the mirror dependence).
      The IH-bridge regression (4 inductive theorems) was caught by the
      GOLDEN GATE — `evtrue_of_fuel_eq` generalized over the rhs env
      (`evalOpt_substTerm_subst1` relates two envs).
- [x] Phase 4: `native_of_mirror_equal` consumes `EvTrue` (moved after
      `conv_equalT` — forward ref); new `implies_t_of_ne_nil`; assembly
      lemmas take the truthiness mirror, hand mirrors inject via
      `evtrue_of_eq_t`; entries 6/7 `conv_unique`-against-mirror →
      `ne_nil_of_evtrue_conv` + `implies_t_of_ne_nil`; entries 3/4/5/8
      align through the ender unchanged.
- [x] Phase 5: DELETED `re_dp_if_split`, `if_fact_elim`,
      `re_extract_else`, `truthy_of_evrel_siff`, `eq_t_of_truthy_boolean`,
      `arg_nil_of_not_t`, `ne_nil_of_eq_t` (all consumer-free after the
      migration; grep-verified). KEPT with consumers:
      `eval_equal_t_implies_eq` + `fuel_conv_of_eq` (hand proofs,
      value-level recipes), `logic_implies_boolean` (feeds
      `implies_t_of_ne_nil`), `logic_not_t_nil` (step-case literal peel),
      `conv_unique` (generic Conv-kit utility). Dangling docstrings
      reworded. Golden table: expected UNCHANGED (statuses don't encode
      statement shapes) — verified by the gate.

## 8. Risks / what to watch (D8)

- **The mirror gets WEAKER.** `EvTrue` is implied by exact-t, so every
  downstream consumer must be re-checked for places that silently relied on
  the pinned `t` (the decode layer is the audit surface; phase 4 re-runs
  every catalog entry's axiom gate). The flip side is the fidelity gain:
  the new statement is ACL2's actual claim.
- **DriverTests pins**: each pinned statement changes; the new pins must be
  read against the raw logs, not just made to compile.
- **DP-leaf conditional obligations** (`dpFactStmt`): value-level, expected
  UNCHANGED — verify, don't assume (audit-debt item #54 overlaps).
- **G1 lemma layer is in scope of this branch's audit** (G1 merged without
  a recorded milestone audit; G2 builds directly on `EvRel`/`SIff`, so the
  G2 audit adds a G1-fidelity dimension).
