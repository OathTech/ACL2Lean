# Theorem-dependency hypotheses (`rule:<thm>` in the conditional telescope)

*2026-07-05, MDD-ratified. Branch `mdd/perm-display-folding`. Driving exemplar:
perm-transitive's `rewrite:perm-symmetric` application — the corpus's first
theorem-to-theorem dependency.*

## The decision

When a rewrite chain applies a USER rule (a previously-proven theorem used as
a `:REWRITE` rune), the replay does **not** go find and replay the dependency
at the point of use. Instead the node consumes the emitted `:SUBST` to
instantiate a **bound hypothesis** `rule:<thm>` stating the rule's mirror —
a third species in the c2 conditional telescope alongside `total:` and
`tp:`. The theorem replays immediately, *conditionally*, with the dependency
visible in its type (`cond[rule:perm-symmetric, …]`); the hypothesis is
discharged lazily when (and however) the dependency's own mirror becomes
available.

**The operating picture (MDD's framing): we maintain a log of proof
obligations and gradually chew through them, rather than trying to walk the
whole dependency graph in one go.**

Why this over replay-at-point-of-use:
- **No ordering coupling.** perm-transitive replays today even though
  perm-symmetric is itself blocked (wall b). The scoreboard shows the debt.
- **It IS the include-book model (R2).** An included book's theorems have no
  proof tree in our log — a hypothesis discharged "by the book's import" is
  the only shape that generalizes. This design is the R2 down payment.
- **Same final proof.** When the dependency replays, its mirror substitutes
  into the hypothesis slot; the composed proof is identical — only *when*
  is decoupled.
- **Existing pattern.** Totality and TP hypotheses already work exactly this
  way (bound → lazily discharged → residue visible and auditable).

## Baked-in principles (checked against covering ALL of ACL2 — none of these
may be violated by a v1 shortcut)

1. **The hypothesis shape is generated per-rule from its emitted `:EQUIV`** —
   R-parameterized (invariant L2), never hardcoded `equal`. v1 implements the
   `equal` instance (perm-symmetric is stored equal-strengthened via perm's
   boolean TP); `iff`/user-equivalence rules get their instances through the
   same generator when reached.
2. **Rule statements come from EMISSION, never Lean-side rule
   reconstruction.** ACL2 stores RULES, not defthms — a formula is normalized
   into possibly several rules (implies-flattening, and-splitting,
   iff→equal strengthening under known-boolean). The fork emits the stored
   rule's content (hyps/equiv/lhs/rhs per rune) at the point ACL2 creates it
   (`create-rewrite-rule`), so the hypothesis states exactly the rule ACL2
   applies. The node-level validation `substTerm(:SUBST, ruleLhs) == node
   :LHS` is the recompute-and-check joint.
3. **Transitive conditions compose.** A theorem's type may carry its
   dependencies' residual conditions; there is NO requirement that
   dependencies replay first. Dependency order is a DAG (ACL2 certification
   order), so lazy discharge in development order terminates, exactly like
   totality's dev-order prefix.
4. **Instantiation strictly by the emitted `:SUBST`** (which already reflects
   ACL2's free-variable search, `bind-free` extensions, etc. — we consume
   the result, never redo the search). Hypothesis relief is discharged from
   the recorded `:KIND HYP` children (bracketed as of `infra/hyp-log-tail`);
   `syntaxp`/`bind-free` hyps are logically vacuous application guards and
   do not appear as obligations; FORCED hyps become explicit undischarged
   obligations for the forcing-round machinery (G4) — the seam is left open,
   not papered over.

## Barrier analysis (why this does not block full-ACL2 coverage)

- Free-var hyps / bind-free / syntaxp / backchain limits / loop-stoppers:
  all resolved inside ACL2 before emission; `:SUBST` records the outcome.
- `iff` and user equivalences: principle 1; flows into the G1/L2
  R-parameterized judgment, where the spine already consumes SIff chains.
- Forcing: principle 4's explicit-obligation seam feeds G4.
- Include-book: this design is the import mechanism (R2).
- Metafunctions / clause processors / apply$: tier-policy questions
  (EXTENDED/OUT), orthogonal to this choice.
- Built-in axioms' runes (car-cons, …): keep their hand recipes; their
  "formulas" are not in any log. The `rule:` machinery covers runes whose
  theorems the log carries (same-book now; imported books via R2).

## v1 implementation plan

1. **Fork**: at `create-rewrite-rule` (defthm.lisp), when `:structured` mode
   is active, emit a top-level `(:RULE :RUNE … :HYPS … :EQUIV … :LHS …
   :RHS …)` event per created rewrite rule (tagged `emit/rule`).
2. **Parse/reconstruct**: a `RuleSpec` per rune on the `Development`.
3. **Driver**: `replayProofConditional` binds `rule:<name>` hypothesis
   declarations for the development's emitted rules (used-filter as for
   totality; no lazy discharge in v1 — conditions stay visible).
   Hypothesis type (equal instance):
   `∀ env', ⟨truthiness of each rule hyp⟩ → ∃N,∀f≥N, eval env' ruleLhs =
   eval env' ruleRhs` (the rule's variables live in `env'`).
4. **Node recipe** (`replayNode`, rewrite-rune fallback): validate
   `substTerm(:SUBST, ruleLhs) == node.lhs`; build `env' :=
   bindArgs(substVars, substTermValues)`; bridge instance↔formal by
   `evalOpt_substTerm_substN` (the peelIH/replayElim machinery); discharge
   each hyp premise from the `:KIND HYP` children chains (instance ⇒ 't at
   the call env, bridged to `env'`), falling back fail-closed when a hyp was
   relieved without events (type-alist relief — extend when a tree shows
   it); chain: `eval env lhsInst ≡ eval env' ruleLhs ≡ eval env' ruleRhs ≡
   eval env rhsInst`, then the node's RHS-block children continue the chain.
5. **Discharge (follow-up)**: derive the rule-hypothesis from the
   dependency's replayed mirror (implies/equal decodes + the TP two-valuedness
   where ACL2's storage strengthened iff→equal), substituting like #37's
   totality discharge.
