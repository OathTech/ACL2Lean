# c3 — Composition: the first end-to-end driver replay (my-len-my-app)

_Created 2026-06-09. Branch `mdd/c3-composition`. Tasks #52 (scaffold), #53
(preprocess/discharge composition), #38 (end-to-end audit)._

## Target

`my-len-my-app` replayed BY THE DRIVER from the real `simple.proof-log` — the
generic conditional mirror (totality as hypotheses, like the hand proof's
`my_len_my_app_generic`), `#print axioms` clean, every step mapped to a tree
node. Then `app-assoc`.

## The tree review (completeness check — done first, per MDD)

The full dump (114 lines) is structurally complete for replay:

- **Goal → \*1**: `settled-down-clause` (identity) → `push-clause ⇒ proved` →
  pool root `*1` carrying the SAME single-literal clause as the goal formula.
  No preprocess steps on this target (no formula→clause gap here).
- **\*1 induction**: emitted justification `measure (acl2-count x)` under
  `o-p/o<`, controllers `{x}`; case `[(consp x)]` with IH `x:=(cdr x), y:=y`;
  base `[(not (consp x))]`. Child linking: `*1/2` = base, `*1/1` = step — must
  be matched BY TESTS against the children's input clauses (NOT by order; here
  the emit lists step-case first while `*1/2` is the base).
- **\*1/2 (base)**: clause `{(consp x) ∨ EQ}`; literal 1 unchanged (its falsity
  is the case context); literal 2 closes to `t` by the 4-node chain
  (`def:my-app⇒y` / `def:my-len⇒0` / `unicity-of-0`+`def:fix` / `equal-self`),
  each node carrying rune+lhs/rhs+subst+path, recognizer children reading
  `consp x = nil`.
- **\*1/1 (step)**: clause `{¬(consp x) ∨ ¬IH ∨ EQ}`; literal 2 (the IH
  literal) is REWRITTEN in place (`commutativity-of-+`) — the branch then
  carries the rewritten form; literal 3 closes by the 5-node chain ending in
  the SOLIDIFY (`rewriting-equivalence`, `equivSource = literal 2` ✓ linked)
  and `equal-self`.

**Gaps found (none block v1):**
1. **No admission emission** in `simple.proof-log` (zero proof steps precede the
   defthm) — per-function totality cannot be derived from this log. v1:
   totality as CONDITIONAL HYPOTHESES (the hand proof's generic-theorem shape;
   the c2 pattern). Discharged later by termination emission (TODO emission
   backlog).
2. **Ground-zero content**: `fix`'s defun and the rewrite rules
   (`unicity-of-0`, `commutativity-of-+`, `commutativity-2-of-+`, `cdr-cons`)
   are ACL2 bootstrap items, not in the parsed world. v1: a RUNE→COMBINATOR
   REGISTRY of generic Logic-level lemmas (each already proved for the hand
   replay), keyed by rune name, unknown rune → hard-fail. The registry is the
   Lean model of ACL2's ground zero (like `callBuiltin`); the eventual
   alternative is ground-zero emission-at-use (TODO emission backlog).
3. **No per-case measure-decrease proofs** in the log (termination emission
   pending). v1: the induction combinator is keyed on the EMITTED justification
   shape — measure `(acl2-count v)`, rel `o<`, one controller, IH `v:=(cdr v)`
   → instantiate the env-generalized `acl2_induction_consp` (its own Lean
   wellfoundedness via `SExpr.acl2Count`); any other shape → hard-fail
   frontier. The justification consumed is the emitted one; only the
   wellfoundedness proof is Lean's (as decided: "emit ACL2's measure, build WF
   induction").

## Build phases

- **P1 — clause-spine replay (replayClause v2).** A clause is a literal spine
  (the DP work's `re_dp_if_split` shape): per literal, either its rewrite chain
  closes it to `t` (replayLiteral, under the accumulated context) or descend
  with the literal's nil-hypothesis. `ReplayCtx.caseHyps` = the accumulated
  value-characterized nil-facts. Subsumes the current single-closing-literal
  limitation. Literal-REWRITE (not closing) updates the carried hypothesis along
  the chain's eval-equality (the \*1/1 literal-2 case).
- **P2 — recognizer-from-hypothesis + if-simplification.** `recognizer/false|
  true` nodes justified by a caseHyp (`consp x = nil/t`) instead of structural
  computation; the existing `re_if_*` combinators consume the test value.
- **P3 — rune registry for ground-zero with-lemmas** (`unicity-of-0`,
  `commutativity-of-+`, `commutativity-2-of-+`; `cdr-cons` exists) + `fix`
  unfold via the registry (Logic-level lemmas; generalize the hand-proof
  combinators).
- **P4 — solidify mechanized**: `equivSource` → the caseHyp equality (post-
  rewrite form), the `substTerm`/`eval_equal_t_implies_eq` bridge from the hand
  proof, applied at the node's position.
- **P5 — induction scaffold**: read `InductionStep`, validate the v1 shape,
  link cases↔children BY TESTS, instantiate `acl2_induction_consp` with P :=
  the child-clause prop over the controller's value; step case gets the IH as
  a caseHyp-style hypothesis at `env[x ↦ cdr xv]`; base case gets `¬consp`.
- **P6 — wire `replayProof`**: Goal (settled-down identity, push-clause) → \*1;
  the driver-built generic mirror for `my-len-my-app` lands in DriverTests with
  the axiom gate; coverage flips it to REPLAYED (conditional on the declared
  totality hypotheses).
- **P7 — audit** (task #38) before claiming.

Throughout: fail-closed, no sorry, every step read off the tree; the hand proof
(`Imported/SimpleWorld.lean`) is the lemma quarry, NOT the driver's input.
