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

## STATUS (2026-06-09, end of session): P1–P2 done + P3 prep; scaffold next

Landed (branch `mdd/c3-composition`, all green + committed):
- **P0** tree review + this plan; ReplayCtx v2; dpVal value layer moved into the
  driver core.
- **P1 UNIFORM CORE** (per MDD's directive): registry-generic `proveConv`
  (re_conv_builtin{1,2}_reg + re_conv_if; per-builtin special cases DELETED);
  `.boundary` path frames + if-test congruence (relativizeFrames, depth threading,
  evalOpt_congr_if_test — the old backlog item retired); ONE definition recipe
  (unfold with two ORDERED EVIDENCE sources — pinned totality value, else the
  ∀-env analyzer — then children as an ordinary path-directed chain at depth+1);
  replayBodyConvViaIf and all special-casing DELETED; recipes for recognizer /
  standalone if-simplification / unicity-of-0 (with the REPLAYED fix child) /
  commutativity-of-+ / commutativity-2-of-+.
- **P2 CLAUSE SPINE + SOLIDIFY**: replayClause proves the CLAUSE
  (`eval (disjoinTerm inputClause) = some t`); the spine's own split IS the case
  hypothesis (induction children are SELF-CONTAINED clause proofs); falsity facts
  accumulate in ctx.litFacts, bridged across literal rewrite chains; SOLIDIFY
  consumes the equivSource literal's spine fact (logic_not_equal_nil_eq) — more
  faithful than the hand proof's scaffold-IH route; push-clause defers to the pool
  root. sq/pair regress green through the uniform machinery.
- **P3 prep**: pinVal/pinVal_spec (choice-based opaque pinning — no Exists.elim
  plumbing), re_extract_else, logic_not_t_nil, re_val_var_insert,
  evalOpt_substTerm_subst1 confirmed.

## STATUS UPDATE (2026-06-09, #53 part A): preprocess CHAINS + reducible Env

Branch `mdd/c3-preprocess`. The "no literal items in clause" frontier split into
shapes (real-artifact review of 00/05/07/08):
- **Preprocess eval/abbreviation chains** (ground-arith, sq-of-3, cdr-cons-refl,
  idf-rewrites): clause-level `:REWRITE-STEP`s with NO `:PATH` (preprocess has no
  gstack) composing formula → 't. LANDED: `replayPreprocessChain` — positions
  reconstructed DETERMINISTICALLY (lhs must occur EXACTLY ONCE in the current
  term; 0/≥2 hard-fail), `executable-counterpart` nodes re-checked by KERNEL
  REDUCTION of `evalOpt` at a concrete fuel (`conv_of_eval_at`), other runes via
  their ordinary recipes. Coverage: REPLAYED 9/38 (ground-arith, sq-of-3,
  cdr-cons-refl unconditional).
- **Env made kernel-reducible (trusted-core change, deliberate).** `Env` was
  `Std.HashMap Symbol SExpr` — string hashing is opaque to the kernel, so
  `evalOpt` of any defined-fn call could NOT be re-checked by reduction (rfl
  definitively stuck). Replaced with a minimal assoc list (insert-prepend /
  first-match get?) in `Syntax.lean` — smaller trusted core, same observable
  semantics, all existing kernel proofs rebuilt, differential test vs real ACL2
  re-run as the semantic guard.
- **Verdict-only discharge leaves at Goal** — #53B LANDED: discharge nodes are
  ordinary preprocess-node recipes keyed by ORIGIN; `replayDischargeNode`
  instantiates the DP machinery from the ambient ReplayCtx PINS + bound TP
  hypotheses (no quantified telescope at composition). DischargeLeaf.lean folded
  into Driver.lean, all MetaM (`Lean.Elab.runTactic` works in MetaM); the
  standalone telescope/assumeFact form kept for the coverage harness. Coverage
  12/38 — equal-symm/equal-trans UNCONDITIONAL, len2-nonneg
  cond[total:len2, tp:len2]. Conditional (◌, assumed-fact) leaves at composition
  need CONDITION THREADING — recorded, later. linear-chain needs a
  `definition:implies` recipe (implies is an evalOpt builtin; must NOT enter
  groundZeroDefs — would shadow the no-shadow/callBuiltin facts).
- **Clausify splits** (preprocess ⇒ N subgoals, e.g. 07's admission proof) and
  `mutual-recursion` defun emission (07 logs ZERO `:DEFUN` events — stage-2
  emission gap, Track B) — recorded, later.

## STATUS UPDATE (2026-06-09, later): END-TO-END LANDED (audited, #38 done)

`my_len_my_app_real_mirror` (Tests/DriverTests.lean) — the driver replays the REAL
`simple.proof-log` end-to-end; `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (no sorryAx); type = the conditional generic mirror
`∀ env, total:my-len → total:my-app → total:fix → tp:my-len → ∃N∀f≥N, eval
(equal (my-len (my-app x y)) (+ (my-len x) (my-len y))) = some t`, conclusion
machine-generated from the parsed formula. Coverage (kernel-checked, quantified
env): REPLAYED 5/38 — my-len-my-app, sq-rewrites ×2 (`cond[total:sq]`), len2-app,
len2-app-helper (the scaffold generalized to 01/04 without target-specific work).

Final pieces landed beyond the planned recipe (all driven by real-tree errors):
- `replayLiteralChain`: `:NOT-FLG T` literals — ACL2's rewriter works on the ATOM
  (paths are atom-relative); chain the atom, lift through `not` by unary congruence.
- Branch-frame STRIP: ACL2's `rewrite-if` keeps a resolved if on the gstack, so
  nodes after a chain-root if-simplification carry the surviving branch's path
  frame; `replayRewrites` records consumed branch indices, `emitCongruence`
  validates+drops them.
- `commutativity-of-+`/`-2-` nodes chain their CHILDREN at depth+1 (the rule step
  alone is not the recorded rhs — same recipe as definition nodes).
- `groundZeroDefs` (fix) folded into `Development.toWorld`.
- `replayProofConditional` binds ONLY hypotheses the proof actually uses
  (unused offers must not weaken the statement).
- Pinning is PROVISIONING: moved uniformly into `replayClause` (case lambdas no
  longer pin); no-hypothesis → skip, the value layer hard-fails at use.
- `acl2-numberp` added to the dpUnary registry.
- Coverage `tryReplay` → the conditional harness over a QUANTIFIED env,
  `Meta.check`ed, conditions reported per theorem.

Remaining in c3: #38 audit (next, before claiming), then #53 preprocess-chain
composition; frontier list per coverage (car-cons rune, pushed≠pool-root on
multi-literal pushes, 2-IH/multi-var measures, clause-context-resolution, …).

## The original remaining-work recipe (now landed, kept for the record):
1. **replayInduction** (in replayClause's induction branch):
   - validate the emitted justification shape: measure `(acl2-count v)`, rel `o<`,
     single controller, step case tests `[(consp v)]` with IH `v:=(cdr v)` (other
     vars identity), base `[(not (consp v))]`; anything else → frontier error.
   - link children BY first literal: step child's literal 1 == `(not (consp v))`;
     base child's literal 1 == `(consp v)` (strict, validated).
   - P xv := ∀ e, (eval_e (var v) = some xv) → eval_e (disjoin pushedClause) = some t.
   - instantiate `acl2_induction_consp P base step`:
     - base (v, h_consp, e, h_xe): pin opaques (pinVal over the totality hyps,
       inside-out; TP-int refinement via logic_integerp_int .choose where the fn
       has a TP hyp) → ctx_b; `replayClause ctx_b baseChild`; then
       `re_extract_else` with `eval (consp x) = some nil` (ctxValProof + cast
       h_consp) peels literal 1, leaving the pushed clause. Verify term equality.
     - step (v, h_ne, ihP, e, h_xe): consp-t via logic_consp_ne_nil_t; pin → ctx_s;
       `replayClause ctx_s stepChild`; extract literal 1 (value
       `Logic.not (Logic.consp v) = nil` via logic_not_t_nil after consp-t);
       IH: ihP (Logic.cdr v) at e' := e.insert v (cdr-value) with
       re_val_var_insert; bridge eval_e (substTerm [v] [(cdr v)] pushedLit) =
       eval_{e'} pushedLit via evalOpt_substTerm_subst1 (cdr-of-var conv from
       h_xe); verify the substTerm result == the clause's IH literal body; then
       eval (not IH-term) = some nil (conv_builtin1 + logic_not_t_nil-style cast)
       → re_extract_else peels literal 2, leaving the pushed clause.
2. **The conditional-mirror harness** (`replayProofConditional`): generate the
   hypothesis telescope from the development — per defined fn: a totality
   hypothesis `∀ env' args…, (each arg converges) → ∃M ∃v ∀f≥M eval (fn args…) =
   some v`, and (when a `:TYPE-PRESCRIPTION` was emitted) a lifted-corollary
   hypothesis `∀ env' args… v, (eval (fn args…) = some v) → <lift, (fn formals)↦v>
   = t`; bind with withLocalDecls; pin per clause entry; λ-abstract; report the
   conditions (the c2 pattern — same shape as the hand proof's generic theorem).
3. **DriverTests**: `my_len_my_app_generic_mirror` via the driver from the REAL
   parsed simple.proof-log, `#print axioms` gate; coverage flips my-len-my-app to
   REPLAYED (conditional).
4. **P7 audit** (task #38) before claiming.
