# Driver build plan — mechanizing the schematic replay

**Date:** 2026-06-08
**Branch:** `mdd/driver-assembly`
**Status:** plan, grounded in the real artifacts. Not yet started. Companion to
`docs/notes/2026-06-07_driver-design.md` (type + soundness) and
`2026-06-07_schematic-replay-rule.md` (per-node discipline). This note answers
"how do we build it, in what order, validated against what."

## 1. What the driver is, restated against the real artifact

The driver (stage 7, the eventual `acl2_replay`) is a `MetaM` procedure that walks
the reconstructed proof tree and emits a Lean `Expr` proving the mirror theorem.
**The two hand proofs already ARE its output, schematically** — the driver is
"write down the function that emits what `SimpleWorld.lean`/`AppAssoc.lean` were
written by hand to be instances of." Concretely, reading the real step case
(`SimpleWorld.lean:443–727`) against the real tree
(`lake exe acl2lean dump-proof-tree acl2_samples/simple.proof-log`):

- **Per node** the proof is a fact `∃ N, ∀ f ≥ N, evalOpt f w e before = evalOpt f w e after`,
  produced by **that rune's combinator** (the dispatch table in the schematic-rule
  note), with values existential.
- Each node fact is **lifted to the whole literal** by composing the arity-specific
  congruences `evalOpt_congr_unary / _binary_left / _binary_right` along the path
  from the literal root down to the rewritten subterm (`c1…c6`).
- The lifted facts are **chained** with `fuel_chain_eq`, and the literal is closed
  by `evalOpt_equal_self` once it reaches `(quote t)` (`node5`).
- The **clause/induction layer** is `acl2_induction_consp P base step`, with the
  step continuation receiving the IH; the case hypothesis (`consp xv = t`) and the
  IH flow **down** into the node proofs (the solidify node `node4c` consumes the IH).

All schematic combinators this requires already exist and are kernel-proven in
`ACL2Lean/Replay/EvalLemmas.lean` (verified 2026-06-08): `fuel_chain_eq`,
`evalOpt_congr_unary/_binary_left/_binary_right`, `evalOpt_unfold1_conv` /
`evalOpt_unfold2_conv` (compound-arg definition unfold), `evalOpt_substTerm_subst1`,
`re_cdr_cons`, `re_plus_comm`, `re_plus_comm2`, `re_if_true`, `re_if_false`,
`eval_equal_t_implies_eq`, `evalOpt_equal_self`, `acl2_induction_consp`,
`conv_builtin1`, `conv_builtin2`. **The driver invents no new math; it orchestrates
these.**

## 2. State of the existing skeleton (`ACL2Lean/Replay/ProofProducer.lean`)

It is the **old value-computation skeleton** and must be largely rewritten:

- **Orphaned and non-building.** Imported by nothing; its chain path calls
  `evalOpt_replace_congr_fwd`, which was **deleted** with the rest of the sorried
  `pcEq`/`EvalCtx`/`replaceSubterm`-congruence cluster — so it would not compile
  if built.
- **Banned pattern.** `proveExecCounterpart`/`proveEqualSelfNode`/`proveIfSimplNode`
  prove a node by **computing both sides to a value and matching** (`findFuel` +
  `metaEval` + `mkFuelEqExist`). That is exactly the "compute-and-match" the
  schematic rule forbids; it cannot replay a symbolic, universally-quantified tree.
- **Reusable as-is** (framing-neutral plumbing): the reflection layer
  (`reflectSExpr`/`reflectSymbol`/`reflectNumber`/`reflectAtom`/`reflectInt`),
  the side-condition provers (`proveBySimp`, `proveByDecide`, `proveNotSpecial`,
  `proveWorldLookupNone`), and the fuel-existential wrappers (`mkFuelPred`,
  `mkFuelConvergeExist`, and a value-/equality-existential builder analogous to
  `mkFuelEqExist`). Keep these; delete the node/chain logic.

## 3. The gap — what the driver must synthesize that the tree does not hand it

The tree gives, per node, `(rune, lhs, rhs, subst, equivSource, children)`. To turn
that into the combinator calls the hand proof makes, the driver must additionally
synthesize five things (each visible as scaffolding in the hand proof):

- **(G1) Operand convergence facts.** Every combinator's side-conditions are
  `∃ N ∀ f≥N, eval operand = some <witness>` facts (`hxc`, `hcdrx`, `hconspx`,
  `hcarx`, `hcons`, `hA`, …). The driver needs a **symbolic convergence analyzer**:
  given a subterm + the convergence context, emit its convergence proof and a
  witness. Witnesses are concrete for builtins over known structure
  (`Logic.consp xv`, `Logic.car xv`) and **opaque/existential** for recursive calls
  (`rv` from `h_myapp_total`, introduced by `obtain`). The analyzer is essentially a
  second evaluation pass producing *proofs* (not values), mirroring ACL2's
  "every subterm has a type-set / converges".
- **(G2) The congruence path.** Where the node's `lhs` sits inside the current
  literal term (`c1…c6`). The driver locates the redex (`replaceSubterm` still
  exists, framing-neutral), walks the path, and emits the matching arity-specific
  congruence at each level (head symbol → which `congr_*`; argument index → left vs
  right), discharging each `…_not_special` side-condition by `decide`.
- **(G3) World facts: totality + type-prescription.** Currently *hypotheses* of the
  generic theorem (`h_mylen_total`, `h_myapp_total`, `h_mylen_int`), hand-discharged
  for `world`. The driver must **produce** these per defined function: totality from
  the admission (`WorldEvent.defun.termination`), the integer fact from the emitted
  `:TYPE-PRESCRIPTION` corollary (`WorldEvent.typePrescription`).
- **(G4) The IH bridge** for `rewriting-equivalence` (solidify) nodes: take the IH
  named by `equivSource`, bridge it from the induction's child env
  (`e.insert x (cdr xv)`) to the goal env via `evalOpt_substTerm_subst1` under the
  node's `subst`, then `eval_equal_t_implies_eq`. The subst is the induction
  scheme's recursive-call argument.
- **(G5) The induction scaffold + `ReplayCtx`.** Emit `acl2_induction_consp` for the
  `consp/cdr` scheme; thread the case hypothesis and IH **down** into the step
  subgoal's `ReplayCtx`. Non-`consp` schemes **hard-fail** (incompleteness frontier).

## 4. Components (mapped to the design-note types)

```
ReplayCtx            -- caseHyps, ih (+ its env/subst), typeFacts, envBindings   [design note §type]
ConvergenceAnalyzer  -- term + ctx → (convergence proof Expr, witness)            [G1]
emitCongruence       -- literal, redex path, node proof → lifted proof Expr       [G2]
worldFacts           -- defun/type-prescription → totality / int lemmas (Expr)    [G3]
replayNode           -- (rune,lhs,rhs,subst,equivSource) + ctx → node eval-eq     [dispatch table; G4 for solidify]
replayLiteral        -- fold ProofNode chain: lift+chain, close with equal-self
replayClause         -- ClauseNode: settled/push pass-through, induction (G5),
                        case branches; builds child ReplayCtx
replayTheorem        -- ClauseProof → mirror-goal proof; reuses gen-world's World + statement
acl2_replay tactic   -- frontend: tie emitted Expr to the Lean goal
```

The **no-shortcut invariant** (design note): the only inhabitants of a rewrite
node's claim are the per-rune combinators. The convergence analyzer (G1) is the one
place that "computes", and it is confined to producing *convergence/value* facts for
operands — never a proof of the node's own `before = after`. Enforce by giving
`replayNode` a return type that only the combinators inhabit, and never calling the
analyzer to discharge a node's top-level equality.

## 5. Staging — skeleton-first, every stage typechecks against the REAL mirror goal

The recurring failure mode is building pieces in isolation. The structural guard:
**the driver emits a complete, typechecking proof of the real `my-len-my-app` mirror
theorem from stage 0**, with every not-yet-handled node's eval-equality filled by a
correctly-typed `mkSorry`. `#print axioms` then shows `sorryAx`, shrinking as node
kinds are implemented — the mechanized analog of "skeleton, one `sorry` per node,
filled one at a time *in the real theorem*." No stage builds infra that isn't wired
into that goal.

- **Stage 0 — skeleton harness (highest-value de-risk).** Frontend: `simple.proof-log`
  → `Development` → the `my-len-my-app` `ClauseProof`; build the `World` + mirror
  statement via the existing `gen-world`; emit a proof where **every** node
  eval-equality is `mkSorry` of the correct type, but the **induction scaffold (G5),
  congruence lifting (G2), chaining, and equal-self closing are all real.** Wire as an
  `elab`/`example` that the emitted `Expr` typechecks against the real mirror
  statement. *Validates the whole structure (G2, G5, chaining) before any node logic.*
- **Stage 1 — convergence analyzer (G1) + easy runes.** Implement G1; replace the
  sorries for `recognizer` (→ `conv_builtin1`), `if-simplification` (→ `re_if_*`,
  truthiness from `ReplayCtx` case hyp), and `equal-self` (→ `evalOpt_equal_self`).
- **Stage 2 — definition unfold.** `:DEFINITION fn` → **`evalOpt_unfold{1,2}_conv`**
  (the compound-arg form — *always*, never the over-specialized `re_unfold*_var`;
  documented lesson). Body value is existential, from totality (G3, supplied as a
  hypothesis until Stage 5).
- **Stage 3 — with-lemma runes.** `cdr-cons` → `re_cdr_cons`; `commutativity-of-+` →
  `re_plus_comm`; `commutativity-2-of-+` → `re_plus_comm2`. Operand convergence from
  G1; integer-ness (where needed) from the type-prescription fact.
- **Stage 4 — solidify / IH (G4).** The hardest node: `evalOpt_substTerm_subst1`
  bridge + `eval_equal_t_implies_eq`, IH located via `equivSource`, subst from the
  scheme. After this, the step case has **zero** sorries.
- **Stage 5 — mechanize world facts (G3).** Produce `h_*_total` from the admission
  and `h_*_int` from the `:TYPE-PRESCRIPTION` corollary, so the driver is
  self-contained (no hand-supplied hypotheses). Also handles the base case's
  `fix`/unicity-of-0 (task #24/#29).
- **Stage 6 — second theorem + audit.** Run the driver on `app-assoc`; confirm both
  mirror theorems are emitted with `#print axioms` = `{propext, Classical.choice,
  Quot.sound}` (no `sorryAx`). Re-run the adversarial audit with the schematic
  dimension (read-only reviewers; verify git clean after).

## 6. Risks / open design questions (resolve at the named stage, against the goal)

- **Redex uniqueness (G2).** If a node's `lhs` occurs more than once in the current
  term, the congruence path is ambiguous. For my-len-my-app each redex is unique at
  its step; confirm at Stage 0 and **hard-fail** on ambiguity rather than guess.
- **Opaque witnesses in the analyzer (G1).** Recursive-call witnesses are
  `Exists`-bound fvars; the emitted `Expr` must thread the `Exists.elim`/`obtain`.
  This is the main analyzer-implementation risk — prototype it at Stage 1 on the
  real `hrv`/`h_myapp_total` shape before generalizing.
- **Truthiness side-conditions (G1/G5).** `re_if_true` needs the test value to be
  truthy; that comes from the `ReplayCtx` case hypothesis (`consp xv = t`), not from
  computation. Confirm the ctx carries enough to discharge it.
- **Induction scheme generality (G5).** Only the `consp/cdr` scheme is handled
  initially; the `InductionStep` carries the real scheme. Dispatch on it; hard-fail
  on anything else (documented incompleteness, not unsoundness).
- **`Expr` blowup.** Shared convergence subproofs (e.g. `hcdr`, `hrv`) are reused
  across nodes — `let`-bind them in the emitted term (design note).
- **Reuse vs rewrite of `ProofProducer.lean`.** Keep reflection + side-condition
  provers + fuel wrappers; delete the value-computation node/chain core. Decide at
  Stage 0 whether to rewrite in place or in a new module and retire the old file.

## 7. What this plan deliberately does NOT do

- No building of a node combinator that isn't being wired into the real goal in the
  same stage (the banned anti-pattern).
- No generic/`decide`/`rfl` proof of a symbolic node equality (no-shortcut invariant).
- No inference in the checker: a missing rune handler, absent fact, or exotic scheme
  **hard-fails**; it is never papered over with an eval-shortcut.

---

## ADDENDUM (2026-06-08) — methodology correction: fail-closed, bottom-up by tree size

After a first attempt, two corrections supersede the staging in §5 above (kept for
the record; the gap analysis §3, component map §4, and risks §6 still stand).

### Correction 1 — the driver NEVER emits `sorry`. It fails the proof.

The §5 "skeleton with every node `mkSorry`'d" is **wrong**: a driver that emits
`mkSorry` is unsound — it "succeeds" by cheating, exactly the shortcut-to-green the
project forbids. The contract instead:

> `replayNode` / `replayClause : … → MetaM Expr` returns a **real, kernel-checkable**
> `Expr` of the node's exact goal, **or `throwError`s**. Never `sorry`, anywhere.

Failure ⇒ the tactic errors ⇒ **the theorem does not compile** — the honest signal.
Soundness invariant: a driver built only from `throwError` + kernel-checked per-rune
lemmas can *only* emit valid proofs; incompleteness is a failed compile, never a
false theorem.

### Correction 2 — bootstrap on the SIMPLEST POSSIBLE tree, hand-built as a value.

Not "the simplest tree in the sample corpus" — the simplest possible inhabitant of
the proof-tree **type**, hand-constructed as a `ClauseProof`/`ProofNode` literal.
This is NOT pre-staging: the forbidden thing is transcribing the *output* (a proof
skeleton); writing the driver's *input* (a value of the tree type, exactly what the
parser would emit) is normal unit-testing of `tree → MetaM Expr`. Proviso: the
hand-built tree must be a faithful value of the REAL reconstructed type, so swapping
in `ProofLog.parse → buildDevelopment` later is a drop-in.

### Revised sequence (supersedes §5)

- **S1 — dummy driver, correct type, fail-closed.** Define `ReplayCtx` (design-note
  fields) and `replayNode`/`replayClause : World → Env → ReplayCtx → {ProofNode,
  ClauseNode} → MetaM Expr` with bodies that `throwError`. Define the `acl2_replay`
  frontend. Validate at the TYPE/WIRING level (a fail-closed dummy can't make a
  theorem *compile*): `#check` the signatures; a NEGATIVE test that it fails cleanly
  on a tree (throws the frontier error — no `sorry`, no crash).
- **S2 — one `equal-self` node → a real mirror theorem.** Hand-build the minimal
  `ClauseProof` value (one SIMPLIFY clause, one literal `(equal '5 '5)`, one
  `equal-self` node). Teach `replayNode` the `equal-self` rule (via a kernel-checked
  `re_equal_self` combinator) and `replayClause` the trivial single-step/no-induction
  clause. `theorem … := by acl2_replay` **compiles**; `#print axioms` =
  `{propext, Classical.choice, Quot.sound}` (NO `sorryAx`). Solves the universal
  proof-object plumbing (reflection, fuel wrapper, mirror-statement matching, tactic)
  on the minimal case. Explicitly breadth-1: no congruence/induction/IH yet.
- **S3+ — grow by tree complexity.** `executable-counterpart` (ground compute), then
  one-level congruence (reusing `emitCongruence`), then recursion/induction/IH —
  each driven by a progressively larger hand-built tree, ending at the real parsed
  `simple.proof-log`. The native-theorem bridge is a separate per-theorem micro-step,
  deferred until there is a meaningful native statement.

### Testing discipline (new)

Accumulate a suite of **hand-built proof trees, positive and negative**, growing in
size: positive = the driver emits a real sorry-free proof (`#print axioms` clean);
negative = the driver `throwError`s cleanly at the named frontier (e.g. unsupported
rune, malformed clause, ambiguous redex). Every new node-kind adds both a positive
case (it now works) and keeps the negative cases for the still-unsupported frontiers.
