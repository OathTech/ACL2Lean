# ACL2Lean — project TODO

Running backlog across all tracks. Keep this current: update when a milestone lands,
scope changes, or a new gap/frontier is found (see the injunction in `CLAUDE.md`).
This is a living index, not a spec — design detail lives in `docs/plans/` and
`docs/notes/`.

_Last updated: 2026-06-08._

## Where we are

Stages 1–4 of the pipeline (ACL2 instrumentation → proof-log parse → proof-tree
reconstruction) are built and validated on the sample corpus. The **proof-producing
driver** (stage 7) now exists and has replayed its first real proof-tree node kind
end-to-end (`equal-self`), with the result lifted to a native Lean fact. See
`docs/plans/2026-06-08_driver-build-plan.md` for the driver methodology.

---

## Track A — the rewriting-replay driver (`ACL2Lean/Replay/Driver.lean`) — CURRENT FOCUS

A recursive, fail-closed `replayClause`/`replayNode` over the real tree; grow by tree
complexity, each step driven by a real (or faithfully-synthesized) tree, with
positive + negative tests. Goal: replay `my-len-my-app` (then `app-assoc`)
end-to-end via the driver, not the hand proofs.

- [x] **S1** — dummy driver, correct type, fail-closed (`throwError`, never `sorry`).
- [x] **S2** — one `equal-self` node → universal mirror fact
      `∀ env, ∃N ∀f≥N, evalOpt … (equal x x) = some t`; native `∀ n:Nat, n=n` via the
      `enc:Nat→SExpr` bridge. Axiom-clean.
- [ ] **S3** — congruence + one with-lemma rewrite (`cdr-cons`): activate the
      built-but-unused congruence-path emitter (`emitCongruence`) on a real rewrite
      node; multi-node literal chaining. (task #39)
- [ ] **S4** — solidify / `rewriting-equivalence`: a clause-hypothesis (or IH) equality
      consumed by a solidify node (`equivSource`); `ReplayCtx.caseHyps`; the
      `evalOpt_substTerm_subst1` + `eval_equal_t_implies_eq` bridge. (task #36)
- [ ] **definition-unfold** nodes — `evalOpt_unfold{1,2}_conv` (compound-arg form
      ALWAYS; never the over-specialized `re_unfold*_var`). (task #34)
- [ ] **recognizer / if-simplification** nodes (`re_if_true/false`, builtin step
      lemmas). (task #33)
- [ ] **convergence analyzer (G1)** — general: builtins over known structure +
      defined-fn totality, threading opaque (existential) witnesses for recursive
      calls. (currently: variable + quote only)
- [ ] **world facts (G3)** — produce per-function totality from the admission
      (`WorldEvent.defun.termination`) and the integer/type fact from the emitted
      `:TYPE-PRESCRIPTION` corollary, so the driver is self-contained. (task #37)
- [ ] **induction scaffold (G5)** — `replayClause` emits `acl2_induction_consp` for the
      `consp/cdr` scheme by reading the `InductionStep`; threads case-hyp + IH down via
      `ReplayCtx`; multi-literal clauses & case-split children. Non-`consp` schemes
      hard-fail.
- [ ] **preprocess-clause + `:ABBREVIATION-EXPANSION`** idiom (car/cdr-cons real shape)
      + implicit `(equal x x)` tautology closure (no equal-self node).
- [ ] **executable-counterpart / ground eval** node.
- [ ] Replace the hardcoded `World.empty`/empty-env frontend with **`gen-world`** output;
      feed the **real parsed `simple.proof-log`** (drop the hand-built test trees once
      the real tree replays).
- [ ] The **`acl2_replay` tactic** frontend (read the Lean goal, emit the proof, close
      it) — vs the current term-elaborator test harness.
- [ ] Replay **`my-len-my-app` end-to-end** via the driver; then **`app-assoc`**;
      `#print axioms` clean.
- [ ] **`Expr` blowup** — `let`-bind shared convergence subproofs in emitted terms.
- [ ] Generalize the over-specialized `re_unfold*_var` (driver should always use the
      compound unfold).

## Track B — type-set / decision-procedure instrumentation (separate track)

ACL2 closes many goals (e.g. equality transitivity/symmetry, and much arithmetic) by
**type-set / linear** decision procedures at `preprocess-clause`, logged atomically as
`fake-rune-for-type-set` (or linear) with **no derivation** — see
`acl2_samples/recon-tests/08-equality-reasoning.lisp`. These are currently a driver
**frontier (hard-fail)**, NOT replayable.

- [ ] Instrument ACL2's `preprocess-clause` / type-set path to emit the type-set facts
      (type-alist entries, type-set bitmasks) that justify a whole-clause closure.
      (within-rewriter recognizer type-set IS already logged — `:TYPESET`/`:TRUETS`.)
- [ ] Consume those facts in Lean to **replay** the closure as a decision *from the
      logged facts* — NEVER re-derive type-set in Lean (that would be inference).
- [ ] Same treatment for **linear arithmetic** (`fake-rune-for-linear`) and other
      `fake-rune-*` decision steps.
- [ ] Decide the modeling: how a type-set closure becomes an `evalOpt`-level fact.

## Other pipeline / cross-cutting work

- [ ] **Native-theorem bridge — generalize.** Currently hand-built for `my-len-my-app`
      (List.length_append) and `app-assoc` (List.append_assoc). Systematize the
      type-morphism + simulation recipe (`docs/comms/2026-03-22_acl2-lean-bridge.md`),
      ideally driver-assisted.
- [ ] **`evalOpt` faithfulness to ACL2** — expand the differential harness
      (`scripts/diff_eval.sh`, 51/51) corpus; it is one of the two trust-note
      circle-breakers.
- [ ] **Mirror-statement builder / `gen-world`** (`WorldGen.lean`) — completeness &
      correctness for new theorems the driver targets.
- [ ] **Reconstruction coverage** — work through `docs/notes/2026-06-07_silent-drop-inventory.md`
      and the recon-tests findings; ensure no silent drops.
- [ ] **#24** — model `fix` (+ `definition:`-runed ground-zero fns) as defined functions
      (also de-collapses the base-case `node3`).
- [ ] **#29** — rework `my-len-my-app` base case *1/2 to schematic + totality (currently
      compute-and-match; blocked partly on #24).

## Done (recent milestones, for context)

- Faithful sorry-free hand proofs of `my-len-my-app` and `app-assoc` (schematic;
  no functionality facts), each lifted to an idiomatic native Lean theorem; ACL2
  pipeline untrusted for both.
- Differential testing of `evalOpt` vs real ACL2 (51/51).
- Driver S1+S2 + native Nat bridge (first real proof-tree replay).
- `capture-proof-log.sh` failure detection hardened.

---

_Conventions: `[ ]` open, `[x]` done. Task numbers (#NN) refer to the live task list.
Tracks A and B are independent; A needs no new instrumentation, B does._
