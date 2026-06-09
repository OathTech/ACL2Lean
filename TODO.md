# ACL2Lean — project TODO

Running backlog across all tracks. Keep this current: update when a milestone lands,
scope changes, or a new gap/frontier is found (see the injunction in `CLAUDE.md`).
This is a living index, not a spec — design detail lives in `docs/plans/` and
`docs/notes/`.

_Last updated: 2026-06-09._

> **`just ci` is GREEN again (2026-06-09).** The black-box-leaf emission frontier is
> CLOSED: the evaluation chunk emits the preprocess reduction chains, and every
> decision-procedure discharge (tau / type-set-forward-chain) now emits an explicit
> **discharge node** (clause ⇒ t, mechanism origin) under the ratified
> decision-procedure-leaf carve-out (CLAUDE.md). The coverage harness still hard-fails
> on any item-less PROVED leaf (emission gap) and tags discharge leaves
> `[DISCHARGE-LEAF (replay pending)]` — their DRIVER replay (lift + omega/lean-smt,
> c1/c2) is the next work. See `docs/plans/2026-06-09_direct-proof-emission.md`.

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
- [ ] **Position threading (retire `findPath`).** The congruence path is NOT in the
      ACL2 log (no rule fires at congruence nodes, so they're unlogged); the driver
      currently recovers it by locating the node's `lhs` as a unique subterm
      (`findPath`, hard-fail on ambiguity) — deterministic but it's recovery in the
      checker and fragile on ambiguous redexes. Fix: **emit the rewrite address/focus
      from ACL2** (the rewriter knows it), thread it through the proof tree, and carry
      it schematically so the driver never matches. (Track-A instrumentation; decide
      before/with S3.)
- [ ] **Inductive clause structure (next big gap).** `replayClause` only handles a clause
      that closes via a literal; the real `my-len-my-app` `Goal` is pushed to an induction
      pool root (`*1`) with case-subgoal children (`*1/1`, `*1/2`) — the driver fail-closes
      at `Goal` ("no literal closing to (quote t)"). Needs: recurse `push-clause → *1 (emit
      acl2_induction_consp) → children`, threading `ReplayCtx` (case-hyp + IH). Then
      recognizer / if-simplification / with-lemma(comm) / solidify nodes (the `*1/1`,`*1/2`
      chains) + def-unfold for if-bodies.
- [x] **`car`/`cdr`/`consp`/`binary-+` convergence** in `proveConv` — `re_conv_car/cdr/
      consp` (unary) + `re_conv_plus` (binary), wired in; tested by `builtinsEq_mirror`.
- [ ] **recognizer + if-simplification nodes** (`re_if_true/false` + the recognizer that
      feeds the test value). NOT decoupled: `re_if_true/false` need the test's value, which
      in real trees comes from the recognizer child reading the **case hypothesis**
      (`consp x = nil/t`). They consume `ReplayCtx.caseHyps` → land WITH the induction
      scaffold, not before it.
- [ ] **Driver coverage harness** (QoL). One command/test that runs the driver over every
      `.proof-log` in the corpus and prints replayed-vs-frontier per theorem. DEPENDS on
      gen-world config below (a meaningful harness needs per-theorem `ReplayConfig`, not
      hand-marshalled facts).
- [ ] **def-unfold for REAL def shapes.** The current handler only does the *easy* case
      (1-arg fn, direct non-`if` body, no children). Real `def:my-app`/`def:my-len` are
      2-arg and/or have an `if`-body whose recognizer + if-simplification CHILDREN do the
      simplification — `re_unfold1_conv`'s `substTerm`-of-the-`if`-body ≠ the node's
      simplified rhs there. Needs: multi-arg unfold + replaying the def node's children
      (recognizer/if) to reach the net rhs.
- [ ] **Driver: `.boundary` path frames (child-node congruence).** `emitCongruence` is
      now path-directed (`pathStepsFromFrames` navigates the literal via `:PATH`; numeric
      `.arg` → `congr_unary/_binary_left/_binary_right`); `findPath`/`occursIn` retired.
      Remaining: handle `.boundary` (BODY/RHS) frames — child nodes inside an unfold /
      rule-RHS — which currently hard-fail (they align with the tree's child-nesting).
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
- [ ] **Eliminate ALL hand-marshalling — driver derives facts on demand** (the chosen
      full-design direction; see `docs/plans/2026-06-08_defmap-refactor.md`). Architecture:
      the driver, recursing the tree, derives every fact it needs from the World/Development
      — nobody enumerates anything. Structural facts by kernel computation; semantic facts
      (totality/type-prescription) from admission data later (measure track).
  - [x] **P0** coverage: World.defs contract characterization + `#guard_msgs` axiom gates.
  - [x] **P1+P2** `World.defs : HashMap → DefMap` (assoc list, same interface, lookups
        reduce); all concrete world facts now `by decide`. Build/contract/axiom-gates green.
  - [x] **P3** driver derives `defs.get?`/no-shadow + `DefInfo` on the fly (`proveNoShadow`/
        `deriveDefInfo` via `proveByDecide`); ALL hand world facts + `DefInfo` deleted from
        the harness. `ReplayConfig` = `{worldExpr, envExpr, worldVal}`. Mirrors axiom-clean.
  - [x] **P4** `Development.toWorld` projects the World from the parsed development;
        `reflectWorld` + `derive_world` emit it as a concrete def. sq frontend derives BOTH
        theorem and world from one `sqDevelopment` — only input is the log. (`pairWorld`
        stays a synthetic fixture: the pair test drives a hand-built tree, no proof-log.)
  - [x] **Coverage harness** (`Tests/DriverCoverage.lean`, `just driver-coverage`): runs the
        driver over the whole corpus, world derived per sample via `toWorld`/`reflectWorld`;
        prints REPLAYED-vs-frontier per theorem (currently 1/27 — `sq-rewrites`; the rest are
        clean frontiers: induction, multi-arg unfold, exec-counterpart). Logs `include_str`'d
        so an absent log is a HARD failure (no silent skip). Shook out the new derive/toWorld
        code across 0/2/3-defun worlds with zero dirty failures. Fills in as node kinds land.
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

## ACL2 submodule (instrumentation hygiene)

- [ ] **Comprehensive `TRACE-LOG` tag review.** The scheme is `TRACE-LOG[<origin>]`
      above each output site, `<origin>` = the emitted `:origin` value (one unique tag
      per site). Review the whole `acl2/` submodule: (1) every output site is tagged and
      the tag matches its `:origin`; (2) no duplicate/orphan tags; (3) **ratify a
      convention for INFRA tags** — the new non-output tags `structured-rewrite-path`
      and `set-raw-proof-format/gstackp[-off]` (and the `:path` field, documented at the
      helper) are the first non-origin tags; decide how infra is tagged vs outputs.
      Goal: keep the logging infra cleanly trackable for eventual upstreaming.

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
- [ ] **Careful revision of the capture / emission infra (2026-06-09).** Repeated issues
      have surfaced here (the `:DEFTHM`-count heuristic was fooled by a FAILED proof —
      a non-theorem rendered a full tree and exited 0; `let`/`let*` semantics diverged;
      untagged ACL2 insertions; measure-instantiation bug). Do a deliberate end-to-end
      pass over stages 2–4 infra, not piecemeal patches. Known sub-items:
    - **Explicit `emit/proof-failed` (the proper positive failure signal).** ACL2 knows
      when a proof fails; emit a structured `(:PROOF-FAILED :NAME …)` (or `:RESULT :FAILED`
      on the `:DEFTHM`-close) at the single event-summary choke point — there are many
      failure paths in `prove.lisp` (≈L202/610/4537/5177/7758), so find the common one.
      Then parse it (`ProofEvent`) and hard-fail reconstruction on it. **Backstop already
      in place** (2026-06-09): `buildDevelopment` hard-fails on any `:DEFTHM` block lacking
      its `:QED`; the CLI exits non-zero; `capture-proof-log.sh` warns on `qed < defthm`
      and on the "proof attempt has failed" prose. The explicit emit upgrades inference→positive.
    - Re-audit the capture script's other heuristics (source `(defthm` count vs logged,
      `:STOP-LD` suppression under `:structured`) and the `recon-test-dump.sh` `|| true`
      (which swallows the new non-zero dump exit — decide if that should surface).
    - Differential-test the emission itself, not just `evalOpt` (does the log faithfully
      reflect the proof? a failed/odd proof should be detectable from the log alone).
    - [x] ~~`abbreviation-expansion` placeholder RHS~~ — FIXED 2026-06-09: the emit now
      carries the instantiated rule RHS (`sublis-var unify-subst rhs`); 08's `cdr-cons`
      step shows `(cdr (cons x y)) ⇒ y`.
- [x] **#24** — `fix` modeled as a defined function in the hand-proof world (ACL2 ground-zero
      body); base-case node3 unfolds it via `definition:fix`. (Other `definition:`-runed
      ground-zero fns: add as needed.)
- [x] **#29** — `my-len-my-app` base case *1/2 reworked to schematic per-rune replay (driver
      combinators: re_unfold{1,2}_var ; recognizer ; re_if_false/true ; unicity-of-0 + fix
      unfold ; equal-self) — no more compute-and-match. Found+fixed via the adversarial audit.

## Done (recent milestones, for context)

- Faithful sorry-free hand proofs of `my-len-my-app` and `app-assoc` (schematic;
  no functionality facts), each lifted to an idiomatic native Lean theorem; ACL2
  pipeline untrusted for both.
- Differential testing of `evalOpt` vs real ACL2 (51/51).
- Driver S1+S2 + native Nat bridge (first real proof-tree replay).
- Driver S3 (first real rewrite rune): `(equal (cdr (cons a b)) b)` via a `cdr-cons`
  node + path-directed congruence (`equal arg1`) + equal-self — axiom-clean mirror.
- Driver 3a(i) convergence analyzer recurses into compound operands (`cons`).
- Driver 3a(ii) DEFINITION-UNFOLD node: `(defun pair (x) (cons x x))`,
  `(equal (pair x) (cons x x))` via `re_unfold1_conv` (body ∀-env convergence threaded
  to the bindArgs env) + carried `DefInfo` (def/closed/no-let) + equal-self. Axiom-clean.
- Adversarial audit (3 decorrelated reviewers): driver confirmed GENUINE replay — no
  hand-hacking, no answer-smuggling, axiom-clean, fail-closed.
- **FIRST REAL TREE replayed end-to-end**: `sq-rewrites` (`(equal (sq n) (* n n))`)
  parsed from the real `09-defn-unfold.proof-log` → driver → `sq_real_mirror`, axiom-clean
  (`binary-*` convergence + def-unfold + equal-self). The hard real tree `my-len-my-app`
  fail-closes cleanly at the `Goal` (push→induction) frontier.
- `capture-proof-log.sh` failure detection hardened.
- SExpr reader now supports dotted pairs (`(a . b)` → true `.cons`); fixes the `(. x)`
  artifact in `:subst` and `:path` frames (previously `.` was read as a symbol).
- Driver made heuristic-free: removed `proveBySimp` (default-simp); all side-conditions
  via kernel `decide` (`proveByDecide`); world non-shadowing facts now CARRIED in
  `ReplayConfig.noShadow` (established once, never re-derived).

---

_Conventions: `[ ]` open, `[x]` done. Task numbers (#NN) refer to the live task list.
Tracks A and B are independent; A needs no new instrumentation, B does._
