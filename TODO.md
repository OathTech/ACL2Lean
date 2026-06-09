# ACL2Lean — project TODO

Running backlog across all tracks. Keep this current: update when a milestone lands,
scope changes, or a new gap/frontier is found (see the injunction in `CLAUDE.md`).
This is a living index, not a spec — design detail lives in `docs/plans/` and
`docs/notes/`.

_Last updated: 2026-06-09._

> **`just ci` is GREEN** and now includes the driver-coverage sweep: it hard-fails
> on any item-less PROVED leaf (emission gap), on reconstruction-integrity
> failures, and reports per-theorem replay + per-leaf DP-discharge status
> (✓ proved / ◌ conditional with the missing obligation in the proof's type /
> ✗ failed — currently ✓6 ◌13 ✗0). See
> `docs/plans/2026-06-09_direct-proof-emission.md`.

## Where we are

Stages 1–4 of the pipeline (ACL2 instrumentation → proof-log parse → proof-tree
reconstruction) are built and validated on the sample corpus (recon-tests 00–16,
incl. boundary inductions). The instrumentation now emits the **full induction
justification** (measure/rel/controllers/per-case IH substitutions), the
**preprocess evaluation chains**, and an explicit **discharge node** for every
verdict-only decision-procedure closure. The **proof-producing driver** (stage 7)
replays single-literal rewrite trees end-to-end (`sq-rewrites` from the real log)
and, under the ratified decision-procedure-leaf carve-out, replays discharge
leaves (✓6 ◌13-conditional ✗0 of 19 — the ◌ proofs carry their missing fact as an
explicit bound hypothesis, no `sorry`). **CURRENT FOCUS: c3 composition** — wire
preprocess chains + the WF-induction scaffold + discharge leaves into
whole-theorem replay; target: `my-len-my-app` end-to-end via the driver. See
`docs/plans/2026-06-08_driver-build-plan.md` and
`docs/plans/2026-06-09_direct-proof-emission.md`.

---

## Track A — the rewriting-replay driver (`ACL2Lean/Replay/Driver.lean`) — CURRENT FOCUS

A recursive, fail-closed `replayClause`/`replayNode` over the real tree; grow by tree
complexity, each step driven by a real (or faithfully-synthesized) tree, with
positive + negative tests. Goal: replay `my-len-my-app` (then `app-assoc`)
end-to-end via the driver, not the hand proofs.

### Done (driver foundations)

- [x] **S1/S2** — fail-closed dummy; `equal-self` node → universal mirror fact; native
      `Nat` bridge. Axiom-clean.
- [x] **S3** — congruence + with-lemma rewrite (`cdr-cons`) via the PATH-DIRECTED
      congruence emitter (`:PATH` emitted from ACL2, threaded, navigated —
      `findPath`/`occursIn` retired); multi-node literal chaining.
- [x] **definition-unfold (basic)** — 1-arg, direct body (`re_unfold1_conv`,
      ∀-env body convergence). FIRST REAL TREE replayed: `sq-rewrites` from
      `09-defn-unfold.proof-log`.
- [x] **convergence (easy shapes)** — var/quote/`car`/`cdr`/`consp`/`cons`/
      `binary-+`/`binary-*` in `proveConv`; value-characterized variants
      (`re_val_*`, incl. value-level `if` as `cond`) in the DP lift.
- [x] **Eliminate hand-marshalling (P0–P4)** — `DefMap` repr; driver derives
      no-shadow/`DefInfo` by kernel `decide`; `Development.toWorld` +
      `reflectWorld` derive everything from the log; coverage harness
      (`just driver-coverage`, in `just ci`) sweeps the corpus per theorem.
- [x] **Decision-procedure discharge leaves (c1+c2, ratified carve-out)** —
      `Replay/DischargeLeaf.lean`: lift to Logic primitives, spine fold
      (`re_dp_if_split`), DP fact closed by fixed simp/split_ifs/omega; opaque
      user-fn subterms as quantified values with totality + emitted-TP
      hypotheses; unclosable facts become BOUND HYPOTHESES (conditional proofs,
      no `sorryAx`). ✓6 ◌13 ✗0 of 19; obligations explicit in the proof types.

### c3 — COMPOSITION (current focus; first end-to-end inductive proof)

Target: `my-len-my-app` (then `app-assoc`) replayed by the driver from the real
log, `#print axioms` clean. The pieces exist; c3 wires them:

- [ ] **Induction scaffold (WF)** — `replayClause` recurses `push-clause → *1 →
      case children`, building the induction from the EMITTED measure
      justification (measure/rel/controllers/`:CASES` tests + IH substitutions —
      the measure-emission track's output), threading case-hyp + IH via
      `ReplayCtx`. Includes case↔child linking (match `:CASES` tests to `*1/k`
      input clauses — NOT by order). (task #52)
- [ ] **Preprocess-chain replay** — the emitted preprocess items (final-implies
      expansion, if-folds, abbreviation steps, clause-level chains) compose
      formula → clause, so `Goal'`-style steps and discharge-leaf statements
      connect to the theorem formula. Includes the implicit clausify gap
      (IF-flattening is not emitted — assess whether more emission is needed).
- [ ] **Solidify / IH bridge in the driver** (`equivSource` → `ReplayCtx.caseHyps`;
      the hand proofs' `evalOpt_substTerm_subst1` + `eval_equal_t_implies_eq`
      machinery, mechanized). (task #36)
- [ ] **recognizer + if-simplification nodes** — `re_if_true/false` + recognizer
      reading the CASE HYPOTHESIS (`consp x = nil/t`); lands WITH the scaffold.
- [ ] **def-unfold for REAL def shapes** — multi-arg unfold + if-body whose
      recognizer/if children do the simplification (real `my-app`/`my-len`).
      (task #34)
- [ ] **Totality from admission** — produce per-function totality from the
      termination proof (`WorldEvent.defun.termination` + the emitted measure),
      discharging the DP leaves' `total:…` hypotheses; TP corollaries are
      already consumed as hypotheses. (task #37)
- [ ] **Discharge-leaf composition** — attach `replayDischargeLeaf` proofs as
      clause children inside `replayClause` (today they are validated standalone
      per leaf in the harness).

### Later (Track A backlog)

- [ ] **convergence analyzer (G1), general** — defined-fn totality threading
      opaque witnesses for recursive calls (subsumes the c2 `hConv` hypotheses).
- [ ] **`.boundary` path frames** — child-node congruence inside an unfold /
      rule-RHS (currently hard-fail; aligns with tree child-nesting).
- [ ] Replace the hardcoded frontend with **`gen-world`** output; drop hand-built
      test trees once the real tree replays.
- [ ] The **`acl2_replay` tactic** frontend (read the Lean goal, emit the proof,
      close it).
- [ ] **`Expr` blowup** — `let`-bind shared convergence subproofs.
- [ ] Retire/generalize the over-specialized `re_unfold*_var`.
- [ ] **DP-leaf debt:** 11/\*1/4+\*1/5' tactic residue (simp leaves a non-omega
      goal in one case — likely closable); ground-zero type facts (`len`) —
      emission decision; 03/linear-chain rationals → lean-smt (task #50).

## ACL2 submodule (instrumentation hygiene)

- [x] **Comprehensive `TRACE-LOG` tag review** — DONE 2026-06-09: full systematic
      survey (all 81 hunks vs upstream, with context), ratified namespaced
      convention (`emit/` round-trips `:origin`; `suppress/`; `infra/`), enforced
      by `just check-acl2-tags` (bidirectional). Convention documented in
      CLAUDE.md + `docs/notes/2026-06-09_acl2-tagging-survey.md`; reviewed by two
      decorrelated agents (conformance + semantic accuracy).
- [ ] **Emission backlog** (each is a known, documented gap):
    - **Ground-zero type facts** — `len` etc. have no emitted `:TYPE-PRESCRIPTION`
      (their facts live in ACL2's bootstrap world); decide emit-at-use vs curated
      ground-zero defuns. Blocks 5 assumed DP leaves (12/16).
    - **Non-default well-founded relation / `include-book`** — lexicographic `l<`
      measures need the ordinals book; `include-book` is untested in capture.
      (See the measure plan's deferred section.)
    - **Termination-proof emission** — the admission's measure-conjecture clause
      tree (`WorldEvent.defun.termination` is parsed but ACL2 doesn't yet emit
      the per-case decrease proofs structured) — needed for c3's
      totality-from-admission.

## Track B — type-set / decision-procedure facts (richer emission)

Status change 2026-06-09: every verdict-only decision-procedure closure now emits
an explicit **discharge node** (`preprocess/tau*`, `preprocess/type-set-fc`, …),
and the driver replays these leaves under the ratified carve-out (✓6 ◌13 of 19).
What remains is the RICHER fact emission for the ◌-assumed leaves — each missing
obligation is stated precisely in its conditional proof's type:

- [ ] **Type-set derivation facts** — e.g. `true-listp x ∧ consp x → true-listp
      (cdr x)` (a recursive-definition type-set fact; closes 01/02's 4 leaves).
      Emit the type-alist entries / rules the forward-chain contradiction used;
      consume as DP-fact hypotheses — NEVER re-derive type-set in Lean.
- [ ] **ts-bits lifting** — `:BASICTS`/`:LEAVES` bitmask facts (04's booleanp
      leaf) as DP hypotheses.
- [ ] **Linear arithmetic over rationals** — 03/linear-chain (`<`-transitivity,
      nonlinear after `toRat` cross-multiplication): beyond `omega`; the concrete
      **lean-smt** target (task #50, gated: toolchain pinning, cvc5, axiom
      hygiene).
- [ ] Tau detail (`tau-clause1p` signature/bounder rules) if the above ever
      proves insufficient — Option 1 of the direct-proof plan, deliberately
      deferred.

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

### Audit / correctness debt (revisit — do not drop)

- [ ] **Systematic log↔dump fidelity checker.** The 2026-06-09 dump audit found no
      reconstruction defects, BUT the clause-tree/waterfall layer was verified
      mainly by SELF-consistency (re-dump matches `.dump`), not against the raw
      log — one reviewer over-claimed "byte-identical to expected." Two reviewers
      independently recommended a mechanical checker that re-derives every dump
      claim (steps, ids, results, runes, LHS/RHS) from the raw `.proof-log`.
      Build it; run in ci.
- [ ] **DP-proof sorry/axiom gate.** The coverage harness `Meta.check`s each
      DP-leaf proof, but `Meta.check` does NOT reject `sorryAx` — with
      `assumeFact` there is no `mkSorry` path left, but guard it mechanically:
      scan emitted DP proof terms for `sorryAx`/`Lean.ofReduceBool` (and keep the
      `#guard_msgs` axiom gates on the spike/test theorems).
- [ ] **c3 end-to-end audit.** Before claiming the first driver-replayed
      inductive theorem: ground-truth build + `#print axioms`, then decorrelated
      adversarial reviewers per the CLAUDE.md audit practice (genuine-replay /
      answer-smuggling / statement-fidelity dimensions), as was done for S2/S3.
      (task #38)
- [ ] **Verify the conditional-proof obligations are REAL statements.** The
      ◌-assumed DP facts are bound hypotheses whose statements were machine-built
      (`dpFactStmt`); spot-audit a sample against the source clauses (a malformed
      lift could state a vacuous obligation and "complete" later against the
      wrong fact).
- [ ] (carried) **Careful capture/emission infra revision** — see the item below;
      includes `emit/proof-failed` (positive failure signal),
      `recon-test-dump.sh`'s `|| true` (now swallows the non-zero dump exit),
      capture-heuristic re-audit, and differential-testing the EMISSION itself.
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

- **2026-06-09 (the measure/emission/discharge arc, merged to main):**
  - Measure emission: `(:INDUCTION …)` carries measure/rel/mp/controllers/per-case
    tests + IH substitutions, instantiated at the conjecture; dump renders it;
    validated on boundary recon-tests 10–16 (multi-IH, custom measure,
    multi-controller, swap/constructor IHs, nested induction, 3-way).
  - Failed-proof safety net: QED-less `:DEFTHM` hard-fails reconstruction; CLI
    exits non-zero; capture script keys on QED-per-DEFTHM.
  - Black-box-leaf emission gap CLOSED: preprocess eval chains emitted
    (cons-term folds, ev-fncall, if/equal-self, real abbreviation RHS) +
    explicit discharge nodes at all verdict-only decision-procedure sites;
    harness hard-fails item-less PROVED leaves; `just ci` gates it.
  - Decision-procedure-leaf carve-out ratified (CLAUDE.md); DP-lift replay
    (`Replay/DischargeLeaf.lean`): ✓6 ◌13-conditional ✗0 of 19, kernel-checked,
    no `sorryAx`; missing obligations explicit in proof types (MDD's
    conditional-proof design).
  - ACL2 tag convention ratified + enforced (`just check-acl2-tags`); 4-reviewer
    dump audit (found: 00-direct empty-capture bug → fixed + integrity gate).
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
