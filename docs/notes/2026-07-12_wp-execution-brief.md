# WP execution brief — external-knowledge arc (handoff note, 2026-07-12)

Purpose: hand the WP0–WP5 implementation queue to an execution-focused
session. The DESIGN is done and ratified — do not redesign. This note
condenses per-task specs, end states, and stop triggers; the authority for
anything ambiguous is `docs/plans/2026-07-10_external-knowledge-design.md`
(RATIFIED — §§D1–D8, WP table §7, audit record §8, MDD decisions §9), and
the binding process rules are in `CLAUDE.md` (fidelity section + working
discipline + audit practices). Read both before starting.

## Ground state (verified 2026-07-12)

- Branch `mdd/external-knowledge`, tip `8785ed0`, 12 commits ahead of
  `main` (172c8ec), UNMERGED. Working tree clean.
- Landed, each gate-verified: BUG-012 canonical `Number`; BUG-013 minimal
  nil/t identity (`canonSym`); BUG-014 KEYWORD-package duplicate; the four
  lexorder ORDER THEOREMS (`ACL2Lean/LexorderOrder.lean`:
  `lexorder_refl`/`_antisymm`/`_trans`/`_total`, axioms ⊆
  {propext, Classical.choice, Quot.sound}).
- Gates: `lake build` clean (warnings are failures), `just test`,
  `just diff-test` (386 match / 7 known-bug / 0 FAIL), `just ci` exit 0
  (coverage golden byte-identical, check-bugs consistent).

## STOP TRIGGERS — surface these, never work around them

Return to the user (do NOT decide unilaterally, do NOT paper over) when:

1. **A new value-representation duplicate** appears (two SExpr shapes for
   one ACL2 value). It happened three times in this arc (BUG-012/013/014);
   the remaining known candidate surface is packages/strings. Log the
   evidence, propose nothing beyond the pattern, stop.
2. **A statement would need weakening** to go through (extra premise,
   generalized case, "almost the ACL2 theorem"). Forbidden — stop.
3. **The tree/log lacks information** to replay a step. That is missing
   instrumentation to add at the ACL2 source, never license to infer in
   Lean. Hard-fail + stop (carve-out: DP leaves + admission decrease
   obligations only, exactly as in CLAUDE.md).
4. **A gate goes green only via a shortcut** (omega/decide/collapse where
   the tree takes a different route; disabling/skipping anything). Stop.
5. **The golden changes in rows you did not predict.** Diff it, explain
   every changed row, and if any change is unexplained — stop.
6. Anything that smells like a **new MDD design decision** (new species of
   external knowledge, a soundness side condition, a fork behavior choice).

Non-negotiables (from CLAUDE.md, they bind every session): no
sorry/admit/axiom/native_decide in anything reported done; report
mechanically (counts + row names, not adjectives); never merge or push
(commits on this branch only after presenting the increment and getting
explicit alignment); audit-plan sign-off before spawning any subagents;
verify `#print axioms` before any "done" claim.

## Task queue (do in order; pause + report after each)

### Task 0 — BUG-015 interim: fail-closed single-colon package markers
Small warm-up. Spec: `docs/BUGS.md` BUG-015 (interim option). A token
containing a single `:` package marker (not `::`, not a leading-colon
keyword, not inside `|…|` escapes) becomes a PARSER ERROR (fail-closed) —
never a silent colon-in-name symbol. Then reclassify the two BUG-015
corpus pins in `Tests/differential/corpus/complex-and-packages.lisp` to
`known-bug bug:BUG-015 lean <refused>` (ACL2 accepts `keyword:foo` /
`common-lisp:car`; we refuse — over-strict is acceptable and pinned; the
full fix needs BUG-013's external-symbol tables). Update the BUG-015
entry. End state: diff-test 0 FAIL with the two pins refused; ci green.
Care: don't break `:foo` keywords, `|a:b|` escapes, or FOO.BAR symbols —
add corpus rows for those as `match` guards.

### WP0 — fork rule-flush fix (D8) + ground-zero snapshot emission (D3/D5)
Spec: design §D8 (the flush bug is audit finding C — fix it FIRST, it is
load-bearing for every species) and §D3 (cited-closure ground-zero defun
snapshots: `:SOURCE :GROUND-ZERO`, recomputed termination clauses,
builtin-named fns EXCLUDED from the world) + §D5 (emit the cited
ground-zero RULE statements so D5 constants are recompute-checked, incl.
the fail-closed check that the lexorder rules' stored `:EQUIV` is
EQUAL/'T as verified in perm.proof-log).
Mechanics: work in the `acl2/` submodule (branch `acl2-lean-output`);
EVERY inserted region carries exactly one `; TRACE-LOG[<ns>/<label>]:` tag
(`emit/` origins must round-trip); `just check-acl2-tags` enforces.
Rebuild ACL2 (`just build-acl2`), recapture the proof logs (they are
gitignored and regenerated — see `just ci`'s regeneration step), and
verify with `lake exe acl2lean parse-proof-log` / `dump-proof-tree` that
the new events parse (extend `ProofLog.lean` fail-closed — no
default-case swallowing).
End state: isort/perm logs contain the snapshot + rule-statement events,
parser consumes them, ci green with golden byte-identical (emission alone
must not change replay behavior).

### WP1 — D3 world entries + retire groundZeroDefs; D6 totality
Spec: §D3, §D6. Non-builtin snapshot defuns become World entries at
Development build; `groundZeroDefs` in the Driver is retired (the FIX
migrates — read its current call sites first); D6 = totality prover runs
on the RECOMPUTED admission clauses for snapshot defuns (same carve-out
scope as #37, never an obligation ACL2 didn't emit).
End state: no scoreboard rows flip today (audit F1 said so — that is
expected, don't chase rows); ci green; golden changes only if predicted.

### WP2 — D4 builtin definition facts
Spec: §D4. Per cited builtin fn a definition fact stating
`callBuiltin`-vs-emitted-body agreement, statement RECOMPUTE-CHECKED
against the emitted snapshot body (never hand-written free-floating).
Order: TRUE-LISTP (rerouted here by audit F1 — it IS a callBuiltin entry,
EvalOpt.lean:82), LEN, NFIX; then BOOLEANP/ENDP/ATOM as cited.
End state (the design's scoreboard): TRUE-LISTP-ISORT, APP-NIL ×2,
TRUE-LISTP-REV, REV-REV, LEN-REV-ACC advance or replay; CD2-BOUND
advances but KEEPS its ◌ dp-fact leaves (audit F9 — do not force it).

### WP3 — D5 prelude constants + builtin-boolean discharge branch
Spec: §D5. The mathematical core is DONE (`LexorderOrder.lean`). Remaining:
(a) state the two prelude constants — ∀-env mirror statements of
LEXORDER-REFLEXIVE and LEXORDER-TRANSITIVE — and prove them from
`lexorder_refl`/`lexorder_trans` + `lexorder_boolean`/
`cond_toBool_lexorder` (EvalLemmas.lean) through evalOpt; recompute-check
the statements against the WP0-emitted rule statements (fail-closed on
mismatch). (b) the builtin-boolean branch in `dischargeRuleHyp`'s boolean
route (audit F2): the routeBool TP pin (Driver.lean ~6214) requires an
emitted TP + world def — LEXORDER has neither; a builtin-boolean fn
discharges via `lexorder_boolean` instead. (c) verify the
FC-rules-inside-DP-leaves interaction against a real dumped isort tree
(audit F3's caveat) before claiming the row.
End state: ORDEREDP-ISORT advances past `rule LEXORDER-TRANSITIVE: no
stored-rule hypothesis in scope` (it may hit a later wall — report which).

### WP4 — D1 mirror registry + rewire dischargeRuleHyp
Spec: §D1 (+ scalability analysis §4 — this exists because inlining does
not scale; ≈557M-node perm-equiv precedent). Mirror statements become
per-theorem `addDecl` constants; `dischargeRuleHyp` references them
instead of `letBindFVar` re-inlining; same-book first. Also the
dependency-ordered one-session harness mode (audit F7).
End state: perm book still replays IDENTICALLY (this is the regression
gate); proof sizes measured before/after and reported; golden
byte-identical.

### WP5 — D2 `evalOpt_world_mono` + D7 cross-book assembly
Spec: §D2 — the statement is FIXED, including the `hnew` side condition
(world-first dispatch shadows callBuiltin: EvalOpt.lean:150-155); prove it
as stated, a fuel induction over evalOpt. Long grind; no shortcuts — if a
case seems to need a semantic change, that's stop-trigger 6. Then §D7:
assemble isort from its 3 includes (identity check → registry → transfer
→ normalization bridge; obligations home-world book-tagged; cross-book
TP-pin route per audit F4b).
End state: ORDEREDP-ISORT / HOW-MANY-ISORT rule hyps discharge; report
row-by-row.

### NOT in this queue
WP6 (HOW-MANY-ISORT clausify-spine residual at *1/3'4') is an open-ended
investigation — leave for a design-capable session. Same for the BUG-013
full import table and anything hitting a stop trigger.

## Verification crib

```sh
lake build                 # zero warnings tolerated
just test
just diff-test             # 0 FAIL; new divergences get BUGS.md + pins
just ci                    # golden byte-identical unless rows predicted
just check-acl2-tags       # after any fork edit
lake exe acl2lean dump-proof-tree <f>   # drive off the REAL tree
```
Axioms for any new theorem: `#print axioms` must be within
{propext, Classical.choice, Quot.sound} — no sorryAx, no ofReduceBool.
