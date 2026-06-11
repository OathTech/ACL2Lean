# #37 totality-from-admission — decision log (2026-06-10)

Arguable calls made while MDD afk, for review. Ratified beforehand: emit
ACL2's own termination clauses (no Lean-side derivation of obligations);
discharge per the DP-leaf carve-out — NOTE this is a WIDENING of the
carve-out's originally ratified scope (theorem-proof leaves, 2026-06-09) to
admission-time obligations; flagged in the briefing, blessed by MDD
2026-06-11, and recorded in CLAUDE.md's carve-out section per the
full-audit finding; replay logged admission trees when present; Lean-side
inference only in extremis.

## D1 — emit the RAW measure clauses, not the cleaned set
`prove-termination` computes `measure-clauses-for-clique` then runs
`clean-up-clause-set` (which can DROP trivially-true clauses) and proves the
cleaned set. The Lean totality prover needs a decrease fact at EVERY
recursive call site; if a dropped clause's call site were missing, the
checker would have to re-derive it (inference). So the emission carries the
RAW set — the complete, deterministic output of ACL2's termination-machine —
even though what ACL2's prover literally processed is the cleaned set. The
raw clauses are each verdict-class (carve-out-dischargeable) regardless.
*Alternative:* emit both sets. Rejected as redundant for now.

## D2 — stash-via-global rather than recompute-at-emit
The clauses exist inside `prove-termination` (pre-install); our `:DEFUN`
emitter runs post-install. Chosen: an `infra/` global stash
(`*structured-termination-clauses*`, `(names . cl-set)`), consumed by the
emitter under a names-match guard, cleared on the non-recursive path.
*Alternative:* recompute at the emit site from the world's `recursivep` +
body via `termination-machine` + `measure-clauses-for-clique`. Cleaner
(no timing coupling) but re-runs the machinery and risks divergence from
what admission actually computed (e.g. ruler-extenders in force at
admission). The stash captures the actual artifact.

## D3 — clique clauses attached to every member's :DEFUN event
`measure-clauses-for-clique` is clique-level. For mutual recursion the same
clause set is emitted on each member's event (duplication; corpus has no
multi-member clique with a proof yet). *Alternative:* a separate
`(:TERMINATION …)` event keyed by the clique. Revisit at G5/mutual-recursion.

## D4 — parser strictness for the new fields
`:TERMINATION-CLAUSES` must be present exactly when the justification triple
is (a recursive defun), absent otherwise; a mismatch hard-fails. An EMPTY
clause list parses (skip-proofs logs could produce it), but the totality
PROVER hard-fails when a recursive call site has no covering decrease
clause — safety lands where it matters.

## D5 — prover scope cut (frontiers, not silent gaps)
The WF-induction totality prover initially supports: measure
`(acl2-count <single-formal>)` under `o<`/`o-p`, if-spine bodies, self-calls
plus calls to previously-proven-total functions (defuns processed in
development order, accumulating a totality environment). Sum measures
(`interleave`), custom measures (`cd2`), and multi-member cliques HARD-FAIL
with named frontier messages. This covers my-len/my-app/app/len2/rev-class
functions — the ones the catalog's `total:` hypotheses actually mention.

## D6 — wiring: auto-discharge with hypothesis fallback
`replayProofConditional` tries the totality prover for each `total:fn`
condition; on success the hypothesis is DISCHARGED (disappears from the
mirror's type), on a frontier failure it remains an explicit hypothesis
(today's behavior — visible in the type, so nothing is silently assumed).

## D7 — o< / acl2-count lift primitives
The decrease clauses mention `o<` and `acl2-count`. For Nat-valued measures
(the D5 scope) `o<` is `<` on `Count.acl2Count` values. These enter the
DP-lift vocabulary (`dpValExpr`) as new primitives mapping to the Count
library; ordinal-valued measures are out of scope (frontier).

## D8 — (2026-06-11) the non-recursive-path stash clear was DROPPED
The belt-and-braces clear at the top of `prove-termination-non-recursive`
broke the ACL2 build (an ACL2 defun body admits exactly ONE form after the
declares; the loop-only reading `(PROG2$ NIL NIL)` landed where a declare
was expected). Rather than restructure that function, the clear is removed:
the emitter-side CONSUME-ONCE clear plus the `just`-presence and names-match
guards already make a stale stash unreachable. Residual exposure: none
identified (a stash can only attach to a same-named recursive defun emitted
before any other emission consumes it — which is the defun it belongs to).

Process note: the failed image rebuild initially reported success because
`just build-acl2 2>&1 | tail` masks the exit status (pipeline exit = tail's).
Caught by the unbound-defvar symptom; rebuilds now run with the exit checked
directly.

## 2c — the totality prover: implementation plan (for the continuation)
State at this point: emission (2a) + parse (2b) land the justification AND
the raw termination clauses end to end (validated live: my-len carries
((O-P (ACL2-COUNT X))) and ((NOT (CONSP X)) (O< (ACL2-COUNT (CDR X))
(ACL2-COUNT X)))). `acl2Count_strong_induction` (EvalLemmas) is the WF spine.

The prover `proveTotalityFromAdmission` (Driver.lean), per defun in
development order, accumulating `totalEnv : List (String × Expr)`:

1. NON-RECURSIVE fn (no justification): the body-convergence walk alone —
   conv_defn_N + the convergence analyzer over the body with formal values
   bound; calls to earlier fns use totalEnv; builtins use conv_builtin/
   conv_if lemmas (this is the fixBody_conv pattern, generalized).
2. RECURSIVE fn (D5 scope: measure (acl2-count <formal>) under o<):
   - target: ∀ e' a…, Conv a → … → Conv (fn a…)   (the driver's v-fixed
     hypothesis shape, mkTotalityHypType)
   - acl2Count_strong_induction with motive P av := ∀ e' (args with the
     measured formal's VALUE = av), Conv args → Conv (fn args)
   - inside: conv_defn_N requires body convergence at bindArgs values;
     walk the body tracking branch context (the if-tests' VALUES, as in the
     DP discharge walk); at the SELF-call site, the walk has the argument
     values; the IH applies provided acl2Count(arg-value) < acl2Count(av) —
     justified by the EMITTED decrease clause for that call site, lifted to
     values (clause literals: ruling tests already in branch context; the
     o</acl2-count literal discharged by the Count library:
     acl2Count_cdr_lt_of_consp etc. via the DP-lift with new primitives
     o< ↦ Nat.lt ∘ acl2Count-lift, acl2-count ↦ Count.acl2Count — D7).
   - clause→call-site matching: each non-(O-P …) raw clause is
     (ruling-test-negations…, (o< (acl2-count CALLARG) (acl2-count FORMAL)));
     match by CALLARG = the recursive call's measured-argument TERM.
     No match for a call site ⇒ hard-fail (D4).
3. Wire into replayProofConditional: before declaring htotal_<fn>, try the
   prover; on success put the proof term (not the fvar) into ctx.totalHyps
   (the `used`-filter only sees fvars, so discharged fns simply vanish from
   the telescope); on frontier failure keep the hypothesis (D6).
4. Validation: the coverage table's cond[…] lists shrink (my-len/my-app/fix
   etc. disappear); catalog entry 1's by-decide discharges become redundant
   (switch mylenMirror_uncond to consume the now-unconditional mirror —
   or keep both as regression); axioms stay clean.

## D7' — revision: the obligations are VALUE-level, not evalOpt-level
The decrease clauses never pass through evalOpt (no callBuiltin for
acl2-count/o< needed): the prover interprets them directly over the walk's
VALUE assignment — (acl2-count t) ↦ Count.acl2Count (value-of t) : Nat,
(o< a b) ↦ <, ruling-test literals ↦ the branch context's toBool facts —
and discharges with the Count library (acl2Count_cdr_lt_of_consp etc.).
dpUnary/dpBinary are untouched.

## D9 — the (o-p (measure)) obligation is absorbed by construction
For acl2-count measures the o-p clause asserts the measure is an ordinal;
in Lean the measure lands in Nat and the WF spine is Nat.lt — well-founded
by construction. The prover SHAPE-CHECKS the clause (must be exactly
((o-p <the measure term>)); anything else hard-fails) and records it as
absorbed rather than proving an o-p fact. Not a silent skip: the clause is
consumed by the choice of measure type, and a mismatch fails closed.

## 2c progress (state at this checkpoint)
DONE: Development.justifications projection; walk lemmas in EvalLemmas —
conv_if_split (case-split walk: branch hypotheses `toBool vc = true/false`
in scope for each branch, exactly what the decrease discharge consumes),
conv_defn_1_ex / conv_defn_2_ex (∃N∃v defn-unfold steps),
acl2Count_strong_induction (the WF spine).

REMAINING — the walker proveTotality (Driver.lean), design refined:
- The walk is CASE-SPLIT style (conv_if_split), NOT whole-body value
  characterization: a recursive call converges only under its ruling tests,
  so branch facts must be hypotheses. At each if: characterize the TEST's
  value via the existing dpValProof machinery (varP := formals ↦ av values),
  then walk both branches under the branch-fact fvar.
- Subterm classes inside a branch: var (re_conv_var/varP), quote
  (re_conv_quote), dp-known builtin (conv_builtin1/2 via dpUnary/dpBinary —
  value-characterized where the args are), defined fn:
  * earlier fn → totalEnv proof applied at the arg conv facts,
  * SELF → the IH, applied at the measured arg's VALUE; its `<` premise is
    discharged by matching the emitted clause for this call site (CALLARG
    term match), interpreting (acl2-count t) ↦ Count.acl2Count (value-of t)
    and using Count.acl2Count_cdr_lt_of_consp-class lemmas + the in-scope
    branch facts (+ omega for arithmetic composition),
  * unknown call shape / unmatched site → hard-fail (named frontier).
- Non-recursive fns: same walk, no IH (validates first on total:fix).
- Wiring: replayProofConditional takes justs (Development.justifications);
  per fn try proveTotality (development order, accumulating totalEnv); on
  success ctx.totalHyps gets the PROOF TERM (the used-filter only sees
  fvars, so the hypothesis vanishes); frontier ⇒ hypothesis as today.
- First validation target: simple.proof-log — total:fix (non-recursive),
  then total:my-len (recursive, the cdr/consp shape), then the corpus
  coverage table's cond[] shrinkage + catalog entry 1 simplification.

## 2c VALIDATED (2026-06-11)
The walker (proveTotality + totWalk + totDischargeDecrease, Driver.lean) is
built and wired. First-build validation EXCEEDED the plan: building the
catalog auto-discharged ALL FOUR in-scope totality classes at once —
total:fix (non-recursive 1-ary), total:my-len (1-ary recursive, cdr/consp),
total:my-app and total:app (2-ary recursive, measured first formal). The
catalog entries simplified accordingly (entry 1 keeps only the TP
hypothesis; entries 2/8's mirrors are now UNCONDITIONAL), the audit-#38
pinned statement in DriverTests was updated to the stronger type, and
axioms remain clean on all driver-backed native theorems.

## Leaf-harness wire (in progress at handoff)
The composed replay path already consumes auto-totality via ctx.totalHyps
(theorem-level cond[] shrinkage validated). The remaining surface — the
STANDALONE per-leaf diagnostic harness (replayDischargeLeaf, reported in the
coverage table's [DISCHARGE: …] lines) — now derives each opaque
application's convergence via totWalk + buildTotalEnv where possible and
consumes it with exists_conv_elim instead of binding a total:(…) hypothesis;
underived opaques and tp:/ASSUMED:dp-fact entries are unchanged. Validation
target: leaf lines like "✓ cond[total:(len2 x), tp:len2]" become
"✓ cond[tp:len2]". buildTotalEnv extracted (shared by
replayProofConditional and the harness).

## Solo error-focused audit (2026-06-11, pre-adversarial-audit)
Findings (none blocking; all fail-closed or cosmetic):
- A1 (improvement): the IH applications use RAW mkApp2/mkApp3 (unchecked at
  construction); a value-alignment bug would surface only at the final
  Meta.check/kernel rather than at the construction site. The alignment is
  by construction (dpValExpr of (cdr m) = Logic.cdr av = the Count lemma's
  subject), and the backstop catches any drift — but switching to mkAppM
  would fail earlier with a better message.
- A2 (improvement): buildTotalEnv's catch-all `catch _ => pure ()` swallows
  REAL walker bugs along with frontier errors (fail-closed direction — the
  hypothesis stays — but masks defects). Should distinguish frontier
  messages from unexpected exceptions, at least via trace.
- A3 (improvement): the leaf harness rebuilds the totality environment PER
  LEAF (buildTotalEnv inside tryDischarge); correct but wasteful — hoist
  per development.
- A4 (cosmetic): totDischargeDecrease's callArgVal/avE params are dead
  (`let _ :=`); the value-alignment argument they were meant to carry is
  implicit. Either use them for an explicit defeq assertion or drop them.
- Verified clean: clause-literal polarity logic (ruling (not T) ⇔ fact
  T=true; positive literal ⇔ refutation); fact keying (test terms come from
  the same translation on both sides); capper statements match walker uses
  (the checked mkAppM applications enforce the v-fixed shapes); the
  liftable fast-path for ifs is sound (re_val_if requires all three
  subterm convergences — vacuously safe, and self-calls are excluded by
  liftability); leaf derivations are scoped OUTSIDE the vop binders (no
  capture); the lisp stash is consume-once incl. the non-structured path;
  the gitlink matches the submodule HEAD; no sorry/admit/axiom/
  native_decide in the diff; zero warnings in the gate.

## Audit-fix + efficiency pass (2026-06-11, pre-adversarial baseline)
All solo-audit findings fixed:
- A1: IH applications via checked mkAppM' (construction-time failure).
- A2: buildTotalEnv's catch keeps only "proveTotality:"-prefixed
  (frontier-class) errors; anything else rethrows.
- A3: per-FILE hoists in the coverage harness — reflectWorld once per file
  (was per theorem AND per leaf) and the leaf totality environment once per
  file (was per leaf; it is env-independent).
- A4: dead params dropped; the measured-formal presence guard kept.
The structural efficiency win (the slow-proof complaint): LAZY totality —
replayProofConditional replays against hypothesis fvars exactly as pre-#37
(cheap), then proves admission totality ONLY for the USED total: hypotheses
(building the dev-order dependency prefix once, bounded by buildTotalEnv's
new upTo) and substitutes via replaceFVar. Theorems consuming no totality
pay nothing; prover cost is proportional to use. Coverage outcomes after
the refactor REPRODUCE the documented pre-refactor table (17/37; leaves
✓9 ◌9 ✗0; theorem-level conds tp:-only; TP-paired leaf retentions) — per
the full-audit finding, no pre-refactor baseline artifact was persisted, so
this is reproduction of recorded numbers, not a diff of saved outputs; a
committed golden coverage snapshot folds into #54's audit-debt checker.
TODO.md gains the general
performance-pass item with MDD's optimization model (pipeline latency for a
fresh/updated ACL2 proof is the core OODA loop; library build time is
secondary).

## Full adversarial audit (2026-06-11) — RESULT
5 decorrelated reviewers (emission fidelity incl. live-image adversarial
runs, prover fidelity, lemma layer with scratch instantiations, fail-closed
plumbing with handcrafted malformed events, outside-view claims audit) +
refute-by-default verification. ZERO technical findings survived across the
four code dimensions (prover fidelity: 17 checks, none; lemma layer: 8
positive notes, none; fail-closed: 9 checks, none; emission: 11 checks,
none confirmed). Refuted: a lazy-dependency gap (used fns' callees
necessarily register as used + the hard-fail backstop) and a D8 multi-clique
stash edge case (guard flow traced). CONFIRMED (both documentation-class,
both fixed in this commit): the carve-out widening was blessed in
conversation but unrecorded in CLAUDE.md (now recorded, with the
non-trivial-admission boundary stated); the "verified IDENTICAL" coverage
claim lacked a persisted baseline (reworded to reproduction-of-recorded-
numbers; golden snapshot → #54).
