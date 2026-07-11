# External-knowledge discharge — design (RATIFIED 2026-07-11)

*2026-07-10, branch `mdd/external-knowledge`. Supersedes the roadmap's R2(c)
paragraph (see its 2026-07-10 addendum); problem statement + measured evidence
in `docs/notes/2026-07-10_external-knowledge-assessment.md`.*

*RATIFIED (MDD 2026-07-11), post-audit: D5's justification policy
(prove-in-Lean-about-the-primitive, 2026-07-10) plus all four §9 decisions —
D3 snapshot scope = CITED-CLOSURE; D4 growth = PER CITED FN with H3 gates;
D7 obligations = HOME-WORLD, BOOK-TAGGED; sequencing = REGISTRY (WP4)
BEFORE cross-book (WP5). Work proceeds in WP order, WP3's lexorder_trans
feasibility spike first (the audit's top open risk).*

## 1. Problem

A book's proofs lean on definitions and rules that do not originate in that
book's log — four species (assessment note §table): (1) ground-zero built-in
defuns, (2) ground-zero built-in rules, (3) included-defun totality, (4)
included-book rules. The replay must discharge all four fail-closed, with
**scalability as a first-class constraint** (MDD directive 2026-07-10):
compositional proofs, not inlining — the same-book inlining discharge already
produces ≈557M-node proof terms (perm-is-an-equivalence), and cross-book
inlining would compound multiplicatively with dependency depth (isort pulls
3 books; qsort has 6931 rewrite steps).

## 2. Verified code facts the design rests on

- `evalOpt` dispatch is **WORLD-FIRST**: `w.defs.get? s` and only on `none`
  fall back to `callBuiltin` (EvalOpt.lean:150-155). A world entry SHADOWS a
  builtin. The no-shadow discipline exists because of this.
- `evalOpt_defs_ext` (EvalOpt.lean:389) is an **agreement** congruence
  (`∀ s, w1.defs.get? s = w2.defs.get? s`) — NOT extension monotonicity.
  No world-extension lemma exists yet.
- `groundZeroDefs` (ClauseTree.lean:115) holds only `FIX`, hand-transcribed;
  its own docstring names emission-at-use as the eventual alternative.
- The builtin/ground-zero-defun OVERLAP set: `TRUE-LISTP` (EvalOpt.lean:82),
  `LEN`, `NFIX`, `BOOLEANP` (+ `ENDP`, `ATOM`) are `callBuiltin` entries AND
  ACL2 defuns; `SYMBOLP` is a genuine primitive. **Every ground-zero fn the
  current scoreboard walls cite is in the overlap set** — so D4, not D3's
  world entry, is what flips the current rows (audit F1, 2026-07-11; the
  doc's first draft mis-classified TRUE-LISTP as a pure gap).
- Boolean-conclusion rewrite rules are stored EQUAL-class with rhs `'T`
  (ACL2's boolean strengthening at create-rewrite-rule): verified on every
  perm-book boolean rule, e.g. `((:REWRITE PERM-SYMMETRIC) ((PERM X Y))
  EQUAL (PERM Y X) 'T)` (perm.proof-log). The equal-only rule filter
  (Driver.lean:6282) therefore KEEPS them; their discharge goes through
  `dischargeRuleHyp`'s boolean route, which pins the truthy value via the
  head fn's emitted TP + world def (Driver.lean:6214-6217) — both absent
  for a BUILTIN head like `LEXORDER`.
- `dischargeRuleHyp` (Driver.lean:6141) takes `depProofs : List (String ×
  ClauseProof)` — same-log only — and RE-REPLAYS the dependency inside the
  consumer's telescope (the inlining to be retired).
- Mirror statements are `∃N ∀f≥N, evalOpt f w env φ = some v ∧ v ≠ nil`,
  stated over the book's concrete log-derived world.

## 3. The design

### D1 — The mirror REGISTRY (the compositional core)

Each book's replay emits one Lean CONSTANT per replayed theorem
(`addDecl`): `<book>.<thm>_mirror : <telescope> → Mirror w_B stmt`.
Consumers — same-book AND cross-book — discharge `rule:<thm>` hypotheses by
**applying the constant**, never by re-replaying the dependency. The kernel
checks each proof once; a reference is O(1). `dischargeRuleHyp` is rewired
from re-replay to registry application (this alone should collapse the
≈557M-node perm-equivalence term to roughly its own replay size).

Mechanics v1: the coverage harness processes books in dependency order
(`books.txt` already is that order) within one MetaM session; the registry is
the environment (constants addDecl'd as each book replays). Deterministic —
re-derived per run; persistence via generated modules is a later
optimization if wall-time bites.

Scope honesty (audit F7): this is a real harness rework, not a flag — today
the harness replays each `.proof-log` INDEPENDENTLY, `replayProofConditional`
returns an ephemeral `Expr`, and the only `addAndCompile` is for WORLDS
(`derive_world`). D1 adds per-theorem mirror-constant emission and a
one-session, dependency-ordered, multi-book pass. Budget WP4 accordingly.

### D2 — World transfer: a NEW monotonicity lemma, and the shadow trap

Cross-book application needs: a mirror over `w_B` used in a proof over
`w_C ⊇ w_B`. The needed lemma (new, EvalOpt.lean, proved by the same case
bash as `evalOptStep_mono`):

```
theorem evalOpt_world_mono {w1 w2 : World}
    (hext  : ∀ s d, w1.defs.get? s = some d → w2.defs.get? s = some d)
    (hnew  : ∀ s, w1.defs.get? s = none →
               w2.defs.get? s = none ∨ (∀ args, callBuiltin s.name args = none))
    : evalOpt f w1 env t = some v → evalOpt f w2 env t = some v
```

`hnew` is NOT bureaucracy — it is the soundness condition world-first
dispatch forces: if `w2` adds a def for a name `w1` resolved via
`callBuiltin` (e.g. `LEN`), the two evaluations take different routes and the
implication is false without it. Both side conditions are DECIDABLE per book
pair, no search: `hext` by folding `w_B.defs` (decide); `hnew` per new
symbol — a non-builtin name makes `callBuiltin` fall through to `none`
(provable per name). Caveat (audit F6): `callBuiltin` dispatches on the bare
NAME string (EvalOpt.lean:154 passes `s.name`), so a new world symbol whose
name string collides with a builtin (e.g. a non-ACL2-package `LEN`) makes
`hnew` unprovable and correctly BLOCKS the transfer — fail-closed, sound,
but the provability claim is per-name-string, not unconditional. Fuel shape
is preserved (the lemma is per-fuel, so `∃N∀f≥N` transfers directly).

Proof-effort note (audit F5): this is NOT the same case bash as
`evalOptStep_mono` — that lemma has ONE world (one `defs.get?` scrutinee);
this one splits `w1.defs.get? s` × `w2.defs.get? s` four ways in the call
branch (def/def via hext-injectivity of values, def/none impossible by hext,
none/def and none/none via hnew's disjunction). A new lemma of moderate
size, not a transcription.

Where hypotheses live (audit F4a — the first draft was wrong here):
`rule:`-hypotheses are STATED over the CONSUMER's world — `mkRuleHypType`
builds `EvTrue w_C … → evalOpt w_C lhs = evalOpt w_C rhs` (Driver.lean:
3821-3827). What stays stated over the HOME world `w_B` is the dependency's
OWN telescope (its `total:`/`tp:` base facts), which the registry constant
carries; those are convergence-shaped and transfer FORWARD by this same
lemma when needed. No backward transfer exists or is needed.

ACL2 fidelity note: ACL2 prohibits redefinition of built-ins, so on legal
input the shadow case never arises in real worlds; `hnew` is how the Lean
side makes that assumption explicit and checked rather than ambient.

### D3 — Species 1: ground-zero defun SNAPSHOT EMISSION

At capture start the fork emits `(:DEFUN … :SOURCE :GROUND-ZERO)` events for
the def-closure of every ground-zero LOGIC-mode function cited anywhere in
the captured events (definition runes, clause terms, induction schemes),
with **recomputed termination clauses** for the recursive ones — the same
termination-machine recomputation as D6 (deterministic recomputation =
emission, not inference; the R2b-ratified argument). They flow through the
normal pipeline: parser → Development → `toWorld` → totality prover →
`deriveDefInfoN` unfolds. `groundZeroDefs` (the hand-pinned `FIX`) retires
in favor of the emitted events.

**Exclusion rule (forced by D2):** a ground-zero defun whose name is a
`callBuiltin` builtin (`TRUE-LISTP`, `LEN`, `NFIX`, `BOOLEANP`, `ENDP`,
`ATOM`, …) must NOT enter the world — it would shadow the builtin, break
the no-shadow facts, and violate `hnew`. Those go the D4 route. The
no-shadow CI gate enforces the boundary.

**Honest scope note (audit F1):** on the CURRENT corpus every cited
ground-zero fn is in the overlap set, so D3's world-entry species has no
scoreboard row of its own today — its deliverables are (a) migrating the
hand-pinned `FIX` to emission, (b) the emitted BODIES that D4's statements
recompute-and-check against, and (c) the fail-closed path for future
non-builtin cites. D4 is what flips the rows.

### D4 — Builtin DEFINITION FACTS (the overlap set)

For each builtin that ACL2 defines by defun, the replay of a
`definition:<FN>` rune needs `evalOpt f w (FN x…) = evalOpt f w body[x…]`.
Provide it as a proved Lean lemma per fn (world-parametric, no-shadow
hypothesis — L3), with the body statement RECOMPUTE-AND-CHECKED against the
emitted ground-zero snapshot (never hand-transcribed). `deriveDefInfoN`
consults this registry species when the fn is absent from the world.

Bonus, not incidental: each such lemma is a kernel-checked proof that our
`callBuiltin` primitive agrees with ACL2's own definition of the function —
a fidelity validation of the trusted core that the differential harness can
only sample.

### D5 — Species 2: ground-zero rules as PRELUDE CONSTANTS (ratified core)

Justification policy (MDD-ratified 2026-07-10): proved ONCE in Lean about
the trusted-core primitive — the mirror's meaning is defined by
`Logic`/`evalOpt`, so this adds zero trust assumptions beyond the wiring
assumption already policed differentially; the standard ACL2 build admits
these theorems with proofs SKIPPED (`ld-skip-proofsp`,
interface-raw.lisp:9638), so no replayable ACL2 evidence exists in any
capturable image. Precedent: the #37 TP-prover ratification.

Shape: `gz.lexorder_transitive : <no-shadow hyps on cited builtins> →
Mirror-fact over ANY w` — world-parametric (the formula evaluates through
`callBuiltin` only: `IMPLIES` and `LEXORDER` are builtins), entering
`dischargeRuleHyp` through the same registry interface as D1 constants,
followed by the existing formula→stored-rule recompute-and-check. The
STATEMENT + rune identity + normalized rule form (incl. rule-class flags —
`lexorder-transitive` is `(:rewrite :match-free :all)`; the parser's
RuleSpec must learn to carry match-free) come from a ground-zero RULE
SNAPSHOT emitted at capture start, read off ACL2's world; the Lean lemma
discharges an obligation whose statement is the emitted artifact
(fail-closed on mismatch).

**Discharge-path gap this must close (audit F2, verified):** the expected
stored shape is EQUAL-class `(LEXORDER X Z) → 'T` (boolean strengthening —
every perm-book boolean rule is stored this way; confirm on the real
snapshot when WP0 lands, fail-closed if not). That passes the equal-only
rule filter, but `dischargeRuleHyp`'s boolean route pins the truthy value
via the head fn's emitted TP + WORLD DEF (Driver.lean:6214-6222) — and
`LEXORDER` is a builtin with neither. Work item: a BUILTIN-BOOLEAN branch
in the boolean route, pinning via the registered builtin two-valuedness
lemmas (`lexorder_boolean` already exists, landed 2026-07-09). Free-var
hyp relief (`y` is free in transitive's hyps) rides the existing recorded
relief-chain machinery — use sites are in the CONSUMER's tree as for any
rule.

**Proof-risk note (audit F3 — the first draft undersold this):** the
Lexorder.lean order-property proofs are commented out AND BROKEN — the
BUG-006/007/008 alphorder correction changed `lexorder.induct` and breaks
their case structure; `lexorder_trans` previously ran at maxHeartbeats
12.8M (Lexorder.lean:95-102). WP3 therefore STARTS with a feasibility
spike: re-prove `lexorder_trans` against the corrected definition before
any plan claims depend on it. D5's policy is ratified; its central kernel
obligation is real work, not a restore.

**SPIKE RESULT (2026-07-11) — WP3 BLOCKED on BUG-012 (MDD decision
required).** The spike found the obligation FALSE as currently statable:
`lexorder` transitivity fails over ALL SExpr (executed countermodel —
x=((2/4) . 5), y=((1/2) . nil), z=((2/4) . 3): T, T, NIL), because
`Number` admits non-canonical representations ACL2's value space excludes
and the cons branch's structural `==` distinguishes value-equal junk. The
∀-env rule hypothesis mkRuleHypType would state for LEXORDER-TRANSITIVE is
therefore false — undischargeable, fail-closed, but a statement-meaning
divergence of the trust-note class that also silently affects any
canonicity-sensitive ACL2 theorem (verified: `(equal (* 1 q) q)` = NIL for
q = `.rational 2 4`). Full entry: docs/BUGS.md BUG-012. Resolution options:
(A) canonical-by-construction `Number` — junk unrepresentable, statements
unchanged, value space = ACL2's (masquerade-aligned; trusted-core surgery);
(B) canonical-env hypotheses in mirror/rule statements (statement-builder +
mkRuleHypType change; matches ACL2's own quantification). WP0-WP2, WP4,
WP6 are UNAFFECTED and proceed; WP3/WP5's rule discharge waits on the call.

Scope note: of the four ground-zero lexorder theorems, anti-symmetric and
total are :FORWARD-CHAINING — expected to surface inside DP leaves where
the ratified carve-out already governs discharge (asserted from rule
classes, not yet checked against a dumped isort tree — verify at WP3).

### D6 — Species 3: included-defun totality (R2b, ratify here)

Included defuns re-emit with recomputed termination clauses (the
termination machine is deterministic; recomputation = emission). The
totality prover then treats them exactly like local defuns; the D6-kept
`total:<included-fn>` hypotheses discharge. One mechanism shared with D3.

### D7 — Species 4: cross-book rule discharge (assembly of D1+D2)

Consumer theorem in book C cites rule R from included book B:
1. **Identity check** (fail-closed): C's `includedTheorem` statement for R
   ≡ B's own theorem statement, compared after parse.
2. **Registry lookup**: `B.R_mirror` over `w_B`, conditional on B's
   obligations.
3. **Transfer**: `evalOpt_world_mono` with the two decided side conditions
   → the mirror over `w_C`.
4. **Recompute-and-check**: the dischargeRuleHyp normalization bridge
   (formula → stored rule), with the stored-rule datum taken from
   **B's own log's `(:RULES)` entry** (captured at B's certification).
   NOT free cross-book (audit F4b): the bridge's boolean route reads the
   conclusion head fn's TP from the CONSUMER's `ctx.tpHyps` + world
   (Driver.lean:6214-6222). For a boolean rule whose head fn comes from B
   (e.g. `HOW-MANY`), the pin is supplied by either (i) the consumer's TP
   prover run against `w_C` — the fn's def IS in `w_C` via include
   re-emission, and `proveTp` proves emitted corollaries from the body —
   or (ii) B's own TP fact transferred forward by `evalOpt_world_mono`
   (TP facts are convergence-shaped over `w_B`). (i) is the default (no
   new machinery); (ii) is the fallback where the prover's frontier bites.
5. **Obligations compose book-tagged**: B's residual base facts (e.g.
   `total:perm`, `tp:memb`) remain stated over `w_B` in the composed
   telescope; the obligation log gains (book, fact) keys and the H2d
   dashboard reports them per book. They are discharged once, at B, and
   shared by every consumer — obligations do not multiply with fan-out.
   (The consumer's own `rule:` hypotheses remain stated over `w_C` — see
   D2's "where hypotheses live".)

### D8 — Prerequisite fork fix: the rule flush (audit finding C)

A book's LAST theorem's `(:RULES)` entry never flushes into its own log —
harmless for single-log replay, load-bearing the moment D7 step 4 reads
stored rules from source-book logs. Fix in the fork (flush at
end-of-certification), tag per the TRACE-LOG discipline, recapture corpus.

## 4. Scalability analysis (why this shape)

- Two distinct scale axes (audit F8 — keep them separate): `letBindFVar`
  (landed, 14-36×) shares a discharge term used N times WITHIN one proof;
  the registry removes per-consumer RE-REPLAY of dependencies — the axis
  that multiplies with dependency depth and fan-out. The ≈557M figure
  (perm-is-an-equivalence, sizeWithoutSharing of the replay output,
  POST-letBindFVar era measurement) is motivation for the second axis;
  re-measure as the WP4 baseline before/after.
- Inlining: kernel+elaboration work ≈ Σ over the dependency TREE per
  consumer theorem — multiplicative in depth/fan-out.
- Registry: proof size per theorem ≈ own replay + O(1) constant references
  + one transfer application per cited book. Kernel work is Σ over
  theorems, each ONCE — linear in corpus size. This is how Mathlib scales,
  and it is the compositionality MDD asked for.
- The side-condition `decide`s are per book PAIR, not per theorem — cache
  the `w_B ⊆ w_C` fact as a constant too (and note the project's perf
  lesson: `mkDecideProof` over big worlds is O(world) kernel evaluation
  per fact — one more reason they must be per-pair constants, not
  per-theorem re-derivations).

## 5. Alternatives considered (and why not)

- **Instrumented proveall capture** for species 2: run `make proofs` under
  the fork and replay boot proofs. Faithful to a proof ACL2 *can* produce,
  but heavy, replays an artifact no distributed image relies on, and adds
  nothing over D5's kernel proof epistemically (rejected; recorded).
- **Builtin-first dispatch** (makes extension monotonicity unconditional):
  changes trusted-core semantics observable only on illegal input (ACL2
  bans builtin redefinition), but forces re-deriving every kernel proof +
  full differential re-run. `hnew` gets the same guarantee checked, not
  assumed (rejected for now; revisit only if `hnew` bookkeeping bites).
- **World-parametric mirror STATEMENTS from the driver** (roadmap shape
  (i)): also compositional, but requires a statement-builder + telescope
  rework now. Transfer (shape (ii)) gets the same scaling with a single new
  lemma. NOT foreclosed: R6 (encapsulate) is already slated as a
  statement-builder change; revisit shape (i) there. Hand/Imported lemmas
  stay world-parametric per L3 regardless.
- **One giant re-emitted log** (rejected at R2 already: re-proves nothing,
  breaks one-log-one-book).

## 6. Invariant + fidelity compliance

- L1: registry entries sit behind the judgment-layer interfaces; no
  monolithic inductive. L2: untouched (R unchanged). L3: D4/D5 lemmas are
  world-parametric; per-book constants are instances over log-derived
  worlds.
- Statements always from emitted ACL2 artifacts (snapshots, logs);
  recompute-and-check at every joint; hard-fail at every gap (unknown
  ground-zero fn → emission bug, identity mismatch → fail, missing stored
  rule → fail).
- The carve-out boundary is unchanged: D5 covers boot-admitted rules where
  ACL2 records no proof; every recorded proof is still fully mirrored.

## 7. Work packages (leverage order) + gates

| WP | Content | Unblocks (scoreboard) |
|----|---------|----------------------|
| WP0 | D8 fork flush fix + ground-zero defun/rule snapshot emission (D3/D5 statements) + recapture | — (enabler; supplies D4/D5 statements) |
| WP1 | D3 world entry for non-builtin snapshot defuns + retire `groundZeroDefs` (FIX migrates); D6 totality on recomputed clauses | no rows of its own today (audit F1) — enabler for D6 + future non-builtin cites |
| WP2 | D4 definition facts: TRUE-LISTP (audit F1 — rerouted here), LEN, NFIX (+BOOLEANP/ENDP/ATOM as cited) | TRUE-LISTP-ISORT, APP-NIL ×2, TRUE-LISTP-REV, REV-REV, LEN-REV-ACC advance/replay; CD2-BOUND advances (retains its ◌ dp-fact leaves, audit F9) |
| WP3 | D5 prelude constants: lexorder-reflexive/-transitive — STARTS with the lexorder_trans feasibility spike (audit F3); + the builtin-boolean branch in the discharge boolean route (audit F2) | ORDEREDP-ISORT advances past both |
| WP4 | D1 registry + rewire dischargeRuleHyp (same-book first — perm book as regression, measure proof-size before/after) + the one-session dependency-ordered harness mode (audit F7) | scale headroom; golden byte-identical gate |
| WP5 | D2 `evalOpt_world_mono` + D7 assembly (isort ← its 3 includes, incl. the cross-book TP-pin route, audit F4b) | ORDEREDP/HOW-MANY-ISORT rule hyps discharge; R3 opens |
| WP6 | HOW-MANY-ISORT clausify-spine residual at *1/3'4' (independent investigation) | HOW-MANY-ISORT |

Gates per WP: `just ci` green, golden updated only with expected-row
justification, axioms clean, differential green; audit before the
R2-complete claim.

## 8. Audit record (2026-07-11)

Single-Opus adversarial review (read-only, primary-sourced), findings
independently verified before incorporation. Outcome: **the riskiest new
piece — `evalOpt_world_mono`'s soundness (hext+hnew sufficient, hnew
necessary) — was verified sound by the reviewer against the real
`evalOptStep`.** Incorporated findings: F1 (BLOCKER: TRUE-LISTP is a
builtin, EvalOpt.lean:82 — first draft mis-classified it and
self-contradictorily routed the main WP1 rows into D3's own exclusion
rule; rerouted to D4/WP2), F2 (boolean-route TP pin can't serve builtin
heads → the builtin-boolean branch; the iff-storage half of the finding
was REFUTED by the real perm log — boolean rules are stored EQUAL/'T),
F3 (Lexorder order proofs are broken-by-correction, not "half-drafted" —
feasibility spike first), F4 (rule hyps are stated over the CONSUMER
world; cross-book boolean TP pin needs an explicit route), F5-F9 (proof
effort, hnew name-string caveat, D1 harness scope, scale-axis
separation, CD2-BOUND residual). Reviewer's could-not-verify list that
remains open: lexorder_trans provability under the corrected definition
(the WP3 spike), the actual `:EQUIV` a ground-zero snapshot will record
(fail-closed check at WP0), and the FC-rules-only-in-DP-leaves assertion
(verify against a dumped isort tree at WP3).

## 9. MDD decisions (RATIFIED 2026-07-11 — all as proposed)

1. D3 snapshot scope: **CITED-CLOSURE** (fail-closed, corpus-driven; an
   uncited-but-needed fn hard-fails at replay and drives the next emission).
2. D4 fn growth: **PER CITED FN**, each with its consistency lemma
   recompute-checked against the emitted body + differential entries per H3.
3. D7 obligation surfacing: **HOME-WORLD, BOOK-TAGGED** (discharged once at
   the source book, shared by all consumers; the reverse transfer direction
   is false in general, so this is also the only sound uniform choice).
4. Sequencing: **REGISTRY (WP4) BEFORE CROSS-BOOK (WP5)** — same-book
   rewire on the perm book first, golden-gated, proof-size measured.
