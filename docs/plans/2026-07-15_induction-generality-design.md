# Induction generality — design (Stage 1 PROPOSAL, 2026-07-15)

Status: **RATIFIED (MDD, 2026-07-16)** — after Stage-2 adversarial review
(§8), full-plan self-review (§9), and the theory-specialist audit (§10),
all incorporated. Execution begins at J1. MDD rulings
(2026-07-16): **Q1 RESOLVED** — the decrease-obligation emission already
exists (see I4; verified on the real 13-multi-measured-var log: the defun's
`:TERMINATION-CLAUSES` carry the exact per-IH decrease facts incl. the
variable swap, plus the `O-P` well-formedness clause); **Q2 RATIFIED** —
the reconstruction WPs (J5–J7) are in-arc; **Q3 RATIFIED** — the
admission-decrease carve-out ratification (2026-06-11) COVERS scheme
decrease discharge (same emitted clauses, same prover; noted here, no
separate decision entry).
Grounding: `docs/notes/2026-07-15_induction-generality-survey.md` (Stage 0;
all axes anchored to real trees). Directive for this arc (MDD, 2026-07-15):
**design for the future — do not bake in limitations** that the sorting
corpus's tail (lexicographic measures, mutual-recursion schemes, custom
measures) will break.

## 1. Goal and non-goals

Goal: replace `replayInduction`'s hardwired scaffold (single controller,
literal `(ACL2-COUNT v)`, cdr-decrease, one IH) with a GENERIC scaffold that
consumes exactly what ACL2's induction machine emits — measure term, wf
relation, measured subset, per-case ruling tests and IH substitution
alists — for ANY scheme those fields can express. Target rows now:
TRUE-LISTP-FLATTEN, LEN-ZIP2, LEN-INTERLEAVE, LEN-ZIP3, NESTED-INDUCTION.
The same arc carries the two reconstruction frontiers (msort/ordered-perms
pool linkage; bsort equivalence source) and the dotted-rune parse as
separate WPs — WITHOUT them the sorting books stay blocked regardless of
scaffold generality (survey, "reconstruction-level walls").

Non-goals: `:induct` hints beyond what the logs already record; changing
what ACL2 emits for cases/tests/substitutions (believed sufficient — checked
assumption C1 below).

## 2. Design pieces

### I1 — Measure interpretation: the META-LEVEL REGISTRY over pinned
### values (REVISED TWICE: review OUT-1/IN-3, then self-review 2026-07-16)

FIRST, the trust observation that governs this whole section: **the
measure term appears in NO statement.** The mirror theorem says nothing
about measures; μ is internal well-foundedness bookkeeping for OUR proof.
Faithfulness lives in mirroring ACL2's emitted cases/tests/IH-alists —
the measure interpretation only gates our ABILITY to construct the proof
(worst case: a failed proof, never a wrong statement). So the
interpretation may be meta-level without any fidelity compromise.

μ : Env → Nat is the COMPOSITIONAL META-LEVEL INTERPRETATION of the
emitted measure term over the measured variables' env values, via an
EXTENSIBLE HEAD REGISTRY (the `dpUnary` pattern, L1-fragment style):
`ACL2-COUNT ↦ SExpr.acl2Count`, `BINARY-+ ↦ Nat.add` (post-decode),
builtin heads ↦ their `Logic` value functions + Nat decode (covers CD2's
`(NFIX N)` class). μ is total and pure by construction — exactly the shape
the current single-var scaffold already uses (`SExpr.acl2Count`), and the
WF motive needs (review OUT-1). An UNKNOWN measure head HARD-FAILS at
scaffold-construction time — an honest, loud frontier; extension is
additive registration.

Rejected on self-review (2026-07-16, superseding the first OUT-1 fix):
the "defaulted classical eventual-value" decode. Defining μ by evaluating
the measure through the WORLD would demand object-vs-meta agreement
theorems (the world's recursive `ACL2-COUNT` def vs `SExpr.acl2Count` —
induction-grade work with zero consumers, since the measure is in no
statement), and a reachable default value adjacent to a WF argument is a
soundness smell no "never reasoned about" promise should paper over.
The registry keeps the loud-frontier property that motivated the original
"no grammar" instinct while adding zero new theory.

Two obligations previously conflated (review IN-3) are SEPARATE:
(i) the emitted `((O-P measure))` clause is ACL2's ORDINAL well-formedness
for the `o<` relation — it maps to the future ordinal instance and does
NOT establish naturalness; (ii) the Nat decode for THIS arc's instance is
discharged by value lemmas (`acl2Count`/`+`/`nfix` are nat-valued), not by
consuming the O-P clause.

The WF IMAGE is an interface, not Nat: `MeasureImage` = (carrier, relation,
WELL-FOUNDEDNESS PROOF, decode) — each instance re-proves its
strong-induction lemma over its own wf relation (review OUT-5: the lemma
statement stays relation-polymorphic so Nat does not leak into the
contract). Instance 1 (this arc): naturals with `Nat.lt`. Instance 2
(future — a REAL WP with real cost, not a free slot): ACL2's o-p ordinal
notations for lexicographic `llist` measures, whose `o<`
well-foundedness (ε₀) is its own theorem. NOTHING in the scaffold may
match on the measure term's syntax.

### I2 — Env-level strong induction (one scaffold lemma), POOL-SHAPED

The motive is over the ENVIRONMENT and over a CLAUSE LIST from day one:
`P env := EvTrue w env ⟪conjoined pool entry⟫`. Justification (corrected
by theory-audit T1): ACL2 pool entries hold clause SETS
(`to-be-proved-by-induction` takes a cl-set), and a REVERTED original
conjecture (I6) clausifies to possibly several clauses — so the
non-singleton case is real, just not for the reason first given.
Building the motive single-clause and retrofitting at J5 would rebuild
the scaffold's front door; the singleton is the degenerate case, not the
design. One
once-proved lemma (per MeasureImage instance):

```
measure_strong_induction :
  (∀ env, (∀ env', μ env' < μ env → P env') → P env) → ∀ env, P env
```

(strong induction on the image, `generalize`d exactly like the existing
`acl2Count_strong_induction`, which becomes/remains the single-var
specialization used by the totality prover.) This single move subsumes the
survey's axes A1–A3 STRUCTURALLY:

- A1 multiple IHs per case = several instantiations of the ONE strong IH
  (FLATTEN: at env[X ↦ car xv] and env[X ↦ cdr xv]);
- A2 compound ruling tests = the case-entry branch facts (I5) from which
  each decrease proof draws, no hardwired consp/endp;
- A3 unmeasured substitutions and INTERLEAVE's swap = arbitrary env
  updates; only the measure decrease needs justification, and it is stated
  about μ of the WHOLE updated env.

Honest budget (review OUT-4): the env-level motive does NOT reduce
per-node proof complexity — the substN bridge relating
`EvTrue env' ⟪pushed⟫` to `EvTrue env ⟪substTerm σ pushed⟫` is RETAINED
machinery, reproduced per (case, IH). The motive's value is UNIFORMITY
(swaps, unmeasured updates, multi-IH), not fewer bridge steps. Likewise
the per-case k^m cross-product clausification is retained (review OUT-6):
every WP gate carries a proof-term-size prediction alongside the golden
prediction, and if the sorting corpus's larger clauses blow up, the k^m
product gets its own consolidation lemma BEFORE J5–J7 scale it.

### I3 — IH instantiation from the emitted substitution alist

Per case, per emitted IH alist σ: env' := env with each σ-bound variable
updated to the EVALUATED substituted term (values pinned by the existing
value layer). The IH instance is `P env'`, obtained from the strong IH via
the decrease obligation μ(env') < μ(env) (I4). Variables not in σ are
untouched (identity — matches ACL2's alist semantics). RIDE-ALONG pairs —
substitutions of variables OUTSIDE the measured subset, e.g. ZIP2's
`Y := (CDR Y)` and ordered-perms' `B := (RM (CAR A) B)` (review IN-2) —
are FREE env updates with NO obligation: μ reads only the measured
variables, so they cannot change it. The current scaffold's per-literal
cross-product clausification of (tests ∧ ⋀ᵢ(∨C)σᵢ) → (∨C) is unchanged —
it already handles m IHs symbolically; only the σ-shape restriction is
lifted.

### I4 — Decrease obligations: the join of two ALREADY-EMITTED artifacts
### (Q1 RESOLVED 2026-07-16)

Each (case, IH) pair owes `μ(σ env) < μ(env)` under the case's ruling
tests. VERIFIED on the real logs: these obligations are already emitted —
the scheme fn's defun event carries `:TERMINATION-CLAUSES` (user fns since
#37; ground-zero fns since WP0), and for 13-multi-measured-var they contain
EXACTLY the IH's decrease fact including the variable swap —
`((ATOM X) (O< (+ (acl2-count Y) (acl2-count (CDR X)))
              (+ (acl2-count X) (acl2-count Y))))`
— plus the `((O-P measure))` clause, which is precisely I1's
measure-well-formedness side obligation.

So the scaffold consumes: the defun's emitted termination clauses,
instantiated by the FULL formal→actual substitution read off the emitted
induction term — `sublis-var (pairlis$ formals (fargs term))`, exactly
ACL2's own flesh-out operation (review OUT-3), NOT a mere symbol swap.
The measured sub-part is a variable renaming precisely because ACL2's
sound-induction condition forces MEASURED actuals to be distinct
variables; the scaffold CITES that condition and HARD-FAILS if any
measured actual is a non-variable (never silently assumes). Matching is
per IH by the same covering-clause pattern the totality prover uses per
call site — with the covering obligation applying ONLY to the measured
subset's substitution (review IN-2): ride-along pairs are free (I3), so
a merged scheme's extra pairs or an ordered-perms-style custom-fn
ride-along do not hard-fail. An IH whose MEASURED substitution has no
covering emitted clause hard-fails. Discharge is by the admission-decrease
prover (Count library + the case's branch facts) — Q3, as QUALIFIED by
review IN-6: the 2026-06-11 carve-out covers VERDICT-CLASS emitted
decrease clauses; where a scheme fn's admission ran a REAL waterfall
(bsort's BNEXT-class custom decreases), the logged termination proof must
be replayed, not assumed verdict-class (the carve-out's own original
caveat, restated here).

No new fork work, no corpus recapture. Checked assumption C2 (Stage 2,
PARTIALLY verified): the MEASURED-subset substitution of every IH of every
target tree is covered by an emitted termination clause under the
substitution — verified for INTERLEAVE (swap clause) and refuted-as-
originally-stated for the ride-alongs (ZIP2's `Y := (CDR Y)`,
ordered-perms' `B := (RM (CAR A) B)` — hence the measured-subset-only
restatement above). J1 carries a per-tree verification of the restated C2
as its first deliverable.

### I5 — Case-entry facts from emitted ruling tests

Branch facts per case = each emitted test term's truthiness (step) or the
case-polarity assignment the induction machine recorded — consumed at the
VALUE level by the existing branch-fact machinery. Anything the decrease
proof needs about a measured variable (e.g. consp-ness inside
`(NOT (IF (ATOM X) (ATOM X) (ATOM Y)))`) is DERIVED from these values by
value lemmas — never pattern-matched from test syntax. Honest budget
(review IN-4): this derivation is a NEW compound-test-INVERSION lemma
family (invert a nested-IF test value to the component facts), explicitly
budgeted in J2 — not covered by existing machinery; inversion unavailable
⇒ hard-fail.

### I6 — Nested inductions: REVERT-TO-ORIGINAL-CONJECTURE semantics
### (REVISED TWICE: review IN-5's pool-composition diagnosis was itself
### REFUTED by the theory audit T1, verified on the emitter)

The truth, from the raw artifact + fork emitter: 15-nested's Subgoal 1
PUSH-CLAUSE carries NO `:POOLNAME` (log line 162; only lines 155/677 have
one), and the emitter (acl2/prove.lisp:2700-2703) omits `:POOLNAME`
exactly when the push signaled `abort` — ACL2's
REVERT-TO-ORIGINAL-CONJECTURE heuristic ("we prefer to prove the original
input conjecture… and reassign the name *1 to the original conjecture").
Pool entry (1) is therefore the ORIGINAL theorem's clause set — which is
why the emitted scheme clauses carry the whole original conjunction as
one if-shaped goal literal. IN-5's pool-of-two-clauses composition was
the WRONG mechanism (its observable — the embedded conjunction — was
real). The msort wall shares the signature (msort.proof-log:2554
`:POOL-CONSIDER :NAME (1)` preceded by a Goal'' push with no POOLNAME).

EMISSION GAP (fork work — the arc's one new emission item): the abort
cause is NOT emitted, and reconstructing revert from POOLNAME-ABSENCE
would be inference, which the fail-closed rule forbids. J5 therefore
starts with a small fork change — emit the push-clause abort cause (a
`:REVERT` marker naming what pool entry (1) becomes) — plus corpus
recapture; reconstruction then consumes the marker, hard-failing on an
un-annotated POOLNAME-less push.

I2's clause-LIST motive is RE-JUSTIFIED on the correct ground: ACL2 pool
entries hold clause SETS (`to-be-proved-by-induction` takes a cl-set),
and a reverted original conjecture clausifies to possibly several
clauses — the motive shape stands, the 15-nested-specific justification
is retracted.

### I7 — Reconstruction WPs (scope: IN this arc)

- **Pool linkage** (msort, ordered-perms): `no PUSH-CLAUSE with :POOLNAME
  [1] for the induction the pool considered there` — extend
  buildDevelopment's push→induct adjacency to the lineage shape those logs
  actually contain (grounding first: dump the msort pool/push events).
- **Equivalence source** (bsort): rewriting-equivalence node with no
  clause/segment hypothesis and no if-branch frame — classify the real
  node's source, extend the linker fail-closed.
- **Dotted-rune parse** (qsort; also gates sorts-equivalent = the D7
  consumer): parse `(:REWRITE name . k)` as a rune with an index field,
  thread through RuleSpec identity (display + matching), fail-closed on
  other dotted shapes.

Each is grounded-then-fixed as its own WP; none blocks the scaffold WPs.

## 3. Don't-bake-in table (REVISED per review IN-1/OUT-2/OUT-7 — honesty
## over optimism: rows now state their EVIDENCE class)

| Future need | Where it lands | Status/evidence |
|---|---|---|
| Lexicographic (`llist`) measures | new MeasureImage instance (o-p ordinals + its own WF theorem + strong-induction lemma) | REAL WP with real cost (OUT-5), interface-ready |
| Custom measures (`(NFIX n)`, world fns) | I1 eventual-value route + D6 totality | structurally general; BNEXT-class waterfall admissions replay their logged proof (IN-6) |
| >2 IHs, ride-along substitutions incl. custom-fn terms | I2/I3 (strong IH, free env updates) | verified against real logs (ZIP2, ordered-perms) |
| MERGED schemes (one theorem suggesting several candidates) | measured-subset-only covering (I4) tolerates the merge's extra pairs; but the merge is INVISIBLE in the emitted event (`:OTHER-TERMS` dropped) | UNVERIFIED — no merged scheme in the corpus; needs a constructed sample before reliance (OUT-7); a combined measure with no single-defun clause source would need fresh emission |
| Mutual-recursion schemes | N/A — ACL2 does not produce them (induct.lisp:1870 "we haven't implemented mutually recursive inductions yet"); that tail arrives only via `:induct` hints/induction rules | corrected claim (IN-1); nothing to design for until ACL2 changes |
| `:induct` hint schemes | join defined ONLY for distinct-variable measured actuals (hard-fail otherwise, I4); non-variable-actual hints are a DISTINCT FRONTIER | corrected claim (IN-2/OUT-3) |
| `do$`/loop$ inductions | EMISSION GAP — the hint-fn is never admitted, so NO `:TERMINATION-CLAUSES` exist; needs the applied-scheme measure conjecture emitted from `induction-formula` | scoped OUT of this arc with reason (OUT-2); none in corpus |
| encapsulate/functional instantiation | world-parametric scaffold (L3) | as before |

## 4. Invariant + fidelity compliance

- L1: the scaffold is fragment-local (its own lemma family behind the
  clause-replay judgment); MeasureImage is an interface, no monolithic
  inductive. L2: untouched (R unchanged); the MeasureImage interface is the
  same parameterization discipline. L3: world-parametric throughout (the
  measure evaluates under the ambient w; custom-measure fns enter via the
  world and D6 totality).
- Fidelity: everything consumed is emitted (cases, tests, substs, measure,
  measured subset; plus Q1's measure conjectures); decrease obligations
  are verdict-class (the ratified carve-out's class); hard-fail at every
  gap (an IH with no covering obligation, a non-natural measure value, an
  unmatchable scheme clause). No syntax-driven inference anywhere.

## 5. Alternatives considered

- **Per-shape scaffold tiers** (add a two-var tier, then a sum-measure
  tier, …): rejected — each tier is a new baked-in limitation and a fresh
  audit surface; the strong-IH-over-μ shape is not harder to prove once.
- **Measure grammar with interpretation table**: rejected for I1 evaluation
  (grammar = future breakage); the table survives only as decrease-LEMMA
  selection inside the prover, which is additive.
- **Induct directly on the controller value tuple** (not env): rejected —
  swaps (INTERLEAVE) and unmeasured updates make tuple bookkeeping a
  special-case farm; env-level updates are uniform.
- **Skip the reconstruction WPs** (scaffold only): rejected — 5 rows flip
  but the sorting corpus (the G6 driving target) stays fully blocked.

## 6. WP queue (sketch — sequencing after ratification)

| WP | Content | Unblocks (scoreboard) |
|---|---|---|
| J1 | HAND-PROOF SPIKES (§6b): (a) TRUE-LISTP-FLATTEN mirror by hand — validates env motive + substN bridge + multi-IH; (b) LEN-INTERLEAVE mirror by hand — validates μ registry + swap decrease + measured-subset covering. Real statements (gen-world), kernel-checked, axioms clean. ACCEPTANCE RULE (theory-audit T6): every spike step is ANNOTATED with the driver primitive that will produce it (an existing lemma constant or a named new one, from the driver's own set); a joint closed by an unannotatable tactic move is a STOP TRIGGER. Deliverables also include: the exact ZIP2 compound-test-inversion lemma STATEMENTS written (not proved) off the real tree (T4a), and the per-tree verification of restated C2. STOP TRIGGER: a shape that fights the hand proof is a design error — return to Stage 1, before any driver code | — (design validation) |
| J2 | Scaffold core: MeasureImage(Nat) + pool-shaped measure_strong_induction + μ registry (measured subset := free vars of the fleshed-out measure term, hard-fail unless ⊆ `:CONTROLLERS` — T3) + env-update layer + covering join (I4); REGRESSION GATE (restated per T2): every currently-GREEN induction row's golden line byte-identical; still-RED induction rows' NEW frontier messages predicted in advance as part of the golden diff (the old guard messages necessarily change). "Refactor-under-identity" = status-level identity + clean axioms, NOT proof-term equivalence (the env motive produces different terms by construction — tree-driven and kernel-checked is the claim) | — (proven base) |
| J3 | Generality rewire: cases/tests/substs consumption, multi-IH, compound-test-inversion lemmas (IN-4/T4a), one row at a time | TRUE-LISTP-FLATTEN; LEN-ZIP2; LEN-ZIP3 |
| J4 | Sum-measure decrease discharge (Count prover reuse) | LEN-INTERLEAVE |
| J5 | REVERT-semantics reconstruction (I6, corrected per T1): fork emits the push-clause abort cause (`:REVERT` marker) + recapture; reconstruction consumes it (POOLNAME-less push without a marker hard-fails — no absence-inference); covers 15-nested + the msort/ordered-perms signature (ordered-perms signature to be confirmed at grounding — T1 verified msort only) | NESTED-INDUCTION; msort, ordered-perms reach replay |
| J6 | Equivalence-source reconstruction | bsort reaches replay |
| J7 | Dotted-rune parse | qsort + sorts-equivalent parse (D7 consumer) |
| J8 | ARC-EXIT criterion (T5): one native lift through the existing decode kit (TRUE-LISTP-FLATTEN or LEN-INTERLEAVE class) — the owner's "obviously right Lean theorem" test, closed end-to-end | one new native theorem in Imported/ |

Gates per WP: golden diff predicted in advance AND a proof-term-size
prediction (OUT-6); `just ci` + diff-test; stop triggers as in the
external-knowledge brief (new representation duplicate / statement
weakening / missing emission / shortcut-green / unexplained golden change /
new MDD-decision shape → surface and stop).

## §6b. Validation strategy — creep up, never leap (self-review 2026-07-16)

This is fiddly work with the project's worst historical failure mode
(plausible pieces built in isolation that don't fit the real trees). The
sequencing above encodes the anti-failure structure explicitly:

1. **Hand proofs BEFORE driver code (J1).** The two spikes are real mirror
   theorems (real statements, real trees, kernel-checked) written by hand
   in the intended shapes — exactly how `my-len-my-app` validated the
   original scaffold before the driver existed. Each spike is a proof
   skeleton with one `sorry` per joint (motive, IH instantiation, bridge,
   decrease, case link), filled one at a time — so "the pieces fit" is
   established by construction on the REAL artifact, at the cost of two
   proofs instead of an arc. FLATTEN first (minimal generality increment:
   only multi-IH is new), INTERLEAVE second (the measure joints).
2. **Refactor-under-identity BEFORE generality (J2).** The generic
   scaffold's first driver milestone is replaying the ALREADY-GREEN
   induction rows through it, golden byte-identical — a pure-refactor gate
   on a known-good base. Generality then lands on a scaffold that is
   already proven equivalent where it overlaps the old one.
3. **One row per increment thereafter (J3–J4).** Each row's golden change
   is predicted before acceptance; a surprise is a stop trigger, not a
   shrug.
4. **Reconstruction WPs grounded separately (J5–J7).** Each starts with
   its own artifact dump (msort pool events; bsort's equivalence node;
   qsort's dotted runes) before any code — same Stage-0 discipline at WP
   scale.

## 7. MDD questions — ALL RESOLVED (2026-07-16)

- **Q1** (I4): RESOLVED by verification — the obligations are already
  emitted (defun `:TERMINATION-CLAUSES` + the induction event's term/
  alists); the scaffold joins two emitted artifacts deterministically.
  The user's emission preference is satisfied with zero new fork work.
- **Q2**: RATIFIED — the reconstruction WPs (J5–J7) are in-arc.
- **Q3**: RATIFIED — the 2026-06-11 admission-decrease carve-out covers
  scheme decrease discharge (same emitted clauses, same prover); recorded
  here, no separate decision entry. QUALIFIED per review IN-6: covers
  VERDICT-CLASS emitted clauses only; a scheme fn whose admission ran a
  real waterfall (bsort's BNEXT class) has its logged termination proof
  REPLAYED, never assumed — the original carve-out's own caveat.

## 8. Stage-2 adversarial review record (2026-07-16)

Two decorrelated Opus reviewers (inside: fidelity-to-sources; outside:
architecture), primary sources only. All findings adjudicated and
INCORPORATED above; the blocking ones each refuted a load-bearing claim
of the original draft:

- IN-1 (blocking): C1 was FALSE — ACL2 produces no mutual-recursion
  schemes (induct.lisp:1870), and merged schemes are invisible in the
  emitted event. §3 rewritten with per-row evidence classes.
- IN-2 (blocking): the per-IH covering-clause rule would have hard-failed
  real rows (ZIP2's `Y := (CDR Y)`, ordered-perms' `B := (RM (CAR A) B)`).
  I4 restated: covering obligation for the MEASURED subset only.
- OUT-1 (blocking): measure-by-evalOpt made μ partial where the WF motive
  needs total. I1 rewritten: defaulted classical eventual-value decode
  (total by construction) with per-use-site convergence obligations; pure
  acl2Count/+ fast path for all current rows.
- IN-5 (major): 15-nested re-diagnosed as pool COMPOSITION (two-clause
  pool), re-filed under J5; J4 deleted.
- IN-3 (major): O-P ≠ naturality — obligations separated in I1.
- OUT-2 (major): do$ inductions are an emission gap — scoped out with
  reason in §3.
- OUT-3 (major): the join is sublis-var of formals→actuals; measured
  actuals distinct-variable condition cited and enforced (hard-fail).
- IN-4, IN-6, OUT-4, OUT-5, OUT-6, OUT-7 (minor/major-qualifications):
  compound-test-inversion budgeted in J2; Q3 qualified; substN bridge and
  k^m cross-product budgeted honestly with proof-size predictions in
  every WP gate; MeasureImage carries per-instance WF proofs; merged
  schemes need a constructed sample before reliance.

Reviewer could-not-verify items carried into J1's verification
deliverable: the restated C2 per tree; the msort/bsort/qsort wall
characterizations against the linker code; BNEXT's admission record
class.

## 9. Self-review record (2026-07-16, full-plan coherence pass)

A complete joint-by-joint walk-through (motive → IH instantiation →
substN bridge → decrease → discharge → case children → pool shape) after
the Stage-2 incorporation, prompted by the volume of blocking findings.
Two corrections came out of it, both incorporated above:

- **The first OUT-1 fix was itself wrong.** The defaulted eventual-value
  μ would have required object-vs-meta agreement theorems (world
  `ACL2-COUNT` vs `SExpr.acl2Count`) with zero consumers, and put a
  reachable default adjacent to a WF argument. Superseded by the
  meta-level head REGISTRY (I1), legitimized by the observation that the
  measure appears in NO statement — interpretation is proof bookkeeping,
  not fidelity surface.
- **J5 changed what J1 consumes.** Pool composition means the induction
  input is a clause LIST; the motive is pool-shaped from day one (I2),
  singleton as the degenerate case.

Joints verified as fitting: the env motive is the current per-value
motive's generalization (P v = P_env(env.insert X v)); the N-formal
simultaneous substitution lemma (EvalLemmas:1360) already exists for the
bridge; ride-along env'-values come from existing totality pins and
cannot perturb μ (measured-subset reads only); the discharge reuses the
totality prover's ratified emitted-clause-as-coverage-guide pattern;
nesting recursion is already structural. Validation strategy in §6b.

## 10. Theory-audit record (2026-07-16, single specialist reviewer)

One theory-specialist reviewer (owner-requested), adversarial brief over
the mathematics AND the by-example strategy, all findings verified
against primary sources. Incorporated above:

- **T1 (major)**: IN-5's pool-composition diagnosis of 15-nested was
  REFUTED against the emitter — the mechanism is ACL2's
  revert-to-original-conjecture abort (POOLNAME omitted exactly on
  `signal = 'abort`, prove.lisp:2700-2703; independently spot-verified).
  I6/J5 rewritten around revert semantics + the abort-cause EMISSION WP
  (the arc's one new fork item); I2's motive shape re-justified on pool
  clause-SET semantics. Lesson recorded: a verifier can confirm an
  observable while the claimed MECHANISM is wrong — mechanism claims
  need emitter/source-level verification.
- **T2 (major)**: J2's golden gate restated — byte-identity for GREEN
  induction rows; predicted new frontier messages for red rows (the old
  guard strings necessarily change); refactor-under-identity is
  status+axioms, not proof-term equivalence.
- **T3**: measured subset DEFINED as free vars of the fleshed-out
  measure term, hard-fail unless ⊆ `:CONTROLLERS`.
- **T4**: ZIP2 inversion lemma STATEMENTS written at J1; k^m
  cross-product and non-singleton pool acknowledged as spike residuals
  under the J3/J5 one-row gates.
- **T5**: J8 arc-exit native lift added — the "obviously right" test
  closed end-to-end (verified: no statement-side gap; driver_mirror%
  states mirrors from the tree alone, decode kit covers the class).
- **T6**: J1 acceptance rule — driver-primitive annotation per spike
  step; unannotatable tactic move = stop trigger (the hand-vs-driver
  gap made a gate, not a hope).

Held under attack (auditor-verified): the strong-IH-over-μ core; the
substN bridge is genuinely SIMULTANEOUS substitution (args valued in the
original env — INTERLEAVE's swap exactly covered, matching sublis-var);
∀-env mirror × per-env μ interact benignly; the conjoined-pool motive
matches ACL2's induction-formula semantics; I4's Q1 verification
genuine; I1's measure-in-no-statement trust observation correct;
Count.lean already carries the spike decrease lemmas; FLATTEN +
INTERLEAVE are the right first two spikes.
