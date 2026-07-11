# External-knowledge discharge — design (PROPOSAL for MDD review)

*2026-07-10, branch `mdd/external-knowledge`. Supersedes the roadmap's R2(c)
paragraph (see its 2026-07-10 addendum); problem statement + measured evidence
in `docs/notes/2026-07-10_external-knowledge-assessment.md`. Nothing here is
ratified except D5's justification policy (species-2 = prove-in-Lean-about-
the-primitive, MDD-ratified 2026-07-10 in discussion).*

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
- The builtin/ground-zero-defun OVERLAP set: `LEN`, `NFIX`, `BOOLEANP`
  (+ `ENDP`, `ATOM`) are `callBuiltin` entries AND ACL2 defuns; `SYMBOLP` is
  a genuine primitive; `TRUE-LISTP` is neither (pure gap).
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
symbol — user fn names make `callBuiltin` fall through to `none` uniformly
(provable per name). Fuel shape is preserved (the lemma is per-fuel, so
`∃N∀f≥N` transfers directly). Hypotheses (`total:`/`tp:` — also
convergence-shaped) stay stated over their HOME world; no backward transfer
exists or is needed (D7).

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
`callBuiltin` builtin (`LEN`, `NFIX`, `BOOLEANP`, `ENDP`, `ATOM`, …) must
NOT enter the world — it would shadow the builtin, break the no-shadow
facts, and violate `hnew`. Those go the D4 route. The no-shadow CI gate
enforces the boundary.

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
`callBuiltin` only), entering `dischargeRuleHyp` through the same registry
interface as D1 constants, followed by the existing formula→stored-rule
recompute-and-check. The STATEMENT + rune identity + normalized rule form
(incl. rule-class flags — `lexorder-transitive` is `(:rewrite :match-free
:all)`) come from a ground-zero RULE SNAPSHOT emitted at capture start,
read off ACL2's world; the Lean lemma discharges an obligation whose
statement is the emitted artifact (fail-closed on mismatch).

Scope note: of the four ground-zero lexorder theorems, anti-symmetric and
total are :FORWARD-CHAINING — they surface inside DP leaves where the
ratified carve-out already governs discharge; the rewrite-side prelude at
isort is exactly reflexive + transitive (both half-drafted as Lexorder.lean's
commented-out order proofs).

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
4. **Recompute-and-check**: the existing dischargeRuleHyp normalization
   bridge (formula → stored rule), with the stored-rule datum taken from
   **B's own log's `(:RULES)` entry** (captured at B's certification).
5. **Obligations compose book-tagged**: B's residual base facts (e.g.
   `total:perm`, `tp:memb`) remain stated over `w_B` in the composed
   telescope; the obligation log gains (book, fact) keys and the H2d
   dashboard reports them per book. They are discharged once, at B, and
   shared by every consumer — obligations do not multiply with fan-out.

### D8 — Prerequisite fork fix: the rule flush (audit finding C)

A book's LAST theorem's `(:RULES)` entry never flushes into its own log —
harmless for single-log replay, load-bearing the moment D7 step 4 reads
stored rules from source-book logs. Fix in the fork (flush at
end-of-certification), tag per the TRACE-LOG discipline, recapture corpus.

## 4. Scalability analysis (why this shape)

- Inlining: proof size ≈ Σ over the dependency TREE (re-elaborated per
  consumer, per theorem) — exponential in depth in the worst case; already
  ≈557M nodes at same-book depth 2.
- Registry: proof size per theorem ≈ own replay + O(1) constant references
  + one transfer application per cited book. Kernel work is Σ over
  theorems, each ONCE — linear in corpus size. This is how Mathlib scales,
  and it is the compositionality MDD asked for.
- The side-condition `decide`s are per book PAIR, not per theorem — cache
  the `w_B ⊆ w_C` fact as a constant too.

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
| WP0 | D8 fork flush fix + ground-zero defun/rule snapshot emission (D3/D5 statements) + recapture | — (enabler) |
| WP1 | D3 world entry for snapshot defuns + retire `groundZeroDefs`; D6 totality on recomputed clauses | TRUE-LISTP-ISORT, APP-NIL ×2, TRUE-LISTP-REV, REV-REV advance/replay |
| WP2 | D4 definition facts for LEN/NFIX (+BOOLEANP/ENDP/ATOM as cited) | CD2-BOUND, LEN-REV-ACC advance |
| WP3 | D5 prelude constants: lexorder-reflexive/-transitive (restore Lexorder.lean order proofs, mirror-shaped) | ORDEREDP-ISORT advances past both |
| WP4 | D1 registry + rewire dischargeRuleHyp (same-book first — perm book as regression, measure proof-size collapse) | scale headroom; golden byte-identical gate |
| WP5 | D2 `evalOpt_world_mono` + D7 assembly (isort ← its 3 includes) | ORDEREDP/HOW-MANY-ISORT rule hyps discharge; R3 opens |
| WP6 | HOW-MANY-ISORT clausify-spine residual at *1/3'4' (independent investigation) | HOW-MANY-ISORT |

Gates per WP: `just ci` green, golden updated only with expected-row
justification, axioms clean, differential green; audit before the
R2-complete claim.

## 8. Open questions for MDD (beyond the ratified D5 policy)

1. D3 snapshot scope: cited-closure (proposed) vs a fixed curated set —
   cited-closure is fail-closed and corpus-driven; confirm.
2. D4 fn list growth policy: add per cited fn (proposed), each with its
   consistency lemma + differential entries per H3.
3. D7 step 5 obligation surfacing: book-tagged home-world facts (proposed)
   vs transferring obligations to `w_C` (more uniform-looking telescopes,
   but requires the reverse transfer direction, which is false in general).
4. WP4 ordering: registry BEFORE cross-book (proposed — de-risks the scale
   question on a book that already replays) vs after.
