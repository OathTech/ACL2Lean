# External-knowledge assessment — what actually blocks isort and the many-books goal

Date: 2026-07-10. Post-merge assessment (reader/lexorder arc merged at 172c8ec;
scoreboard 26/50, perm 8/8 replayed + lifted). Purpose: pin, from the real
artifacts, what the next architecture item is — and correct the roadmap's
R2(c) framing before writing its design doc. This note is the problem
statement the design doc should cite; it makes no design decisions.

## The finding: "cross-book rule discharge" is the wrong name for the wall

The roadmap (2026-07-06_long-term-roadmap.md, R2(c)) frames the remaining R2
architecture item as discharging `rule:<included-thm>` hypotheses across book
boundaries. Probing the real isort log shows the binding constraint is
broader: **the world and rule-base a book's proofs lean on extend beyond that
book's log** — in FOUR distinct species, only one of which is cross-book.

Measured evidence (all from `acl2_samples/sorting/isort.proof-log` and the
coverage scoreboard, 2026-07-10):

| # | Species | Evidence | Blocks |
|---|---------|----------|--------|
| 1 | **Ground-zero built-in DEFUNS** (axioms.lisp logic-mode defuns, in every session's world) | `deriveDefInfoN: TRUE-LISTP not defined in the world`; same for `NFIX`, `LEN` | TRUE-LISTP-ISORT **+ 6 recon rows**: APP-NIL (01 + 02), TRUE-LISTP-REV, REV-REV, CD2-BOUND, LEN-REV-ACC |
| 2 | **Ground-zero built-in RULES** (theorems in axioms.lisp — `lexorder-reflexive` :27154, `lexorder-transitive` :27162) | cited **60× / 43×** in isort.proof-log; NO book's log can carry a `(:RULES)` entry for them (created at ACL2 boot, not during any certification) | ORDEREDP-ISORT (`rule LEXORDER-TRANSITIVE: no stored-rule hypothesis in scope`) |
| 3 | **Included-defun TOTALITY** (roadmap R2b) | included defuns re-emit with `:INCLUDED T`, justification but no clauses; `total:<included-fn>` hyps D6-kept | unconditional composition of every including book |
| 4 | **Included-book RULES** (R2c proper) | `NOT-MEMB-IMPLIES-HOW-MANY-IS-0` cited 17×, `HOW-MANY-RM` 4× (both from convert-perm-to-how-many, arriving as `.includedTheorem` events) | ORDEREDP/HOW-MANY-ISORT once #2 clears; then all of R3–R7 |

The correction that matters: `LEXORDER-TRANSITIVE` — the wall ORDEREDP-ISORT
actually reports — is species #2, NOT #4. A design doc scoped to "discharge
included-book rules from the included book's replayed mirror" would not have
fixed it: there is no source book whose replay could supply the rule. Every
real ACL2 book sits atop ground-zero + includes, so all four species are on
the many-books critical path.

The only isort wall OUTSIDE this family: HOW-MANY-ISORT's clausify-spine
residual at Subgoal *1/3'4' (`no child clause matches the residual`) — a
replay-mechanics frontier of unknown size; investigate on the real tree,
independently of the design work.

## Consequence for sequencing (assessment of 2026-07-10, MDD-agreed direction)

1. **One design doc covering all four species** ("external-knowledge
   discharge"), not an R2(c)-only doc. Decisions it must make:
   - Species 1: ground-zero defuns — emit from ACL2's world at capture vs pin
     as `groundZeroDefs` (precedent: `fix`) with differential coverage per the
     H3 trusted-core policy.
   - Species 2: ground-zero rules — their statements are fixed axioms.lisp
     theorems; candidate shape: replay each ONCE from its own captured log and
     reuse everywhere (they are ordinary defthms with ordinary proofs at boot).
     How they enter the telescope / stored-rule channel is the design question.
   - Species 3: R2(b) termination-machine recomputation emission — ratify (it
     is the totality face of the same problem).
   - Species 4: the genuine cross-book shape — (i) world-parametric mirror
     statements with def-hypotheses (Imported/ prefers this; L3 designed for
     it) vs (ii) world-extension transfer (`w ⊑ w' → mirror w → mirror w'`).
   Designing #4 without #1/#2 in view risks a mechanism the built-in species
   doesn't fit.
2. **Implementation in leverage order** once ratified: #1 (cheapest, ~7 rows),
   #2 (validates rule-discharge shape on the simplest case, no book
   composition needed), then #3/#4 (validated by isort ← perm /
   convert-perm-to-how-many).
3. **R3** (convert-perm-to-how-many + ordered-perms, 19 theorems) is the
   at-scale validation. NOTE: ordered-perms wraps its lemmas in `encapsulate`
   with `local` defthms — a slice of R6's problem arrives early; the design
   doc should spend a paragraph on whether `.includedTheorem` import already
   suffices for its exports.
4. **Just-in-time industrialization (H2)** follows the spine: the
   decode-theorem generator's trigger ("two books exercising the schema") is
   met at isort; the exec-corr elab command is needed before R4.

## Representation impact — does the proof tree change? (assessed 2026-07-10)

**The per-theorem clause tree (ClauseProof/ClauseNode/ProofNode) needs NO
change, and nothing new is "inserted into the tree."** External rules already
appear in trees exactly as ACL2 itself uses them: a rune application inside a
literal chain, with `:SUBST` and hyp-relief records. ACL2's waterfall does not
inline a cited rule's proof either — it consults the stored rule — so the tree
as reconstructed IS the complete record of this theorem's reasoning. External
facts enter the **scope the tree is replayed in** (the telescope), not the
tree. The telescope/obligation-log model (`total:`/`tp:`/`rule:` hypotheses)
was designed as exactly this insertion point, so the two-phase decomposition
(reconstruct, then replay) survives intact.

**What DOES change is one level up — the Development layer:**
- Today a Development is the right-nested event sequence of ONE log, and
  `dischargeRuleHyp` (Driver.lean:6141) looks up the dependency's proof tree
  in the SAME Development (`depProofs`), replaying it inside the consumer's
  telescope. `WorldEvent.includedTheorem` (ClauseTree.lean:95) carries
  statement + stored rules (via `.rules`) but NO proof tree — discharge
  fail-closes there today, correctly.
- Species 4 makes Developments a DAG: the proof of an included rule lives in
  the SOURCE book's Development. Discharge must consult a cross-Development
  registry of replayed mirrors keyed by (book, theorem) instead of same-log
  `depProofs`. `includedTheorem` likely gains its source-book identity.
- Species 1/2 add a PRELUDE scope (ground-zero world entries + stored rules)
  below every Development — a provenance tag on events, not a new node kind.

**Rough edges the corrected understanding exposes (design-doc must address):**
1. **Discharge is currently INLINING** — the dependency is re-replayed inside
   each consumer's telescope. Proof terms already balloon along same-book
   dependency chains (perm-is-an-equivalence ≈557M Expr nodes, known scale
   note). Cross-book inlining would multiply this; a proved-once-per-book
   registry of mirror CONSTANTS is probably forced — which couples this to
   the (i) world-parametric vs (ii) world-extension-transfer choice, because
   a stored constant is stated over the SOURCE book's world.
2. **The normalization recompute-and-check crosses the boundary.**
   dischargeRuleHyp validates the stored rule against the dependency's
   formula from the same log (Driver.lean:6155). Cross-book, the formula
   comes from the includedTheorem re-emission and the proof from the source
   log — statement identity between the two must be validated explicitly
   (as included-defun identity already is).
3. **Ground-zero rules have NO capture path at all today** — `(:RULES)` is
   emitted at create-rewrite-rule during certification; boot-world rules
   never pass through it. A new emission surface is needed for the
   STATEMENTS (ground-zero rule snapshot at capture start — rune identity +
   normalized lhs/rhs/hyps/equiv/rule-class flags read off ACL2's world, not
   hand-transcribed).
   **Justification question, sharpened (2026-07-10, MDD discussion).** The
   standard ACL2 build ADMITS axioms.lisp theorems WITHOUT PROOF: pass 2
   runs with `ld-skip-proofsp = 'include-book` (interface-raw.lisp:9638,
   `initialize-acl2`); proving them is the separate maintainer `make proofs`
   (proveall) target. So in ANY image we capture from — including our
   instrumented one — there is no ACL2 proof record for these rules to
   replay. (They are NOT metatheorems — ordinary first-order theorems ACL2
   can and does prove in proveall runs, with :hints in the source — the
   evidence just isn't in the artifact.) Candidate justifications:
   (a) **Prove once in Lean about the trusted-core primitive.** The mirror's
       meaning is DEFINED by Logic/evalOpt, so a kernel-checked proof of
       `Logic.lexorder` transitivity is a fact about the very function that
       gives every mirror statement its meaning. This adds ZERO new trust
       assumption: the only fidelity premise — Logic.lexorder = ACL2's
       lexorder extensionally — was already assumed when lexorder entered
       callBuiltin, and is policed by the differential corpus (34 pinned
       entries + audit). Epistemically STRONGER than what ACL2's own image
       has at boot. Precedent: the #37 TP-prover ratification (consuming the
       emitted fact and constructing a proof object ACL2 never had is NOT
       the banned inference). Lexorder.lean's commented-out order-property
       proofs are literally these statements.
   (b) **Instrumented proveall capture** — run `make proofs` under the fork
       and replay the recorded boot proofs like any theorem. Faithful to a
       proof ACL2 *can* produce, but heavier, and the artifact replayed is
       one no distributed ACL2 image actually relies on.
   Either way the STATEMENT comes from the emitted snapshot (fail-closed
   recompute-and-check against it). MDD call for the design doc; (a) is the
   recommended default.
   **Rule-class detail that shapes the design:** of the four ground-zero
   lexorder theorems (axioms.lisp:27154–27172), reflexive is a plain
   :rewrite, transitive is `(:rewrite :match-free :all)` (free-var hyp
   relief!), while anti-symmetric and total are :FORWARD-CHAINING rules —
   the latter feed type-set/fc, i.e. surface inside DP LEAVES where the
   ratified carve-out already governs discharge (with emitted type facts as
   hypotheses). So species 2's rewrite-side scope may be just
   reflexive+transitive; `(in-theory (disable lexorder))` at :27178 explains
   why proofs cite the properties rather than unfolding.
4. **Audit finding C becomes load-bearing**: a book's LAST theorem's rule
   never flushes into the log — harmless for single-log replay, but a real
   gap once includes import stored rules.
5. **Fuel across worlds**: mirror statements are `∃N ∀f≥N …`; composing a
   source-world mirror into a consumer-world proof needs the fuel/world
   monotonicity story stated once as part of the transfer design.

## Corpus assessment (toward "many target books")

- The sorting corpus remains the right spine (includes, user equivalences,
  forcing at qsort, encapsulate at equisort, functional instantiation at the
  end — in dependency order).
- **Free breadth in the same directory**, not in the roadmap table:
  sorts-equivalent2/3, equisort2/3, term-ordered-perms,
  merge-sort-term-order, no-dups-qsort (~32 more theorems). Should replay
  nearly for free once R2–R7 machinery lands — a cheap de-overfit check
  before any second corpus.
- **The honest gap to most community books is guards/`verify-guards`**
  (roadmap H4c). Corpus-driven rule holds — build it only with a driving
  consumer — but when the SECOND corpus is picked (H4b), pick a
  guard-verified book so the probe measures the real gap rather than
  re-measuring list processing.
- Explicitly NOT now: drilling recon-test induction walls (len-zip2/3,
  len-interleave — R4's msort/bsort force them naturally), the live tactic
  (after R4), differential expansion beyond trusted-core growth moments.
