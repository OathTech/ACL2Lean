# Triage: proof producer vs the REAL reconstructed proof tree

Created: 2026-06-05

## Why this exists
We built/validated the producer's node handlers against **synthetic, hand-authored
`ProofNode`s** (bare-variable shapes) and never ran them against the **reconstructed
proof tree** (`buildAllTheoremProofs`) of an actual ACL2 log. That gave false
confidence. This triages how much survives, measured against the real tree for
`my-len-my-app` (`lake exe acl2lean dump-proof-tree acl2_samples/simple.proof-log`).

(An earlier pass mistakenly read the FLAT ACL2 log; the producer consumes the
reconstructed TREE. `if-simplification`/`recognizer` steps are CHILDREN of
`definition` nodes there — not standalone — which matches the definition handler.)

## UPDATE (2026-06-05, after actually running it + cleanup)

The per-node predictions below were made from analysis, BEFORE running the
producer on the real tree. We then built `Tests/ProofProducerRealLog.lean` and
ran it. **Measured result: 0 of 10 top-level nodes discharged — every handler
fails on real data.** This is harsher than the analysis below predicted (which
guessed `equal-self` "works" and base-case nodes are "handler-ready"). On the
real tree even those fail: base-case `definition`/`recognizer` hard-fail because
there is no per-case context driver (`consp x = nil` fact, var bindings), the
simp side-conditions don't discharge for the real world/symbols, and the
step-case `equal-self` arg `(binary-+ …)` is an unsupported converger shape. So
the analysis's "what survives" was over-optimistic: the mechanisms are reusable,
but **nothing actually replays a real node yet.**

Hand proof (`SimpleWorld.my_len_my_app`): its BASE case faithfully mirrored the
tree's 4 nodes, but its STEP case did NOT — it computed values to integers and
equated them with native `Int` arithmetic instead of replaying the tree's
`commutativity-of-+`/`commutativity-2-of-+`/`rewriting-equivalence`/recursive-
definition nodes. As a replay blueprint the step case was garbage. **Deleted**
`my_len_my_app_generic` + `my_len_my_app` (and dead helpers); kept only the
standalone totality lemmas `my_len_total`/`my_app_total`.

Also deleted: all synthetic hand-built `ProofNode` tests (`ProofProducerTest.lean`)
— pure false confidence. `Tests/ProofProducerRealLog.lean` (the real-tree run) is
now the single source of truth. The producer handlers are tagged
BROKEN-ON-REAL-DATA in `ProofProducer.lean` (kept as reusable, not trusted).

The analysis below is retained as a record of what we PREDICTED vs the 0/10
reality; trust the harness, not the predictions.

## The real tree (shape the producer must walk)
- `my-len-my-app`: **induction on `(my-app x y)`, 2 subgoals**, with a scheme. The
  producer must build this (proveTheoremProof) — NOT built.
- Base case `*1/2` (clause `[(consp x), (equal …)]`): the proved literal has a chain
  of **4 top-level nodes**.
- Step case `*1/1` (clause `[(not (consp x)), IH, (equal …)]`): one literal is a
  single `commutativity-of-+` node; the main literal is a chain of **5 top-level
  nodes**; the IH literal uses `rewriting-equivalence`.
- Nodes nest: `definition` nodes carry `recognizer` (the test) + `if-simplification`
  (the branch) children; arithmetic `rewrite` nodes carry the type-reasoning
  (`definition:fix` → `acl2-numberp` recognizer, `type-prescription` runes) as
  children. **The tree itself directs where type facts come from.**

## Per-node status (walking the real tree)
Base `*1/2`, literal `(equal (my-len (my-app x y)) (binary-+ (my-len x) (my-len y)))`:
| node | shape | status | gap |
|---|---|---|---|
| `definition:my-app` | `(my-app x y) ⇒ y` (2-arg, non-rec, var args) | handler-ready* | needs case-context (bind x,y; consp-x=nil fact) |
| `definition:my-len` | `(my-len x) ⇒ '0` (1-arg, non-rec, var) | handler-ready* | needs case-context |
| `rewrite:unicity-of-0` | `(binary-+ '0 (my-len y)) ⇒ (my-len y)` | MISSING | arithmetic rule + integer-typed convergence of `(my-len y)` |
| `equal-self` | `(equal (my-len y)(my-len y)) ⇒ 't` | **WORKS** | (validated — existential converger) |

Step `*1/1`:
| node | shape | status | gap |
|---|---|---|---|
| `commutativity-of-+` | args `(my-len (cdr x))`,`(my-len y)` | MISSING | arithmetic + builtin/rec-call convergence + int typing |
| `definition:my-app` (recursive) | `⇒ (cons (car x) (my-app (cdr x) y))` | FAILS | recursive RHS → handler hard-fails (frontier); needs totality/IH |
| `definition:my-len` (recursive) | arg `(cons (car x)(my-app …))`, child `cdr-cons` | FAILS | rec RHS + arg is cons-of-calls |
| `definition:my-len` (recursive) | `(my-len x) ⇒ (binary-+ '1 (my-len (cdr x)))` | FAILS | recursive RHS |
| `commutativity-of-+` → `commutativity-2-of-+` → `rewriting-equivalence` | the IH application | MISSING | arithmetic rules + **IH (rewriting-equivalence)** |
| `equal-self` | arg is `(binary-+ '1 …)` | FAILS | converger has no `binary-+` case |

\* "handler-ready" = the handler's logic fits the shape, but it cannot run until the
case-context driver supplies `ctx.vars`/`ctx.facts`.

Net: of the real per-node obligations, **1 is validated working** (`equal-self`),
~2 are handler-ready pending the case driver, and the rest need new capability. And
**0 full cases run** until `proveTheoremProof` exists.

## What SURVIVES (saved — reuse intact)
- Entire lemma library (`EvalLemmas`), reflection, side-condition provers, fuel infra,
  `liftCongr` + existential chain composition (`proveLiteralChain`),
  `addTheoremFromChain`, the node-proof type. (~the majority of the producer.)
- `synthTotality1` (1-arg structural totality).
- The fixed-fuel `proveConverges` base-case engine + `liftConvergeToExist` + the
  existential converger SKELETON.
- `equal-self` handler — runs on a real node shape.
- **The traversal architecture + handler designs** — the real tree's node nesting
  (definition → recognizer/if-simp children) matches what we built. Not wasted.
- The 3 cleanup refactors (orthogonal).

## What needs REWORK (sound design, wrong fuel assumption)
- Arg convergence inside `recognizer`/`definition`/`rewrite` handlers: fixed-fuel →
  existential, because real args are pervasively builtin/recursive calls. The
  dispatch/parse/shape-match/skeletons survive; the literal-fuel proof plumbing
  (`mkGeProof` bumping, literal-cons value extraction) is the part replaced.
- `definition` handler: add the recursive-RHS path (currently a hard-fail frontier).

## What was NEVER BUILT (always the frontier — not "wasted", just todo)
- `proveTheoremProof`/`proveCaseProof`: induction from the scheme + per-case context
  (bind vars, derive recognizer facts from the clause). **Required for any full case.**
- Converger coverage: builtin 1-arg calls (`car`/`cdr`/`fix`), 2-arg calls, `binary-+`.
- `synthTotality2` (2-arg, for `my-app`).
- Arithmetic rewrite rules + integer-typed convergence (tree-directed via the
  `type-prescription`/`acl2-numberp` children — see
  `project_instrumentation_lever_type_facts`).
- `rewriting-equivalence` (the induction hypothesis application).

## Bottom line
- **~Nothing is delete-garbage.** No code gets thrown away; the real tree validates
  the traversal model and handler designs.
- **Salvageable:** all infrastructure + `synthTotality1` + `equal-self` + the handler
  skeletons/designs.
- **Reworked (bounded):** the fixed-fuel arg-convergence plumbing inside 3 handlers.
- **The real miss was process, not code:** we unit-tested handlers on synthetic nodes
  and never ran the reconstructed tree, so we didn't see that (a) no full case can run
  without the induction/case driver, and (b) handlers need existential convergence for
  the call-args that are everywhere in real nodes.

## Path forward
Wire `ProofLog.parse → buildAllTheoremProofs → proveTheoremProof` over
`simple.proof-log` now. It fails immediately (at the induction/case driver, then at the
first call-arg convergence). From then on we develop against the real tree, pushing the
failure deeper as we add: case driver → converger coverage + 2-arg totality →
arithmetic rules + int typing → IH. See `feedback_work_against_real_proof_log`.
