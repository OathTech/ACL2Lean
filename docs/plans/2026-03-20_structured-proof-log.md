# Structured Proof Log: Extracting Machine-Readable Proof Data from ACL2

Created: 2026-03-20
Updated: 2026-03-20 — discovered existing `set-raw-proof-format` and
`get-event-data` mechanisms

## Problem

When ACL2 proves a theorem, it knows *exactly* what it did at each step:
which rules it applied, which processor acted, what the clause looked like
before and after, what induction scheme it chose. All of this is available
internally as structured data (tag-trees, clause-ids, rune lists).

We need per-subgoal structured proof data to generate Lean proof
certificates.

## Existing Mechanisms (Already Built Into ACL2)

### 1. `set-raw-proof-format` — per-subgoal structured rune lists

**This is the key discovery.** With `(set-raw-proof-format :clause)` and
`(set-gag-mode nil)`, ACL2 already outputs per-subgoal data in a mostly
structured form:

- Clauses in internal disjunctive form (list of literals, not IMPLIES)
- Per-step rune lists as parseable s-expressions (not English!)
- Which processor acted (simplification, preprocess, elimination, etc.)
- Induction schemes

Example output with `(set-raw-proof-format :clause)`:

```
Subgoal *1/1
((NOT (CONSP X))
 (NOT (EQUAL (MY-REV (MY-APP (CDR X) Y))
             (MY-APP (MY-REV Y) (MY-REV (CDR X)))))
 (EQUAL (MY-REV (MY-APP X Y))
        (MY-APP (MY-REV Y) (MY-REV X)))).

This simplifies, using primitive type reasoning and the list of runes,

 ((:DEFINITION MY-APP)
  (:DEFINITION MY-REV)
  (:REWRITE CAR-CONS)
  (:REWRITE CDR-CONS)),

to

Subgoal *1/1'
((NOT (CONSP X))
 ...new clause...).
```

Compared to default output for the same step:
```
But simplification reduces this to T, using the :definition MY-APP,
primitive type reasoning and the :rewrite rules CAR-CONS and CDR-CONS.
```

The rune list goes from English to a proper s-expression. The clause goes
from `(IMPLIES hyps concl)` to internal clausal (disjunctive) form. Both
are directly parseable.

**Enabling it:**
```lisp
(set-gag-mode nil)              ; verbose output (show all subgoals)
(set-raw-proof-format :clause)  ; structured runes + clausal goals
(set-inhibit-output-lst '(proof-tree))  ; suppress proof-tree noise
```

### 2. `get-event-data` / `last-event-data` — post-event structured summary

After each event, ACL2 stores structured data accessible via
`(@ last-event-data)`. This is an alist with keys:

| Key | Value |
|-----|-------|
| `RULES` | Global rune list (same as Summary block) |
| `HINT-EVENTS` | Hints that fired |
| `PROVER-STEPS-COUNTED` | Step count |
| `SPLITTER-RULES` | `(case-split immed-forced if-intro)` |
| `TIME` | `(prove print proof-tree other)` |
| `EVENT` | The full event form |
| `FORM` | `(event-type . name)` |
| `ABORT-CAUSES` | List of abort reasons (nil on success) |

Example:
```lisp
ACL2 !>(@ last-event-data)
((RULES (:DEFINITION MY-APP) (:INDUCTION MY-APP)
        (:REWRITE APP-ASSOC) (:REWRITE CAR-CONS) ...)
 (PROVER-STEPS-COUNTED . 1643)
 (EVENT DEFTHM REV-APP (EQUAL (MY-REV (MY-APP X Y)) ...))
 ...)
```

### 3. `saving-event-data` / `certify-book :event-data t` — file output

During `certify-book`, passing `:event-data t` writes a
`BOOK@event-data.lsp` sidecar file containing `(name . alist)` entries
for every defthm/defun/verify-guards event. This gives the global rule
list per theorem in a file we can parse.

### What each channel provides (updated)

| Channel | Per-subgoal? | Per-step runes? | Formulas? | Structured? |
|---------|-------------|-----------------|-----------|-------------|
| Default prose | Yes | English only | Yes (IMPLIES form) | No |
| **raw-proof-format :clause** | **Yes** | **S-expr lists** | **Yes (clausal)** | **Mostly** |
| Summary / event-data | No (global) | Yes | No | Yes |
| Proof tree | Yes (goal tree) | No | No | Semi |
| `@event-data.lsp` file | No (global) | Yes | No | Yes |

## What's Still Missing (Gaps to Fill)

Even with `set-raw-proof-format :clause`, the output is *mostly* but not
*fully* structured. The remaining prose includes:

1. **Induction scheme selection** — "We will induct according to a scheme
   suggested by (MY-APP A B)" is still English, though the scheme itself
   is printed as an s-expression
2. **Processor identification** — "simplification reduces this to T" vs
   "preprocess reduces the conjecture to T" vs "destructor elimination"
   is prose, not a keyword
3. **Cross-fertilization** — "We now use the hypothesis by substituting X
   for Y" is English
4. **Generalization** — "We generalize this conjecture, replacing (FOO X)
   by V" is English
5. **Elimination details** — "The destructor terms (CAR X) and (CDR X) can
   be eliminated by using CAR-CDR-ELIM" is English (though the elim-sequence
   is in the ttree)

The rune lists and clauses are structured; the glue between them isn't.

### What the rewriter hides

**Critical concern:** a single ACL2 "simplification" step is not a single
rewrite — it's a fixpoint computation. `accumulated-persistence` reveals
what happens inside a single simp step on `rev-app`:

```
(:TYPE-PRESCRIPTION MY-APP)   — 388 tries
(:TYPE-PRESCRIPTION MY-REV)   — 366 tries
(:DEFINITION MY-REV)          — 35 tries (all useful)
(:DEFINITION MY-APP)          — 64 tries (all useful)
(:REWRITE DEFAULT-CDR)        — 116 tries (mostly backchaining failures)
(:REWRITE DEFAULT-CAR)        — 113 tries (mostly backchaining failures)
(:REWRITE APP-ASSOC)          — 1 try (useful)
(:REWRITE TRUE-LISTP-REV)     — 1 try (useful)
```

The rune list in the output says WHICH rules contributed, but not:
- **How many times** each was applied
- **To which subterms**
- **In what order**
- **What instantiations** were used (critical for rules with free vars)
- **What backchaining** was done to relieve hypotheses

For Lean's `simp`, this may not matter — `simp only [r1, r2, ...]` will
find its own rewriting order. The hypothesis is that **given the same
lemma set, Lean's simp can close the same goals ACL2's rewriter closes**.
This needs to be tested empirically. If it fails, we may need to
instrument the rewriter more deeply (see Phase 2 below).

Specific risks where `simp only [runes]` may be insufficient:
- **Free variable rules** — ACL2 searches the context for instantiations;
  Lean `simp` may not
- **Conditional rewrites with backchaining** — ACL2's backchaining limit
  and strategy differs from Lean's
- **Definition unfolding depth** — ACL2 unfolds definitions to fixpoint;
  `simp` may need `unfold` or `delta` hints
- **Type reasoning** — ACL2's type-set is a specialized decision procedure
  with no direct Lean equivalent

## Approach

### Hack ACL2 to emit machine-parseable output only

The existing `set-raw-proof-format :clause` is close but still mixes
structured data with English prose. We modify ACL2 to emit purely
structured s-expression output — no English at all. The hook point is
`waterfall-msg1` in `prove.lisp`, which dispatches to the prose
generators. We replace (or supplement) those with s-expression emitters.

The output goes directly into the existing ACL2Lean s-expression parser
(Parser.lean), which produces Lean data structures. No intermediate
format (JSON, etc.) is needed — the parser already handles everything
ACL2 emits, and the consumer is Lean code in this repo.

```
ACL2 (hacked structured output) → stdout
  → ACL2Lean s-expression parser (Parser.lean)
    → Lean proof step AST (Syntax.lean types)
      → Lean tactic generation
```

### Instrument the rewriter incrementally as needed

If `simp only [runes]` proves insufficient to close goals that ACL2's
rewriter closed, we add more instrumentation. This is driven by actual
failures, not done upfront. Options:

- **Per-application logging** — hook `push-lemma` in the rewriter to log
  each individual rule application with its target subterm and
  instantiation. This produces a detailed rewrite trace.
- **accumulated-persistence :all with :list** — already exists, gives
  per-rule try/success counts and per-hypothesis stats. Useful for
  diagnosing where replay fails.
- **break-rewrite / dmr** — existing interactive debugging tools that
  show the rewrite stack. Could be adapted for batch output.

This would let us emit individual `rw [rule]` steps instead of bulk
`simp only [...]` calls if needed.

This would let us emit individual `rw [rule]` steps instead of bulk
`simp only [...]` calls if needed.

## Lean Receiving Side: Tactic Mapping

### Rune types in the sorting corpus

From running the full sorting corpus through ACL2:

| Rune type | Count in corpus | Meaning |
|-----------|----------------|---------|
| `:REWRITE` | dominant | Apply a rewrite lemma |
| `:DEFINITION` | very common | Unfold a function |
| `:TYPE-PRESCRIPTION` | common | Type reasoning about return values |
| `:EXECUTABLE-COUNTERPART` | occasional | Evaluate on concrete values |
| `:ELIM` (CAR-CDR-ELIM) | 41 steps | Destructor elimination |
| `:INDUCTION` | 58 schemes | Induction |
| `:FORWARD-CHAINING` | occasional | Forward chaining rules |
| `:LINEAR` | occasional | Linear arithmetic |
| `:CONGRUENCE` | rare | Congruence-based rewriting |
| `:COMPOUND-RECOGNIZER` | rare | Compound type recognizers |
| `:FAKE-RUNE-FOR-TYPE-SET` | common | Built-in type reasoning |
| `:FAKE-RUNE-FOR-LINEAR` | occasional | Built-in linear arithmetic |

### Waterfall processor frequencies (sorting corpus)

| Processor | Occurrences | Notes |
|-----------|-------------|-------|
| simplify | ~457 | Dominates — 85% of all steps |
| preprocess | ~42 | Light simplification / case analysis |
| destructor-elimination | ~41 | CAR-CDR-ELIM → pattern matching |
| generalization | ~10 | Replace subterms with fresh vars |
| induction | ~58 | Choose induction scheme |
| fertilization | ~2 | Substitute IH into goal |
| forcing rounds | 0 | Not seen in this corpus |

### Proposed tactic mapping

| ACL2 step | Lean tactic | Notes |
|-----------|-------------|-------|
| **Induction** on `(FOO X)` | `induction x using foo.induct` | Must generate matching `.induct` lemma from ACL2 defun |
| **Simplify** with rune list | `simp only [r1, r2, ...]` | Each `:REWRITE`/`:DEFINITION` rune → Lean simp lemma. May need `@[simp]` annotations on translated theorems |
| **Preprocess** (case analysis) | `simp` or `omega` or `decide` | Light; often just propositional |
| **Destructor elimination** | `match x with \| .cons a b => ...` or `obtain` | CAR-CDR-ELIM → destructure the cons |
| **Fertilization** (use IH) | `rw [ih]` | Substitute induction hypothesis |
| **Generalization** | `generalize term = v` | Replace subterm with fresh var |
| **Type reasoning** | built-in Lean type system + `decide` | ACL2's type-set has no direct analog; many cases should be free in Lean's type system |
| **Linear arithmetic** | `omega` | Lean's `omega` covers most of what ACL2's linear does |
| **Executable counterpart** | `native_decide` or `decide` | Evaluate closed terms |
| **Forward chaining** | `have` + the forward-chaining conclusion | Add derived fact to context |

### Key risk: the simp gap

The biggest risk is that `simp only [rune_list]` in Lean doesn't close
the same goals that ACL2's rewriter closes with the same rule set. This
could happen because:

1. **ACL2 unfolds to fixpoint** — a single simp step may unfold `MY-APP`
   64 times. Lean's `simp` has a max heartbeat and may give up earlier.
   Mitigation: tune `maxHeartbeats`, or use `simp` in a loop.

2. **Conditional rewrite backchaining** — ACL2 tries to establish rule
   hypotheses by recursive rewriting. Lean's `simp` does this too, but
   with different depth limits. Mitigation: pass all relevant lemmas.

3. **Free variable instantiation** — rules like `MEMB-RM` with free var
   `B` require searching the context. Lean `simp` won't do this.
   Mitigation: use `have` to supply the instantiation, or fall back to
   explicit `rw` with instantiation.

4. **Type-set reasoning** — ACL2's type-set is a specialized bitwise
   decision procedure. No direct Lean analog. Mitigation: many cases
   are trivial in Lean's richer type system; remainder needs dedicated
   `acl2_type_set` tactic or `decide`.

## Development Workflow

The approach is iterative, failure-driven, over the sorting corpus:

### Loop

```
1. Run ACL2 on sorting corpus → structured proof log
2. Translate theorems to Lean + generate tactic scripts from log
3. Run Lean on the generated proofs
4. Collect failures
5. Investigate each failure class:
   - Is the rune list sufficient but `simp` needs tuning? → adjust tactic
   - Is a rune mapping wrong? → fix the translator
   - Is the rewriter doing something `simp` can't? → add ACL2
     instrumentation to get more data, then generate finer-grained
     tactics (individual `rw` steps instead of bulk `simp`)
   - Is the proof structure wrong (bad induction, etc.)? → fix the
     structural tactic generation
6. Fix, re-run, goto 1
```

### Instrumentation escalation

Add ACL2 instrumentation only when a failure demands it, not upfront:

**Level 0** (start here): Per-subgoal rune lists + clauses from
`waterfall-msg1`. Generate `simp only [runes]` for each step.

**Level 1** (if simp gaps appear): Enable `accumulated-persistence :all`
to get per-rule try/success counts. This tells us which rules are
failing to fire in Lean and helps diagnose the gap.

**Level 2** (if ordering/instantiation matters): Hook `push-lemma` in
the rewrite loop to log individual applications with subterm positions.
Generate ordered `rw [rule]` / `conv` sequences instead of `simp`.

**Level 3** (if backchaining matters): Log hypothesis-relief attempts
inside `relieve-hyp`. Generate `have` steps to supply intermediate
facts that Lean's `simp` can't derive on its own.

The expectation is that Level 0 handles the majority of cases in the
sorting corpus. Levels 1-3 are there for the long tail.

### Success metric

The sorting corpus (10 files, ~58 inductions, ~500 simp steps) is the
target. The goal is 100% automated replay — every theorem that ACL2
proves should produce a Lean proof that type-checks with no manual
intervention.

## Appendix: ACL2 Internal Architecture (for Phase 2 hacking)

### Tag-trees (ttrees)

The core proof-justification data structure. Defined in `linear-a.lisp`
(Essay on Tag-Trees, ~line 189). A ttree is an alist mapping tags to lists
of values:

```
ttree ::= ((tag1 . (val1 val2 ...))
           (tag2 . (val3 ...))
           ...)
```

Primitives:
- `(push-lemma rune ttree)` — record that a rule was used
- `(cons-tag-trees t1 t2)` — merge two ttrees
- `(tagged-objects tag ttree)` — retrieve values for a tag

Key tags:

| Tag | Values | Meaning |
|-----|--------|---------|
| `'lemma` | runes | Rules used in this step |
| `'assumption` | assumption records | Forced hypotheses |
| `'pt` | parent-tree | Which clause literals were involved |
| `'splitter-if-intro` | runes | Rules that introduced if-splits |
| `'splitter-case-split` | runes | Rules that caused case splits |
| `'elim-sequence` | `((rune rhs lhs alist ...) ...)` | Destructor elimination details |
| `:use` / `:by` / `:cases` | lemma instances | Hint-derived information |
| `'abort-cause` | symbol | Why proof was aborted |

### The waterfall

Defined in `prove.lisp` (~line 7257). Goals flow through processors in order:

1. `apply-top-hints-clause` — user hints
2. `preprocess-clause` — trivial simplification
3. `simplify-clause` — full rewriting
4. `eliminate-destructors-clause` — destructor elimination (car/cdr elim)
5. `fertilize-clause` — cross-fertilization (use IH by substitution)
6. `generalize-clause` — replace terms with fresh variables
7. `eliminate-irrelevance-clause` — drop irrelevant hypotheses
8. `push-clause` — give up on this goal, push for induction

Each processor receives a clause and returns `(signal, clauses, ttree)`.
The ttree contains everything about what happened.

### Where prose is generated

The structured-to-prose pipeline:

```
waterfall processor returns (signal, clauses, ttree)
    ↓
waterfall-msg1 (prove.lisp ~line 2641)
    dispatches to processor-specific msg functions:
    ↓
    simplify-clause-msg1 → calls:
        extract-and-classify-lemmas (simplify.lisp ~line 9122)
            → produces alist: ((:DEFINITION (APP) (REV FORCED))
                               (:REWRITE (LEMMA1) (LEMMA2 IF-INTRO))
                               ...)
        tilde-*-simp-phrase (simplify.lisp ~line 9417)
            → turns alist into English
        fms "But simplification reduces this to T, using ~*1"
            → prints it
```

Similarly for induction: `induct-msg/continue` (induct.lisp ~line 5989)
has the full induction scheme, candidate list, and scoring before it
formats the English output.

### Hook points for Phase 2

**`waterfall-msg1`** (prove.lisp ~line 2641) — dispatch point where
processor results become prose. Receives `processor`, `cl-id`, `signal`,
`clauses`, `new-clauses`, `ttree`.

**`induct-msg/continue`** (induct.lisp ~line 5989) — induction output.
Has chosen scheme, `:induction` rune, measure, candidate count.

Hooking these points to emit s-expressions instead of prose requires
~150-300 lines of Lisp. No changes to proof logic — purely output.

## Key Source File References

| File | What's there | Key locations |
|------|-------------|---------------|
| `acl2/linear-a.lisp` | Ttree definition + primitives | Essay ~line 189, `push-lemma` ~line 365 |
| `acl2/prove.lisp` | Waterfall + `waterfall-msg1` | `waterfall` ~line 7257, `waterfall-msg1` ~line 2641 |
| `acl2/simplify.lisp` | Prose generation from ttrees | `extract-and-classify-lemmas` ~line 9122, `settled-down-clause-msg` ~line 9918 |
| `acl2/induct.lisp` | Induction selection + output | `induct-msg/continue` ~line 5989 |
| `acl2/history-management.lisp` | Summary block, proof-tree | `print-runes-summary` ~line 2575, `goal-tree` ~line 37 |
| `acl2/tau.lisp` | `all-runes-in-ttree` (complete tag list) | ~line 739 |
