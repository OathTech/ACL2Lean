# Proof Replay Pipeline: End-to-End ACL2 → Lean Proof Generation

Created: 2026-03-21

## Goal

Replace `sorry` in translated theorems with actual proofs, driven by
structured proof data from ACL2. The system must be fully general —
it should handle any ACL2 book, not just the sorting corpus. The sorting
corpus is the test harness, not the specification.

**Key principle:** Never specialize on target examples. Every component
(proof log parser, rune mapper, tactic generator) must work from the
general structure of ACL2's output, not from patterns observed in
particular proofs.

## Current State

**What works:**
- ACL2 emits structured proof output via `(set-raw-proof-format :structured)`
  - `(:STEP :CLAUSE-ID "..." :PROCESSOR ... :RESULT ... :RUNES (...))`
  - `(:INDUCTION :TERM ... :SUBGOAL-COUNT ... :SCHEME ...)`
  - `(:QED)`
- The translator generates Lean `theorem ... := sorry` for each defthm
- The parser handles arbitrary ACL2 s-expressions
- Custom tactics exist: `acl2_simp`, `acl2_induct`, `acl2_grind`
- `scripts/translate-book.sh` does batch translation and verification

**What's missing:**
- No pipeline to run ACL2, capture structured output, and feed it to the
  translator
- Translator emits `sorry`, not proof scripts
- No Lean types for the new structured output format
- No tactic generation from proof steps

## Pipeline Architecture

```
┌─────────────┐    ┌──────────────┐    ┌─────────────────┐
│  ACL2 file  │───▶│ ACL2 prover  │───▶│ .proof-log file  │
│  (*.lisp)   │    │ (structured) │    │ (s-expressions)  │
└─────────────┘    └──────────────┘    └────────┬────────┘
                                                │
┌─────────────┐    ┌──────────────┐    ┌────────▼────────┐
│  Lean file  │◀───│  Translator  │◀───│  Proof log      │
│  (*.lean)   │    │  (enhanced)  │    │  parser         │
└──────┬──────┘    └──────────────┘    └─────────────────┘
       │
       ▼
  lake build (kernel check)
```

## Implementation Phases

### Phase 1: Wire up the pipeline (run ACL2, capture output)

**Goal:** `just proof-replay file.lisp` runs ACL2 with structured output
and saves the proof log alongside the translated Lean file.

**Steps:**

1. **Add a script `scripts/capture-proof-log.sh`** that:
   - Takes an ACL2 .lisp file
   - Runs it through `acl2/saved_acl2` with:
     ```lisp
     (set-gag-mode nil)
     (set-raw-proof-format :structured)
     (set-inhibit-output-lst '(proof-tree event summary warning observation))
     (ld "file.lisp")
     ```
   - Captures stdout to `file.proof-log`
   - Strips the ACL2 startup banner (everything before first `(:` line)

2. **Add Justfile targets:**
   ```
   capture-proof-log file:
       ./scripts/capture-proof-log.sh {{file}}
   ```

3. **Test:** Run on each sorting corpus file, verify the `.proof-log`
   files contain only s-expressions.

**Files to create/modify:**
- `scripts/capture-proof-log.sh` (new)
- `Justfile` (add target)

### Phase 2: Parse proof logs into Lean types

**Goal:** `ProofLog.lean` defines types and a parser for the structured
output.

**Steps:**

1. **Define Lean types in `ACL2Lean/ProofLog.lean`:**

   ```lean
   inductive ProofResult where
     | proved
     | subgoals

   structure ProofStep where
     clauseId : String
     processor : String        -- "SIMPLIFY-CLAUSE", "PREPROCESS-CLAUSE", etc.
     result : ProofResult
     runes : List (String × String)  -- (type, name) e.g. ("REWRITE", "CAR-CONS")
     newClauses : Option (List SExpr)

   structure InductionStep where
     term : SExpr              -- the function call triggering induction
     subgoalCount : Nat
     scheme : List SExpr       -- clause set (each clause is a disjunction)

   inductive ProofEvent where
     | step : ProofStep → ProofEvent
     | induction : InductionStep → ProofEvent
     | qed : ProofEvent

   structure ProofLog where
     events : List ProofEvent
   ```

2. **Write parser in `ACL2Lean/ProofLog.lean`:**
   - Use existing `Parser.parseAll` to get a `List SExpr`
   - Match on head keywords: `:STEP`, `:INDUCTION`, `:QED`
   - Extract fields by keyword lookup in the plist-style s-expression

3. **Add CLI command:**
   ```
   acl2lean parse-proof-log file.proof-log
   ```
   Parses and pretty-prints the structured proof log (for debugging).

**Files to create/modify:**
- `ACL2Lean/ProofLog.lean` (new)
- `Main.lean` (add command)

### Phase 3: Generate tactic scripts from proof logs

**Goal:** The translator emits tactic proofs instead of `sorry`, guided
by the proof log.

**Steps:**

1. **Map rune types to Lean simp lemmas:**

   Rune mapping must be systematic, not case-by-case. The translation
   follows from the rune's *type*, not its specific name:

   | Rune type | Lean mapping rule |
   |-----------|------------------|
   | `(:DEFINITION name)` | `sanitize(name)` — the translated function def |
   | `(:REWRITE name)` | `sanitize(name)` — a previously translated theorem |
   | `(:EXECUTABLE-COUNTERPART name)` | `native_decide` or `decide` |
   | `(:ELIM name)` | destructor elimination (generate `match` / `obtain`) |
   | `(:INDUCTION name)` | `sanitize(name).induct` |
   | `(:TYPE-PRESCRIPTION name)` | type lemma (may need generation) |
   | `(:FORWARD-CHAINING name)` | `have` with the forward-chaining conclusion |
   | `(:LINEAR name)` | `omega` or linear arithmetic |
   | `(:CONGRUENCE name)` | congruence lemma |
   | `(:COMPOUND-RECOGNIZER name)` | recognizer lemma |
   | `(:FAKE-RUNE-FOR-TYPE-SET NIL)` | drop (built-in type reasoning) |
   | `(:FAKE-RUNE-FOR-LINEAR NIL)` | `omega` |

   `sanitize(name)` is the existing `Translator.translateSymbol` function
   that maps ACL2 names to Lean identifiers. No per-name special cases —
   every rune goes through the same pipeline.

   Built-in ACL2 names (CAR-CONS, CDR-CONS, etc.) map to lemmas in
   `Logic.lean` via the same sanitization. If a needed lemma doesn't
   exist in the Lean side, that's a gap to fill in Logic.lean — not a
   special case in the rune mapper.

2. **Generate per-step tactics:**

   For each `ProofStep` in the log, generate a Lean tactic:

   | Processor | Tactic template |
   |-----------|----------------|
   | `SIMPLIFY-CLAUSE` (proved) | `simp only [rune1, rune2, ...]` |
   | `SIMPLIFY-CLAUSE` (subgoals) | `simp only [rune1, ...]; ...` (continue) |
   | `PREPROCESS-CLAUSE` | `simp` or skip (often trivial) |
   | `ELIMINATE-DESTRUCTORS-CLAUSE` | `match` or `obtain` |
   | `FERTILIZE-CLAUSE` | `rw [ih]` |
   | `GENERALIZE-CLAUSE` | `generalize` |
   | `PUSH-CLAUSE` | (no tactic — means induction is coming) |
   | `SETTLED-DOWN-CLAUSE` | (no tactic — internal bookkeeping) |

3. **Generate induction structure:**

   For each `InductionStep`, generate:
   ```lean
   induction x using foo.induct with
   | case1 ... => simp only [...]  -- from subsequent STEP events
   | case2 ... => simp only [...]
   ```

4. **Assemble the proof:**

   The proof log for a theorem is a sequence: maybe some preprocessing
   steps, then an induction, then per-case steps. The assembler groups
   steps by their clause-id hierarchy and generates a structured proof.

5. **Modify `Translator.translateDefthm`:**
   - Accept an optional `ProofLog` parameter
   - When present, generate the tactic proof from the log
   - When absent, fall back to `sorry` (current behavior)

**Files to create/modify:**
- `ACL2Lean/ProofLog.lean` (extend with tactic generation)
- `ACL2Lean/Translator.lean` (modify `translateDefthm`)

### Phase 4: Iterate on failures

**Goal:** Run the full sorting corpus, find failures, fix them.

**Steps:**

1. **Add `scripts/replay-book.sh`:**
   - For each .lisp file: capture proof log, translate with log, run
     `lake build`
   - Report per-theorem pass/fail

2. **Add Justfile target:**
   ```
   replay-sorting:
       ./scripts/replay-book.sh acl2_samples/sorting/
   ```

3. **Iterate:**
   - Run replay on corpus
   - For each failure class, diagnose and fix:
     - **Rune mapping wrong** → fix RuneMap
     - **`simp` insufficient** → try `simp` with more lemmas, or `omega`,
       or `decide`
     - **Induction mismatch** → fix induction scheme generation
     - **Need rewriter instrumentation** → add ACL2 instrumentation
       (Level 1-3 from structured-proof-log.md plan)
   - Re-run, repeat

**Instrumentation escalation (if needed):**
- Level 0: Per-subgoal rune lists (current)
- Level 1: `accumulated-persistence :all` for per-rule try/success counts
- Level 2: Hook `push-lemma` for individual rewrite application log
- Level 3: Log hypothesis-relief attempts

## Generality Principles

1. **No corpus-specific logic.** The proof replay system must work from
   the structure of ACL2's output format, not from patterns in particular
   proofs. If we find ourselves writing `if theoremName == "perm-cons"`
   anywhere, we've gone wrong.

2. **Rune mapping is systematic, not enumerated.** The translation from
   ACL2 rune names to Lean identifiers uses the same `translateSymbol`
   function as everything else. No lookup table of specific rune names.

3. **Processor handling covers all processors.** The waterfall has 8
   processors. We must handle all of them from day one, even if some
   (like `ELIMINATE-IRRELEVANCE-CLAUSE`) are rare. Unhandled processors
   are a bug, not a TODO.

4. **The proof tree structure is general.** Clause-ids can nest to
   arbitrary depth (*1.1.1.1/3'''''). The assembler must handle
   arbitrary nesting, not just the 2-3 levels seen in the sorting corpus.

5. **Built-in ACL2 lemmas belong in Logic.lean.** When replay fails
   because a built-in ACL2 rune (like `CAR-CONS`) has no Lean equivalent,
   the fix is adding the lemma to `Logic.lean` — not special-casing the
   replay. This grows our trusted semantic model, which is the right
   place for that knowledge.

## Key Design Decisions

### Proof log as sidecar file vs. inline

The proof log is a separate `.proof-log` file, not embedded in the Lean
source. This keeps the translator deterministic (same .lisp → same .lean
modulo proof body) and lets us re-run ACL2 independently of Lean
translation.

### Tactic style: `simp only` vs. `rw` sequences

Start with `simp only [runes]` — bulk application of the exact rule set
ACL2 used. If this proves insufficient (the "simp gap"), fall back to
individual `rw` steps, which requires deeper ACL2 instrumentation.

### Where to put generated proofs

The translator currently writes to `ACL2Lean/Translated/`. Proof-replay
output goes to the same place — the only change is the proof body.
The `ACL2Lean/Imported/` directory is for hand-curated proofs.

### Handling the proof tree structure

ACL2's proof is a tree: Goal → induction → subgoals → sub-inductions.
The clause-id naming convention encodes this: `"Goal"`, `"Subgoal *1/2"`,
`"Subgoal *1.1/3"`. The proof assembler must group steps by their
position in this tree and generate nested Lean tactics accordingly.

Clause-id hierarchy:
- `*N` = induction pool N
- `/K` = subgoal K of that pool
- `.M` = sub-induction M
- `'` primes = successive waterfall passes on the same subgoal

## Success Criteria

1. `just replay-sorting` runs end-to-end without manual intervention
2. Every theorem in the sorting corpus produces a Lean proof that
   type-checks (no `sorry`)
3. Existing translation mode (`just translate-sorting`) continues to
   work unchanged
4. The system handles any well-formed ACL2 structured proof output —
   nothing in the implementation is specific to the sorting corpus
5. Running on a new ACL2 book requires zero code changes (may require
   adding missing built-in lemmas to Logic.lean, but no replay logic
   changes)

## File Inventory

| Phase | File | Status |
|-------|------|--------|
| 1 | `scripts/capture-proof-log.sh` | New |
| 1 | `Justfile` | Modify |
| 2 | `ACL2Lean/ProofLog.lean` | New |
| 2 | `Main.lean` | Modify |
| 3 | `ACL2Lean/ProofLog.lean` | Extend |
| 3 | `ACL2Lean/Translator.lean` | Modify |
| 4 | `scripts/replay-book.sh` | New |
| 4 | `Justfile` | Modify |
| 4 | `acl2/` submodule | Modify (if instrumentation needed) |
