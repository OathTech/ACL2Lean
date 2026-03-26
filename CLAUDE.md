# ACL2Lean

ACL2-to-Lean 4 bridge: import ACL2 theorems with kernel-checked proofs using Lean as the sole trust anchor. ACL2 serves as an untrusted proof-search oracle.

## Key rules

NEVER specialize the translator on particular examples.

NEVER silently skip or ignore malformed input. All parsers and processors must hard-crash on unexpected input — no default-case swallowing, no `| _ => none`, no "skip unknown forms". If something doesn't parse, that is an error, not something to paper over. This applies everywhere: s-expression parsing, proof log parsing, event classification, rune mapping. Unexpected input means either the input is wrong or the code is incomplete — both must be surfaced immediately, never hidden.

## Architecture

```
Lean kernel (trust anchor)
├── Layer 1: SExpr semantic model + Logic primitives (trusted)
├── Layer 2: Book translator: ACL2 .lisp → Lean .lean (untrusted)
└── Layer 3: Proof replay from ACL2 transcripts (untrusted, partially built)
```

**Core type:** `SExpr` (nil/atom/cons). Not `ACL2Object` (that was the legacy prototype at `septract/acl2-lean`).

## Project Layout

```
ACL2Lean/               Lean 4 library
  Syntax.lean           SExpr, Atom, Symbol, Event, TheoremInfo, GoalHint, ProofInstruction
  Parser.lean           S-expression reader (comments, macros, quoting, numerics)
  Logic.lean            ACL2 primitives (car, cdr, cons, arithmetic, predicates, bitwise)
  Count.lean            acl2Count structural size measure + termination lemmas
  Lexorder.lean         Total ordering on SExpr
  EvalOpt.lean          Canonical evaluator (Option-returning, with fuel monotonicity proofs)
  Translator.lean       translateSymbol, translateLiteral, sanitizeName (used by WorldGen)
  WorldGen.lean         Generate World definitions + theorem statements from .lisp
  Rewriter.lean         Subterm replacement guided by proof trace
  ProofLog.lean         Proof trace types (TraceEvent, RewriteStep) + parser
  DSL/                  #acl { } macro for inline ACL2 events
  PrettyPrinter.lean    S-expression pretty printing
  Imported/             Generated worlds + kernel-checked proofs (e.g. SimpleWorld.lean)
  Import.lean           loadEventsFromFile IO wrapper
  Workbench.lean        reportSamples corpus diagnostics
Main.lean               CLI entry point
scripts/                Batch translation and verification tools
acl2_samples/           ACL2 source corpus (including sorting/)
acl2/                   ACL2 fork git submodule (optional)
docs/plans/             Roadmap and design plans
```

## Build & Commands

```sh
lake build                              # Type-check everything (includes tests)
just test                               # Run unit tests only (460 #guard tests)
just ci                                 # Full conformance: build + unit tests
lake exe acl2lean gen-world <file>      # Generate World + theorem stubs from .lisp
lake exe acl2lean parse-proof-log <f>   # Parse and display proof trace
lake exe acl2lean report                # Corpus event histogram
lake exe acl2lean eval "<expr>"         # Evaluate s-expression
lake exe acl2lean eval-in <file> "<e>"  # Eval in file's world
```

`just ci` is the conformance gate. Run it before pushing.

Build system: Lake (`lakefile.toml`). Toolchain pinned in `lean-toolchain`.

