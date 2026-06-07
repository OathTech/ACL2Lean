# Silent-drop / catch-all inventory (no-silent-skip backlog)

**Date:** 2026-06-07
**Purpose:** catalog of places that silently swallow/drop input instead of
hard-failing, violating CLAUDE.md's non-negotiable "never silently skip malformed
input." For follow-up conversion to hard-fails (one at a time, watching what each
surfaces). From a codebase survey (read-only). **Confirmed-fine cases are listed
at the end so we don't re-litigate them.**

> Conversion discipline (per the user): replacing a catch-all with a hard-fail
> may make some logs fail — that's the point; each failure surfaces an unmodeled
> case to handle. Convert incrementally.

## Status (2026-06-07)

- ✅ **F1, F4** — fixed by the branch-tree work (parseProofNodesAux exhaustive,
  buildClauseItems captures inter-literal/branch/type-set; trailing pendingChildren
  flushed not dropped).
- ✅ **F8** — `:FORMULA`/`:BODY`/`:COROLLARY` now hard-fail when missing.
- ✅ **F9** — runes / subst / leaves now hard-fail on a malformed entry or non-list
  (parseRunes, parseRewriteStep?'s :RUNES/:SUBST, type-prescription :LEAVES).
- ✅ **F5** — `collectFlat` hard-fails on a non-step/induction event in a theorem block.
- ✅ **F11** — `:INPUTCLAUSE`/`:NEWCLAUSES`/`:SCHEME` hard-fail on a non-list value.
- ✅ **F2** — dead `BranchDecision`/`BranchJustification` removed.
  (All of the above: zero corpus regressions — the sample logs are well-formed, so
  the hard-fails don't fire; they now guard against malformed input.)
- ⏸ **F7** (`lookupKeyword`) — left as-is: the `| _ :: rest` arm means "key not at
  this position," and `lookupKeyword` is used for *optional* keys too (absence is
  normal). Hard-failing risks breaking valid optional-key lookups; low value.
- ⏸ **F10** (`not-flg` default `_ => true`) — left: `:NOT-FLG` is plausibly
  omittable with `true` the intended default; converting risks breaking valid logs.
- ⚠ **F3** — partially addressed (findLiteralResult now reads the type-set result);
  the fallback to the unrewritten literal is *correct* for a carried/unchanged
  literal, so not converted.
- ⚠ **F13/F14/F15 (EvalOpt — the TRUSTED CORE)** — NOT converted. These need care:
  the evaluator is total (`Option SExpr`, `none` = non-convergence); a silent `.nil`
  for an unknown primitive (F13) is the real soundness concern, but fixing it means
  changing `callBuiltin`'s signature (`SExpr → Option SExpr`) and rippling through
  `evalOptStep` — a change to the semantic model that defines the mirror theorem.
  Handle as a separate, discussed step, not a blind conversion.

## Tier 1 — reconstruction path, genuinely drops data

- **F1 `ProofTree.lean` `parseProofNodesAux` catch-all** — drops any unmodeled
  in-literal event (`typeSetReasoning`, `branchSubstitution`, `caseSplit`,
  `contextSubst`, `beginBranch/endBranch`, `rewrittenLiteral`). *(Addressed by the
  branch-tree work: model these + hard-fail the catch-all.)*
- **F2 `ProofTree.lean` `ifTest*` arm** — IF branch decision discarded; the whole
  `BranchDecision`/`BranchJustification` machinery (declared but) **dead code**.
  The module doc claims steps are "enriched with IF branch decisions" — they are
  not.
- **F3 `ProofTree.lean` `findLiteralResult`** — fold ignores all but the last
  `rewrittenLiteral`, takes it unconditionally (no match against the literal),
  and falls back to the *unrewritten* literal if none — masking missing/duplicate
  results. The literal `result` feeds IH-linking.
- **F4 `ProofTree.lean` `buildLiteralProofs` top loop** — skips any non-
  `beginLiteral` event (inter-literal rewrite-steps, branch substitutions,
  clause-level type-set). *(Addressed by the branch-tree work.)*
- **F5 `ClauseTree.lean` `collectFlat` `| _ => pure ()`** — swallows any
  `ProofEvent` reaching the per-theorem loop that isn't step/induction; hides
  mis-sliced blocks (defun/defthm/qed leaking in).

## Tier 2 — pipeline parser fallbacks that hide malformed fields

- **F7 `ProofLog.lean` `lookupKeyword` `| _ :: rest`** — traverses past malformed
  (non keyword-value) plist entries; a truncated/odd plist is silently accepted,
  and "key absent" is indistinguishable from "plist garbage."
- **F8 `ProofLog.lean` `getD .nil` on event fields** — `:FORMULA` / `:BODY` /
  `:COROLLARY` defaulting to `.nil` silently builds a defthm/defun/type-
  prescription with an empty statement (data loss). (`:JUSTIFICATION`/`:SEGMENT`
  defaulting is lower-priority / plausibly optional.)
- **F9 `ProofLog.lean` `filterMap` for runes / subst / leaves** — silently drops
  malformed entries. Subst feeds definition-expansion fidelity; leaves feed the
  type facts that (per CLAUDE.md) must come from ACL2 — dropping them is exactly
  what the rule forbids.
- **F10 `not-flg` default** — missing and malformed `:NOT-FLG` both → `true`.
- **F11 `inputClause`/`newClauses`/`scheme` non-list → `[s]`** — wraps an
  improper value as a singleton instead of rejecting.
- **F12 `splitByTheorem` "QED without defthm, skip"** — peripheral (not on the
  `buildDevelopment` path; only the older `summary` path).

## Tier 3 — trusted core (EvalOpt/Logic) semantic defaults

- **F13 `EvalOpt.lean` `callBuiltin | _,_ => .nil`** (known) — unknown primitive /
  wrong arity silently evaluates to nil. Highest-stakes (semantic model): a
  mirror theorem could be "proved" about a wrong value.
- **F14 `EvalOpt.lean` `bindArgs | _,_ => {}`** (known) — formal/arg mismatch →
  empty env (guarded into `some .nil`, itself a silent wrong-arity result).
- **F15 `EvalOpt.lean` `evalOptStep | _ => some .nil`** — malformed `quote`/`if`/
  `let`/call/term shapes silently evaluate to nil.

## Confirmed FINE (reviewed — not findings)
- `Logic.lean` recognizer/coercion `| _ => .nil`/`0` defaults — `nil`/`0` is the
  correct ACL2 answer for "not that shape" (the by-design recognizer case).
- `Syntax.lean` `Event.classify` / `TheoremOption.fromSExprs` — **exemplary
  hard-fails** (`panic!` on malformed/unrecognized); model conversions on these.
  Metadata `.raw`/`none`/`headSymbol?` arms are recognizers/renderers (peripheral).
- `Parser.lean` — hard-fails on unterminated string/list/comment; only the
  rational→symbol fallback (`a/b` with unparseable parts) is a minor reinterpret.
- WorldGen/Main/Workbench/DSL `| _ => pure ()` — renderers/emitters skipping
  cosmetic event kinds.

## Possible exception to revisit
- **F18 `Syntax.lean` `Event.classify` `.skip`** allow-list includes `defequiv`/
  `defcong` — these carry congruence/equivalence info the fidelity rules say
  matters; confirm they're truly irrelevant to replay before trusting the skip.
