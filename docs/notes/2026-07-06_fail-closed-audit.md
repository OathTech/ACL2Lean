# Fail-closed audit — silent drops & meaningless defaults

**Date:** 2026-07-06
**Type:** read-only audit (no code changed). Report only.
**Scope:** the whole pipeline — parser/reconstruction, translator/world-gen,
replay driver core, replay support, semantic core (EvalOpt/Logic), and the ACL2
Lisp instrumentation.
**Method:** 6 decorrelated skeptical Opus reviewers (one per stage), each pointed
at primary sources, then the highest-stakes survivors spot-checked against source
by hand. Prior tracked backlog `docs/notes/2026-06-07_silent-drop-inventory.md`
used to separate *new* from *known-deferred* findings.

**Goal (per the request):** find every place where unexpected/malformed input is
**silently dropped** or replaced with a **meaningless default**, ranked by how
badly it could mask a real failure under this project's TDD/coverage-scoreboard
workflow — worst case being a fake value that flows into a *passing* proof of a
subtly wrong statement.

---

## The one distinction that organizes everything

The mirror theorem has the shape `∃N ∀f≥N, evalOpt f w env φ = some t`. So:

- **fail-CLOSED** = returns `none` / `throwError` / `throw` ⟹ the theorem becomes
  *unprovable*. Safe under TDD: a masked case shows up as a replay FAILURE, never
  a false pass. This is the mandated behavior (CLAUDE.md: "hard-fail at frontiers").
- **fail-OPEN** = returns a concrete value (`some .nil`, `.t`, `0`, a placeholder
  Expr, a defaulted subst/origin) on unexpected input ⟹ that value can flow into a
  computation that *succeeds*. This is the toxic class the request targets.

**Headline result:** across all six stages we found **no live CRITICAL soundness
hole** — no `sorry`/`admit`/`axiom`/`native_decide`, no fabricated proof term, no
`decide`/`omega` shortcut past a real node chain, and no fail-open default that is
*currently reachable* with corpus input to forge a passing proof. The dangerous
fail-open defaults that exist (semantic core F1/F2; translator package/escaping)
are **latent** — gated off by `checkTranslatable` and/or not exercised by the
all-`ACL2`, single-package corpus. They are real hazards for the *next* inputs
(multi-package books, `defconst`, translated lambda terms), not for what ships today.

That said, several fail-OPEN defaults and one cross-cutting `panic!` issue do
violate the hard-fail mandate and *will* mask failures the moment their trigger
appears. They are listed below, newest/most-actionable first.

---

## CROSS-CUTTING — `panic!` does not abort; it prints and returns a garbage default (HIGH)

Multiple reviewers credited `Syntax.lean`'s use of `panic!` (in `Event.classify`,
`TheoremOption.fromSExprs`, `parseDefunBody` siblings — e.g. `Syntax.lean:168-169,
497, 511, 521-525, 530, 540-541`) as "exemplary hard-fails." **In Lean 4, `panic!`
by default prints to stderr and returns the type's `Inhabited` default — it does
NOT abort the process** (aborting requires `LEAN_ABORT_ON_PANIC`, which is not set
in `lakefile.toml`/toolchain; grep found no such setting). Every type panicked over
here `deriving Inhabited`.

- **Effect:** a malformed top-level form doesn't crash — it prints a message and
  continues with a default `Event`/`SExpr` (e.g. `.inPackage default`, `.nil`).
  That is a *loud* default, not a silent one, but it IS a "meaningless default
  value substituted for unexpected input," and downstream code proceeds on it.
- **Why it matters here:** `Event.classify`/`parseDefunBody` are on the world-build
  and (transitively) the statement-build path. A defaulted `Event` there could
  drop a defun or mis-shape a body while only printing a line that a batch `just ci`
  run may not surface as a failure.
- **Confidence:** HIGH on the Lean semantics (documented behaviour, not executed
  here). Recommend confirming with a one-off (a deliberately malformed form) and,
  regardless, converting these `panic!`s to `throw`/`Except` so they fail-closed
  like the rest of the parser. This also downgrades the several "exemplary
  hard-fail via panic!" verdicts in the reviews to "loud default."

---

## NEW findings (not in the 2026-06-07 inventory)

### N1 — Driver: frontier-vs-defect classification by message-STRING PREFIX (MEDIUM, soundness-safe)
`Driver.lean:5651-5656` (`buildTotalEnv`) and `5861-5867` (rule-hyp discharge in
`replayProofConditional`); related `5722` (`dischargeRuleHyp`). Verbatim:
```
catch e =>
  let msg ← e.toMessageData.toString
  unless msg.startsWith "proveTotality:" do
    throw e
```
A caught exception is reclassified as a *benign frontier* (the fn/rule stays
hypothesis-backed, D6) iff its message starts with `"proveTotality:"` /
`"dischargeRuleHyp:"`. But that prefix is a **shared namespace across the whole
call subtree** — e.g. the helper `totDischargeDecrease` also throws
`"proveTotality: …"` (`Driver.lean:2910, 2913, 2922, 2926, 2930, 2941, 2950,
2954, 2957`). A genuine Lean-level bug raised via any of those sites is silently
demoted to a "condition," so a real prover/emission defect can hide behind a
`cond[total:fn]` / kept-`rule:` label instead of surfacing.
- **Soundness:** SAFE — the kept hypothesis stays explicit in the proof's type
  and the kernel checks everything actually built; the result is honestly
  *conditional*, not false.
- **Fidelity:** this is exactly the "mask a failure" pattern the request targets,
  in the reporting layer the project's scoreboard depends on. Fix: a typed/tagged
  frontier exception instead of `String.startsWith`.
- Verified verbatim by hand.

### N2 — Parser: `:ORIGIN` present-but-non-symbol silently becomes `""` (MEDIUM-HIGH)
`ProofLog.lean:328-330`: `| _ => ""`. `origin` is a primary replay dispatch key
(`Driver.lean:479, 1491, 1646, 1956, 3278, 3284, 3397`); a malformed origin reads
as `""` and routes the node down the wrong recipe / generic path instead of
surfacing the bad emission. **Inconsistent with the module's own stricter handling**:
`hyp-relief`'s `:ORIGIN` *throws* (`ProofLog.lean:479`). Should throw here too.

### N3 — Parser: `:PARENTS` non-list silently becomes `[]` (MEDIUM)
`ProofLog.lean:348-352`: `| none => []`. `parents` gates solidify/IH-linking
(`ClauseTree.linkNode` only equivalence-matches when `parents.isEmpty`,
`ClauseTree.lean:250`); a malformed `:PARENTS`→`[]` could push a parent-tagged
node into the IH-matching path. **Inconsistent with siblings**: `:RUNES` (:346),
`:SUBST` (:361), `:PATH` (:373) all `throw` on a non-list; only `:PARENTS`
defaults. Strong smell of oversight. Make it throw like its siblings.

### N4 — Parser: `#+`/`#-` reader conditionals ignore the feature test (MEDIUM, latent)
`Parser.lean:143-153`: `#+feature form` **always drops** the guarded form (returns
what follows); `#-feature form` **always includes** it — both independent of the
feature, and backwards from Common Lisp. Silent data loss/insertion in source
translation. No `#+/#-` in the current corpus (not triggered today); latent for
real ACL2 source using reader conditionals.

### N5 — Translator: all packages forced to `ACL2`; package context accepted then dropped (HIGH, latent)
`checkTranslatable` accepts `.inPackage _` as `.ok ()` (`WorldGen.lean:52`),
`renderWorld` drops it (`| _ => pure ()`, :86), `sym` hardcodes
`⟨"ACL2", name⟩` (:97), and `translateLiteral` emits name-only (`Translator.lean:65`).
The parser *preserves* non-ACL2 packages (`Parser.lean:180-187`). Since `evalOpt`
resolves `defs`/`env` by full-`Symbol` `BEq` (package+name), two distinct source
symbols `PKG1::BAR` / `PKG2::BAR` collapse to one `ACL2::BAR` → a *different* world
and mirror statement presented as the original. Corpus is all-`ACL2` (not
triggered today). Fix: honor package context or hard-fail `checkTranslatable` on
any non-`ACL2` package. Verified verbatim by hand.

### N6 — Translator: symbol/string/keyword text interpolated into Lean source unescaped (MEDIUM-HIGH, latent)
`Translator.lean:65,69,70` paste names/strings between `"`…`"` with no escaping.
ACL2 permits `"`/`\` inside `|…|`-symbols and strings (parser reads them raw,
`Parser.lean:131-138, 56-60`). Most cases fail to compile (loud); a crafted `\`/`"`
sequence can silently produce a *different well-formed* Lean string literal → a
mirror theorem over a corrupted constant. Escape `\` and `"` on emit.

### N7 — Instrumentation: speculative-expansion rollback skipped on empty checkpoint tail (MEDIUM, latent)
`acl2/rewrite.lisp:20430-20470`: the `rewrite-fncall` speculative rollback binds
`saved-log-tail` as bare `(cdr *structured-rewrite-log*)` and guards restore on
`(and (consp …) saved-log-tail)`. If the tail was `nil` at checkpoint time, restore
is **skipped** and a rejected expansion's inner events leak into the log. The
**sibling** hyp-relief checkpoint was explicitly hardened against exactly this —
tagged `(cons t (cdr …))` "so an empty tail still restores"
(`rewrite.lisp:20038-20046`). The fncall path never got that tag. In practice a
`:begin-literal` is pushed upstream first so the tail is usually non-empty (bug
masked), but the guard conflates "empty log" with "nothing to restore." Apply the
`(cons t …)` tag here too. Verified verbatim by hand.

### N8 — Instrumentation: `settled-down-clause` rewrite chain dropped unconditionally (MEDIUM-HIGH, needs a real log)
`acl2/prove.lisp:2658-2668`: `:REWRITES` is forced to `nil` whenever
`processor = settled-down-clause`, keyed on processor identity, not on
"produced no change." If a settling pass can re-run the simplifier and change the
clause, the `:STEP` emits changed `:NEWCLAUSES` with no rewrite chain to explain
it → the replay has an unreproducible step. Could not establish from ACL2 sources
alone whether settled-down-clause ever changes a clause when it re-fires; flag for
a check against a log where it fired non-trivially.

---

## KNOWN & DEFERRED (already in the 2026-06-07 inventory — re-confirmed, rationale documented there)

- **`:NOT-FLG` malformed → `true`** (`ProofLog.lean:422-425, 517-519`) = inventory
  **F10**. Polarity-affecting; partly mitigated by a downstream shape check
  (`Driver.lean:2211`) that catches spurious-true on a positive literal, but not
  the symmetric case. Deferred rationale: `true` is the plausible intended default.
  Reviewer rates HIGH→effectively MEDIUM. Still a `| _ => fallback` swallow.
- **`lookupKeyword` / `plistExtras` skip malformed plist entries** (`ProofLog.lean:255-268`)
  = **F7**. `plistExtras` is the "capture everything verbatim" mechanism, so its
  `| _ :: rest` skip arm undercuts its own contract. Deferred: absence is normal
  for optional keys.
- **`findLiteralResult` fold → last result / fallback to unrewritten literal**
  (`ProofTree.lean:265-270`) = **F3**. Partially mitigated by downstream equality
  checks (`Driver.lean:4094, 4165`); not every `lp.result` consumer re-validated.
- **`evalOptStep | _ => some .nil` for malformed `quote`/`if`/`let`/non-symbol head,
  and unbound var → `some .nil`** (`EvalOpt.lean:96-101, 103-140`) = **F15** (F2 in
  the semantic-core review). These are the highest-stakes fail-OPEN defaults, but
  **latent**: `translateLiteral` is total and copies bodies structurally (no dropped
  conjuncts), and `checkTranslatable` hard-rejects `defconst`/`encapsulate`/
  `include-book`/`make-event`/lambda-producing forms, so lambda-apps, defconst refs,
  and free vars don't reach `evalOpt` from the current corpus. **Recommend converting
  F15 to `none`** anyway: it costs only the monotonicity-proof update and removes the
  worst fail-open class from the trust anchor before multi-package/translated-term
  inputs arrive. (`callBuiltin` and the arity branch were already fixed to `none` —
  F13/F14 — so the interpreter is inconsistent: dispatch fail-closed, term-shape
  fail-open.)

---

## VERIFIED BENIGN (checked, NOT findings — recorded so they aren't re-litigated)

- **`callBuiltin | _,_ => none`** (`EvalOpt.lean:84`) and **arity mismatch → none**
  (`:135-137`): fail-closed for unknown primitive / wrong arity. Correct (F13/F14).
- **Fuel exhaustion → `none`** (`EvalOpt.lean:187`): never conflated with a value;
  `#guard` confirms. Central to soundness.
- **`Logic.lean` recognizer/coercion defaults** (`car`/`cdr` of atom → nil;
  `(+ 'a 'b) → 0`; `fix`/`nfix`/`ifix`/`zp`; `/0 → 0`): match ACL2's *total logical*
  semantics (guard-checking-off). Benign. (One real divergence: `symbolp` of a
  **keyword** → nil, but ACL2 keywords are symbols so should be `t` — MEDIUM
  fidelity, flag for `scripts/diff_eval.sh`; also `equal` on non-normalized numeric
  literals — needs a parser-normalization check.)
- **`SExpr.acl2Count` = 0 on all atoms** (`Count.lean:9-12`): diverges from ACL2's
  real `acl2-count` (integer-abs / string-length), BUT `totDischargeDecrease`
  (`Driver.lean:2895-2958`) only accepts `(car/cdr measured-formal)` decreases and
  `throwError`s a frontier on every numeric shape — so numeric measures hard-fail
  (fail-closed), they don't silently use the `0` default. Soundness-safe;
  fidelity/completeness only. Verified by hand.
- **Driver replay:** every proof-tree/rune/processor `match` catch-all ends in
  `throwError`; every recompute-and-check (`unless … == … do throwError`)
  fail-CLOSES on divergence; `applyStepSIff`'s wall-d catches **re-throw** the
  original elaboration error (the earlier "swallowed error" fix holds);
  `decide`/`omega`/`simp_all` are confined to the ratified DP-leaf carve-out on the
  precisely-stated obligation. No forgery/shortcut found in 5956 lines.
- **DpLift / ClausifyBridge / EvalLemmas:** the total functions (`dpLiftF`,
  `clausifyPure`, `substTerm`, `dumbNegateLit`) each have their "unexpected input"
  branch either `none` (caller hard-fails) or *constrained by a real soundness
  lemma* whose vacuous branches are vacuous because the input genuinely cannot
  produce the claimed output. No vacuous-premise lemma; no `sorry`/`native_decide`.
  `dpNoShadow`/`dpOpqWF` premises are load-bearing (checked).
- **Instrumentation:** the common "data unavailable" case is *absence of a
  field/event* (fail-closed), not a fabricated value; round-trip `:origin` rule
  spot-checked (~30 sites) clean; termination-clause stash names-match-guarded and
  consume-once; Satriani/subsumption markers fire only on real set-change.

---

## Residual "could-not-verify" — worth targeted follow-up

1. **N1 reachability** — does any real (non-frontier) defect currently get
   swallowed by the `proveTotality:`/`dischargeRuleHyp:` prefix catch? (typed
   exception would make it moot).
2. **N8** — can `settled-down-clause` change a clause when it re-fires? (needs a log).
3. **Instrumentation, free-variable hyp relief** — a `:match-free` success path that
   relieves a hyp with NO `:hyp-relief` marker would drop the `:SUBST` extension the
   replay needs (deep mutual recursion in `relieve-hyps1-free-*`; not exhaustively
   traced). Matches inventory open residue "finding B" of the perm-transitive audit.
4. **`built-in-clausep` at `induct.lisp:1310`** — confirm it's never on a
   theorem-waterfall path the replay treats as a PROVED leaf (would be a hard-fail
   emission gap, not a fake value, if it is).
5. **`symbolp` keyword** and **numeric-literal `equal`** divergences — run through
   `scripts/diff_eval.sh` (do not run during the concurrent merge).

---

## Recommended priority (if acting later — NOT done here)

1. **Convert `panic!` → `throw`** in `Syntax.lean` (cross-cutting; turns loud
   defaults into fail-closed; also corrects the reviews' "hard-fail" verdicts).
2. **N1 typed frontier exception** (removes the string-prefix defect-masking in the
   scoreboard-reporting layer).
3. **N2/N3** one-line throws (align `:ORIGIN`/`:PARENTS` with their throwing siblings).
4. **F15 → `none`** in `evalOptStep` (remove the worst fail-open class from the
   trust anchor before multi-package/translated-term inputs).
5. **N5/N6** translator package/escaping guards, and **N7** the `(cons t …)` tag —
   before any multi-package or `|…|`-symbol book enters the corpus.

All findings are read-only pointers. No code, artifacts, or generated files were
changed by this audit.

---

## Status update 2026-07-06 (later): fix sprint LANDED (branch mdd/fail-closed-fixes)

All five recommended-priority items are in (one commit, ci green, coverage
golden byte-identical): `panic!`→`Except` (`Event.classify` /
`TheoremOption.fromSExprs`; `generatedEvents` failure keeps the `.makeEvent`
so `checkTranslatable` rejects it), the N1 typed frontier tag
(`throwFrontier`/`isFrontierErr`; `(internal)` throws stay untagged and now
surface), N2/N3 parser throws, N4 reader-conditional hard-fail, N5/N6
translator package gate + `escapeStringLit`, F15 malformed-shape `none` (the
unbound-variable nil default is KEPT deliberately — it is the total-env
modeling choice the `∀ env` mirror statement form relies on, matching ACL2's
total logical semantics), and N7's `(cons t …)` checkpoint tag in the fork.
Open residuals (unchanged): N8, the free-var relief no-marker trace, the
`built-in-clausep` check, `Parser.lean` unterminated-block-comment panic
(loud comment-to-EOF default), and `Driver.rebuild`'s panic default (flows
only into `==` recompute checks, which fail closed).
