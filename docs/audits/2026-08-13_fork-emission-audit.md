<!-- Recovered verbatim from the session transcript (agent final report,
     2026-08-13) and persisted 2026-08-13. Basis commit: main @ 4a600c8.
     Fork-emission gap audit: probe-verified against the built ACL2 image; GAP-1 prototyped in-image.
     Findings feed the R-arc roadmap: docs/plans/2026-08-13_r-arcs-roadmap.md.
     Dated record — where terminology conflicts with docs/LEXICON.md, the
     lexicon wins. -->

Scout complete. Both trees verified clean (no modifications; scratch removed).

# FORK-EMISSION AUDIT — 2026-08-13

**Method note:** every claim below is probe-verified against the real artifact. I ran the built ACL2 image (`acl2/saved_acl2 --no-sysinit`) read-only against the boot world and **prototyped the GAP-1 fix in-image** — it works. Where I could not execute (the Lean driver's frontier messages are swallowed by the D6 kept-hypothesis catch), findings are labelled **RECONSTRUCTED** with the code line that grounds them.

---

## HEADLINE

**The fork batch is smaller than the brief assumed, and its centre of gravity moved.**

| # | Item | Verdict |
|---|---|---|
| 1 | GAP-1 context-refined `:LEAVES` | **REAL, fully solved by prototype** |
| 2 | GAP-2 primitive type snapshots | **REAL but MIS-FRAMED** — the intended design is *impossible*; correct design is different |
| 3 | BINARY-APPEND corollary strength | **REAL, and far simpler than assumed** — ACL2 *does* store the strong rule; the fork **deliberately discards it** |
| 4 | G5 multi-literal (app_nil) | **NOT AN EMISSION GAP — and not a frontier at all.** Label is ~2 months stale |
| 5 | rev family | **NOT AN EMISSION GAP.** Rows are `REPLAYED ✓` with *zero* kept conds |
| 6 | linear route | **NOT AN EMISSION GAP** (one named conditional risk) |
| 7 | sweep | 1, 2, 3 are **ONE mechanism**; 2 new live items found |

Items 4/5/6 are **removed from the fork batch**. That is the audit's most valuable negative result: **the batch is items 1+2+3, which are a single collector rewrite plus a one-line selector change.**

---

## ITEM 1 — GAP-1: context-free `:LEAVES` verdicts

### Site (verified)
- **`acl2/defuns.lisp:12014`** — `TRACE-LOG[infra/tp-leaves]`
- **`acl2/defuns.lisp:12022`** — `(defun tp-collect-if-leaves (body ens wrld))`; the empty type-alist is `defuns.lisp:12033` (`nil ; type-alist (empty — no IF-branch assumptions)`)
- **Two callers**: `defuns.lisp:12178` (live admission, `TRACE-LOG[emit/type-prescription]` at `:12140`) and **`acl2/ld.lisp:5668`** (the ground-zero snapshot variant, `TRACE-LOG[emit/type-prescription]` at `ld.lisp:5647`). *Both must be changed together — the brief named only the first.*

### The analogous in-ACL2 code path (the brief's question)
**`acl2/type-set-b.lisp:8246–8345`** — `type-set-rec`'s `'if` case. It calls `assume-true-false-rec` on `(fargn x 1)` to obtain `true-type-alist`/`false-type-alist`, then recurses into `(fargn x 2)`/`(fargn x 3)` under them; when `must-be-true` **and** `must-be-false` both hold it returns `*ts-empty*` (contradictory context). `tp-collect-if-leaves` is a hand-rolled copy of this walk *with that machinery deleted*.

### PROTOTYPE RESULT (executed in-image, not reasoned)

```
INTEGER-ABS   basic-ts = 7 (*TS-NON-NEGATIVE-INTEGER*)
  CONTEXT-FREE (today)              CONTEXT-REFINED (prototype)
  (UNARY-- X)  127  ✗ not ⊆ 7   →   6  (*TS-POSITIVE-INTEGER*)   ctx ((INTEGERP X) (&lt; X '0))        ✓
  X            -1   ✗ not ⊆ 7   →   7  (*TS-NON-NEGATIVE-INTEGER*) ctx ((INTEGERP X) (NOT (&lt; X '0))) ✓
  '0            1   ✓           →   1                              ctx ((NOT (INTEGERP X)))          ✓
```

**GAP-1 is fully closed by ~15 lines mirroring `type-set-rec`.** All three INTEGER-ABS leaves certify against the class mask. ACL2-COUNT also sharpens (`(BINARY-+ (INTEGER-ABS (NUMERATOR X)) (DENOMINATOR X))`: 6 → 4 `*TS-INTEGER&gt;1*`).

**Free bonus:** the `must-be-true ∧ must-be-false` arm gives a **`:VACUOUS` leaf marker** — exactly the complex-rational branch the TP arc log names as needing the ratified vacuous-branch device. No separate work.

**Second free bonus:** the ruling-test path gives each leaf an **ADDRESS**, retiring the `:LEAVES` occurrence-granularity ambiguity (today two identical leaf terms in different branches are indistinguishable — see PERM/ORDEREDP whose emitted leaves already contain duplicate `'NIL 128` entries).

### What the enriched emission should carry (the brief's question)
Per leaf, probe-verified as available:

| field | example (INTEGER-ABS leaf 1) | why |
|---|---|---|
| term | `(UNARY-- X)` | as today |
| ts | `6` | as today, now context-refined |
| **ruling tests** | `((INTEGERP X) (&lt; X '0))` | the leaf's ADDRESS; matches the driver's existing `facts : List (SExpr × Bool × Expr)` vocabulary (`Provers.lean:699,711`) |
| **type-alist** | `(((&lt; X '0) 256) (X 16) (X 23))` | **the load-bearing new datum** — ACL2's *derivation* from those tests. Deriving it Lean-side would violate "type facts come from ACL2" |

The ruling tests are re-derivable Lean-side (the walk descends the same IF tree); **the type-alist is not**. Emit both — the tests for addressing, the alist for facts. Emit the alist **verbatim with shadowing** (ACL2 semantics = `assoc-equal`, first hit wins; `(X 16) (X 23)` above) rather than de-shadowing in the emitter; document the lookup rule.

### Tag sketch (conforms to the discipline)
```lisp
; TRACE-LOG[infra/tp-leaves]: … the collector now MIRRORS type-set-rec's own
; 'if case (type-set-b.lisp:8246): assume-true-false-rec on the test yields the
; true-/false-type-alist, and each branch is walked under it, so a leaf's verdict
; is the one ACL2 computes IN CONTEXT. A must-be-true ∧ must-be-false test marks
; the branch :VACUOUS (ACL2's own contradictory-context case).
```
Namespace `infra/` is correct (the helper emits nothing itself). The two `emit/type-prescription` tags stay; the **`:LEAVES` field shape changes**, so their purpose sentences want a one-line amendment. **No new `emit/&lt;label&gt;`, so no round-trip-rule impact.**

### Lean-side consumer
- **Parser**: `ACL2Lean/ProofLog.lean:1134-1141` — hard-fails on any leaf that is not exactly `(term ts)` (`| _ =&gt; throw s!"TYPE-PRESCRIPTION {name}: bad leaf"`). **Every log must be recaptured in the same commit; there is no forward-compat path.**
- **Storage**: `ACL2Lean/ClauseTree.lean:98` (`leaves : List (SExpr × Int)`), accessor `ClauseTree.lean:319` (`typePrescriptionLeaves`), config `Provers.lean:1120` (`cfg.tpLeaves`), kit field `Provers.lean:569`.
- **Check site**: `Provers.lean:604-616` `tpEmittedLeafOk` — `tsSubsumed ts cls.tsMask`. This flips from ✗ to ✓ for INTEGER-ABS the moment the refined verdict lands.

### ⚠ THE PART THAT MUST NOT BE BATCHED
Passing `tpEmittedLeafOk` is **necessary, not sufficient.** The walk must still *prove* the corollary at the leaf. For `(UNARY-- X)` the obligation is `P(negate v)` **given** `integerp v ∧ v &lt; 0` — a **fact-conditioned closure lemma**. Today `tpClosure2` (`Provers.lean:735`) holds only *unconditional* `∀ u v, pA u → pB v → P (fn u v)` lemmas. Two candidate designs, and the choice is a **meaning-level ruling, not an executor call**:

- **D-A (recommended, non-drifting):** the emitted **type-alist** entries become `InTs`-style obligations discharged from the in-scope branch facts via the **already-emitted `:GROUND-ZERO-RECOGNIZER-TUPLES`** (`ld.lisp:5526`; fn/rune/true-ts/false-ts/strongp — consumed today at `NodeCore/Compose.lean:258`). Then closure becomes a **ts-algebra family** indexed by (primitive, in-mask) → out-mask, mirroring `type-set-primitive`. General by construction.
- **D-B:** a per-(class, primitive, branch-condition) conditional-closure table. Smaller, and **exactly the per-case accretion the carve-out drift test forbids**.

**Recommendation: land the EMISSION (item 1) in the batch; gate the Lean consumer on the D-A/D-B ruling.** The emission is strictly additive and useful under either.

---

## ITEM 2 — GAP-2: primitive type facts. **THE BRIEF'S PROPOSED DESIGN IS IMPOSSIBLE.**

### The brief asked: "where does ACL2 store its built-in type knowledge?" — answered, decisively

**It does not store it. It is Lisp code.** `acl2/type-set-b.lisp:9118` `(defun type-set-primitive …)` — a `case` on `(ffn-symb term)` dispatching to `type-set-unary--`, `type-set-cons`, `type-set-equal`, … There is no table, no `*ts-*` constant set, no rule record.

### Probe (executed over `*primitive-formals-and-guards*`, all 32 primitives)

**Only 7 of 32 have any `'type-prescriptions` property, and NONE of the ones we need:**

```
DENOMINATOR NONE   NUMERATOR NONE   UNARY-- NONE   REALPART NONE
IMAGPART    NONE   COERCE    NONE   BINARY-+ NONE  CONS NONE   CDR NONE
CHAR-CODE   NONE   SYMBOL-NAME NONE  &lt;  NONE   EQUAL NONE  ...
  (the 7 that DO: CODE-CHAR, PKG-WITNESS, SYMBOL-PACKAGE-NAME,
   INTERN-IN-PACKAGE-OF-SYMBOL, BAD-ATOM&lt;=, BINARY-* (NONNEGATIVE-PRODUCT,
   conditional), CAR (NATP-RANDOM$ — restricted to (CAR (RANDOM$ N STATE)),
   useless generally))
```

**Consequence:** a `:GROUND-ZERO-TYPE-PRESCRIPTIONS` snapshot event modelled on the existing gz patterns would cover **7 primitives, none of them a blocker**. It cannot serve `dis_acl2_count_tp`. This refutes the brief's proposed design *and* the arc log's framing ("a primitive-snapshot emission item").

### The correct design: **PER-LEAF SUBTERM VERDICTS** (and it is the SAME collector as item 1)

What the walk actually lacks is not a *general rule* for DENOMINATOR — it is *ACL2's verdict for this occurrence in this context*. `type-set-rec` computes exactly that, recursively, on its way to the leaf verdict. **Prototype, executed:**

```
LEAF (BINARY-+ (INTEGER-ABS (NUMERATOR X)) (DENOMINATOR X))  ts=4
  ctx ((NOT (CONSP X)) (RATIONALP X) (NOT (INTEGERP X)))
  SUBTERM VERDICTS:
    (INTEGER-ABS (NUMERATOR X)) -&gt; 7   (*TS-NON-NEGATIVE-INTEGER*)
    (NUMERATOR X)               -&gt; 22  (pos-int ∪ neg-int)
    (DENOMINATOR X)             -&gt; 4   (*TS-INTEGER&gt;1*)

LEAF (BINARY-+ '1 (BINARY-+ (ACL2-COUNT (REALPART X)) (ACL2-COUNT (IMAGPART X))))  ts=6
    (REALPART X) -&gt; 63 (*TS-RATIONAL*)   (IMAGPART X) -&gt; 62
```

This is the R2b-ratified "**deterministic recomputation = emission**" argument already used by `gz-termination-clauses` (`ld.lisp:5284-5290`) — same generator, same inputs, read off the world. It is emitted-data-driven and occurrence-specific; it invents no general rule.

Precedent for the division of labour: `Provers.lean:597-604` already states the ratified pattern — *"ACL2's emitted leaf verdict says WHICH type; the Lean side contributes only the class's value CLOSURE lemma; it never derives a type."* Subterm verdicts extend that pattern one level down, unchanged in kind.

**Additive minor arm (cheap, take it):** snapshot the 7 primitives that *do* have a stored TP — `CODE-CHAR`/`PKG-WITNESS`/`SYMBOL-PACKAGE-NAME`/`INTERN-IN-PACKAGE-OF-SYMBOL`/`BAD-ATOM&lt;=`/`BINARY-*`/`CAR`. Zero current customers, but it closes the "primitives have no type facts at all" statement honestly and costs ~10 lines (see item 3's collector, which subsumes it).

### The LEN/COERCE string plumbing (brief item 7) — answered
`ACL2-COUNT`'s `stringp` branch returns `(LENGTH X)`; **`LENGTH`'s body is `(IF (STRINGP X) (LEN (COERCE X 'LIST)) (LEN X))`** (probed). `LENGTH` *has* a defun and *is* snapshotted (verdict 7, ⊆ 7 — fine). `COERCE` has no defun and no stored TP → the callee-TP arm frontiers at `Provers.lean:976` when it descends into LENGTH's body.
- **Classification: (a) a missing primitive TYPE FACT — covered by item 2's subterm-verdict design, NOT a separate item.**
- The interpreter half is **CLOSED**: `Logic.coerce` (`ACL2Lean/Logic.lean:380-396`) is differentially pinned, registered in `EvalOpt.lean:110,133`, and `length_exec_corr` (`ACL2Lean/Imported/Sorting.lean:3122`) *proves* the STRINGP/COERCE/LEN convergence. Residuals are a differential-corpus char-op gap (`docs/BUGS.md:45`, BUG-001) and a **driver-side** STRINGP DP-lift item (`TODO.md:4355`, `NodeCore/Ctx.lean:1027`) — neither is emission.

---

## ITEM 3 — BINARY-APPEND corollary strength. **THE STRONG FACT EXISTS AND THE FORK THROWS IT AWAY.**

### Probe result (decisive)
```
BINARY-APPEND : 2 stored type-prescriptions
 [1] rune (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND)
     HYPS ((TRUE-LISTP B))   BASICTS 1152
     COROLLARY (IMPLIES (TRUE-LISTP B) (TRUE-LISTP (BINARY-APPEND A B)))   ← the strong one
 [2] rune (:TYPE-PRESCRIPTION BINARY-APPEND)
     HYPS NIL                BASICTS 3072
     COROLLARY (IF (CONSP (BINARY-APPEND X Y)) 'T (EQUAL (BINARY-APPEND X Y) Y))
```

**Answers the brief's question directly: YES, ACL2 keeps CONDITIONAL type-prescriptions** — `hyps` is a field of the `type-prescription` defrec (`type-set-b.lisp:3359-3367`). `TRUE-LISTP-APPEND` is a boot-strap `defthm` at **`acl2/axioms.lisp:3326`**, i.e. ground-zero, so no `:DEFTHM` event ever fires for it either. It appears **nowhere** in the repo (`grep -rn TRUE-LISTP-APPEND` → 0 hits across `acl2_samples/`, `docs/`, `ACL2Lean/`, `Tests/`).

### Where it is discarded (the precise site)
**`acl2/ld.lisp:5601` `(defun gz-definitional-tp (name tps))`** under `TRACE-LOG[infra/gz-tp-select]` (`ld.lisp:5596`) — selects the **single** tp whose rune base-symbol equals the fn name, then `ld.lisp:5659-5679` emits only that one. The selector was correct for its purpose (audit 2026-07-19 F1: avoid picking a *user* rule) but it is a **one-of-N filter where N can be &gt; 1**, and the discarded ones are exactly the conditional strengthenings. The live admission emitter (`defuns.lisp:12159`, `(car tps)`) has the same one-of-N shape, though at admission time N=1.

### Emitted evidence
`acl2_samples/sorting/qsort.proof-log:143050` carries only the weak form; `qsort.proof-log:13406` is `QSORT`'s own TP whose leaf 1 is the `BINARY-APPEND` call with verdict `1024`.

### Emission design (simple, general, no new event)
Keep the existing `(:TYPE-PRESCRIPTION name :COROLLARY … :BASICTS … :LEAVES …)` positions for the definitional rule (so every existing consumer path is untouched), and **add one field carrying ALL stored tps, rune-keyed**:

```lisp
(:TYPE-PRESCRIPTION BINARY-APPEND
   :COROLLARY &lt;definitional&gt;  :BASICTS 3072  :LEAVES (...)
   :ALL-TPS (((:TYPE-PRESCRIPTION TRUE-LISTP-APPEND)
              ((TRUE-LISTP B)) 1152 (TRUE-LISTP (BINARY-APPEND A B)))
             ((:TYPE-PRESCRIPTION BINARY-APPEND)
              NIL 3072 (IF (CONSP …) 'T (EQUAL … Y)))))
```
Entry shape `(rune hyps basic-ts corollary)` — mirrors the 4/5/6-field entry shapes the gz linear/recog/rewrite collectors already use (`ld.lisp:5488, 5542, 5405`), so the parser idiom is shared. Same field added at **both** emitters (`defuns.lisp:12179`, `ld.lisp:5672`). Tag: extend the two existing `TRACE-LOG[emit/type-prescription]` purpose sentences; **no new `emit/` label ⇒ no round-trip-rule impact.** This arm also delivers item 2's "additive minor" for the 7 primitives with stored TPs, if the collector's predefined-gate is relaxed the way `gz-linear-rule-entries` was (`ld.lisp:5507-5512`).

### ⚠ THE UNLOCK CLAIM IS NOT SCOUT-VERIFIED — a SECOND, DRIVER-SIDE blocker sits behind it
**RECONSTRUCTED** (the frontier message is swallowed at `Harness.lean:847`, so I could not execute it):

QSORT's TP walk on leaf 1 → `tpWalkCallee` → with `TRUE-LISTP-APPEND` selected, hypothesis `(TRUE-LISTP B)` where `B = (CONS (CAR X) (QSORT (FILTER 'GTE (CDR X) (CAR X))))` → CONS arm → constrained 2nd arg → `tpWalkCall` → self-call arm → **`Provers.lean:847-848`**:
```lean
    unless totLiftable args[mIdx]! do
      throwFrontier m!"proveTp: self-call MEASURED argument not liftable {repr t} (frontier)"
```
`totLiftable t = (collectOpaques t).isEmpty` (`Totality.lean:28`). QSORT's measured argument is `(FILTER 'GTE (CDR X) (CAR X))` — `FILTER` is a world fn ⇒ opaque ⇒ **not liftable**. Today's chain frontiers *earlier* (at `Provers.lean:996`, the class-mismatch), so this second wall is currently unobserved.

**Honest claim: item 3 removes ONE of ≥2 blockers on `tp:QSORT`. Do not promise the 2 rows.** The residual is Lean-side (a non-destructor-argument self-call arm) and belongs to a driver arc, not the fork.

---

## ITEMS 4, 5, 6 — REMOVED FROM THE BATCH (negative results)

### 4 — G5 / `app_nil`: **not an emission gap, and not a frontier**
- `grep -rn "G5" ACL2Lean/` → **zero** frontier throws. The multi-literal restriction does not exist: `Replay/Driver/Waterfall/Induction.lean:237-256` is general in literal count `k` and does the full IH cross product.
- Both rows are green **and unconditional**: `Tests/driver-coverage.golden:11` and `:16`, `APP-NIL → REPLAYED ✓` with no `cond[…]`. The tree carries the 2-literal pushed clause, 3/4-literal scheme clauses, the IH substitution `X := (CDR X)`, and `CONS-CAR-CDR` from the gz snapshot (`01-multi-theorem.proof-log:566`).
- **Stale-label drift, three sites** worth a one-line fix by whoever next touches them: `ACL2Lean/Mirrors/Basics.lean:67`, `ACL2Lean/Imported/WaypointCatalog.lean:69` (and `:71` for rev-rev), `docs/plans/2026-08-13_basics-closeout-charter.md:38`. The machine-readable catalog was already corrected: `Imported/Waypoints/Catalog.lean:116` ("audit F7 corrected the stale G5 reason"). Origin: `TODO.md:3584` (2026-06-10); the wall fell at `TODO.md:3635`.
- Remaining work is decode/lift only (an `appNilReplayedCond` + the existing `Lifting.lean:144 trueListp_enc`).

### 5 — rev family: **not an emission gap; the "discharger frontier" label is also stale**
- `driver-coverage.golden:17-18`: `REV-APP → REPLAYED ✓`, `REV-REV → REPLAYED ✓` — **empty cond lists** (`Runner.lean:314`). REV-REV's `cond[total:(REV (REV X)), tp:REV]` is on a *standalone informational DP probe* (`Runner.lean:589`, golden line 2), not the theorem.
- Zero `[EMISSION-FRONTIER: black-box leaf …]` tags anywhere in the golden.
- Both halves of `Catalog.lean:121-122`'s `blockedOn` are historical: `tp:REV` cleared by commit `bcb181d`; `rule:CONS-CAR-CDR` has a working discharger at `Provers.lean:1367`.
- Real blocker: a Lean `corr_rev_enc`/`revL` kit (APP has one at `Imported/Lifting.lean:443`; REV has none). Decode layer.

### 6 — linear route: **purely driver-side**
- Fork has exactly two linear TRACE-LOG sites: `acl2/ld.lisp:5473` (gz snapshot) and `acl2/simplify.lisp:8695` (`emit/simplify-clause/linear-contradiction`, the discharge node). `grep -c structured` over `linear-a.lisp`/`linear-b.lisp`/`non-linear.lisp` = **0/0/0**.
- Fully consumed: `LinearRuleSpec` (`ProofLogTypes.lean:413`) → `Runner.lean:179` → `Ctx.lean:484` → `mkLinearHypType` (`Waterfall.lean:157`) → offered at `Harness.lean:686-753`.
- 6 rows carry `linear:` (golden `:93,97,99,101,128,153`). The per-application substitution is **reconstructed** by `oneWayMatch` against the emitted `max-term` — a ratified design point (`TODO.md:1356-1363`), not a gap. `omega` is irrelevant to these: `HOW-MANY-BAD-PAIRS-BNEXT` is a same-log replayed theorem (`bsort.proof-log:9236`, row green at golden `:95`); `ACL2-COUNT-CAR-CDR-LINEAR` rides the existing `acl2CountExec` kit.
- **Named conditional risk:** if the pending B4 ruling (`docs/plans/2026-08-12_master-plan.md:95`) chooses **per-clause** rune granularity for admission-path linear premises, emission *would* be needed at `acl2/defuns.lisp:1364`. That granularity was explicitly examined and ruled out (`docs/notes/2026-08-10_leftovers-fork-batch-review.md:87-89`). Absent a reversal, no fork work.

---

## ITEM 7 — SWEEP: what else is emission-classed

**165 `throwFrontier` sites** (Provers 56, Totality 51, Harness 30, ParametricInstantiate 15, Ctx 8, Induction 2, Node 1, Discharge 1, Coverage/Harness 1). The **(E)-classed** ones cluster tightly on items 1–3: `Provers.lean:609` (GAP-1), `:614`, `:799`, `:970`, `:976` (GAP-2), `:996` (the QSORT/BINARY-APPEND site). Everything else in Provers/Totality is (D).

### Live emission items NOT in the brief's list (verified at source)

| Item | Site | Status |
|---|---|---|
| **Ground-hypothesis relief with no record** | consumer `NodeCore/Node.lean:955`; fork region `acl2/rewrite.lisp:19030-19230` (6 `emit/relieve-hyp/*` origins exist: type-alist, known-true, ancestors, free-type-alist, ground-unit, ground-unit-search — none covers this) | **LIVE + PINNED.** `Tests/PatternPins.lean:88` pins verbatim: `rule DEFAULT-&lt;-1: hyp (NOT (ACL2-NUMBERP 'NIL)) has NO emitted relief record`. **Needs its own scout** — I could not identify which `relieve-hyp1` arm silently succeeds. Note the p6 pin *moved here* because the older linear-in-simplify gap was closed by `simplify.lisp:8695`. |
| **`:cong-rune` on abbreviation-expansion steps** | `acl2/induct.lisp:148,168,173` (`emit/abbreviation-expansion`); `geneqv-refinementp` returns the exact rune at `induct.lisp:102-114` | **OPEN**, `docs/BUGS.md:324-329`. *Half of that BUGS entry is now stale*: `:RULE-CLASSES` **did** land — `:DEFTHM … :CLASSES (:EQUIVALENCE)` is emitted (`qsort.proof-log:39`). Worth correcting the entry. |
| **`:PATH` at the 2e equal-self detail sites** | consumer `Replay/Driver/Preprocess.lean:583` — message names it: *"(frontier; emit :PATH at the detail sites)"* | OPEN, tracked follow-up |
| **A silent clause-close class** | `Replay/Driver/CoreSpine.lean:1225` — *"a different silent close class (frontier — emit it)"* | OPEN |
| **Guard-obligation proofs** | wrapper landed (`cov-verify-guards.proof-log` has 1 `VERIFY-GUARDS` event); the **obligation proof itself is still absent** — `ProofLog.lean` throws on it deliberately | OPEN, pattern map `:162-166` |
| **`add-literal` complement folds** | pattern map `:700-701` — *"complement folds (add-literal, never emitted)"* | OPEN |
| **must-be-true silent collapse** | `TODO.md:2727`, documented in `docs/BUGS.md` | OPEN |
| **Occurrence granularity** | pattern map `:236-240` (`cov-rewrite-cache`: *"a subterm occurring TWICE gets ONE recorded unfold"*). The literal string "occurrence-granularity" has **zero** repo hits — the `:LEAVES` half is fixed free by item 1 | partial |
| **P0 un-instrumented sites** | pattern map `:598-609`: rewrite-equal NIL/EQUALITYP forms (`rewrite.lisp:18089-98`), rewrite-if swapped-p (`:17726-37`), if-interp call-stack folds (`:3742-3849`), sublis-var display folds, rewrite-time FC contradictions | OPEN, deliberate backlog |

**Closed since last recorded (verified):** `cov-backchain-limit` (logs now carry `BACKCHAIN-LIMIT-LST`), `cov-force-round` prose leak (`grep -c "Modulo the following"` → **0**), `p6` linear-in-simplify.

**One documentation defect found:** `TODO.md:73-74` still reads `tp:ACL2-COUNT (×7 — non-world callees UNARY--/INTEGER-ABS on its leaves)`. `docs/plans/2026-08-12_tp-replay-charter.md:207-209` claims this was corrected, but `git show a3e838b --stat` shows that commit touched **only the charter**. The refuted diagnosis is still what a reader gets from TODO.md. (INTEGER-ABS **is** a world fn — I confirmed it has a defun body and a gz snapshot.)

---

## INTERACTIONS — items 1, 2, 3 are ONE mechanism

- **1 ∩ 2**: the *same* recursive collector (`tp-collect-if-leaves`) produces both the context-refined leaf verdict and the subterm verdicts — same walk, same type-alist, one function. Doing them separately would mean writing the walk twice.
- **1 ∩ 3**: independent code (collector vs. selector) but the **same event and the same parser change** — both alter `(:TYPE-PRESCRIPTION …)`, both at the same two emitters (`defuns.lisp:12179`, `ld.lisp:5672`).
- **3 ⊃ 2's minor arm**: emitting all stored TPs also emits the 7 primitives' TPs, if the collector's `predefined` gate is relaxed as `gz-linear-rule-entries` already was.
- **1 → the vacuous-branch device**: the `:VACUOUS` marker retires the "third clone" deferral the TP arc log names.

**Net: one collector rewrite (~40 lines, `defuns.lisp`), one selector generalization (~15 lines, `ld.lisp`), one event-field extension at two sites, one parser extension. That is the whole fork batch.**

---

## RECAPTURE BLAST RADIUS

- **Corpus: 91 books / 91 `.proof-log`s** — 11 `acl2_samples/sorting/` + 18 `recon-tests/` + 61 `pattern-tests/` + `simple`. **84 contain `:TYPE-PRESCRIPTION` events.**
- The parser hard-fails on the old leaf shape ⇒ **recapture is all-or-nothing, in the same commit.** `just recapture-all` (`Justfile:130`) is the correct single target; `check-log-provenance` (`scripts/check-log-provenance.sh`) requires every sidecar stamped at the current submodule HEAD, so a partial recapture fails loudly (incident I2).
- **Golden churn expectation: potentially wide.** Sharper leaf verdicts can make `tpEmittedLeafOk` pass where it failed, which changes `cond[…]` sets. Row-by-row diagnosis before repin, per standing discipline. **A `[DISCHARGE]`/cond flip anywhere outside the 10 known `tp:` rows is a mandatory stop.**
- **Known trap (from the item-I fix round, `acl2/` HEAD `f9d4a99b68`):** payload growth in a gz snapshot ballooned every `TAU-BASIS`-carrying world and pushed `sorts-equivalent` over `maxRecDepth`. Subterm verdicts are a **payload-growth change of exactly that class.** Budget for a trim round; the remedy class is emission-side payload trim, never collector surgery.
- **Gate trap (easy to miss):** if any *new* `emit/&lt;label&gt;` tag is introduced, `scripts/check-acl2-tags.sh:37` requires the label to be either a rewrite-step `:origin` or listed in the script's `direct` variable (line 37). **The sketches above deliberately introduce no new `emit/` label**, avoiding this — but a reviewer proposing a new event must add the label to that list or `just check-acl2-tags` fails.
- Standing rule: commit the fork **before** recapture (no artifact overwrites mid-gate).

---

## THE BATCH PLAN — one ordered change-set, one round-trip

**Fork changes (all in `acl2/`, one commit on `acl2-lean-output`):**

1. **`defuns.lisp:12022`** — rewrite `tp-collect-if-leaves` to thread the type-alist via `assume-true-false-rec`, mirroring `type-set-b.lisp:8246`; return per leaf `(term ts ruling-tests type-alist subterm-verdicts)`; emit `:VACUOUS` on the contradictory-context arm. Amend the `infra/tp-leaves` tag.
2. **`ld.lisp:5601`** — generalize `gz-definitional-tp` to `gz-all-tps`: keep the definitional selection for the existing field positions, return the full rune-keyed list for the new `:ALL-TPS` field. Amend the `infra/gz-tp-select` tag.
3. **`defuns.lisp:12179` + `ld.lisp:5672`** — add `:ALL-TPS` to both `fms` forms; amend both `emit/type-prescription` tags' purpose sentences.
4. *(optional, ~5 lines)* relax `ld.lisp`'s `predefined`-gate so the 7 stored-TP primitives snapshot too.

**Then, in order:** `commit-fork` → `just build-acl2` → `just recapture-all` → `just check-log-provenance` → `just check-acl2-tags` → parser extension (`ProofLog.lean:1134`) + storage (`ClauseTree.lean:98`, `:319`) + `TpKit` (`Provers.lean:569`) → golden review row-by-row → `just claim-gate` TRUE_EXIT=0.

**Scout-verified unlock claims (deliberately conservative):**

| Change | What it unlocks — verified | What it does NOT |
|---|---|---|
| Item 1 | INTEGER-ABS's 3 leaves certify (**executed**). `:VACUOUS` marker for the complex-rational branch. Leaf occurrence-addressing. | Does **not** by itself close `dis_acl2_count_tp` — needs the D-A/D-B closure ruling. |
| Item 2 | Removes the `Provers.lean:976` frontier for DENOMINATOR/NUMERATOR/REALPART/IMAGPART/COERCE by supplying ACL2's own per-occurrence verdicts (**probe-verified they exist**). | Same closure-ruling dependency. |
| Item 3 | Removes the `Provers.lean:996` class-mismatch on QSORT's BINARY-APPEND leaf. | **Does NOT close `tp:QSORT`** — a second, driver-side blocker (`Provers.lean:848`, non-liftable measured self-call argument) sits behind it. |

**Realistic scoreboard after the batch alone:** the 7 `sorry`s in `dis_acl2_count_tp` and the 10 main-row `tp:` conds (8× `tp:ACL2-COUNT` at golden `:128,129,136,139,140,148,149,152`; 2× `tp:QSORT` at `:149,152`) become **reachable, not retired.** The emission stops being the blocker; two Lean-side items become the blockers.

### DO NOT BATCH — needs a ruling first

1. **The fact-conditioned closure design (D-A vs D-B).** A meaning-level choice with a live drift risk. The emission is useful either way; the **consumer** must wait. *Recommendation: D-A (recognizer-tuples + ts-algebra), because D-B is per-case accretion.*
2. **The "emitted TP as a verdict-only DP-carve-out fact" alternative** (the TP arc's decision package). It closes ACL2-COUNT immediately but changes what the replay *means*. Not an executor call — and note that item 1 makes it *stronger* if chosen, since the leaf would arrive with its exact context.
3. **The ground-hypothesis-relief gap** (`Node.lean:955` / `PatternPins.lean:88`). Real, live, pinned — but I could not site the un-instrumented `relieve-hyp1` arm. **It needs its own scout before it can join any batch.**
4. **The B4 linear-class ruling.** Only a reversal of the per-admission granularity decision would create fork work; if that reversal is on the table, batch `defuns.lisp:1364` with this round-trip rather than paying a second recapture.