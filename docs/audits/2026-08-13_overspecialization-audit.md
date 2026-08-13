<!-- Recovered verbatim from the session transcript (agent final report,
     2026-08-13) and persisted 2026-08-13. Basis commit: main @ 4a600c8.
     Over-specialization audit (Opus-class, adversarial): F1-F20 ranked inventory over the generator/prover machinery.
     Findings feed the R-arc roadmap: docs/plans/2026-08-13_r-arcs-roadmap.md.
     Dated record — where terminology conflicts with docs/LEXICON.md, the
     lexicon wins. -->

Cleanup done (`.tmp/audit-probe` removed; nothing else written; no repo files modified).

---

# OVER-SPECIALIZATION AUDIT — ranked inventory

**Basis.** Read: `docs/LEXICON.md`, `docs/plans/2026-08-12_master-plan.md`, `docs/notes/2026-07-22_pattern-map.md`, CLAUDE.md. Code read in full: `Replay/Driver/Provers.lean`, `Replay/Lemmas/TpClosure.lean`, `Imported/SimGen.lean`, `MirrorProofs/IsoGen.lean`, `Mirrors/Sorting.lean`, plus targeted reads of `ExecGen.lean`, `Driver/Totality.lean`, `Driver/Harness.lean`, `BranchFacts.lean`, `Waypoints/Macro.lean`, `Tests/MirrorNameCheck.lean`, `Tests/WaypointCensus.lean`. Corpus evidence extracted from the real `.proof-log` artifacts and `Tests/driver-coverage.golden`.

**Verified by execution** (real elaborations, scratch files since deleted): F1, F3, F4, F5. **Verified by artifact extraction**: F6–F14, F20. **Verified by code read + spot-check**: the rest. **Explicitly reconstructed / not run**: F10's impact estimate (see its caveat) and F12's downstream consequence.

**A correction I owe up front.** My first pass counted `tp:ORDEREDP`/`tp:PERM`/`tp:MEMB` as blocked TP conditions and would have headlined a "20% of the B1 lever" figure. That was wrong — those are DP-leaf discharge conditions, not main-row. Stripping `[DISCHARGE:…]` from the golden gives the honest main-row census: **`tp:` = 10 (ACL2-COUNT ×8, QSORT ×2), `total:` = 38**. F10 is re-ranked accordingly, down from Tier 1 to Tier 2 with a latency caveat.

---

## TIER 1 — redesign-class, and the *next* arc walks into all four

The master plan's next move after the Basics exit is Phase A4 / Phase C: sorting mirrors at `Int`. Every one of these fires on the first declaration of that arc.

### F1. `mirror_iso%` requires **every explicit argument to be `List α`** — sorting's first square is rejected

- **Claim** (`IsoGen.lean:15-22`, header): "the SQUARES. Two classes, both measured off the hand file's six squares" — presented as the generator for mirror-level correspondence.
- **Actual bound** (`IsoGen.lean:285-293, 336-339`): `mirrorFnShape` computes `allList` over the explicit binders; `unless allList do throwError "… has a non-list argument — outside the derived square table (the argument reading is `List α` under `List.map`; a named frontier)"`. There is no per-argument reading table at all — the hom statement blindly wraps *every* var in `List.map e.enc` (`:391-397`).
- **Who hits it next**: `insertOrd (a : α) : List α → List α`, `howMany [DecidableEq α] (a : α) : List α → Nat`, `filterRel (keep : α → Bool)`, `Permuted`'s companions. `isort` itself is all-list, but its square resolution needs `insertOrd`'s registered square (`:400-407`), so `isort_map_hom` is unreachable.
- **Witness (executed)**:
  ```
  mirror_iso% insertOrd_map_hom for ACL2Lean.Sorting.insertOrd vars [a, xs] square hom list
  → error: mirror_iso%: ACL2Lean.Sorting.insertOrd has a non-list argument —
    outside the derived square table (the argument reading is `List α` under `List.map`; a named frontier)
  ```
- **Late-discovery cost**: mid-arc. The fix is not a row — it is SimGen's `raw`/`list` per-argument reading table, ported up one level, plus a `hom` statement builder that applies `e.enc` at element positions and `List.map e.enc` at list positions. Note the irony: `derive_sim%` (the layer *below*) already has this table (`SimGen.lean:237-248`); `mirror_iso%` was built in its image and dropped it.
- **Recommendation: GENERALIZE NOW.** ~½ day; it is the literal first line of the sorting mirror arc.

### F2. `Acl2Embed` has no order field — and the square closer is *structurally unable to consume one*

- **Claim** (master plan §"architecture question", route 1): "an embedding class (`Acl2Embed α`: injection into a fragment + **order compatibility**) + generic transport."
- **Actual** (`IsoGen.lean:98-108`): `structure Acl2Embed (α) where enc : α → SExpr; inj : …` — two fields, and the docstring concedes: *"The pathfinder needs nothing more (no order field — that dimension arrives with sorting)."* One instance exists (`intEmbed`).
- **The part that is not a field addition**: the hom square for any order-parameterized function is *false* without order compatibility (`map enc (insertOrd a xs) = insertOrd (enc a) (map enc xs)` needs `enc a ≤ᴬ enc b ↔ a ≤ b`). The square closer is `mirror_square_close` (`:169-174`): `first | rfl | simp_all only [six fixed rfl-lemmas, $xs,*]`, where `$xs` is **definitions only** — `IsoGen.lean:345-352` hard-errors on a lemma: *"`unfold [{n}]` is not a DEFINITION — the square closer unfolds definitions only. A LEMMA here would be exactly the content channel the template gate closes."* An order-restriction fact (`lexorder` on int atoms ≡ `Int.≤` — a CORE-LOGIC theorem, provenance source 2) **is a lemma**. It cannot enter.
- So the order dimension needs a *new admitted rung class* in the ladder — "core-logic restriction facts, registered per embedding" — with its own admission criterion, distinct from the current "every rung is a `rfl`-lemma" criterion the file pins with examples (`:151-163`). That is a design ruling, not an edit.
- **Same problem one level up**: `Ordered : List α → Prop` would be declared `hom scalar` (result not a list, so the drift check at `:366-370` passes), producing the statement `Ordered (map e.enc xs) = Ordered xs` — a **propositional** equality. The ladder has no `propext`/`Iff` rung either.
- **Recommendation: GENERALIZE NOW, but as a RULING first.** The ladder's admission criterion is the file's stated trust argument; widening it silently would dissolve exactly the gate the thin-Lean ruling installed. This is the single highest-stakes item in the report.

### F3. `mirror_transport%` assumes the spec Prop is `Type → Prop` with **no typeclass parameters** — all 14 sorting Props fail at step one

- **Actual** (`IsoGen.lean:492-496`): the crossing type is built as `` `($(mkCIdent specName) $sexprC) `` and elaborated. No instance argument is supplied or synthesized.
- Every sorting Prop is `(α : Type u) [TotalOrder α] [DecidableEq α] : Prop`. Elaborating `isort_ordered SExpr` requires `TotalOrder SExpr`. **No `TotalOrder` instance exists anywhere in the repo** — `grep` over `ACL2Lean/` + `Tests/` returns only the class decl and two derived `LT`/`DecidableRel` instances.
- **Witness (executed)**:
  ```
  mirror_transport% isort_ordered_int : ACL2Lean.Sorting.isort_ordered Int …
  → error: failed to synthesize instance of type class TotalOrder ACL2.SExpr
  → error: mirror_transport%: ACL2Lean.Sorting.isort_ordered at SExpr is not a
    quantified statement (frontier — the transported spec is a `∀`-statement over lists)
  ```
- **Cost**: the `TotalOrder SExpr` instance (from `lexorder` + `LexorderOrder.lean`) is already a named master-plan A4 deliverable, so *that* part is planned work. The generator-side part — accepting an instance-parameterized spec and threading the instance through both rungs — is not planned and is invisible until attempted.
- **Recommendation: GENERALIZE NOW** (small: elaborate `spec SExpr` with instances allowed to be synthesized *after* the core-logic instance lands, and thread `elemTy`'s instance into the mirror rung).

### F4. `mirror_transport%`'s binder table (`List SExpr` only) + conclusion table (list-eq / scalar-eq) covers **0 of the 14** sorting Props

- **Actual**: `IsoGen.lean:500-506` walks the telescope and throws unless *every* binder is `List SExpr`; `:507-509` rejects a residual `forall` body; the closer (`:185-191`) is `simp only […] at h; first | exact h | exact map_inj e h` — exactly two conclusion paths.
- **Prop-by-Prop** (after F3's instance is supplied):

| Prop | binders | conclusion | verdict |
|---|---|---|---|
| `isort/msort/qsort/bsort_ordered` (4) | `[xs]` ✓ | `Ordered (sort xs)` — a Prop, not an eq | closer has no rung |
| `isort/msort/qsort/bsort_perm` (4) | `[xs]` ✓ | `Permuted …` — a Prop | closer has no rung |
| `ordered_perm_unique` | `[xs, ys, h₁ : Ordered xs, h₂, h₃]` ✗ | — | **binder check** |
| `sorts_agree` | `[xs]` ✓ | 3-way **conjunction** | closer has no rung |
| `sorter_unique` | `[f : List α → List α, …]` ✗ | — | binder check |
| `perm_iff_howMany` | `[xs, ys]` ✓ | **iff** | closer has no rung |
| `permWitness_complete` | `[xs, ys]` ✓ | conj of iff + bounded ∀ | closer has no rung |

- **Witness (executed, with a scratch sorry'd `TotalOrder SExpr` to get past F3)**:
  ```
  mirror_transport% opu_int : ACL2Lean.Sorting.ordered_perm_unique Int …
  → error: mirror_transport%: ACL2Lean.Sorting.ordered_perm_unique binds a
    non-`List SExpr` argument — outside the derived transport table
    (a named frontier: every binder is encoded by `List.map`)
  ```
- **The structural point**: hypotheses are not just "one more binder shape". A hypothesis must transport **contravariantly** (`Ordered xs → Ordered (map enc xs)`), i.e. the hom squares must be usable in *both* directions. The current simp set fixes a direction per class (`←` for `homList`, `→` for `homScalar`, `:536-543`). That is a redesign of the transport's rewrite discipline.
- **Recommendation: GENERALIZE NOW** — and it is a *design* item (the hypothesis/iff/conjunction rungs), not three table rows. This is what actually gates Phase D ("every Prop in Mirrors/Sorting.lean is a theorem").

### F5. Both generators' template-failure errors **assert a specific diagnosis that is false** in the failure modes above

- `mirror_iso%:424-434` states the failure means "THE DECLARED CORRESPONDENCE DOES NOT ALIGN WITH `{fn}`'S OWN RECURSION … no library lemma about our names exists and no induction clause or default simp set could have closed it either." Under F2 the correspondence is *correct* and the closer simply lacks the rung.
- `mirror_transport%:565-572` states the failure means the agreement squares don't carry, or a hom square is missing. Observed (executed, `isort_ordered`): the real errors were `simp made no progress` + `introN failed` + a missing instance, and the emitted narrative named neither.
- **Why this matters at claims tier**: the message is the project's *record* of why a frontier exists. A confidently wrong frontier message is how a redesign gets mis-filed as "the reading was misaligned" and papered over per-case — exactly the carve-out-drift failure mode.
- **Recommendation: GENERALIZE NOW** (cheap): make both messages state the *observed* residual goal / first error and list the candidate causes, rather than asserting one.

---

## TIER 2 — table-class but large; blocks the master plan's named levers B1/B2

### F6. `proveTotality`'s measure gate accepts exactly ONE shape — and **100% of the main-row `total:` debt is blocked by it**

- **Actual** (`Provers.lean:108-131`): `wfRel` must be `O&lt;`; `measuredSubset.length == 1`; `measure` must be **syntactically** `(ACL2-COUNT &lt;that formal&gt;)`; an `(O-P …)` clause must be present. Mirrored in `proveTp` (`:1133-1146`).
- **Measure shapes already in the captured corpus** (extracted from the logs): `(ACL2-COUNT f)` ✓, `(BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y))`, `(LEN X)`, `(BNEXT-SIZE X)`, `(NFIX N)`, `(ABS (IFIX I))`, `(ABS (FLOOR X Y))`; `:WFREL` `MY-LT` (`cov-wf-relation`). Measured subsets of size 2: `:MEASURED (Y X)` ×8.
- **Main-row `total:` census (38), with blocker**:

| condition | ×  | blocker |
|---|---|---|
| `total:O`, `total:O-P` | 18 | ACL2 ordinal bootstrap (genuinely hard; out of scope) |
| `total:BNEXT` | 10 | measure `(LEN X)` — shape gate |
| `total:MERGE2`, `total:INTERLEAVE` | 6 | measure `(BINARY-+ …)` **and** `:MEASURED (Y X)` length 2 |
| `total:MSORT`, `total:BSORT`, `total:QSORT` | 9 | M3 decreases through defined fns (`EVENS`/`ODDS`/`FILTER`); BSORT also measure `(BNEXT-SIZE X)` |
| `total:ZIP3` | 1 | F7 below |

- **Who hits it next**: already hit — this *is* master-plan B2 (`with_termination` coverage, REQUIRED class, 5 debt sorries). The arithmetic backlog adds `(NFIX N)` (pattern map P1 names it explicitly) and the `ABS/FLOOR` family.
- **Recommendation: GENERALIZE NOW for the sum-measure + multi-measured-formal case** (it is the single largest table cell, 6 conditions plus every future 2-recursion merge); **TABLE-ROW-WHEN-HIT** for `MY-LT` and the `ABS` shapes.

### F7. 3-ary totality requires the measured formal to be the **second**; 3-ary TP accepts first *or* second

- `Provers.lean:228-230`: `unless measuredFormal == f2 do throwFrontier "proveTotality: 3-ary measured formal {…} is not the second formal (frontier)"`. Only `totality_3_rec_snd_mu` exists (`Judgments.lean:1790`); there is no first-formal twin.
- `Provers.lean:1290-1296` (TP): accepts `mIdx3 ∈ {0,1}` via `tp_3_rec`/`tp_3_rec_snd`.
- **Witness (in-corpus)**: `recon-tests/16-three-way`, `(:DEFUN ZIP3 :FORMALS (X Y Z) … :MEASURE (ACL2-COUNT X) :MEASURED (X))`. Its TP corollary is `(TRUE-LISTP (ZIP3 X Y Z))` (`:BASICTS 1152`, leaves `1024/128/128/128`) — a recognized class whose walk would go through; totality frontiers first. Already tracked in `TODO.md` with the probe-verified message.
- **The over-fit signature**: the position restriction was fitted to `FILTER`/`ALL-REL`'s `(fn x e)` shape; the comment says so (*"other positions stay frontier until a book demands them"*). A book demanded them (ZIP3, in the recon corpus since before the arc) and the asymmetry with the TP twin means the two provers now disagree about what 3-ary means.
- **Recommendation: TABLE-ROW-WHEN-HIT is already overdue** — one lemma (`totality_3_rec_fst_mu`) + one branch. Do it with F6.

### F8. The recorded-termination escape hatch is **silently disabled at arity ≠ 1**

- `Provers.lean:137`: `let recTerm? := if formals.length == 1 then recTerm? else none`. Justified by audit F4 (a mismatched μ would abort untagged) — sound, but it means the *general* escape from F6 is unavailable to `MERGE2`/`INTERLEAVE` (2-ary, and precisely the two whose measure shape needs it).
- Also: `Provers.lean:253-261` still branches on `recTerm?` inside the 3-ary arm, which line 137 has already forced to `none` — dead code that reads as coverage.
- **Recommendation: GENERALIZE NOW** alongside F6 (the arity-2/3 μ-typed wrapper lemmas), or at minimum delete the dead 3-ary branch so the arity-1 restriction is legible.

### F9. A hard **arity-3 ceiling** runs through the whole driver, and the corpus's max defun arity is exactly 3

- `bindArgsVarProofs` (`Provers.lean:32-49`) has arms for 1/2/3 then `throwFrontier "{who}: arity {n} unsupported"`. Same at `proveTotality:106,266`, `proveTp:1217,1328`, args-valued `:1187`. Lemma family stops at `totality_3_of_body` / `tp_hyp_3_of_body` / `convP_defn_3`. Decode side: `conv_builtin1`/`conv_builtin2` only — no `conv_builtin3`.
- Non-recursive `proveTp` stops at **arity 2** (`:1217`) while recursive `proveTp` goes to 3 — another internal asymmetry.
- **Who hits it next**: `qsort.lisp`'s included arithmetic world already contains 5-formal defuns (`BAG-LEAVES LEAVES MFC STATE INTP-BAGS NON-INTP-BAGS`); the user-book tier will hit 4-ary routinely.
- **Recommendation: TABLE-ROW-WHEN-HIT**, but note it is 4 registries at once (bindArgs, totality, tp, conv_defn) — budget accordingly, and consider an n-ary `bindArgs` lookup instead of a fourth positional triple.

### F10. `TpCorClass` (5 shapes) misses the corpus's **most common** corollary shape — with a real caveat about when it bites

- **Class table** (`Provers.lean:373-396`): `nonNegInt` (7) / `consp` (3072) / `trueListp` (1152) / `conspOrNil` (3200) / `conspOrArg` (3072-with-residue-formal). `tpCorClass?` (`:456-473`) is exact-shape match; anything else → `none`.
- **Corollary shapes actually emitted across the corpus** (counts = occurrences of that exact shape):

| `:BASICTS` | shape | count | class? |
|---|---|---|---|
| **384** | `(IF (EQUAL (f …) 'T) 'T (EQUAL (f …) 'NIL))` — **boolean** | **the plurality** (79 for `NOT` alone; `MEMB`/`PERM`/`ORDEREDP`/`ALL-REL`/`REL`/`SET-EQUAL`/`SUBSETP-EQUAL`/`DUPP`/`EVENP`/…) | ✗ |
| 7 | non-neg int | many | ✓ |
| 1152 / 3072 / 3200 | true-list / cons / cons-or-nil | many | ✓ |
| 3072 | `(IF (CONSP (BNEXT X)) 'T (EQUAL (BNEXT X) X))` — **1-ary args-valued** | bsort | ✗ (F10b) |
| 3072 | `(IF (CONSP (MERGE2 X Y)) 'T (IF (EQUAL … X) 'T (EQUAL … Y)))` — **3-way** | msort | ✗ |
| 1024 | `(IF (CONSP (f …)) (TRUE-LISTP (f …)) 'NIL)` — proper-cons | ~15 arith fns | ✗ |
| 23 / 127 | `(INTEGERP (FLOOR I J))` / `(ACL2-NUMBERP (EXPT R I))` | FLOOR/CEILING/ROUND/TRUNCATE/ASH/MOD/REM/EXPT/IFIX/FIX | ✗ |
| 6 | `(IF (INTEGERP …) (&lt; '0 …) 'NIL)` — positive int | `NUMBER-OF-ADDENDS` | ✗ |
| 5248 / 640 / 279 / 255 / 0 / −49 | list-or-string, symbol-or-nil, identity, complement… | scattered | ✗ |

- **THE CAVEAT (this is why F10 is Tier 2, not Tier 1)**: the boolean class is *currently invisible*. `kit.cls` is consulted only at three sites — the 2-ary-primitive return-path arm (`:732`), `tpWalkCallee` (`:966`), and the residue-variable arm (`:788`). Every boolean-class fn in the corpus has the ACL2 list-recognizer idiom — return paths are **only quote-leaves and self-calls** (verified: `ORDEREDP`, `MEMB`, `PERM`, `ALL-REL`, `SUBSETP-EQUAL`, `INTERSECTP-EQUAL`, `DUPP` bodies) — so the walk succeeds with `cls = none`. `dis_all_rel_tp` was retired at increment 4 for a 384-class fn, confirming this.
- **When it bites** (the falsifying shape, *reconstructed* — I did not find one in the current corpus): a boolean fn whose return path is a call or a 2-ary primitive. `(defun equal-sets (a b) (if (subsetp a b) (subsetp b a) nil))` → the then-leaf is a callee call → `tpWalkCallee` → `throwFrontier "proveTp: return-path call to SUBSETP-EQUAL under an UNRECOGNIZED corollary class for EQUAL-SETS (frontier)"`. Likewise any `(defun less (a b) (&lt; a b))`.
- **Arithmetic is next per the brief**, and `INTEGERP`-class (23) / `ACL2-NUMBERP`-class (127) results *are* the arithmetic return-path shapes, with `BINARY-*`/`UNARY--` at the leaves — those are the classes that will be needed by shape, not by accident.
- **Recommendation: TABLE-ROW-WHEN-HIT for boolean** (genuinely cheap: one constructor + `tsMask 384` + one `tpCorClass?` arm; no closure lemma needed until a primitive leaf appears). **GENERALIZE NOW for `integerp`/`acl2Numberp`** if arithmetic is the next book family, since those come with F11 as a package.

### F10b/F11. The `(class × primitive)` closure registry covers **2 primitives of `dpBinary`'s 9**; args-valued mode is 2-ary-measured-first only

- `tpClosure2` (`Provers.lean:509-517`): 5 entries, over `BINARY-+` and `CONS` only. `dpBinary` has `EQUAL, &lt;, LEXORDER, BINARY-+, BINARY-*, COERCE, CONS, IMPLIES, IFF`. A `(BINARY-* …)` return path under `nonNegInt` → `throwFrontier "proveTp: return-path BINARY-* has no value-closure lemma for the nonNegInt corollary class (frontier)"`.
- `tpClassImp` and `tpClassImpAv` have **one entry each**.
- Args-valued mode (`:1147-1188`): 2-ary, measured on the **first** formal, else frontier. `BNEXT` is the corpus's other args-valued fn and is **1-ary** → `"proveTp: args-valued arity 1 unsupported (frontier)"`. `tp:BNEXT` appears 6× in the golden's discharge conditions.
- The 2-ary-primitive arm's *pattern* is `.cons fs (.cons a (.cons b .nil))` — 1-ary and 3-ary primitives on a return path have no arm at all and fall through to the callee arm, which then rejects them as "not a world fn".
- **Recommendation: TABLE-ROW-WHEN-HIT** for closures (each is one small lemma); **GENERALIZE NOW for args-valued arity 1** (BNEXT is a named bsort blocker, master-plan B4-adjacent).

---

## TIER 3 — the waypoint generators (Track FREE's "nearly free" claim)

### F12. `derive_exec%`'s `builtinTwins` = **7 rows**, and the recon corpus's arithmetic defuns use five heads that aren't in it

- `ExecGen.lean:174-181`: `CONSP, EQUAL, CAR, CDR, CONS, LEXORDER, BINARY-+`. Fail-closed at `:332-334`: *"head symbol {n} is not IF/QUOTE, a v1 builtin twin, the function itself, or a registered exec kit (frontier — extend the table or hand-write the kit)"*.
- **Head counts in `recon-tests/*` + `simple` defun bodies**: `&lt;` **87**, `INTEGERP` **71**, `LEN` **48**, `UNARY--` **16**, `ZP` **4**, `BINARY-*` **2** — none in the table. (`dpUnary` on the driver side has 25 entries including all of these; the two registries have diverged.)
- **Consequence for the Track FREE acceptance test** (master plan: "import a book we have NEVER imported … with ZERO hand Lean"): a sorting-adjacent book that compares with `&lt;` instead of `lexorder` — the single most likely variant — cannot generate an exec kit.
- **Recommendation: GENERALIZE NOW** — these are literally one row + one `callBuiltin_*` bridge each, and the acceptance test is the plan's own definition of done for Track FREE.

### F13. Measure classes **M1/M2 only**; M3 is 7 hand kits

- `MeasureSpec` (`ExecGen.lean:368-371`): `m1 (idx)` = `(ACL2-COUNT formalᵢ)` with destructor-chain recursion; `m2 (i,j)` = sum-of-two-counts with single-CDR one-side decreases. M3 (decrease through a defined fn) hard-errors; the header names the victims (`msort`'s `EVENS`, `qsort`'s `FILTER`).
- 7 live `register_exec_kit%` sites (MEMB, RM, PERM, PERM-COUNTER-EXAMPLE, BINARY-APPEND, MSORT, QSORT, BNEXT).
- **Note the cross-layer asymmetry**: `derive_exec%` *has* M2 (merge2's shape); `proveTotality`/`proveTp` do **not** (F6). Same measure, two tables, opposite answers.
- **Recommendation: as scheduled (master-plan B6, "M3+ measure shapes")** — but unify the M2 row with F6 so the two layers stop diverging.

### F14. `derive_sim%`'s reading tables: **2 argument readings, 5 result readings** — no product, option, or nested-list reading

- Arguments (`SimGen.lean:237-248`): `raw` (bare `SExpr`) or `list` (`List SExpr` under `enc`). Nothing else; `throwError "reading {kind} … is outside the derived table"`. A `Nat`/`Bool`/`Int`-typed native argument is unrepresentable.
- Results (`:358-392`): `allowed = [enc, boolEnc, SExpr.atom, cond]` plus the raw-element reading admitted *by result type* (`t.isConstOf ACL2.SExpr`).
- **Who hits it next (brief item 6)**: `zip` returns **pairs**. A native `zipL : List α → List β → List (α × β)` has result head `List`/`Prod` — outside the table. `ZIP3` returns a list of 3-lists; representable only as `enc (List.map enc xss)`, which puts a nested `enc` under the closer's fixed enc-normal-form kit (`enc_cdr/enc_car/enc_cons/…`, `:104-129`) — those lemmas are stated for `enc : List SExpr → SExpr`, so the nested layer is not normalized and the closer will not converge.
- The closer's leaf rungs are `rfl | omega | grind` — `omega` covers the integer readings; there is no rational/`Rat` rung (the pattern map has rationals `frontier-pinned`).
- **Recommendation: TABLE-ROW-WHEN-HIT for `Prod`** (add a `pair` argument/result reading + its enc lemmas); **fine-as-is** otherwise.

### F15. **Mutual recursion is a hard frontier in all three generators** — and the pattern map marks it `corpus`

- `derive_sim%:268-274` and `:353-357` (exec side and native side); `mirror_iso%:328-331`. `derive_exec%` inherits the same limit via its single-function induction.
- `recon-tests/07-mutual-recursion` is in the corpus and its `termination:MY-EVENP` is a main-row failing condition today. Anything `evenp`/`oddp`-shaped in a user book kills all three generators simultaneously.
- **Recommendation: TABLE-ROW-WHEN-HIT** — but note it is *three* independent frontiers, so the discovery is triple-cost. Log it as one item, not three.

---

## TIER 4 — the decode / waypoint layer

### F16. 44 hand decodes, **zero generation**, and the pattern's assumptions are all corpus-shaped

- 45 `*_of_replayed` (44 per-theorem + 1 generic ender). All 44 are sorting- or basics-corpus theorems; **no pattern-test book has one**.
- **Hypothesis-count distribution** (ACL2-side conjuncts): 0→23, 1→14, 2→5, 3→1, 4→1. Max Lean-side bound hyps: 3.
- **Conclusion-shape distribution**: `(EQUAL a b)` → 25 (the one generic ender, `native_of_replayed_equal`, which hard-codes `equalT lhs rhs`); non-equality predicate → 16 (each ad hoc); `(IFF …)` → 1; `(&lt; …)` → 1; nested-IF conjunction tower → 1.
- **Single-literal root clause is assumed, never checked at the decode.** No decode mentions `disjoinTerm`; each pins `hreplayed` to a hand-written `*Formula : SExpr` constant, and the pin works only because `disjoinTerm [l] = l`. A multi-literal root would produce `(IF l₁ 'T (IF l₂ 'T …))` and no `*Formula` in the repo has that shape.
- **Env is a hand-built `insert` chain, ≤ 3 variables**, with `if_pos`/`if_neg` proof chains whose length equals the variable index. No n-ary builder.
- **Hypotheses are hand-nested `conv_if_true`**; the 4→2 reduction on `ordered-perms` relies on **type absorption** (dropping `(TRUE-LISTP X)`/`(CONSP X)` because the native quantifies over the `enc` image). That is a property of *this* corpus (true-listp everywhere), not a mechanism.
- **Shapes present in the corpus with no decode**: `defun-sk` (recon frontier), `p4-iff-or-shape` (the decorrelated IFF book), `p2-beta-equiv-iff`, `equisort3`'s **5 FORCEd hypotheses**, the three `:functional-instance` capstones, `no-dups-qsort`'s 2-hyp `double-rewrite`.
- **Recommendation: as scheduled (master-plan B6, "the decode-assembly generator")** — but the generator's *requirements* should be read off this distribution, not off the 25-decode equality majority. The 16 predicate-conclusion decodes and the ≤3-variable env chain are where the generality actually has to come from.

### F17. **A false generality claim in the shared library** (claims-tier defect)

`ACL2Lean/Imported/Lifting.lean:1033-1037`, verbatim:
&gt; `/-! ## Decode-kit v2 (sorting-absolute 1d — promoted from Sorting.lean's privates at 3+ consumers each: the boolEnc conjunction ladder (conv_if3), the false-branch collapse (conv_if_false'), the EQUAL/IFF Bool readings (toBool_equal, bool_of_iff_truthy, eq_of_iff_truthy_two_valued)). -/`

Measured call sites outside the defining block (I re-ran this myself as a spot-check):

| lemma | sites | claim |
|---|---|---|
| `conv_if_false'` | 11 | ✓ |
| `toBool_equal` | 9 | ✓ |
| `conv_if3` | **1** | ✗ |
| `bool_of_iff_truthy` | **1** | ✗ |
| `eq_of_iff_truthy_two_valued` | **1** | ✗ |

Three of five were promoted at **n = 1**, under a header asserting "3+ consumers each". This is the over-fitting phenomenon in its purest form — a one-use bespoke lemma filed as shared infrastructure — and it is also a factual over-claim in a docstring, which is a claims-tier item under the two-standard rule. **Recommendation: correct the header** (state the real counts, or split the two genuine promotions from the three one-use enders). CLAUDE.md's own extraction rule is "extract only what exists in 2–3 concrete copies."

### F18. Dependency offers **silently drop** multi-literal Goal clauses

`Harness.lean:571-575` (and repeated for cong / usefi / equivfull / tpthm): `match root.inputClause with | [f] =&gt; some {…} | _ =&gt; none`. A dependency theorem whose Goal clause has ≥ 2 literals is not offered as a hypothesis — no frontier, no message. Fail-closed downstream (the consumer will just miss a fact), but silent. **Recommendation: TABLE-ROW-WHEN-HIT**, with a logged frontier rather than a silent `none`.

---

## TIER 5 — `BranchFacts` and the linters/census

**Note on standard**: per the two-standard rule these last two are *speedbumps*, so the right question is "does it catch the honest mistake / could we delete it", not "can it be evaded". I report their coverage bounds because the brief asked whether they will silently under-cover — but the disposition I recommend is *not* hardening.

### F19. `BranchFacts` knows exactly **three recognizers**, and that is co-extensive with the set of termination proofs that currently replay

- `recogView` (`BranchFacts.lean:37-43`): `CONSP` (true-sense), `ENDP`/`ATOM` (false-sense). Unary applications only. IF normal forms: `(IF a a c)` (by structural `a == b`) and `(IF a b 'NIL)` (by `c == quoteNil`); anything else → `false`.
- **Corpus survey** of admitted defuns: as IF-test heads — `CONSP` 49 books, **`ZP` 5**, **`INTEGERP` 4**, `RATIONALP`/`SYMBOLP`/`STRINGP` 1 each. In `:TERMINATION-CLAUSES` — `CONSP` 28, `ENDP` 13, `ATOM` 7, **`ZP` 5**.
- **Why `ZP` has never forced an extension**: in all 5 ZP books ACL2 emits the ruler `(ZP N)` *and* the body test is `(ZP N)`, so the direct-equality rule covers it — no duality needed. And none of those books reach `BranchFacts` anyway: their termination proofs fail upstream (`06-measure`, `07-mutual-recursion`, `11-custom-measure` all die at `replayRecognizer: value of (CONSP (IF (INTEGERP N) …)) does not reduce to NIL`; `CD2-BOUND` at `μ-registry: unary measure head NFIX not registered`). **The triple looks general because nothing else has been allowed to reach it.**
- **A fourth duality is already in the corpus, unhandled**: `COMMON-FACTORS`/`COMMON-FACTORS-AAA` emit the ruler `(NULL FACTORS)` against the body test `(EQUAL FACTORS 'NIL)` — a spelling mismatch `recogView` cannot bridge.
- **Clone divergence (engineering)**: `Totality.lean:692-700`'s `endpDualOf` on the recorded-termination route knows **`ENDP` only, not `ATOM`** — it did not receive the 2026-08-13 ATOM-leg extension `recogView` got. Its own comment records the previous instance of exactly this bug (*"audit F1 — this gate's siblings got it, this one didn't and the whole route was dead"*). This is CLAUDE.md's "a fix applied to one clone silently missing its twin", live, in the same file as the shared rule it declines to call.
- **Also**: `Totality.lean:555-565` carries a hardcoded "MERGED-IH complementary pair" special case accepting only the literal pattern `[[l₁], [l₂]]` with `l₁ == (NOT l₂)`, whose comment names its originating book (`how-many`). A per-case accretion sitting one line below the general rule.
- **Recommendation: `endpDualOf` → call `recogView` (GENERALIZE NOW, one line, it is a live divergence bug).** Recognizer table: **TABLE-ROW-WHEN-HIT** (it is genuinely one-sided and fail-closed). The `NULL`/`(EQUAL x 'NIL)` duality: table row when the arithmetic books are wired.

### F20. `MirrorNameCheck`'s fixed carrier list (7) + non-recursive `readDir`

- `carriers = [List, Option, Nat, Int, Bool, Prod, Function]`; `libRoots = [Init, Lean, Std, Batteries, Mathlib]`. Each spec name is tested against 8 candidates.
- The brief's four shapes: Nat / Int / pair are **covered**; **tree is not** (no tree carrier). Also absent: `Multiset`, `Finset`, `Set`, `String`, `Char`, `Array`, `Vector`, `Rat`, `Ordering` — and dependencies outside `libRoots` (`Aesop`, `Qq`, `Plausible`) are not collisions.
- Coverage arm enumerates **files** via a **non-recursive** `readDir` filtered on `extension == "lean"`, so a future `ACL2Lean/Mirrors/Sub/Foo.lean` is silently uncovered. Nested declarations are excluded by `!env.contains c.getPrefix`.
- The file is admirably honest about all of this (*"THREAT MODEL … this is a SPEEDBUMP, not a gate"*, *"If it ever becomes fragile or wrong, DELETE IT"*).
- **Recommendation: FINE-AS-IS.** Add carriers opportunistically when a spec file introduces one; do not build a general resolver.

### F21. `WaypointCensus` — namespace list of 2, classification by **name affix**, no enforcement

- `nss = [ACL2.Worlds, ACL2.Lifting]`. Classes: `_of_replayed` / `dis_`+`drv_` / `_exec_corr` / `_enc` / `world_has_`+`world_no_`, plus a drop list; everything else → `other`. Never inspects `ci.type`.
- **Silently outside the census**: `ACL2.Spike.Flatten`, `ACL2.Spike.Interleave` (including two `*_replayed` theorems), `ACL2.SimGen` (the whole `enc_*` family), `ACL2.ExecGen`. Note `_enc` is a *suffix* class while `SimGen`'s lemmas are `enc_*`-*prefixed* — two conventions, one class.
- Unmatched → an `other` bucket printed via `logInfo`; **nothing here can fail the build** (deliberate — the enforcing version was demoted at the 2026-08-11 gate-cruft review).
- Any rename silently re-classifies (`foo_of_replayed` → `replayed_foo` moves decode→other with no signal but a number).
- **Recommendation: FINE-AS-IS or DELETE.** It is already a watched number by design. If it is kept, widening `nss` is one line and restores the signal for `Imported/`; that is the only change worth making.

---

## Cross-cutting patterns (the phenomenon itself)

1. **Two registries for the same concept, silently diverged.** Four instances found: `builtinTwins` (7) vs `dpUnary`+`dpBinary` (25+9); `ExecGen`'s M2 measure class vs `proveTotality`'s measure gate (no M2); `proveTotality`'s 3-ary measured position (second only) vs `proveTp`'s (first or second); `recogView` (CONSP/ENDP/ATOM) vs `endpDualOf` (ENDP only). Each pair was extended on one side by the arc that needed it.
2. **A generator built "in the image of" a lower one that dropped the lower one's generality.** `mirror_iso%` was explicitly modelled on `derive_sim%` (`IsoGen.lean:6-9`) yet has no per-argument reading table, which `derive_sim%` has had since it was written. The imitation copied the *template-failure* discipline and not the *shape* discipline.
3. **Frontier messages that assert a cause.** F5, and the `mirror_transport%` transport-rung message. When the cause is wrong the record is wrong, and a redesign gets filed as a per-case misalignment.
4. **Promotion-at-n=1** (F17), with a docstring asserting n≥3. The clean counterexample to the codebase's own de-duplication rule.
5. **The narrowness is exactly the shape of what is currently green.** F19 is the sharpest instance: the recognizer triple covers precisely the termination proofs that reach it, because everything else fails upstream. This is the structural reason over-fitting is invisible from inside the green scoreboard — the gate table and the passing set are computed from each other.

## What I could not verify

- **F10's forward impact is reconstructed, not observed.** I found no current corpus fn whose boolean-class TP walk actually frontiers; my witness shape (`(defun equal-sets (a b) (if (subsetp a b) (subsetp b a) nil))`) is authored, not captured. The honest statement is: the class is absent, the absence is currently masked by the ACL2 list-recognizer idiom, and it will surface the first time a boolean fn returns a call or a primitive.
- **F12's downstream consequence** (that an arithmetic sorting variant cannot generate a kit) follows from the table + the head counts; I did not run `derive_exec%` on such a book.
- I did **not** run the full `just ci` or `driver-coverage`; all coverage figures are read off the committed `Tests/driver-coverage.golden` at `4a600c8`, and the main-row/discharge split is my own derivation from that file.
- I did not audit `Replay/ParametricInstantiate.lean` (the encapsulate/order-generic lane, master-plan route 2) beyond noting it re-enters `proveTp` and therefore inherits F6–F11.

## Suggested arc ordering, from the above

1. **F5 + F19's `endpDualOf`** — hours, and F19's is a live divergence bug.
2. **F1 + F3** — the two blockers on line one of the sorting mirror arc; both mechanical.
3. **F2 + F4** — bring as a *ruling* (the ladder's admission criterion; the hypothesis/iff/conjunction rungs) before writing code. These are what gate Phase D.
4. **F6 + F7 + F8** — one item: the measure/arity table in `proveTotality`, unified with `ExecGen`'s M2. Retires the entire non-ordinal main-row `total:` debt and is master-plan B2.
5. **F12** — three or four rows; unblocks the Track FREE acceptance test.
6. Everything else: table-row-when-hit, logged now so the discovery is a row and not a redesign.