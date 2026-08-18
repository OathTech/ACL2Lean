# The zero-ruling broadening lane — capability landed, products NOT admitted (2026-08-18)

Branch `mdd/r4-broaden`, from `dc1cadd` (R4 wave 2f). Lane goal: widen the
decode layer past its EQUAL-only frontier and take the corpus's cheapest
untouched whole books end to end.

**Outcome in one line: the MACHINERY and the METRIC landed; NEITHER
candidate product was admitted to the shop window.** This note is the
permanent record of both halves — including the two draft `Prop`s
verbatim, so that if the product bar ever moves, re-admission is a paste
rather than a re-derivation.

---

## 1. THE NON-ADMISSION DECISION (Mike, at the lane's checkpoint)

Two `Prop`s were drafted, proved via replay trio-clean, and presented for
the shop-window bless. **Both were refused.**

Mike's rationale, as applied by the orchestrator: *the aim was to expand
the PRODUCT — idiomatic top-level Lean mirrors worth reading. Books whose
theorems are trivial, equivalent to existing Props, or without
Lean-interesting content don't earn shop-window space, however cheaply
they green.* `app_nil_twice` is a visible corollary of `app_nil`;
`len_dupEach` is marginal. Neither passes the bar.

The corollary that matters for future lanes: **"it greened cheaply" is
not an argument for admission.** Cheapness is a property of the
machinery, and the machinery is scored by the METRIC (waypoints, catalog
rows). The PRODUCT is scored by whether a Lean reader gets something
worth reading. A lane that widens the decode layer should expect to land
capability and NO products, and should say so up front rather than
proposing whatever the new capability happens to reach first.

What this means concretely for the strip that followed:

- products stay at **15** (they had briefly been 17 in-worktree);
- `ACL2Lean/Mirrors/Basics.lean` and `ACL2Lean/MirrorProofs/Basics.lean`
  are **byte-identical to `dc1cadd`** on this branch — verified by
  `git diff --stat` returning empty;
- everything whose ONLY consumer was a stripped transport went with it
  (the `dupEach` squares, and the projected waypoint
  `len_dup_native_driver` that existed solely to be the second mirror's
  crossing source);
- the waypoint layer, the catalog rows, `LiftingRel.lean`, the enc-image
  facts, and the negative probes all STAY. The combinators keep their
  consumers because those consumers are the native DECODES, not the
  transports.

### 1a. The two draft Props, VERBATIM (record only — NOT the shop window)

These are preserved exactly as drafted, together with the one supporting
definition they needed. **Nothing here is in `ACL2Lean/Mirrors/`.** They
belong to this record document.

```lean
/-- Duplication (the 15-nested-induction book's `dup`): every element
    repeated in place. -/
def dupEach : List α → List α
  | [] => []
  | a :: t => a :: a :: dupEach t

/-- TLP-APP-NIL-TWICE (the 17-rule-application book) — DRAFT, awaiting
    the shop-window bless. The book's capstone (`:rule-classes nil`, so a
    RESULT and not a rule): appending nothing TWICE changes nothing.

    What makes it a distinct book result rather than a restatement of
    `app_nil` is the ROUTE, not the statement: ACL2 proves TLP-APP-NIL by
    induction and stores it as a conditional `:REWRITE` rule, then proves
    this one with NO induction at all — its entire proof is two
    applications of that stored rule (the inner redex, then the outer),
    each hypothesis relieved from the clause's own `(NOT (TLP X))`
    literal. In Lean the statement is visibly a corollary of `app_nil`;
    the honest claim is that the ACL2 rule-application proof replays, not
    that the Lean statement is hard. -/
def app_nil_twice (α : Type u) : Prop :=
  ∀ (xs : List α), app (app xs []) [] = xs

/-- NESTED-INDUCTION, second conjunct (the 15-nested-induction book) —
    DRAFT, awaiting the shop-window bless. Duplicating every element
    doubles the length.

    ACL2 proves it as one half of a CONJUNCTION whose two conjuncts need
    DIFFERENT recursion schemes (the book's feature: it inducts on
    `app`'s scheme for the first, then again on `dup`'s for this one,
    under a synthesized `*1.k` pool root). The first conjunct's statement
    is `len_app` above, already a product off `simple.lisp`; this one is
    new. Stated with `+` rather than `2 *` because that is the shape ACL2
    proves — `(+ (LEN Z) (LEN Z))`. -/
def len_dupEach (α : Type u) : Prop :=
  ∀ (xs : List α), len (dupEach xs) = len xs + len xs
```

And the three declarations in `MirrorProofs/Basics.lean` that proved
them (all were trio-clean — `[propext, Classical.choice, Quot.sound]` —
with `#guard_msgs`-pinned receipts, so their removal is not the removal
of anything unproved):

```lean
mirror_transport% app_nil_twice_int : ACL2Lean.Basics.app_nil_twice Int
  embed intEmbed
  crossing app_nil_twice_sexpr
    from Imported.Waypoints.tlp_app_nil_twice_native_driver

mirror_iso% dupEach_agree_dupL for ACL2Lean.Basics.dupEach
  vars [xs]
  square agree (Worlds.Nested.dupL xs)
  unfold [Worlds.Nested.dupL]

mirror_iso% dupEach_map_hom for ACL2Lean.Basics.dupEach
  vars [xs]
  square hom list

mirror_transport% len_dupEach_int : ACL2Lean.Basics.len_dupEach Int
  embed intEmbed
  crossing len_dupEach_sexpr from Imported.Waypoints.len_dup_native_driver
```

plus the projected waypoint the second one crossed from
(`Imported/Waypoints/NestedInduction.lean`, also removed — its only
consumer was that transport, and its content is fully contained in
`nested_induction_native_driver`):

```lean
/-- The ENTRY's SECOND CONJUNCT, projected and read back at `Nat` — the
    non-trivial half (duplication doubles a length), and the one the
    mirror layer's crossing consumes. The projection is `And.right` of
    the single replayed fact and the `Nat` reading is the standard cast
    normalisation (`my_len_my_app`'s idiom); no new content enters. -/
theorem len_dup_native_driver (zs : List SExpr) :
    (Worlds.Nested.dupL zs).length = zs.length + zs.length := by
  have h := (nested_induction_native_driver [] [] zs).2
  omega
```

Re-admission, if the bar ever moves, is: paste the two `Prop`s + `dupEach`
back into `Mirrors/Basics.lean`, the four `mirror_*%` declarations plus
receipts back into `MirrorProofs/Basics.lean` (re-adding the
`Waypoints.RuleApp` / `Waypoints.NestedInduction` imports), and the
projected waypoint back into `Waypoints/NestedInduction.lean`. Each
landed first attempt when originally written.

### 1b. A third candidate that never reached the checkpoint

Book 17's FIRST theorem, TLP-APP-NIL, has the mirror statement
`∀ xs, app xs [] = xs` — **byte-identical to the existing `app_nil`
Prop**, already a product off 02-rev. No duplicate Prop was proposed and
no second theorem was added into the existing Prop. Book 17's waypoint
row is `.native`; it yields no product, by construction rather than by
ruling.

---

## 2. WHAT LANDED (the capability)

### 2a. The decode layer past EQUAL-only — `ACL2Lean/Imported/LiftingRel.lean` (227 lines)

Its own module per the module-size norm (`Imported/Lifting.lean` is at
1125 and carries the equational spine; this is a new lemma family).

Until this lane the decode family was **EQUAL-only**: every waypoint
ended at `Lifting.native_of_replayed_equal`, so any corpus row whose
conclusion was a COMPARISON or a CONJUNCTION had no ender at all and was
decode-blocked regardless of how green its replay was.

| combinator | line | consumer |
| --- | --- | --- |
| `native_of_replayed_le` | `LiftingRel.lean:122` | `Worlds.Linear.len2_nonneg_native_of_replayed` (03-linear LEN2-NONNEG) |
| `native_of_replayed_lt` | `:108` | `native_of_replayed_lt_of_implies` |
| `native_of_replayed_lt_of_implies` | `:216` | `Worlds.Linear.len2_cdr_smaller_native_of_replayed` (03-linear LEN2-CDR-SMALLER) |
| `native_of_replayed_and` | `:166` | `Worlds.Nested.nested_induction_native_of_replayed` (15 NESTED-INDUCTION) |
| `replayed_split_and` | `:142` | `native_of_replayed_and` |
| `replayed_of_replayed_implies` | `:198` | `native_of_replayed_lt_of_implies`, both `Worlds.RuleApp` decodes |
| `conv_ltT` / `conv_notT` | `:56` / `:65` | the above |
| `logic_lt_int` / `lt_of_lt_truthy` / `le_of_not_lt_truthy` | `:76` / `:83` / `:94` | the above |
| `ltT` / `notT` / `andT` | `:47` / `:49` / `:51` | the above |

The shapes are read off what ACL2 actually emits, not off Lean taste:
`(< a b)` verbatim; `(NOT (< b a))` for `<=` (03-linear's LEN2-NONNEG is
emitted as `:TFORMULA (NOT (< (LEN2 X) '0))`); `(IF A B 'NIL)` for `AND`
(15's is emitted as `:TFORMULA (IF (EQUAL …) (EQUAL …) 'NIL)`).

**The comparisons are `intRep`-only, deliberately.** `Logic.lt` is ACL2's
full rational comparison; the native `x < y` at `Int` is sound for it only
because `intRep` pins both sides to INTEGER atoms. A `Rep`-generic version
needs an order on the represented type plus an agreement lemma — build it
when a row needs it, not before.

### 2b. The design flip, recorded

The lane was briefed to build `native_of_replayed_lt` in the bare
`EvTrue (< a b)` shape, modelled on `native_of_replayed_equal`. That
shape has **no unconditional consumer in the green corpus**: every
`<`-conclusion sweep row is `(IMPLIES …)`-headed. (`SZ-CONS-GROWS` and
`SZL-BOUND` are unconditional but live in `acl2_samples/pattern-tests/`,
outside the golden's 29 books.)

Rather than leave it unwired (the banned build-now-wire-later pattern) or
rename the conditional form dishonestly, the peel was extracted as a
**replayed-statement transformer**:

```
replayed_of_replayed_implies : EvTrue w e (impliesT hyp concl) → … → EvTrue w e concl
```

so a conditional row's decode is literally *the unconditional ender ∘ the
peel*, whatever the conclusion's shape. That wires
`native_of_replayed_lt` genuinely and gives the whole layer one uniform
conditional/unconditional story. `<=` needed no such move (LEN2-NONNEG is
unconditional).

The same extraction de-duplicates glue that had been pasted out verbatim
four times in the waypoint layer.

### 2c. Five waypoints, five catalog rows `.pending` → `.native` (54 → 59)

All five landed **first attempt**, all trio-clean
(`[propext, Classical.choice, Quot.sound]`).

| book / theorem | waypoint statement |
| --- | --- |
| 17-rule-application TLP-APP-NIL | `xs ++ [] = xs` |
| 17-rule-application TLP-APP-NIL-TWICE | `(xs ++ []) ++ [] = xs` |
| 03-linear LEN2-NONNEG | `(0 : Int) ≤ (xs.length : Int)` |
| 03-linear LEN2-CDR-SMALLER | `(t.length : Int) < ((a :: t).length : Int)` |
| 15-nested-induction NESTED-INDUCTION | `(xs ++ ys).length = … ∧ (dupL zs).length = …` |

Support modules: `Imported/RuleApp.lean` (243), `Imported/Linear.lean`
(148), `Imported/NestedInduction.lean` (208); waypoints
`Imported/Waypoints/{RuleApp,Linear,NestedInduction}.lean`.

### 2d. World-parametricity paid off ACROSS books

Books 15 and 17 both reuse `Worlds.Rev.appExec` / `app_exec_corr` /
`appExec_enc` **verbatim**: their `APP` is the same symbol with the same
emitted body as 02-rev's, so the world-parametric kit instantiates at
their worlds by `decide`. This is structural, not a convenience — the
exec/iso registries are keyed by ACL2 NAME, so re-deriving `APP` is
rejected outright by `derive_sim%` as a duplicate registration.

Only `TLP` (book 17) and `DUP` (book 15) needed new kits. `LEN2` needed
**no kit at all**: its emitted body IS `Lifting.lenBody "LEN2"`, the
name-generic length shape, so `Lifting.corr_len_enc` covers it.

### 2e. THE STALE-BLOCKER FIND — 03-linear's "len2 dischargers"

The catalog had carried `.pending "len2 dischargers"` on both 03-linear
rows. **That reason was stale, in exactly the way 02-rev's was (R0 item
7).** Both rows' `cond[…]` labels sit inside `[DISCHARGE: …]` — i.e. on
the standalone informational DP probe, not on the row — and the driver
emits both replayed statements UNCONDITIONAL. The `_uncond` theorems in
`Waypoints/Linear.lean` are the proof: a surviving hypothesis would not
typecheck.

What was genuinely missing was an ENDER, not a discharger. The lesson is
the generalisable one: a `.pending` reason written when a row was red can
outlive the reason, and the cheap test is to write the `_uncond` theorem
and see whether it elaborates.

### 2f. The `LEN`-is-a-builtin enc-image fact

Book 15's log carries `(:DEFUN LEN … :SOURCE :GROUND-ZERO)`, but `LEN` is
in `EvalOpt.builtinNames`, so world-derivation deliberately keeps it OUT
of `w.defs` (the D3/D2 design note: a world body for `LEN` would shadow
the builtin, recurse per element instead of one step, and falsify the
`hnew` side condition of `evalOpt_world_mono`). This was caught by a
`decide` failure on a world fact that "obviously" held, and fixed with a
new enc-image fact:

```
Worlds.Nested.logic_len_enc : Logic.len (enc xs) = intRep.enc (xs.length : Int)
```

This is the `Lifting.trueListp_enc` analogue for the length builtin. Its
sibling for a DEFUN recognizer is `Worlds.RuleApp.tlpL_true`: book 17's
`(TLP X)` antecedent is this book's OWN structural recognizer, not the
builtin `TRUE-LISTP`, so the 02-rev absorption does not apply; the
analogous fact is proved from the book's own program (the generated iso
`tlpExec_enc` reads `TLP` on an encoded list as `tlpL`, and `tlpL_true`
says that reading is `true` on every Lean list). Neither row's hypothesis
is assumed — both are discharged at the encoded instance.

### 2g. Negative probes — `Tests/LiftingRelProbes.lean` (92 lines)

Three `#guard_msgs`-pinned elaboration failures: the `<` decode fed an
EQUAL-shaped replayed statement; the `≤` decode fed the **un-negated**
`<` shape (dropping the `NOT` would read a strict comparison as a
non-strict one); the conjunction decode fed a bare equality. The check IS
the type, so the probes declare nothing and cost no `sorryAx`.

Per the deterrent standard they carry the explicit comment: a SPEEDBUMP
against the honest mistake (citing the wrong replayed constant when
wiring a new waypoint), never a barrier against circumvention — **DO NOT
HARDEN IT**; if it becomes fragile, delete it.

---

## 3. RESIDUALS (verbatim)

1. `Imported/Rev.lean`'s two hand-pasted implies-peel copies (APP-NIL,
   REV-REV) are not yet routed through
   `Lifting.replayed_of_replayed_implies`. The lane converted its own two
   copies (`Imported/RuleApp.lean`) but left Rev alone — behavior-preserving
   churn on already-landed products, deliberately not spent. Clean
   follow-up; the risk it manages is the real one (a fix applied to one
   clone silently missing its twin).
2. `17-rule-application/TLP-APP-NIL` is `.native` at the waypoint layer
   but yields **no product** — its mirror statement is the existing
   `app_nil` Prop. If the "two independent replay routes to one product"
   demonstration is ever wanted, it is a 3-line second transport, not a
   new Prop.
3. `03-linear/LINEAR-CHAIN` remains `.pending "#50 DP tactic decode"` —
   untouched, out of this lane's scope.
4. The `≤`/`<` combinators are **`intRep`-only** by design (see 2a). Any
   row needing a comparison at another representation is a frontier, not
   a small edit.
5. `native_of_replayed_and` is the both-conjuncts-EQUATIONAL instance
   (15's shape). `replayed_split_and` is the generic splitter for other
   conjunct shapes when one appears.
6. No spec `Prop` is proposed off 03-linear, and that judgement predates
   the ruling: `0 ≤ length` and *tail-shorter* are facts core Lean gives
   for free (`enc` lands only on genuine lists; `List.length : Nat`).
   Those rows establish the ROUTE — a comparison-concluded ACL2 theorem
   decoded through the interpreter with no equational disguise — and
   nothing more. Recorded in `Imported/Linear.lean`'s header.

---

## 4. VERIFICATION STATE AT THIS COMMIT (fast-gate)

Run in the lane's isolated worktree, AFTER the strip:

- `lake build` — 6472 jobs, exit 0, **zero warnings**;
- `just test` — green; `MirrorNameCheck`: no collision over
  `[Init, Lean, Std, Batteries, Mathlib]` × `[List, Option, Nat, Int, Bool, Prod, Function]`;
- sweep `just driver-coverage` — **REPLAYED 116/116 (116 unconditional + 0 conditional)**, 29 books;
- `just check-golden-current` — golden matches the live assembly;
  `git diff Tests/driver-coverage.golden` empty (**untouched**);
- green: `lint-sh`, `check-bugs`, `check-no-shadow`, `check-gz-agreement`,
  `check-mirrors-pure`, `check-file-weight`, `check-dark-files`,
  `check-proof-logs`, `check-pattern-map`, `check-no-getd-done`;
- sorries **0** in every file the lane added;
- `Mirrors/Basics.lean` and `MirrorProofs/Basics.lean` byte-identical to
  `dc1cadd`.

**Two gates are OWED at collection**, and could not run here:
`check-acl2-tags` and `test-provenance-gates` / `check-log-provenance`
both fail because the `acl2/` submodule is **uninitialized** in this
worktree (only proof-logs were rsynced). The provenance gate consequently
reports the *superproject* commit as "submodule HEAD". These are
environment artifacts of the worktree setup, not regressions — the same
submodule triple the previous wave already owed.
