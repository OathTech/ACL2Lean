# Toolchain bump INVENTORY — v4.28.0 → v4.33.0 (phase 0 artifact, 2026-08-19)

Charter: `docs/plans/2026-08-19_toolchain-bump-charter.md`. This file is
phase 0's deliverable: the complete breaking-change / deprecation
inventory for the five releases we cross, mapped to our call sites, with
a risk verdict and a fix direction per item. Phases 1–2 work from this.

**STANDING OF THE VERDICTS — read first.** Nothing here was built. No
toolchain was installed, no pin was touched, `lake` was not run. Every
"WILL break / MAY break / benign" below is a STATIC reading of the
release notes against a grep of the tree. The phase-1 triage is what
turns these into facts; where I could not decide on paper I say
`VERIFY@P1` rather than guess. Counts are raw grep hits over
`ACL2Lean/ Tests/` (183 `.lean` files) and include comment/prose lines
unless stated otherwise.

Sources read IN FULL (converted from HTML, no summarisation):
`https://lean-lang.org/doc/reference/latest/releases/v4.{29,30,31,32,33}.0/`
— 2126 / 1686 / 1675 / 688 / 1105 lines of rendered text respectively.
The lean4 repo's `RELEASES.md` at tag v4.33.0 is a 9-line stub that
redirects to those pages, so there is no second source to cross-check
against; the reference site IS the changelog.

---

## 0. Environment facts

| | current | target |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.28.0` | `leanprover/lean4:v4.33.0` |
| `lakefile.toml` mathlib `rev` | `v4.28.0` | `v4.33.0` |
| manifest format | `1.1.0` | `1.2.0` (mathlib v4.33.0 ships this) |

### 0.1 Dependency compatibility (charter phase-0 item 4) — CLEAN

Fetched `mathlib4@v4.33.0`'s own `lake-manifest.json` and
`lean-toolchain` and diffed the package set against ours:

* mathlib v4.33.0 `lean-toolchain` = `leanprover/lean4:v4.33.0`. Exact
  match with the target. No toolchain/mathlib skew.
* Package set is **identical** to ours — same eight transitive deps,
  same URLs, same scopes: `plausible`, `LeanSearchClient`, `importGraph`,
  `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`. Nothing added,
  nothing removed.
* Every one of the eight is `"inherited": true` in OUR manifest (we
  require only mathlib), so bumping the mathlib pin and re-resolving
  pulls mathlib's own revisions wholesale. No per-dep pin to hand-manage.
* One cosmetic delta: mathlib v4.33.0 lists `proofwidgets` with
  `inputRev = "main"` where our (v4.28.0-era) manifest has
  `inputRev = "v0.0.87"`. That field is inherited from mathlib, so it
  simply follows; not an action item.
* `Cli` follows the toolchain tag (`inputRev = "v4.33.0"`) — again
  inherited.

**Verdict: the charter's escape-hatch condition "Mathlib's v4.33.0 tag is
incompatible with any pinned dependency" is NOT triggered.** Manifest
version moves 1.1.0 → 1.2.0, which is a Lake-side format bump handled by
`lake update mathlib`.

### 0.2 Things that make several release items NOT APPLY to us

Recording these up front so phase 1/2 do not chase them:

* **We do not use the module system.** Zero `module` headers, zero
  `public`/`meta` sections, zero `@[expose]`/`@[no_expose]` in
  `ACL2Lean/ Tests/` (the three `^module` grep hits are the word "module"
  in prose). Everything gated on `module` is therefore inert for us:
  4.30 #13005 meta-import enforcement, #12602 `evalConst checkMeta`,
  #13043 / #13059 / #13315 meta-marking of derived instances, 4.31
  #13132 `linter.redundantVisibility`, #13359 `linter.redundantExpose`,
  #13239, #13374, #13630, #13843, 4.33 #13679 / #14609.
* **We do not use `native_decide` / `bv_decide`.** So 4.29 #12217 (one
  axiom per native computation; `#print axioms` stops showing
  `Lean.trustCompiler`) changes nothing in our 162 `#print axioms`
  receipts. Grep confirms zero `native_decide` outside one comment
  (`Imported/Waypoints/Catalog.lean:604`) and zero `trustCompiler`.
* **`reference/Log2Replay.lean` is not built.** It is not under any
  `lean_lib` root in `lakefile.toml` (`ACL2Lean`, `Tests`, `Main`,
  `ReplayMain`). Its `Nat.ne_of_gt` uses — the only hits for the 4.33
  `protected` change (#14216) — are therefore not a build item. (It is
  presumably covered by `check-dark-files`; if that gate says otherwise,
  reclassify.)
* **No `aesop` calls, no `Std.Time`, no `String.Slice`, no
  `Lean.RBMap`/`RBTree`, no `Subarray`, no `PostCond`, no `Squash`/
  `Setoid`, no `Float`.** Grep-zero. All the associated 4.29–4.33
  breaking items are inert.

---

## 1. The completed watchlist

The charter seeded four items and said "complete it from the full
changelogs". Completed list below, ordered by my risk ranking, not by
the charter's order. **The charter's ranking needs one correction, called
out at W1: the highest-risk simp surface is not the transport/iso
closers, it is `dpLeafTactic` — a fixed `simp_all` kit sitting inside the
certified replay path and byte-gated by the coverage golden.**

### W1 — `simp`/`dsimp` no longer process typeclass instances (4.29 #12244 / #12195) — **WILL break something**

Release text: "`simp` and `dsimp` no longer process typeclass instances.
This behaviour was producing non-standard instances… The old behavior can
be restored with `set_option backward.dsimp.instances true` or
`simp +instances` for `simp`." Companion: 4.29 #12172 changes how a
function parameter is classified as an instance (`isClass?` instead of
binder syntax), with knock-on effects in discrimination trees, congruence
lemma generation and grind's canonicalizer — "a rewrite rule in `simp`
that was not firing due to incorrect indexing may now fire". So this cuts
BOTH ways: rules stop firing AND new rules start firing.

Our exposure, in descending order of consequence:

1. **`ACL2Lean/Replay/Driver/Discharge.lean:226-260` — `dpLeafTactic`.**
   The fixed leaf-closing tactic of the ratified DP carve-out: a
   `simp_all [...]` kit of ~24 named `Logic.*` lemmas with two
   suppressions (`-Logic.toBool`, `-Logic.endp`) plus `beq_iff_eq`,
   `Bool.cond_eq_ite`, chained `<;> omega`, in a two-alternative `first`
   (the second adds `at *`). Run via `Lean.Elab.runTactic` at
   `Discharge.lean:601` and `:676`, under a split/fuel loop
   (`dpSplitAndClose`). This is **in the certified replay path** and its
   result is pinned byte-exactly: `Tests/driver-coverage.golden` records
   `REPLAYED 116/116` plus standalone DP probe counts `✓62 ◌9 ✗0 of 71`.
   The kit reaches through `Decidable`/`BEq` instance arguments
   constantly (`beq_iff_eq`, `Bool.cond_eq_ite`, `Logic.equal`,
   `decide`), which is exactly what #12244 stops doing. A single leaf
   that stops closing flips a row and moves the golden.
   **Risk: WILL break or WILL move the golden.** Fix direction: real fix
   — add the instance equations the kit now needs as explicit rows
   (e.g. the `decide`/`Decidable` bridging lemmas), keeping the kit
   FIXED and per-case-free (the carve-out drift rule). `simp +instances`
   is the `backward.*`-class last resort and would need a TODO entry.

2. **`ACL2Lean/MirrorProofs/IsoKit.lean:561-570` — `mirror_square_close`.**
   `first | rfl | simp_all only [List.map_nil, List.map_cons,
   List.nil_append, List.cons_append, List.length_nil, List.length_cons,
   Bool.cond_true, Bool.cond_false, ite_true, ite_false, decide_true,
   decide_false, enc_inj_iff, Bool.decide_eq_true, Bool.false_eq_true,
   ← Bool.and_eq_true, $xs,*]`. Every square over an order-using mirror
   definition splits on `if a ≤ b` with a `TotalOrder.decLE`-derived
   `Decidable` instance in the term; `decide_true`/`decide_false`/
   `Bool.decide_eq_true` are precisely instance-argument rewriting.
   Wrapped by `mirror_square_close_split` (`IsoKit.lean:665-671`), driven
   from `IsoGen.lean:967` / `:970`. Consumers: the 15 sorting squares +
   the `Basics` squares. **Risk: WILL break.** Same fix direction.

3. **`ACL2Lean/Imported/SimGen.lean:147-157` — `sim_iso_close`.**
   `repeat' (first | simp_all [-Logic.toBool, -Logic.consp, -Logic.car,
   -Logic.cdr, -Logic.cons, -Logic.equal, enc_*, toBool_*, boolEnc,
   $xs,*] | split) <;> (first | rfl | omega | grind)`. Note this one is
   `simp_all` (not `only`) so it also inherits the five-release drift in
   core's default simp set, AND it terminates in `grind` — see W9.
   **Risk: WILL break.**

4. **`ACL2Lean/MirrorProofs/TransportGen.lean:54-73` and `:111-124` —
   `mirror_transport_close` / `_close_hyps`.** `simp only [$xs,*] at $h`
   then a `first`-ladder of `exact` / `map_inj` landings. Narrower than
   the above (the kit is the registered homomorphism squares, the
   landings are `exact`), so the instance change bites less. The
   `List.map_nil` row in rung 2 is a `rfl`-lemma. **Risk: MAY break.**

5. **The bulk simp surface.** 632 `simp only`, 83 `simp_all`, ~1499 other
   `simp` (excluding `simpa`), concentrated in
   `Replay/Lemmas/Core.lean` (175 `simp only`),
   `Replay/Lemmas/TsAlgebra.lean` (117),
   `Replay/Lemmas/FnAlias.lean` (86),
   `Replay/ClausifyBridge.lean` (53), `EvalOpt.lean` (46).
   These are hand proofs of our own lemmas; individually low-stakes,
   collectively the largest source of phase-1 error volume.
   **Risk: MAY break, high volume, low per-site difficulty.**

### W2 — `isDefEq` no longer raises transparency on implicit args (4.29 #12179) + `respectTransparency.types` on by default (4.33 #13895) + the instances/implicit split (4.33 #13637) — **MAY break, highest diagnosis cost**

Three coordinated changes, best treated as one item:

* 4.29 #12179: `isDefEq` stops bumping to `.default` when comparing
  implicit arguments. Escape: `set_option backward.isDefEq.respectTransparency false`
  (documented as available "for the medium term"; also settable
  project-wide in `lakefile.toml` under `[leanOptions]`). Mathlib ships
  `scripts/add_set_option.py` / `rm_set_option.py` and a
  `#defeq_abuse in ...` command to localise failures — available to us at
  `.lake/packages/mathlib/scripts/`.
* 4.31 #13280 adds `backward.isDefEq.respectTransparency.types`
  (mvar-assignment type check at `.instances` rather than `.default`),
  default OFF.
* 4.33 #13895 turns `respectTransparency.types` ON by default. Release
  text: "the symptom of a breakage is a lemma that `simp`, `grind`, or
  another tactic stops applying".
* 4.33 #13637 splits `instances` into `none < reducible < instances <
  implicit < default < all`; `@[implicit_reducible]` no longer carries
  `@[instance_reducible]`'s side effect of letting TC search see through
  the declaration. New `with_implicit` tactic.

Our exposure:

1. **The `TotalOrder` instance layer — the concrete hot spot.**
   `ACL2Lean/Mirrors/Sorting.lean:164-177`:
   `class TotalOrder (α) extends LE α` with a `decLE : DecidableRel (· ≤ ·)`
   field, `attribute [instance] TotalOrder.decLE`, a low-priority
   `instance : LT α := ⟨fun a b => ¬ b ≤ a⟩`, and
   `instance : DecidableRel (· < ·) := fun _ _ => instDecidableNot`.
   That last one only typechecks by unfolding the `LT` instance to expose
   `¬ b ≤ a` and then finding `Decidable (b ≤ a)` — an instance-through-
   instance defeq step at exactly the transparency level #13637 split.
   Plus `attribute [local instance 5000] ACL2Lean.Sorting.decEqOfOrder`
   (`MirrorProofs/SortingSquares.lean:877`), a priority-forced local
   instance. **Risk: MAY break, and if it does it is the single hardest
   diagnosis in the arc** because it is load-bearing for every sorting
   square and every `Int`/`Option Int` mirror.
2. **The formula/statement pins (the charter's item 2).** 43 top-level
   `example : <hand type> := <machine constant>` across
   `Tests/SortingPins.lean`, `Tests/ParametricPins.lean`,
   `Tests/SortingPinsEndgame.lean`, `Tests/DriverTests.lean`. The check
   is `ensureHasType` = `isDefEq` at DEFAULT transparency between the
   hand-transcribed type (built from `private def sym/ap1/ap2/quo/...`
   helpers, plain semireducible `def`s) and the constant's type. Plain
   defs still unfold at default transparency, and the world constants are
   `derive_world`-produced with `hints := .abbrev`. **Risk: MAY break
   (I lean benign).** Charter rule stands: a pin that fails here is a
   diagnosis item, never a loosening.
3. **70 `mkExpectedTypeHint` sites** (`Replay/Driver/Harness.lean` ×10,
   `Replay/Driver/Discharge.lean`, `Replay/Runner.lean:453`) — these
   build `@id ty pf`, kernel-checked at default transparency, so the
   elaboration-side transparency change does not reach them. **Benign.**
4. **70 `isDefEq` guard sites** in the driver
   (`Replay/Runner.lean:450`,`:479`; `Replay/Driver/Discharge.lean:820`,
   `:856`; `Replay/Driver/Preprocess.lean:558`,`:719`,`:819`;
   `Replay/Driver/NodeCore/Literal.lean:34`;
   `Replay/ParametricInstantiate.lean:86`). These run at MetaM's ambient
   (default) transparency on largely mvar-free terms. **Risk: MAY break**
   where the compared types carry implicit args or assigned mvars; the
   ParametricInstantiate loop (`while n < 24 && !(← isDefEq ...)`) is the
   likeliest.
5. **~1244 `mkAppM` sites.** `mkAppM` unifies implicit arguments — the
   exact operation #12179 changed. Volume makes this the most likely
   source of surprise failures in the driver. **Risk: MAY break.**

Fix direction throughout: real fix (`@[implicit_reducible]` /
`@[instance_reducible]` on the definitions involved, or restating so the
term is well-typed at implicit transparency). `backward.isDefEq.respectTransparency`
and `...types` are last resorts and MUST be scoped per-declaration with a
comment + TODO entry, never set project-wide in `lakefile.toml` — the
project-wide form is exactly what the arc exists to avoid.

### W3 — `simpa using h` now closes at REDUCIBLE transparency (4.31 #13636) — **MAY break, 193 sites**

Release text: "makes `simpa using h` close at reducible transparency
rather than the ambient (default/semireducible) transparency used
previously… The previous behaviour is available as `simpa using! h`"
(the `using!` syntax was added in #13833 for exactly this).

193 `simpa` hits, concentrated:
`Replay/ClausifyBridge.lean` (50), `Imported/Lifting.lean` (23),
`Replay/Lemmas/Core.lean` (22), `Imported/Sorting.lean` (22),
`Replay/Lemmas/FnAlias.lean` (21), `Replay/DpLift.lean` (11),
`Replay/Lemmas/Discharge.lean` (9), `MirrorProofs/OrderBridge.lean` (4).
The `OrderBridge` ones are load-bearing (`simpa [lexorderB] using h1` in
the `TotalOrder SExpr` instance, `OrderBridge.lean:36-44`) and sit right
next to W2's hot spot.

Fix direction: real fix per failing site (add the unfolding lemma the
reducible close now needs to the `simpa` set). `simpa using!` is the
mechanical escape and is NOT a `backward.*` option — it is a supported
syntax — but it is still a "restore old behaviour" move and should be
justified per site rather than applied wholesale. **This item is the most
likely to produce a large, boring, mechanical round.**

### W4 — `compileDecl` callers may need `markMeta` (4.30 #13005 / #13311) — **BENIGN for us**

Charter item 3. Findings:

* We have **8 `addAndCompile` sites, zero `compileDecl` sites, zero
  `markMeta` sites**:
  `Replay/Runner.lean:717`, `:728`, `:786`, `:805`;
  `Replay/Driver/DevQuery.lean:83`;
  `Imported/Waypoints/Macro.lean:137`, `:223`, `:233`.
  Plus 7 plain `addDecl`: `Replay/ParametricInstantiate.lean:525`,
  `:868`, `:960`; `Replay/Runner.lean:315`, `:427`, `:483`;
  `MirrorProofs/IsoKit.lean:758`.
* All eight `addAndCompile` calls build a `.defnDecl` holding either
  `List String` (the cross-book conditions cache, read back by
  `unsafe Meta.evalExpr` at `Runner.lean:703`/`:770` and
  `Macro.lean:125`/`:213`) or a reflected `World`
  (`DevQuery.lean:83`, `hints := .abbrev`, followed by
  `enableRealizationsForConst`).
* #13005's requirement is scoped to the module system ("all modules used
  in compile-time execution must be meta imported"), and #13311 made the
  new capability an OPTIONAL parameter (`markMeta : Bool := false`) on
  `addAndCompile` — so the existing calls keep compiling unchanged.
  We have no `module` files.

**Verdict: benign; no action. Charter item 3 is discharged by this
inventory** — the audit it asked for is above and found nothing to fix.
(30 `unsafe … evalExpr` sites are likewise unaffected for the same
reason: #12602's `evalConst` tightening is `module`-gated.)

### W5 — `noncomputable` / inductive / universe changes (4.29 #12028, #12514, #12603) — **BENIGN to MAY break**

* **#12028 stricter `noncomputable`.** 5 `noncomputable` hits, only 2
  real declarations: `Replay/Lemmas/Discharge.lean:800` (`pinVal`) and
  `Replay/Lemmas/Judgments.lean:1481` (`interpCount`). The new rule
  ("needed whenever an axiom or another `noncomputable` def is used by a
  def", with proofs/types/`@[extern]`/`@[implemented_by]`/`@[csimp]` uses
  exempt) can require MORE annotations than before. Interacts with 4.30
  #12678, which marks `List.flatten`/`flatMap`/`intercalate`
  noncomputable — but those carry `@[csimp]` variants, so per #12028's
  own carve-out our 6 use sites
  (`Replay/Driver/Discharge.lean:372`,`:395`;
  `Replay/Driver/Provers.lean:535`; `Imported/ExecGen.lean:220`;
  `MirrorProofs/IsoGen.lean:218`; `Replay/Lemmas/Core.lean:685`) are
  exempt. **Risk: MAY break (small, mechanical: add `noncomputable`).**
* **#12514 universe inference.** "Universe level metavariables present
  only in constructor fields are no longer promoted to universe level
  parameters" and "recursive types do not count as obvious `Prop`
  candidates". 31 `inductive` declarations. Our core `SExpr`/`Atom`/
  `ProofNode`/`ClauseNode` family is monomorphic (`Type`), so promotion
  does not arise; `Mirrors/Sorting.lean:273 RelMode` is a plain enum.
  **Risk: benign** — but `Mirrors/Sorting.lean:231 Ordered : List α → Prop`
  and `:454 Permuted` are recursive `Prop`-valued definitions (`def`, not
  `inductive`), so the "obvious Prop candidate" clause does not apply.
  `VERIFY@P1`.
* **#12603 inductive typeless binders.** "`(x)` may need to become
  `(x : _)` if there is a `variable` with that name or it shadows a
  parameter." Requires a constructor written with a bare `(x)` binder;
  grep of our 31 inductives shows the conventional `| ctor (f : T)` form
  throughout. **Risk: benign.**

### W6 — NEW LINTERS AND WARNINGS (4.29 #12325; 4.31 #13325, #13223; 4.33 #14196, #14325, #14259) — **MAY break the zero-warnings rule**

This is the watchlist entry the charter did not have, and under our
"warnings are unacceptable" rule a new default-on warning is a build
break, not a nit.

* **4.29/4.30 #12325** — warning on any `def` of class type that does not
  declare a reducibility. Candidates: `MirrorProofs/IsoKit.lean:37
  intEmbed : Acl2Embed Int`, `:129 optEmbed`, `MirrorProofs/OrderBridge.lean:113
  intOrderedEmbed : OrderedEmbed Int`. `Acl2Embed`/`OrderedEmbed` are
  `structure`s, not `class`es, so strictly this should not fire —
  `VERIFY@P1`. Fix if it does: add `@[reducible]` or `@[implicit_reducible]`.
* **4.31 #13325** — warnings when registering an `@[simp]` theorem whose
  LHS has a variable head (`warning.simp.varHead`, default TRUE) or an
  unrecognised head (`warning.simp.otherHead`, default TRUE). We declare
  **73 `@[simp]` theorems**, mostly in `ACL2Lean/Logic.lean` with concrete
  heads (`append_nil`, `len_cons`, `trueListp_cons`, `toInt_times_int`).
  **Risk: MAY break** — needs the real list of our simp LHS heads, which
  only the build produces. `VERIFY@P1`.
* **4.31 #13223** — warning for a GLOBAL attribute applied via
  `attribute [foo] x in ...`. Our 2 real `attribute` sites
  (`Mirrors/Sorting.lean:170 attribute [instance] TotalOrder.decLE`;
  `MirrorProofs/SortingSquares.lean:877 attribute [local instance 5000] …`)
  are not in `... in ...` form, and the second is `local`. **Benign.**
* **4.31 #13389** — `addInstance` now ERRORS (not warns) on a non-class
  instance target and on arguments that instance synthesis can never
  infer. 41 `instance` declarations. `Replay/DpLift.lean:113
  instance (w : World) : Decidable (dpNoShadow w)` takes an explicit
  non-instance-implicit `w` that DOES appear in the return type, so it
  should pass the impossible-argument check. **Risk: MAY break.**
* **4.33 #14325** — new linter warning on an `open B` that does not open
  every namespace ending in `B`. We `open Lean ACL2 ACL2.Replay
  ACL2.Replay.Driver` widely. **Risk: MAY break, mechanical fix.**
* **4.33 #14259 / 4.31 #13715** — `unusedVariables` message text changed
  and now carries an applicable hint. Only matters if a `#guard_msgs`
  captures it; none of our 82 do (they all wrap `#print axioms`).
  **Benign.**
* **4.33 #14196** — "improves on the warnings and errors regarding
  reducibility attributes". Pairs with #12325 above. `VERIFY@P1`.

### W7 — the app elaborator beta-reduces arguments (4.31 #13807) + MVarId bookkeeping (#13528) — **MAY break, 45 `dsimp` sites**

Release text: "Breaking change: tactic proofs may need to be modified to
remove unnecessary steps, e.g. `dsimp only` steps that were previously
for beta reductions." #13528 adds: it "revealed many `dsimp`s that did
nothing and can be deleted".

We have **45 `dsimp` sites, 42 of them in
`ACL2Lean/Replay/Lemmas/FnAlias.lean`**, and the overwhelming majority
are literally `dsimp only []` — an empty lemma list, i.e. beta/eta/proj
normalisation and nothing else. That is precisely the construct #13807
makes redundant, and a redundant `dsimp` FAILS with "dsimp made no
progress". Split: **35 bare, 10 `try dsimp`** — the `try`-wrapped ten are
safe by construction; the 35 bare ones are the exposure. Other sites:
`Replay/Lemmas/FnAliasLift.lean:163` (`try`), `Derived.lean:645`,
`Core.lean:853`.

Fix direction: real fix = delete the no-op steps (behaviour-preserving by
definition, since they made no progress). Do NOT wrap in `try` wholesale
— that hides a `dsimp` that was doing real work and stopped.

### W8 — kernel `maxRecDepth` bound (4.33 #13956) + heartbeat inflation (4.31 #13030) — **MAY break, resource-budget item**

* **#13956**: kernel type checking is now bounded by `maxRecDepth`
  instead of the physical stack, so `(kernel) deep recursion detected` is
  deterministic — and can now FIRE where a big native stack previously
  saved us. We are unusually exposed: `lakefile.toml` gives both
  `lean_lib`s `moreLeanArgs = ["--tstack=524288"]` (512 MB thread stacks)
  precisely because of depth, and
  `Replay/ParametricInstantiate.lean:509` documents adding a constant "so
  the kernel checks it once at addDecl". Our 4 `set_option maxRecDepth`
  sites are all in `Imported/Waypoints/SortsEquivalent.lean` (100000
  file-level, 1000000 ×3 per-declaration); everywhere else runs the
  default 512. **Risk: MAY break** — expect new `(kernel) deep recursion`
  errors in the deep-replay modules. Fix direction: raise `maxRecDepth`
  at the affected declarations (this is the release's own documented
  remedy, not a `backward.*` escape).
  Also note 4.30 #12971 raised Lean's default stack to 1 GB and 4.33
  #14343 fixed that for the main thread — so our `--tstack=524288`
  (512 MB) is now *smaller* than the default. It may be removable, but
  that is a phase-3 cleanup, not a compat fix, and must be measured.
* **#13030**: level-metavariable pretty printing now records per-
  definition indices, and "the heartbeat counter also increases quicker
  due to counting allocations… In some tests we needed to increase
  `maxHeartbeats` by 20–50%". We have **82 `set_option maxHeartbeats`
  sites** with hand-tuned budgets (1600000 / 3200000 / 4000000 /
  12000000, plus `0` ×3 in `SortsEquivalent.lean`), across
  `Imported/Waypoints/{Qsort,Bsort,ConvertPerm,Isort,OrderedPerms,EquisortParametric,SortsEquivalent}.lean`.
  **Risk: MAY break** — expect deterministic-timeout failures needing a
  budget bump. Also metaprogramming note: level pretty printing must use
  `delabLevel` / `MessageData.ofLevel`; `format`/`toString` now print
  `?_mvar.nnn`. We do not format levels in error messages (grep-zero), so
  that half is benign.

### W9 — `grind` behaviour churn (4.29–4.33, ~30 PRs) — **MAY break, 31 sites but one is structural**

Not in the charter's list; it belongs there. Across the five releases
`grind` got: higher-order Miller pattern e-matching (4.29 #12483), a
replaced canonicaliser (4.31 #13166 — the O(n²) `isDefEq` approach
removed in favour of `Sym.canon`), `genLocal` bound (4.31 #13699),
`ringMaxDegree` (4.31 #13585), `mbtc` disabled in `NoopConfig` (4.31
#13593), retuned e-matching aggressiveness on container ops (4.33
#14177 / #14192 / #14194 / #14182 / #14178 — several make a lemma fire
LESS eagerly), and a batch of BitVec/ring correctness fixes.

Our 31 `grind` hits: 26 in `ACL2Lean/Logic.lean`, 4 in
`Imported/SimGen.lean`, 1 in `MirrorProofs/IsoGen.lean`. The structural
one is **`sim_iso_close`'s terminal `(first | rfl | omega | grind)`**
(`SimGen.lean:157`) — the last rung of the `derive_sim%` ladder, used by
91 `derive_sim%` invocations. Reduced e-matching aggressiveness is
exactly the direction that turns "grind closes it" into "grind doesn't".
**Risk: MAY break.** Fix direction: real fix (add the missing fact to
the ladder's kit) — never `grind`-parameter tuning per case, which is
carve-out drift.

### W10 — equation generation and `fun_induction` case shape (4.29 #12429; 4.30 #12987; 4.31 #13512 / #13475 / #13477) — **MAY break**

* 4.29 #12429 sets `irreducible` before generating equations for
  recursive definitions (so the equations are not marked `defeq`).
* 4.30 #12987 extracts the functional passed to `brecOn` in structural
  recursion into a named `foo._f` helper.
* 4.31 #13512 changes `whnfAux` in equation-theorem generation from
  instances transparency (`whnfI`) to reducible (`whnfR`) — motivated
  by `dite`/`ite` marked `implicit_reducible`.
* 4.31 #13475/#13477 store equation-affecting option values at definition
  time and realise equations lazily.

Our exposure is `MirrorProofs/IsoKit.lean:696 undestructuredGuardCtor?`,
which calls `getEqnsFor?` and then **reads the guard hypothesis shape off
the generated equation** (`(x = [] → False)` for `merge2.eq_2`) to pick
the constructor for `mirror_definition_split`. That is a direct
dependency on equation SHAPE. Paired with **38 `fun_induction` sites**
(6 of them `fun_induction … with` and therefore naming cases explicitly —
`Mirrors/Sorting.lean:374`, `:383`), whose case tags come from those same
equations. Also `MirrorProofs/IsoGen.lean:957`/`:959`
(`fun_induction`/`fun_cases` generation) and `SimGen.lean:328`.
Plus 31 `termination_by` / 24 `decreasing_by`, several of whose
`decreasing_by` scripts are `simp_all [...]; omega`
(`TermOrder.lean:106`, `:133`) and so also inherit W1.
**Risk: MAY break.** Fix direction: real fix, and any case-name change is
a diagnosis item (it means the recursion structure Lean sees changed).

### W11 — `apply`/`rewrite` subgoal tags (4.31 #13476) — **MAY break, 43 sites**

"Assigned metavariables are now filtered out before computing subgoal
tags. As a consequence, when only one unassigned subgoal remains, it
inherits the tag of the input goal instead of being given a fresh
suffixed tag. Breaking change: scripts relying on the previous tag names
(e.g. `case h => …` after `funext`) may need updating."

43 `case <tag> =>` sites. Most (e.g.
`LexorderOrder.lean:237-251 case number.number …`) come from
`cases`/`rcases` on our own inductives and are unaffected. The named ones
after `apply`/`refine`/`funext` are the exposure; we have 2 `funext`
sites (`EvalOpt.lean:500` — a term, not a tactic;
`MirrorProofs/SortingQsortSquares.lean:69` — tactic, followed by
`funext a b`). **Risk: MAY break, small and mechanical.**

### W12 — the new `do` elaborator becomes the default (4.32 #13305, #13912, #13931) — **MAY break the metaprograms**

`backward.do.legacy` flips to `false`. Breaking consequences named in the
notes:

1. `do` now always requires a `Pure` instance, not just `Bind`.
2. `do match` arms are non-dependent by default; `do match (dependent := true)`
   recovers the term-match expansion.
3. `try`/`catch` no longer accepts a body whose result type matches the
   expected type only via coercion.
4. Unreachable code is a WARNING (was an error) — relevant to the
   zero-warnings rule.
5. `let pat := rhs | otherwise` now scopes over the following `doSeq`
   (this one landed already in 4.29 for BOTH elaborators).
6. #13912: `return e` inside `(← do …)` or `(← try … catch …)` now
   early-returns from the ENCLOSING `do` block. Migration is `pure e`, or
   `(← (do …))`.

Our whole driver/elaborator layer is `do`-notation MetaM/CommandElabM
code. Grep is reassuring on the sharpest edge: **zero `(← do` / `(<- do`
sites**, so #13912's semantic reversal has no call site. `try`/`catch` in
do blocks does exist (`Replay/Runner.lean:273`/`:320`/`:418`) — item 3
applies there. `do match` is common. **Risk: MAY break; expect a
moderate, mechanical round.** No `backward.*` needed except as a triage
crutch (`set_option backward.do.legacy true` is available and would be a
last resort with a TODO).

### W13 — renamed / moved / removed APIs — **BENIGN (grep-zero across the board)**

Checked every rename in the five changelogs against the tree. All
grep-zero in `ACL2Lean/ Tests/`:

| release | change | our uses |
|---|---|---|
| 4.29 #12441 | `Subarray.foldl(M)`/`toArray`/`size` removed → `Std.Slice.*` | 0 |
| 4.29 #12359 | `extract_eq_drop_take` → `extract_eq_take_drop` (deprecated) | 0 |
| 4.29 #12301 | `Slice.findNextPos` → `Slice.posGT` (deprecated) | 0 |
| 4.29 #12161 | `Except.of_wp` deprecated → `Except.of_wp_eq` | 0 |
| 4.29 #12504 | `Rat.abs_*` now `protected` | 0 |
| 4.29 #12281 | `true_equivalence`→`equivalence_true`, `trueSetoid`→`Setoid.trivial` | 0 |
| 4.30 #12749 | `isStructureLike`→`isNonRecStructure`, `matchConstStructLike`→`matchConstNonRecStructure`, `getStructureLikeCtor?`→`getNonRecStructureCtor?`, `getStructureLikeNumFields`→`getNonRecStructureNumFields` | 0 |
| 4.30 #12771 | `String.Slice.Pos.cast` signature | 0 |
| 4.30 #12435 | `Option.getElem?_inj` signature | 0 |
| 4.30 #12708 | `PostCond.*` implicit param order | 0 |
| 4.30 #12710 | `cons₂` names deprecated → `cons_cons` | 0 |
| 4.30 #13029 | `change ... with` syntax removed | 0 |
| 4.31 #13627 | `UInt8.ofNatTruncate` → `ofNatClamp` (all widths) | 0 |
| 4.31 #13516 | `Lake.Util.Opaque` gains `namespace Lake` | 0 (we have no Lake plugin code) |
| 4.31 #13400 | `String.Pos.skipWhile_le` → `le_skipWhile` | 0 |
| 4.32 #13908 | `Lean.RBMap`/`RBTree` deprecated → `Std.TreeMap`/`TreeSet` | 0 |
| 4.32 #13798 | `Std.Time` `DateTime (tz)` removed / `ZonedDateTime` renamed | 0 |
| 4.32 #13910/#13911 | `Lean.Parser.Term.liftMethod` → `nestedAction` (alias removed) | 0 |
| 4.33 #14255 | `Int.Linear` → `Int.Internal.Linear` | 0 |
| 4.33 #14263 | `IO.AsyncList` → `Lean.AsyncList` | 0 |
| 4.33 #14256 | `LLVM` → `Lean.LLVM` | 0 |
| 4.33 #14258/#14260/#14265/#14293/#14302/#14303 | namespace hygiene moves | 0 |
| 4.33 #14216 | `Nat.ne_of_gt` now `protected` | 0 in built code (4 in unbuilt `reference/Log2Replay.lean`) |
| 4.33 #14372 | `Lean.initializing`/`enableInitializersExecution`/`isInitializerExecutionEnabled` moved `IO` → `BaseIO` | 0 |
| 4.33 #14290 | `int_toBitVec` split; use `int_toBitVec_meta` | 0 |
| 4.33 #14241 | `bv_decide` structure equality needs `@[ext]` | 0 (no bv_decide) |
| 4.33 #14091 | `Float.lt`/`Float.le` → `Bool` | 0 |
| 4.29 #12897 / 4.30 | `inferInstanceAs` — see W14, NOT zero | **3** |

### W14 — `inferInstanceAs` requires an expected type and now rewraps (4.29 #12897, restated as a 4.30 breaking change) — **2 sites WILL break, 1 probably**

Release text (4.30 breaking-changes section): "As `inferInstanceAs A` now
needs to know the source and target types exactly before it can continue,
it cannot be used anymore as a synonym for `(inferInstance : A)`, use the
latter instead when source and target type are identical." And 4.29
#13115: "the old example (`#check inferInstanceAs (Inhabited Nat)`) no
longer works."

Exactly 3 sites, all in `ACL2Lean/MirrorProofs/OrderBridge.lean`:

* `:101 toLE := inferInstanceAs (LE Int)` — source type == target type.
  **WILL break.** Fix: `inferInstance`.
* `:106 decLE := inferInstanceAs (DecidableRel (α := Int) (· ≤ ·))` —
  source type == target type. **WILL break.** Fix: `inferInstance`.
* `:48 decLE a b := inferInstanceAs (Decidable (_ = true))` — an
  underscore in the SOURCE type, with the expected type only reachable by
  unfolding the `le` field default to `lexorderB a b = true`. This is the
  "must know both types exactly" case. **Very likely breaks.** Fix: spell
  the type (`inferInstanceAs (Decidable (lexorderB a b = true))`) or use
  `inferInstance` with an explicit ascription.

Also relevant here: the 4.29 `inferInstanceAs` rewrapping is controlled
by `backward.inferInstanceAs.wrap` (+ `.reuseSubInstances`, `.instances`,
`.data`), all default-enabled. Those are the porting escapes; same
last-resort discipline.

### W15 — `theorem`s are now opaque, including in the kernel (4.30 #12973) — **VERIFY@P1**

One line in the changelog with no migration note: "makes theorems opaque
in almost all ways, including in the kernel." We addDecl 7 `.thmDecl`s
(`Replay/Runner.lean:315`,`:427`,`:483`;
`Replay/ParametricInstantiate.lean:525`,`:868`,`:960`;
`MirrorProofs/IsoKit.lean:758`) and then CONSUME those constants in
later proof objects — `Runner.lean:238` describes reading the
"freshly `addDecl`'d D1 REPLAYED CONSTANT". If any consumer relies on
unfolding a theorem's PROOF (as opposed to using its statement), it
breaks. I could not settle this on paper. **`VERIFY@P1`.** Also
`Replay/Runner.lean:434` and `Replay/WorldTransport.lean:32` both note
proofs closed by `rfl` where "kernel whnf reduces the 55-arm match" —
that is definitional unfolding of a `def`, not a theorem, so it should
be unaffected.

### W16 — Mathlib and core name-surface growth vs `Tests/MirrorNameCheck.lean` — **MAY break**

`Tests/MirrorNameCheck.lean` is a BUILD-TIME collision linter: a mirror
spec name declared in `ACL2Lean/Mirrors/` must not collide with any
constant whose defining module is rooted at `Init`/`Lean`/`Std`/
`Batteries`/`Mathlib`, at the root or dot-notation-reachable on
`List`/`Nat`/`Bool`/`Int`/`Option`. Five months of core and Mathlib
growth is therefore a live break vector for the mirror layer.

Our spec names at risk (all under `ACL2Lean.Sorting` / `ACL2Lean.Basics`):
`len, app, rev, revAcc, evens, odds, Ordered, insertOrd, isort, merge2,
msort, RelMode, relMode, filterRel, qsort, bnext, howManySmaller,
howManyBadPairs, bsort, howMany, memb, rm, Permuted, permWitness`.

Checked against every library addition named in the five changelogs —
`List.minOn/maxOn/minIdxOn/maxIdxOn`, `List.scanl/scanr`,
`List.splitOn/splitOnP`, `List.prod`, `Array.prod`, `Vector.prod`,
`Array.mergeSort`, `Nat.sqrt`, `BitVec.flattenList`, `Float.Model`,
`List.Nodup.length_le_of_subset`, `List.perm_ext_iff_of_nodup`,
`List.getElem_idxOf`, `List.Nodup.idxOf_getElem`,
`List.pairwise_lt_finRange`/`pairwise_le_finRange`/`nodup_finRange`,
`String.Slice.join`, `PersistentHashMap.alter` — **no collision from the
core side.** The risk that remains is MATHLIB's own five months of
growth, which the changelogs do not cover and which only the build can
answer. **`VERIFY@P1`.** If it fires, the fix is a rename in
`ACL2Lean/Mirrors/` — which is a MIRROR STATEMENT CHANGE and therefore a
phase-4 golden/receipt event, not a quiet edit. Flag it to Mike rather
than absorbing it.

---

## 2. Deprecation sweep (charter phase 3)

"Every API the 4.29–4.33 notes deprecate that we USE." Grep result:
**none.** Every deprecation in the five changelogs — `Except.of_wp`,
`extract_eq_drop_take`, `Slice.findNextPos`, the `cons₂` family,
`Lean.RBMap` / `Lean.RBTree`, the `Subarray` operations, the
`liftMethod` alias — is grep-zero in `ACL2Lean/ Tests/`. See W13 for the
full table.

**So phase 3's forward-compat debt is not "remove deprecated API uses"
(there are none). It is exactly two things:**

1. **New deprecation MACHINERY that could hit us via imports.** 4.31 adds
   `deprecated_module` (#13002, warning on IMPORT of a deprecated module,
   controlled by `linter.deprecated.module`), `deprecated_syntax`
   (#13108), and deprecated OPTIONS (#13195, `linter.deprecated.options`).
   4.32 #13908 uses `deprecated_module` on `Lean.RBMap`/`RBTree`. We do
   not import those, but a transitive Mathlib/Batteries import could pull
   a deprecated module and emit a warning into OUR build under the
   zero-warnings rule. **`VERIFY@P1`** — this only shows up in the real
   build log.
2. **The `backward.*` ledger.** Per the charter, any `backward.*` option
   we cannot avoid gets recorded in `TODO.md` with rationale. The
   candidate set this inventory identifies, in the order we would reach
   for them: `backward.isDefEq.respectTransparency`,
   `backward.isDefEq.respectTransparency.types`, `backward.dsimp.instances`
   / `simp +instances`, `backward.inferInstanceAs.wrap*`,
   `backward.do.legacy`, `backward.defeqAttrib.useBackward`. **The target
   is zero of these.**

Also per the charter's "do NOT adopt opt-in new semantics" rule, note but
DO NOT ADOPT: the `cbv` / `decide_cbv` tactics (4.29–4.32), `sym =>`
interactive mode (4.30+), `mvcgen'`/`vcgen` (4.31–4.33), `lake lint`
builtin linting (4.31–4.32), `unlock_limits` (4.31 #13211),
`autoTry.*` (4.33 #13830), `--incr-save`/`--incr-load` (4.32 #13965),
`postprocess_traces` (4.33 #14352). All are future options, not compat.

---

## 3. Lake / infrastructure items

Not code-breaking, but they change how phases 1 and 4 behave:

* **4.29 #12203 / #12537 / #13141**: Lake prefers HARD LINKS over copies
  when pulling from the local cache and marks cache artifacts read-only;
  `git clean -xf` now runs when updating dependency repositories. The
  latter interacts with the standing `~/.gitconfig` tripwire (memory:
  "Lake gitconfig footgun") — the charter's "stop all lake on any
  gitconfig warning" rule stands and matters MORE here.
* **4.30 #12927**: `lake cache get` downloads artifacts by DEFAULT
  (`--download-arts` obsolete; `--mappings-only` is the new opt-out).
  The charter's phase 1 says `lake exe cache get` — that is Mathlib's own
  cache exe and is unaffected, but if anything switches to `lake cache
  get` the semantics differ.
* **4.30 #12935**: new `fixedToolchain` package option, which Mathlib
  sets. Affects Lake's toolchain update procedure.
* **4.31 #13500**: `lake build` with no jobs now WARNS ("Nothing to
  build.") and is slated to become an error; `--allow-empty` suppresses.
  Our `just driver-coverage` runs `lake build Tests.DriverCoverage` —
  fine, that has a target.
* **4.31 #13028**: Lake rejects configs where multiple executables share
  a root module name. Ours are `Main` and `ReplayMain` — distinct.
  Benign.
* **4.30 #13683 / 4.33 #14284 / #14285**: compiled-config location moved
  and `compiled configuration is invalid; run with '-R'` failures made
  self-recovering. Net positive.
* **4.32 #13893**: `lake lint` flags `--extra`, `--lint-all` and the
  `@[builtin_nolint]` attribute REMOVED. We do not call `lake lint`
  (`Justfile` has no such recipe). Benign.
* **`.github/workflows/lean_action_ci.yml`** keys its dep cache on
  `hashFiles('lean-toolchain')` + `hashFiles('lake-manifest.json')` and
  installs elan with `--default-toolchain "$(cat lean-toolchain)"`. Both
  follow the pin automatically; no CI edit needed. (Remote CI is
  validated at the next networked push per the sandbox protocol.)

---

## 4. Estimate (charter phase-0 item 5)

### Which watchlist item is likely the biggest

**W1 — the simp/simp_all family, and within it `dpLeafTactic`
specifically.** Reasoning:

* It is hit by FOUR independent changes, not one: 4.29 #12244 (instances
  not processed), 4.29 #12172 (instance-parameter reclassification →
  rules fire that did not), 4.31 #13807 (arguments arrive beta-reduced),
  4.33 #13895 (mvar type checks at implicit transparency) — on top of
  five releases of churn in core's DEFAULT simp set (#12977 removed
  annotations, #12945 added forall lemmas, #12352 retuned slice
  annotations, #12449, #12642, #13054, #14231, #14267, and the 4.33
  grind/e-matching retunes) which the two `simp_all`-without-`only` kits
  (`dpLeafTactic`, `sim_iso_close`) inherit wholesale.
* It sits in the CERTIFIED path, not the scaffolding: `dpLeafTactic` is
  the discharge of the ratified DP carve-out.
* Its result is pinned BYTE-EXACTLY. `Tests/driver-coverage.golden` (153
  lines) records `REPLAYED 116/116` and the DP probe tally `✓62 ◌9 ✗0 of
  71`, and `just check-golden-current` compares golden to the live
  `.actual` with `cmp`. There is no slack: one leaf that stops closing
  moves the file, and per the charter phase 4 a golden move is a
  row-by-row diagnosis, never a repin.
* The fix has to stay carve-out-clean: adding a per-case tactic or a
  per-book kit row would be exactly the drift failure the project has
  ruled against, so the fix must be a behaviour-preserving addition to
  the FIXED kit.

Runner-up for *difficulty* (not volume) is **W2's `TotalOrder` instance
layer** — if `MirrorProofs/OrderBridge.lean` + `Mirrors/Sorting.lean`'s
class/instance stack does not survive the transparency changes cleanly,
it takes the entire sorting mirror corpus with it, and that is a charter
escape-hatch condition ("any closer/kit breakage cannot be fixed
behaviour-preserving").

Runner-up for *volume* is **W3 (`simpa`, 193 sites)** — likely the single
longest round, but boring.

### Rough phase-2 round count

The charter says one watchlist item per round, fast-gate labelled. On
that rule this inventory yields **8–10 rounds**, most likely **9**:

| # | round | driver | expected size |
|---|---|---|---|
| 1 | W14 `inferInstanceAs` (3 sites) | WILL break | tiny — do it first, it unblocks the instance layer |
| 2 | W2 instance/transparency layer (`TotalOrder`, `OrderBridge`) | MAY break, hardest | small edits, large diagnosis |
| 3 | W1a `dpLeafTactic` + golden diagnosis | WILL move golden | medium, high care |
| 4 | W1b the three closer kits (`mirror_square_close`, `sim_iso_close`, `mirror_transport_close`) | WILL break | medium |
| 5 | W3 `simpa` reducible-transparency (193) | MAY break | large, mechanical |
| 6 | W1c bulk simp/simp_all fallout in `Replay/Lemmas/*`, `ClausifyBridge`, `EvalOpt` | MAY break | large, mechanical |
| 7 | W7 `dsimp only []` no-progress (35 bare sites) | MAY break | small |
| 8 | W6 new linters/warnings, zero-warnings rule | MAY break | small–medium |
| 9 | W8 resource budgets (`maxRecDepth`, 82 `maxHeartbeats`) + W12 `do` elaborator | MAY break | medium |
| (10) | residual: W9 grind, W10 equations/`fun_induction`, W11 case tags, W15, W16 | MAY break | only if phase 1 finds them |

Rounds 5 and 6 could merge or could each split in two depending on
volume; that is why the range is 8–10. Rounds 1–4 are the ones with real
design content; 5–8 are grinding.

**Calibration caveat.** Every number above is derived from grep counts
and changelog text, not from a compiler. The phase-1 triage (mechanical
bump → categorise every error/warning) is what makes it real, and if
phase 1's error census is wildly off this table, believe phase 1.

---

## 5. `VERIFY@P1` checklist

Things this inventory could not settle on paper. Phase 1's triage should
explicitly answer each:

1. Does `dpLeafTactic` still close all 71 DP probes / does the golden
   move? (W1, the arc's pivot question.)
2. Does the `TotalOrder` / `decLE` / derived-`LT` / `decEqOfOrder`
   instance stack still elaborate? (W2.)
3. Do any of our 73 `@[simp]` theorems trip `warning.simp.varHead` /
   `warning.simp.otherHead`? (W6.)
4. Does #12325/#14196 fire on `intEmbed` / `optEmbed` / `intOrderedEmbed`?
   (W6.)
5. Does `Replay/DpLift.lean:113`'s `instance (w : World) : Decidable …`
   survive #13389's impossible-argument check? (W6.)
6. Do the 7 `addDecl .thmDecl` consumers survive #12973 (theorems opaque
   in the kernel)? (W15.)
7. Does `MirrorNameCheck` still pass against mathlib@v4.33.0's name
   surface? (W16 — and if not, escalate rather than rename.)
8. Do any transitively-imported Mathlib/Batteries modules now carry
   `deprecated_module` and emit an import warning into our build?
   (Section 2.)
9. Does `undestructuredGuardCtor?`'s equation-shape read still find the
   guard, and do the 6 `fun_induction … with` case names still resolve?
   (W10.)
10. Is the panic gone? `grep` the fresh gate artifact for
    `SymbolFrequency` — the charter's stated reason for the bump
    (upstream #13202, which I confirmed present in the v4.31.0 changelog
    under Tactics: "fixes a heartbeat timeout from an environment
    extension at the end of the file that cannot be avoided by raising
    the limit").
