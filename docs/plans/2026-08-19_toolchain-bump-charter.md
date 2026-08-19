# Toolchain bump arc charter — v4.28.0 → v4.33.0 (2026-08-19)

Branch: `mdd/toolchain-bump` from main @ a7c30b6 (the reviewer-round
merge). Mike's direction (2026-08-19, verbatim): "Let's merge, then
charter the bump arc. Ideally we'd get to the latest stable version of
Lean (and if there are decisions that would make future bumps easier,
let's do them too - eg. remove things we know are deprecated".

## Why

- The `LibrarySuggestions.SymbolFrequency` panic (diagnosed to the
  mechanism in the reviewer round; classified non-semantic in
  docs/OVERVIEW.md) is FIXED upstream by leanprover/lean4#13202
  (`maxHeartbeats := 0` in the export pass's context — the same
  mechanism our diagnosis isolated, fixing issue #12989). Verified
  present in the tagged sources of v4.31.0/v4.32.0/**v4.33.0**; absent
  in v4.29.0/v4.30.0. Latest stable is v4.33.0 (2026-08-10); Mathlib
  publishes a matching `v4.33.0` tag.
- Crossing the 4.29 breaking changes is the cost at ANY bump level, so
  go straight to current.

## Target state

`lean-toolchain` = `leanprover/lean4:v4.33.0`; `lakefile.toml` mathlib
`rev = "v4.33.0"`; everything green under the full protocol; the panic
GONE from build/gate output (verify by grep of the fresh gate artifact);
docs/OVERVIEW.md's panic classification updated to "eliminated at
v4.31.0+ (upstream #13202); bumped 2026-08-19"; forward-compat debt
paid (below).

## Known breaking-change watchlist (from the 4.29–4.33 release notes —
inventory phase must complete it from the full changelogs)

- **4.29: `simp`/`dsimp` no longer process typeclass instances by
  default.** Our transport/iso closers are fixed `simp only` kits —
  the highest-risk item. Prefer real fixes (add the needed instance
  equations to the kit rows explicitly, behavior-preserving) over
  `set_option backward.dsimp.instances true`.
- **4.29: `isDefEq` no longer auto-raises transparency on implicit
  args.** Our formula pins rely on defeq ascriptions — verify each pin
  still elaborates; a pin failing here is a diagnosis item, never a
  loosening.
- **4.30: `compileDecl` callers may need `markMeta`.** Our elaborators
  (`mirror_iso%`, `mirror_transport%`, `derive_exec%`, the coverage
  harness) are direct callers — audit each site.
- **4.29: `noncomputable` tightening; inductive typeless-binder
  change; universe-metavariable promotion change.**
- 4.31–4.33: inventory from the release notes during phase 0 (not yet
  read in detail — do not assume this list is complete).

## Phases

0. **Inventory.** Read the v4.29.0–v4.33.0 release notes in full;
   produce the concrete breakage watchlist mapped to our call sites
   (grep for each changed API); list every deprecation warning the
   current tree would emit under the new toolchain.
1. **Mechanical bump + triage.** Toolchain + mathlib pin bump; `lake
   exe cache get`; full build; categorize every error/warning by
   watchlist item. No fixes yet — the triage IS the deliverable of
   this phase (commit the pin bump only when the tree builds).
2. **Fix rounds, behavior-preserving.** One watchlist item per round,
   fast-gate labeled. `backward.*` escape-hatch options are a LAST
   resort, used only with a comment naming the real fix and a TODO
   entry — the arc's purpose includes NOT accumulating them.
3. **Forward-compat cleanup (Mike's explicit scope addition).** Fix
   every deprecation warning (zero-warnings rule covers this anyway
   under the new toolchain); remove usages of APIs the release notes
   mark deprecated even where still warning-free; record any
   `backward.*` option we could not avoid, with rationale, in TODO.md.
   Do NOT adopt opt-in new semantics (e.g. the new `do` elaborator)
   — that is churn, not compat; note them as future options instead.
4. **Full verification.** Golden must be BYTE-IDENTICAL (sweep output
   is our own formatting; any diff is a diagnosis item, likely a real
   behavior change — row-by-row, never a repin without diagnosis).
   Regression net over the mirror layer (statements must be
   byte-identical; proof-term movement is expected wholesale under a
   new toolchain — report counts). All 21 receipts re-verified. All
   statics incl. submodule triple. The panic grep (zero occurrences).
   Full `just claim-gate` TRUE_EXIT=0; claim-point commit; merge
   candidate presented for explicit approval.

## Law

Standard: fidelity rules; two-tier gating; golden protocol; never
push; merge only with sign-off at the moment; J-numbered log entries
in this charter; receipts pinned; sorries 0.

**Shared-state note (global-changes rule):** the bump requires elan to
install `v4.33.0` into the SHARED `~/.elan` toolchain store and lake
to fetch the new Mathlib into `.lake/packages` (project-local). The
elan install is ADDITIVE (a new toolchain directory; no default
change, no effect on other projects' pins) but it is machine-global
state: it happens only on Mike's explicit go, recorded here when
given. **GIVEN 2026-08-19, verbatim: "go ahead with the elan update
(or I can do it)" — executed in-session (additive install only).** GIT-config hygiene per the standing tripwire: stop all lake on
any ~/.gitconfig warning.

## Escape hatch (goal-design rule)

Stop and report if:
- the golden moves and the row-by-row diagnosis shows a semantic
  change (not formatting) in replay behavior under the new toolchain;
- any closer/kit breakage cannot be fixed behavior-preserving (i.e.
  only a `backward.*` option or a statement change would restore it);
- a formula pin fails to elaborate for a defeq-transparency reason
  that a real fix cannot restore;
- Mathlib's v4.33.0 tag is incompatible with any pinned dependency;
- the fetch/install fails in-sandbox (network or store permissions);
- remaining work gates on a user decision.

## ARC LOG

### J1 — branch setup + phase-0 artifacts (2026-08-19)

`mdd/toolchain-bump` from main @ a7c30b6. First commit: the charter +
the W1–W16 inventory (both were untracked; the charter is committed so
this log has a home). Docs-only, fast-gate.

### J2 — PHASE 1: mechanical bump + census (2026-08-19)

Pins: `lean-toolchain` → `leanprover/lean4:v4.33.0`; lakefile mathlib
`rev = "v4.33.0"`. `lake update mathlib` checked out mathlib at the
`v4.33.0` tag (db584cd6), all eight deps inherited, manifest 1.1.0 →
1.2.0, cache 8690/8690 — the inventory §0.1 compatibility read
CONFIRMED. No ~/.gitconfig warning at any point.

The census was ITERATIVE (Logic.lean sits at the root, so each fix pass
exposed the next stratum; 14 build passes, logs in
`.tmp/p1-build-pass*.log`). Full error census by watchlist item:

| item | where it bit | count | verdict vs inventory |
|---|---|---|---|
| W1×W2 (#12244 simp skips instance args; #13895 mvar-check at `.instances`) | `Logic.toNat_minus_one`, `Tests/SpikeTauOmega`, `TsAlgebra:606`, `ExecGen:165` (`split at h`/`if_pos` on ite with stale instance arg); `Perm` bindArgs ×3 (ground ite condition undecided); `Derived.not_nil_iff` (default-set drift); **`dpLeafTactic`'s conditional row `trueListp_cdr_of_consp` silently stopped firing** ("failed to assign proof" at the discharger — the #13895 mvar-assignment check) | 7 sites + the DP kit | W1 predicted "WILL break dpLeafTactic / move the golden" — CONFIRMED, mechanism found |
| W3 (#13636 simpa closes at reducible) | `Lifting` ×8, `Linear` ×2, `RuleApp` ×1, `Imported/Sorting` ×11, `SortingOdds` ×1, `Waypoints/Validation` ×2 — every site the `carT`-family abbrevs over plain-`def` `app1`/`app2` | 25 sites | predicted MAY break/large — CONFIRMED, but 25 not 193 (most `simpa`s were fine) |
| W7 (#13807 beta-reduced args) | `FnAlias:291` — ONE bare `dsimp only []` became a no-op | 1 of 35 | predicted 35 exposed — only 1 actually fails |
| W10 (#12987 `._f` extraction) | `mirror_iso%` callee-square resolution went blind (`rev` no longer shows `app` in its value) → Basics/Sorting squares unclosed | 1 mechanism, many squares | NOT specifically predicted (W10 predicted equation-shape risk; the bite was value-shape) |
| W12 (#13912 `return` in `(← match …)`) | `Preprocess:277` — type error; `:286` same construct | 2 arms | inventory grepped `(← do` only — the `(← match` spelling was the miss |
| W15 (#12973 theorems opaque) | `ConstantInfo.value?` now returns `none` for theorems without `allowOpaque := true` → ALL seam gates false-negative (Catalog ×4, SeamGate ×1), Runner's axiom walk + 3 `hasSorry` checks silently weakened | 8 call sites | VERIFY@P1 item 6 — RESOLVED: this was the bite, and it hit the GATES, not the consumers |
| W8 (#13030 heartbeat inflation) | `Waypoints/OrderedPerms:80` deterministic timeout at default 200000 (→ 400000, the release's documented remedy; cascade had refused the capstone registration) | 1 site | predicted |
| W6 (new linters) | `linter.unusedSimpArgs`: LexorderOrder ×4 (+ transient ones in fixed files); `warn.classDefReducibility`: `Mirrors/Sorting.lean:170 TotalOrder.decLE` (the SHOP-WINDOW item, held for bless); `linter.defProp`: **94 warnings**, all `def X := <replay macro>` prop-valued pins (Waypoints ~73, Tests ~21) | 99 warnings | defProp not in the inventory at this volume — the biggest UNRESOLVED item |
| W1 ladder (#12244) | `mirror_square_close` lost the `unfold [instTotalOrderSExpr]` route (agree squares over the order instance): insertOrd/filterRel×4/bnext/ordered + merge2 guard split, isort cascade | 8 squares | predicted (inventory W1 item 2) |
| NEW-1 | `Parser:617` — structure-instance PATTERNS no longer auto-fill a proof field with a tactic default (`Symbol.canon`); fix `..` | 1 site | not in inventory |
| receipts | 3 axiom-receipt movements `[propext]` → `[propext, Quot.sound]` (howMany_map_invariant, memb_map_invariant, permWitness_map_hom) — still inside the pinned family, no sorryAx | 3 pins | charter phase 4 anticipated wholesale movement; actual: 3 |

**Non-events (census negatives, verbatim from the build):**
- **W14 `inferInstanceAs` (the inventory's "do-first WILL break"): did NOT
  break.** All three OrderBridge sites compile unchanged on v4.33.0.
  Round 1 is EMPTY.
- W16 MirrorNameCheck: PASSED — "55 spec names, no collision" against
  mathlib v4.33.0 (VERIFY@P1 item 7).
- W4 compileDecl/markMeta, W5, W11, W13: nothing fired.
- No `deprecated_module` import warnings from Mathlib/Batteries
  (VERIFY@P1 item 8). Only deprecation hit: `Lean.levelOne` →
  `Lean.Level.one` (Reflect.lean ×2, fixed — phase-3 debt folded in).

CHECKPOINT-RULE assessment: the census does NOT materially contradict
the inventory — same biggest item (W1/dpLeafTactic, confirmed with the
exact leaf), smaller overall surface than estimated except `defProp`.
The two flipped golden rows (bsort TRUE-LISTP-BNEXT `*1/5`,
ordered-perms ORDERED-PERMS `*1/3`, both `type-set-fc`) were DIAGNOSED
to the `trueListp_cdr_of_consp` discharge-assignment failure and
RESTORED byte-identically by the `consp` `instance_reducible` fix —
never repinned; `just check-golden-current`: "golden matches the live
assembly".

### J3 — PHASE 2 rounds (2026-08-19; see the round commits)

Round 1 (`inferInstanceAs`): EMPTY — census negative, no commit.
Rounds landed as commits on this branch (fast-gate each; the pins
commit is labeled RED-alone since the fixes use v4.33-only syntax and
the series is green only as a whole):
- Round A — W1×W2 instance-argument fallout + the DP-kit `consp`
  `instance_reducible` fix (golden-restoring).
- Round B — W3 `simpa` reducible-transparency (25 sites, `app1`/`app2`
  named explicitly).
- Round C — metaprogram API behavior: W10 `usedConstsThroughSatellites`
  in IsoGen; W15 `allowOpaque := true` at all 8 `.value?` sites (seam
  gates, axiom walk, hasSorry checks); W12 `return`→`pure`; W7 dsimp
  deletion; W8 heartbeat budget.
- Round D — the FIXED ladder: `mirror_square_close` gains `+instances`
  (the release's supported restore of pre-4.29 behavior; the
  bridge-LEMMA alternative is refused by the `unfold` definitions-only
  gate BY DESIGN — recorded in the kit comment); 3 receipt-movement
  pins updated with in-file notes.
- Round E — W6/NEW: unusedSimpArgs removals, the `Symbol.canon` pattern
  `..`, `Level.one`.

HELD BACK (uncommitted, checkpoint for Mike): the one-line
`Mirrors/Sorting.lean:170` change
`attribute [instance] TotalOrder.decLE` →
`attribute [instance_reducible, instance] TotalOrder.decLE`
(kills the `warn.classDefReducibility` warning; proven to build; SHOP
WINDOW so it needs an explicit bless).

OPEN (gates on a user decision — the goal-design escape hatch):
- **`linter.defProp` (94 warnings).** Every `def X := acl2_replay% …` /
  `driver_replayed% …` pin is a prop-valued `def` BY DESIGN (the
  machine-emitted type is deliberately not hand-ascribed; the hand pin
  is the adjacent `example`). `theorem` requires an explicit type, so
  the linter's own advice means hand-spelling ~90 machine types — a
  records-layer restructure — or scoped `set_option linter.defProp
  false` per declaration, which collides with the "never disable a
  linter" rule. Needs Mike's ruling; both routes are mechanical once
  ruled.
- Phase 3 residue beyond the above: none found (deprecation sweep came
  back empty as the inventory predicted; `--tstack` removal is a
  measure-first cleanup, untouched).
- Phase 4 (full sweep/golden verdict, claim-gate TRUE_EXIT=0, panic
  grep) — next executor; note the panic grep can only be run against a
  fresh full-gate artifact.
