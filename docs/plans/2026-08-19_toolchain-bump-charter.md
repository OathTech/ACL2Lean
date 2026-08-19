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
