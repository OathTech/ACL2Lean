# The `SymbolFrequency` build panic — measurement record (2026-08-19)

> Dated record of a measurement. The live disposition is
> [`docs/OVERVIEW.md`](../OVERVIEW.md) § *Known limitations* → *A non-fatal
> toolchain panic in the build output*; the backlog entry is in `TODO.md`.
> Toolchain-version-specific: everything below was measured against the
> toolchain pinned at the time, `leanprover/lean4:v4.28.0`. A toolchain bump
> invalidates the file/line citations and may remove the panic entirely.

## What is printed

A full build — and `just test`, and the claim gate — prints, while building
the heaviest coverage modules (`Tests.Coverage.BSsortsEquivalent` is the
usual one):

```
PANIC at _private.Lean.LibrarySuggestions.SymbolFrequency.0.Lean.Environment.unsafeRunMetaM
Lean.LibrarySuggestions.SymbolFrequency:75:24: (deterministic) timeout at `whnf`,
maximum number of heartbeats (200000) has been reached
```

## What it is

Lean's own `symbolFrequency` persistent environment extension — the
premise-frequency index behind library-suggestion tactics — runs its
`exportEntriesFnEx` over the module's constants **at export**, i.e. after all
elaboration is done. On our largest modules that post-pass exceeds its
heartbeat budget and panics out of the extension.

## Why it is not a warning being tolerated

Against the "warnings are unacceptable" rule in `CLAUDE.md`: it is not our
elaboration and carries no semantic content — it happens strictly after the
module's declarations are elaborated and kernel-checked, the module still
writes its `.olean` and the build reports `Build completed successfully`;
nothing we check depends on that extension (no proof, no `#print axioms`
receipt, no `#guard_msgs` pin, no golden row, no gate reads it — its only
consumers are suggestion tactics this project does not use); and the full
claim gate records the panic alongside `TRUE_EXIT=0`.

## Why it is not fixed here

Elimination was attempted rather than assumed, and refuted by measurement.

### (a) No switch

The extension is registered by `builtin_initialize` in the Lean shared
library, has no `register_builtin_option` gate and no `lean` CLI flag, and
its heartbeat budget is not user-reachable —
`Lean.Environment.unsafeRunMetaM` builds a FRESH `Core.Context` with
`options := {}`, and `maxHeartbeats` defaults off *those* options
(`Lean/CoreM.lean:217,225` in the pinned v4.28.0 source), so neither
`set_option maxHeartbeats` in the module nor `-DmaxHeartbeats=…` on the
command line reaches it (checked against the toolchain source, 2026-08-19).

### (b) No split — and the reason kills the whole class

The budget is not compared against the export pass's OWN cost. That same
fresh `Core.Context` also takes `initHeartbeats := 0` (the field default,
`Lean/CoreM.lean:224`), so `checkMaxHeartbeatsCore` compares the **absolute**
thread heartbeat count — everything the module burned during its entire
elaboration — against the fixed 200 000 000. Reproduced directly: a `run_cmd`
that burns heartbeats and then runs a `MetaM` job inside a replica of that
context returns the byte-identical timeout string *only* after the burn.

Calibrated against real work, `Runner.runBook` costs ~16 heartbeat-units/ms,
so the budget is spent after ~12 **seconds** of replay elaboration.
`Tests.Coverage.BSsortsEquivalent` replays for ~477 s (~38x the budget);
`BSqsort` at ~423 s (~35x) does *not* panic, so module weight is not even the
discriminator at the margin. Bringing a module under budget would take ~40
pieces — and the coverage harness has no sub-book unit to split into:
`coverage_book%` is one module per BOOK per golden section, and the
aggregate's tiling check requires exactly one section per `corpusOrder`
entry, so a partial-book split is new machinery, not a use of the existing
mechanism.

### (c) The deny-list surface, measured and not taken

The one surface left is the extension's own deny lists (`nameDenyListExt` /
`typePrefixDenyListExt`, both documented for `run_cmd modifyEnv …`): deny
every local theorem and the pass has nothing to do. **Not taken** — measured
on the offending module, a `typePrefixDenyListExt` entry for `ACL2` covers 79
of its 81 processed theorems but not the 2 with `Eq`-headed statements, and
one survivor re-triggers the panic; the alternative is an enumerated name
list over our generated namespaces, i.e. exactly the rotting name-predicate
cruft the audit practices say to delete rather than add.

## How it reads in a gate artifact

The panic text is stored in **Lake's job log** and replayed by every later
build that finds the module up to date — the three copies in a single gate
artifact are one panic replayed by three lake invocations, not three
failures — so any future fix only shows up once that module actually
rebuilds.

## The real fix

Upstream: `withCurrHeartbeats` around the export pass, or a budget derived
from it. Until then the panic is accepted, disclosed noise — and it is never
a licence to wave through a genuine proof, replay or gate failure.
