# Independent validation of the 21 mirror products (comparator harness)

External, independent check that the project's 21 mirror PRODUCTS — the
Lean-idiomatic, zero-ACL2 theorems in `ACL2Lean/MirrorProofs/` (6 Basics +
15 Sorting) — really prove the statements they claim, using only the
permitted axioms, validated by TWO independent kernels (Lean's own and
nanoda, a from-scratch Rust implementation). This is engineering evidence
of the "kernel-checked" claim from OUTSIDE the project's own build: the
validator never runs the project's tactics or macros — it consumes only
exported proof terms.

STATUS: committed on `mdd/validation-harness` (2026-08-19), branched
from main @ 71399d2 (post release-hygiene merge), and RUN CLEAN against
that tree (fresh full run; verdict below). The committed surface is the
harness DEFINITION (challenge, solution, config, spec copies, this
README, the link script); the tools and run outputs stay untracked —
see "Fetching the tools".

## THE VERDICT (2026-08-19, verbatim; exit code 0; `comparator-run.log`;
fresh full run against the `mdd/validation-harness` tree — main @
71399d2 + this harness — after the release-hygiene merge rebuilt the
parent's Waypoints/MirrorProofs chain)

```
Building Challenge
[... 21 `declaration uses 'sorry'` warnings — the challenge's own stubs ...]
Build completed successfully (5 jobs).
Exporting [48 targets] from Challenge
Building Solution
Build completed successfully (3 jobs).
Exporting [48 targets] from Solution
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

All 21 products pass: statement match (transitive, constant-by-
constant), axiom check (exactly `propext`/`Quot.sound`/
`Classical.choice` permitted), nanoda kernel replay, Lean kernel
replay.

NEGATIVE CONTROL (that the harness can fail): demonstrated at landing —
one challenge statement was flipped (`app_assoc` stated at `Nat` while
the solution proves it at `Int`), the comparator rejected with exit 1:
`uncaught exception: Challenge and solution theorem statement do not
match: 'Validation.app_assoc_int'`, and the challenge was restored
(the committed file is the restored one; the clean verdict above is
from the untampered challenge). Organically, too — the
statement-match step genuinely REJECTED two intermediate drafts of this
harness (`Const does not match … 'ACL2Lean.Sorting.isort._f'` for the
concatenated-module draft; `… 'ACL2Lean.Sorting.bnext.induct_unfolding'`
for the renamed-module draft), and the nanoda path rejected the
tagged-release binary on a format mismatch before it was bumped to
master. The comparator's own test suite (`runtests.lean`, 14 projects
incl. adversarial ones) covers the rejection paths systematically.

## What is checked, and by what

The tool is [leanprover/comparator] (Lean FRO's trustworthy judge for
Lean proofs, built for the AIMO competitions). Given a trusted
`Challenge.lean` (statements with `sorry`) and an untrusted
`Solution.lean` (the same statements, proved), it:

1. builds both modules with `lake` (each build inside a `landrun`
   Landlock sandbox);
2. runs `lean4export` on both environments;
3. verifies, over the EXPORTED TERMS, that every constant transitively
   reachable from the 21 challenge statements is IDENTICAL in the two
   environments (so the Solution proves exactly the challenge's
   statements — same defs, same instances, all the way down), plus the
   kernel-primitive constants;
4. verifies the 21 proofs transitively use ONLY
   `propext`, `Quot.sound`, `Classical.choice` (in particular: no
   `sorryAx`, no `Lean.ofReduceBool`/`native_decide`);
5. replays the whole exported Solution environment through the
   independent **nanoda** kernel (`enable_nanoda: true`);
6. replays it through the **Lean kernel** (`Environment.replay` from an
   empty environment — the project's `.olean`s are never trusted as
   proofs, only as term sources for the exporter).

The verdict line on success is `Your solution is okay!`.

## The files

- `Challenge.lean` (+ `ACL2Lean/Mirrors/Basics.lean`,
  `ACL2Lean/Mirrors/Sorting.lean` in THIS directory) — THE TRUSTED
  STATEMENT (the shop window). The two spec modules are BYTE-IDENTICAL
  copies (`cmp`-verifiable) of the project's zero-import mirror spec
  files of the same paths (each with core-prelude-only imports), built
  locally under the project's own module names; `Challenge.lean`
  imports the two and adds the one `TotalOrder Int` instance the
  sorting statements bind (verbatim from
  `ACL2Lean/MirrorProofs/OrderBridge.lean`) plus the 21 product
  statements as `theorem … := sorry` in namespace `Validation`
  (14 sorting at `Int`, `permWitness_complete` at `Option Int`,
  6 basics at `Int`). Provenance blob SHAs are pinned in the headers.
  The verbatim-copy discipline is not decoration: the comparator's
  step 3 REQUIRES the challenge's copy of every spec constant to
  elaborate to exactly the constants the project's own modules produce.
  Two non-obvious consequences, both hit and fixed while drafting:
  the copies must keep the project's one-module-per-file split (in a
  concatenated module the elaborator deduplicates match auxiliaries
  across the two specs — `Sorting.odds` reused `Basics.len.match_1`),
  and they must keep the project's exact MODULE NAMES (private
  auxiliary constants such as `evens.match_1.splitter` embed the
  defining module name: `_private.<module>.0.…`).
- `Solution.lean` — imports `ACL2Lean.MirrorProofs.Basics` +
  `ACL2Lean.MirrorProofs.Sorting` and restates the 21 under the
  `Validation` names, each proof an alias of the project product.
- `comparator-config.json` — the two modules, the 21 theorem names,
  `permitted_axioms = ["propext", "Quot.sound", "Classical.choice"]`,
  `enable_nanoda = true`.
- `lakefile.toml` + `lean-toolchain` — a standalone Lake workspace
  (libs `Challenge`, `Solution`), deliberately with NO `require`.
- `.parent-lean-path` (untracked; regenerated by `link-parent-libs.sh`
  when absent) — snapshot of the parent workspace's
  `lake env printenv LEAN_PATH`. Delete it (with `.lake/`) to re-snap
  after the parent's dependency set changes.
- `link-parent-libs.sh` — symlinks the parent workspace's built
  library dirs into `validation/.lake/build/lib/lean` so the Solution's
  project imports resolve. This is the reason there is no `require
  ACL2Lean from ".."`: a Lake path-dependency would resolve the
  project's own dependencies (mathlib etc.) into THIS workspace and
  then rebuild the project inside the PARENT tree against them,
  clobbering the parent's build state. The symlink route is strictly
  read-only toward the parent. The `ACL2Lean` subtree is materialized
  as REAL directories (entries symlinked one level down, the parent's
  `Mirrors` dir not linked at all) so that building the local spec
  copies can never write through a symlink into the parent, and so the
  local `ACL2Lean.Mirrors.*` oleans shadow the parent's for everything
  loaded in this workspace.
- `probe/` — pp.all statement probes used while drafting (parent
  products vs challenge statements elaborate identically); not part of
  the validation flow proper.
- `comparator-run.log` (untracked) — the latest full run transcript.

## Fetching the tools (all in `validation/tools/`, untracked, all project-local)

From `validation/`:

```sh
mkdir -p tools && cd tools
git clone https://github.com/leanprover/comparator   && (cd comparator   && git checkout v4.33.0 && lake build lean4export comparator)
git clone https://github.com/leanprover/lean4export  && (cd lean4export  && git checkout v4.33.0 && lake build)
git clone https://github.com/ammkrn/nanoda_lib       && (cd nanoda_lib   && git checkout 6ae1f0cd962f081f6c423454c5da729d841236a7 && cargo build --release)
git clone https://github.com/Zouuup/landrun          && (cd landrun      && GOPATH=$PWD/../.go/path GOCACHE=$PWD/../.go/cache GOMODCACHE=$PWD/../.go/modcache go build -o landrun ./cmd/landrun)
```

## Tools (pinned refs)

| tool | ref | note |
|---|---|---|
| `comparator/` | tag `v4.33.0` (3927ad383f208ae977c340a91c48ac9b497d2097) | toolchain v4.33.0; built with `lake build lean4export comparator` |
| `lean4export/` | tag `v4.33.0` (15f6055e299ad5b89345e533cc2192f4cc00f659) | same rev the comparator's manifest pins |
| `nanoda_lib/` | `master` @ 6ae1f0cd962f081f6c423454c5da729d841236a7 (v0.4.15) | **deviation from "latest tag"**: the latest tag v0.3.2 predates the ndjson export format + `eagerReduce` gadget this comparator/lean4export pair emits and fails with a parse error; master is required. `cargo build --release` → `target/release/nanoda_bin` |
| `landrun/` | `main` @ 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4 | REAL landrun, built with Go (project-scoped `GOPATH`/`GOCACHE`/`GOMODCACHE` under `tools/.go/`); WORKS nested inside the outer Landlock sandbox (see scoping note) |

No extra Lean toolchain was pulled: every ref above is at (or agnostic
to) `leanprover/lean4:v4.33.0`, already in the shared elan store.

## Running it

```sh
cd validation
./link-parent-libs.sh                # refresh symlinks (idempotent)
COMPARATOR_LANDRUN=$PWD/tools/landrun/landrun \
COMPARATOR_LEAN4EXPORT=$PWD/tools/lean4export/.lake/build/bin/lean4export \
COMPARATOR_NANODA=$PWD/tools/nanoda_lib/target/release/nanoda_bin \
lake env ./tools/comparator/.lake/build/bin/comparator comparator-config.json
```

(`lake env` supplies LEAN_PATH — including the symlinked parent libs —
to `lean4export`; the sandboxed `lake build` steps resolve the same
imports through the symlinks, so no environment needs to leak into the
sandbox.)

## The landrun scoping note (honest scope of the sandbox layer)

Nested landrun WORKS here: the outer nono sandbox is Landlock-based and
Landlock rulesets stack, so landrun's ruleset applies as a further
restriction (`-ldd` is required so shared libraries stay executable —
without it, exec fails with `permission denied`). The comparator's runs
in this harness therefore use REAL landrun, not the fake-landrun
development shim. The README-documented systemd-run wrapper (a
defense-in-depth guard for a landrun vulnerability fixed in Linux 7.1)
is NOT used: systemd-run is not available inside the sandbox.

Honest scoping, per the two-standard rule: the landrun layer exists to
defend a judge against MALICIOUS submitted solutions (adversarial
`Solution.lean` code attacking the checking environment at build time).
In this harness we validate OUR OWN artifacts — the standard is the
honest mistake, not the motivated adversary — and the properties we
actually consume (statement match, permitted-axioms check, Lean-kernel
+ nanoda replay of exported terms) are established AFTER the builds,
from the exported environments, and do not depend on the build sandbox
at all. So the sandbox is a speedbump we get for free, not a property
we rely on; do not harden it.

## Trust boundaries (what this run does and does not establish)

Established (independently of the project's build): the 21 named
theorems, as stated in the zero-import `Challenge.lean`, have proofs
accepted by two independent kernels from exactly
`{propext, Quot.sound, Classical.choice}` — no `sorryAx`, no
native_decide — and those statements bottom out in the challenge's own
self-contained definitions.

NOT established (unchanged from the project trust note): statement
authenticity (that each product is the named ACL2 theorem) and replay
fidelity (that the proof retraces ACL2's recorded reasoning) are not
kernel properties; they remain enforced one level down by provenance,
pins, seam/axiom gates and review. This harness is an independent
re-check of the KERNEL-side claim only.

## The Justfile recipe (DRAFT — not yet wired: the task boundary this
harness was drafted under forbids editing the tracked Justfile, and the
permission system upheld that boundary at landing time; wiring it is a
one-paste change for whoever owns the Justfile next)

```just
# Independent validation: the 21 mirror products re-checked by
# leanprover/comparator (statement match + axiom check + Lean-kernel
# and nanoda replay of the exported terms). See validation/README.md.
validate-products:
    cd validation && ./link-parent-libs.sh
    cd validation && COMPARATOR_LANDRUN=$PWD/tools/landrun/landrun \
      COMPARATOR_LEAN4EXPORT=$PWD/tools/lean4export/.lake/build/bin/lean4export \
      COMPARATOR_NANODA=$PWD/tools/nanoda_lib/target/release/nanoda_bin \
      lake env ./tools/comparator/.lake/build/bin/comparator comparator-config.json
```

[leanprover/comparator]: https://github.com/leanprover/comparator
