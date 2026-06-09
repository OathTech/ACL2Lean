# World.defs → reduction-friendly `DefMap` (assoc list)

_Created 2026-06-08._

## Why

Goal: **eliminate ALL hand-marshalling** between ACL2 output and the kernel-checked
replay. The driver must derive every fact it needs from mechanically-produced
artifacts (the `Development` + the proof tree), nobody enumerating anything.

The one friction blocking "derive structural facts on demand" is that
`World.defs : Std.HashMap` lookups do **not** reduce by `decide`/`rfl` — so the
facts `w.defs.get? fn = some (formals, body)` and `w.defs.get? builtin = none`
today are hand-written theorems proved with `simp [World.empty]`. We replace the
representation everywhere (same repr in the trust-anchor `evalOpt` and in proofs)
with an assoc-list `DefMap` whose lookups reduce by `decide`. Then the driver
proves each structural fact on the fly — no generated theorems, no hand facts.

This is the spine of the zero-marshalling design AND the socket the later measure
track plugs semantic facts (totality/type-prescription) into.

## Design — preserve the lookup INTERFACE, change only the type

Define `DefMap` mirroring the `HashMap` surface the code already uses, so call
sites are untouched:

```
abbrev DefMap := List (Symbol × (List Symbol × SExpr))
def DefMap.get?   (m : DefMap) (s : Symbol) : Option (List Symbol × SExpr) := m.lookup s   -- List.lookup, BEq
def DefMap.insert (m : DefMap) (s : Symbol) (v : List Symbol × SExpr) : DefMap := (s, v) :: m.eraseKey s
instance : EmptyCollection DefMap := ⟨[]⟩
```

`World.defs : DefMap`. Then `w.defs.get? s`, `w.defs.insert n (f,b)`, `defs := {}`
all typecheck unchanged. **Invariant to preserve:** `get?` semantics must match
`HashMap` exactly — latest insert wins, absent key → `none`. (`eraseKey` before
prepend keeps the list dup-free so `Repr`/enumeration is clean; `get?` correctness
holds either way.) Pinned by characterization tests below.

`get?` on a *concrete* world now reduces by `decide`/`rfl` (List.lookup + BEq on a
concrete list), which is the entire point.

Note: `evalOpt` does one `defs.get?` per function call — assoc-list is O(n) vs
O(1). The corpus has a handful of functions and `evalOpt` is fuel-bounded /
proof-and-test-only, so this is negligible; flagged, not a concern.

## Phases (each ends green; trust-core change gated)

- **P0 — Coverage first (this is the net).**
  1. Baseline: full `just ci` green; record `#print axioms` of the hand proofs
     (SimpleWorld my-len-my-app, AppAssoc) + driver mirrors = clean; note the
     differential harness `scripts/diff_eval.sh` result (evalOpt vs ACL2) as the
     semantic net (run manually — needs ACL2).
  2. Characterization tests for the World.defs interface (`Tests/SyntaxTest` or new
     `Tests/WorldDefsTest`): `get?` on present / absent / shadowed-reinserted /
     empty. These encode the invariant and pass on the CURRENT HashMap impl — they
     are the spec the new impl must satisfy.
- **P1 — Introduce `DefMap`, switch `World.defs`'s type (trust-core edit).** Fix the
  `{}` literals + gen-world emit. Everything else compiles unchanged. Characterization
  tests stay green (now also provable by `decide`).
- **P2 — Reduce concrete fact proofs to `decide`/`rfl`.** Replace `simp [World.empty]`
  / `getElem?_insert` World-fact proofs. Add a reduction-friendliness test:
  `example : world.defs.get? fn = some (...) := by decide`.
- **P3 — Driver derives structural facts (retire hand-marshalling).** Add
  `Driver.proveDefLookup` / `proveNoShadow` / `deriveDefInfo` that build the proof
  by `decide` from the World Expr; remove the hand `sq_def`/`empty_no_*`/`DefInfo`
  from the test harness. The replay elaborator builds its `ReplayConfig` from the
  World/Development alone.
- **P4 (follow-on) — single source.** Build the `evalOpt` `World` as a projection of
  the `Development`'s `defun` events, so the only input is the parsed proof-log.
  Then the coverage harness (item 2) is nearly free.

## Coverage strategy (the explicit ask)

- **Characterization tests** pin the `get?`/`insert` contract before the change.
- **Differential harness** (`evalOpt` vs real ACL2) is the semantic net — unchanged
  lookup semantics ⇒ stays green.
- **Axiom-clean hand proofs + driver mirrors** are the integration net — run
  `#print axioms` before and after each phase; must stay `{propext, Classical.choice,
  Quot.sound}`.
- A **`by decide` reduction test** proves the new repr actually bought us the
  on-the-fly derivation.
