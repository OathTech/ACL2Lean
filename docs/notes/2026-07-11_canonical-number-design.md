# Canonical `Number` — BUG-012 resolution, Option A (RATIFIED MDD 2026-07-11)

Decision: mirror ACL2's value-space restriction at the TYPE level — junk
number representations become unrepresentable. Chosen over Option B
(canonical-env hypotheses in every mirror/rule statement) because it fixes
the whole class once, keeps ∀-env statements unchanged (they become TRUE),
and is the masquerade objective enforced by the type: SExpr's value space =
ACL2's value space. Context + executed countermodel: docs/BUGS.md BUG-012;
design doc §D5 spike addendum.

## The type

```lean
/-- decidable canonicity: a ratio is canonical iff den ≥ 2 and reduced -/
def canonRat (n : Int) (d : Nat) : Bool := 2 ≤ d && n.natAbs.gcd d == 1

inductive Number
  | int (value : Int)
  | rational (numerator : Int) (denominator : Nat)
             (canon : canonRat numerator denominator = true)
```

- The invariant is a Bool-equality Prop: subsingleton (proof-irrelevant),
  decidable, kernel-reduction-friendly. `DecidableEq` hand-written (compare
  the data, proofs equal by proof irrelevance).
- **`decimal` is REMOVED.** ACL2 has no such value type; the reachability
  audit (2026-07-11) found NO constructor outside the unused `Logic.decimal`
  helper and two test literals — the parser stopped producing it at BUG-004.
- Every rational is built by `Logic.mkNumber` (THE smart constructor): its
  gcd-reduction now PROVES the invariant (`Nat.coprime_div_gcd_div_gcd`,
  Mathlib v4.28.0 is a dep). The raw `Logic.rational`/`Logic.decimal`
  helpers retire.

## Migration sites (audited 2026-07-11)

Construction: `mkNumber` (Logic.lean:47 — gains the proof), `expt`
(Logic.lean:194 — see finding below), `Logic.rational`/`.decimal` helpers
(retire), Driver.lean:64 (Expr REFLECTION of a parsed rational — reflect the
proof as a defeq `Eq.refl true`; the parsed value is canonical by
construction so the kernel closes it).
Match sites (arms updated/deleted, behavior-neutral on reachable values):
`toRat` (drop d=0 guard + decimal arm), printer (Syntax.lean:62), translator
(Translator.lean:84-85), TermOrder (fnCountEvg arms), EvalLemmas integerp
lemmas (3462/3503 + decimal arms), Tests/LogicTest + Tests/SpikeTauOmega,
the commented-out Lexorder proof block (superseded; delete when the new
order proofs land).

## Finding in passing — `expt` junk producer + sign bug (latent, unwired)

`Logic.expt` with negative exponent builds `.rational 1 denom.toNat` raw:
(a) `expt 1 -1` → `.rational 1 1` (non-canonical junk for the value 1);
(b) `expt -1 -1` → `denom = -1`, `(-1).toNat = 0`… wrong value (ACL2: -1).
UNREACHABLE today — `EXPT` is not wired into `callBuiltin` (differential
class `unsupported`). Fixed in this surgery by routing through `mkNumber`
with the sign moved to the numerator (`1/p = sign(p)/|p|`); differential
entries to be added when EXPT is wired (H3 policy).

## Gates (behavior must be UNCHANGED on the reachable surface)

1. `lake build` + `just test` green with the new type.
2. `just diff-test` — byte-identical outcomes (the canonicalization was
   already the reachable behavior; only the junk space changed).
3. `just ci` — coverage golden byte-identical.
4. THEN the WP3 spike completes for real: `lexorder_refl` / `_antisym` /
   `_trans` / `_total` proved on the canonical type (the countermodel is now
   unrepresentable; `toRat` becomes INJECTIVE on canonical numbers, which is
   exactly what the antisymmetry/transitivity cons-case needs).
