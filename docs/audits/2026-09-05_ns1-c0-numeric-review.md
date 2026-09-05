# NS1 C0 review — numeric representation and ACL2 semantics

Dated 2026-09-05. Authorized C0 reviewer 1 of 2, numeric semantics and
canonicity. Reviewed the candidate
[numeric design](../notes/2026-09-05_ns1-numeric-design.md), the
[charter](../plans/2026-09-05_bvchop-foundation-charter.md), and the pinned
sources in the `mdd/ns1-bvchop` worktree. ACL2 fork:
`e8d78e513d6867d04002f0df644da1723cc96e89`; Lean 4.33.0.

**Disposition:** the proposed `complex (real imag : Rat) (imag.num ≠ 0)`
representation survives this review. I found two existing numeric-path
divergences that the coherent migration must account for, and concrete reader
and reflection requirements to add to its checks. This is a design review,
not acceptance of implemented complex semantics or completion of C0/NS1.

No project Lean source was edited, no shared Lake target was built, and no
additional agents were used. The baseline claim-gate was running separately;
this report does not assert its result. Scratch inputs, outputs, and Lean
files are under `.tmp/ns1/c0-numeric-review/`.

## Findings

### F1 — reject zero-denominator ratio syntax before smart construction

**Medium; confirmed existing divergence, relevant to the new reader arm.**
`ACL2Lean/Parser.lean:549–560` parses a slash token and sends every parsed
natural denominator, including zero, to `Logic.mkNumber`.
`ACL2Lean/Logic.lean:80–81` returns integer zero for denominator zero.
Consequently `ACL2.Parse.parseAll "1/0"` and `"0/0"` both produce
`Except.ok [0]`. These are verbatim observed Lean outputs, independently
checked in `reflection-and-parser.out:5–6`.

Fresh ACL2 rejects `'1/0` and `'#C(1/0 1)` during reading. The latter's
transcript, `complex-zero-denominator.out:35–38`, says:

```text
failed to build ratio
Original error: arithmetic error DIVISION-BY-ZERO signalled
Operation was (/ 1 0).
```

**Inference:** a new `#C` arm that only checks whether the recursively parsed
components are rational would accept a rational value created from invalid
syntax. Reusing `mkRat`, which also returns zero for denominator zero, cannot
recover this lost distinction. The proposed representation is unaffected;
the validation must happen before the conversion.

Repair the shared rational reader and pin standalone and complex-contained
zero-denominator cases as reader errors. Preserve the arithmetic completion
`(/ 0) = 0`; literal syntax and function completion are different boundaries.
The primary independently reproduced this finding and registered **BUG-028**
while this review was in progress.

### F2 — rational constant weights drop the recursion call limit

**Medium; confirmed existing divergence in a component path the migration
will extend.** `ACL2Lean/TermOrder.lean:44–45` evaluates both components of a
rational through `fnCountEvgInt`, with no `calls` parameter.
`fnCountEvgRec` checks the limit only before handing the entire atom to that
helper (`TermOrder.lean:63–67`). By contrast, the rational arm of
`acl2/linear-a.lisp:1519–1524` recursively evaluates denominator and numerator
with `calls + 1` and `calls + 2`. Each recursive entry checks the limit at
`linear-a.lisp:1503–1505`.

Independent observed outputs:

| Input to `fn-count-evg-rec` / `fnCountEvgRec` | ACL2 | Current Lean |
| --- | ---: | ---: |
| `1/2`, accumulator 0, calls 997 | 6 | 6 |
| `1/2`, accumulator 0, calls 998 | 200000 | 6 |
| `1/2`, accumulator 0, calls 999 | 200000 | 6 |

Artifacts: `term-weight.lisp`, `term-weight.out:31`, `term-weight.lean`,
and `term-weight-lean.out`. This is also reachable through the public
zero-initialized weight function, using a quoted constant consisting of 499
NIL conses followed by rational `1/2`; see `public-term-weight.lisp` and
`public-term-weight.lean`. ACL2 returns `200000`; Lean returns `4497`
(`public-term-weight.out:31`, `public-term-weight-lean.out:1`). These are
ordinary values, not fabricated proof records or proof nodes.

The complex arm at `linear-a.lisp:1532–1537` uses the same recursive entry
for each rational component. ACL2 gives weights `9`, `200000`, `200000` for
`#C(1/2 1)` at calls `995`, `996`, `997`, respectively
(`term-weight.out:32`). Merely adding an atomic complex formula around the
old rational helper would retain the error.

**Inference and action:** make numeric component weighting preserve the
source's per-call checks, including rational subcomponents and saturation.
The design already requires the correct imaginary-then-real order and
limits (`numeric-design.md:95,130`); explicitly include this existing helper
repair and the boundary examples in that requirement. This concerns term
ordering and therefore fidelity; it is distinct from `ACL2-COUNT` and does
not call for changing the source's limits or raising Lean resource budgets.

## Reader acceptance checked independently

`acl2/acl2.lisp:2026` creates the ACL2 readtable from the host Common Lisp
readtable. Its modifications at `acl2.lisp:2135–2197` do not replace the
complex reader. `acl2/axioms.lisp:23239–23253` subsequently admits complex
rational objects and rejects other complex objects. Thus host reading and
ACL2's object validation both matter. The following results are observations
from the pinned, freshly built image; they do not assert portability to every
Common Lisp host.

| Input literal | Observed result | Artifact basename |
| --- | --- | --- |
| `#C(1 2)` | `#C(1 2)` | `complex-two-values` |
| `#C (1 2)` | `#C(1 2)` | `complex-space-after-c` |
| `#C(1 . (2))` | `#C(1 2)` | `complex-dotted-cdr-list` |
| `#C(#C(1 0) 2)` | `#C(1 2)` | `complex-inner-zero` |
| `#C(#f1.5 2)` | `#C(3/2 2)` | `complex-sharp-f-component` |
| `#C(#xA #b11)` | `#C(10 3)` | `complex-radix-components` |
| `#C(1 ; comment` followed by newline and `2)` | `#C(1 2)` | `complex-comment` |
| `#C(#C(1 2) 3)` | Reader error | `complex-inner-nonzero` |
| `#C(1 . 2)` | Reader error | `complex-dotted-cdr-number` |
| `#C(nil nil)` | Reader error | `complex-nil-components` |
| `#C(1/-2 3)` / `#C(1/+2 3)` | Reader error; the purported ratio is a symbol | `complex-negative-denominator` / `complex-positive-denominator-sign` |
| `#C(1.0 2)` | ACL2 rejects the resulting non-rational complex object | `complex-float-component` |
| `#C(1)` / `#C(1 2 3)` | Illegal complex format | `complex-one-value` / `complex-extra-value` |
| `#2C(1 2)` | `#C(1 2)` on this host | `complex-prefix` |

Each basename has an isolated `.lisp` input and `.out` transcript. All
processes, including rejected inputs, returned exit code 0 after `good-bye`;
exit status alone is not a reader-success oracle.

The acceptance requirement should inspect **parsed component values**, not
forbid nested `#C` tokens syntactically: the inner zero-imaginary value has
already become a rational. A dotted presentation of a proper two-element
list is also valid. The `#2C` observation should be explicitly classified if
the importer keeps that dispatch-prefix spelling as an unsupported frontier;
it is not evidence that supporting every host reader extension is required
for canonical complex values.

## Representation, arithmetic, printing, and reflection checks

The pinned `Init/Data/Rat/Basic.lean:31–43` stores `num : Int`, `den : Nat`,
`den ≠ 0`, and coprimality. The existing `canonRat` requires denominator at
least 2 and coprimality (`ACL2Lean/Syntax.lean:90`). **Inference from those
types:** a `Rat` component cannot encode a negative/zero denominator or a
nonreduced ratio; `imag.num ≠ 0` excludes every rational duplicate, including
integer zero. Components cannot be genuine nested complexes. Proof fields do
not create distinct values. I found no counterexample to this representation.

I independently typechecked a copy of the proposed datatype and its smart
constructors. Both constructors report `[propext, Quot.sound]`, as the
candidate states. This checks the construction interface and the two concrete
normalization examples; it is not a proved universal representation theorem.

All 21 original labeled ACL2 probes were independently rerun; their observed
outputs agree with the design's report. Transcript:
`original-probes-rerun.out:31–51`. The cited completion rules match
`axioms.lisp:25380–25460,25537–25542,25717–25726,25760–25778` and the
corresponding `interface-raw.lisp:865–931,974–980,1029–1032` definitions.
The two orders differ exactly as the design describes:
`axioms.lisp:27036–27052` puts every rational before every genuine complex.

Additional independently observed cases to include in focused checks:

- `(< 'foo #C(0 1))`, `(<= 'foo #C(0 1))`, `(>= 'foo #C(0 -1))`, and
  `(> 'foo #C(0 -1))` all return T. Every comparison spelling needs the
  completion rule; changing only `Logic.lt` leaves the separate current
  `le/ge/gt` rational paths at `Logic.lean:321–336` unchanged.
- Powers of a nonzero pure imaginary base must not test only its real part
  for zero. For example `(expt #C(0 2) -3)` is `#C(0 1/8)`, and a complex
  exponent still takes the noninteger-exponent branch returning 1. Source:
  `axioms.lisp:9073–9087`; artifact `zero-real-powers.out:31`.
- Quotient operations complete **after** complex division. For example
  `(floor #C(3 3) #C(2 2))` is 1, whereas `(floor #C(3 4) 2)` is 0;
  corresponding MOD results are `#C(1 1)` and `#C(3 4)`.
  Source: `axioms.lisp:7165–7173,7266–7270`;
  artifact `cancel-before-quotient.out:31`. This does not authorize turning
  FLOOR/MOD into new primitives instead of replaying their definitions.
- The completed numeric order is not an ordered-field structure:
  `#C(0 1) > 0` and its square is below zero. Both return T in
  `public-term-weight.out:32`. Ordinary positivity-of-products principles
  require rational hypotheses. This is a test obligation, not a new reported
  defect in a particular DP lemma.

Core `Rat` printing has two different outputs: `toString (mkRat (-5) 7)` is
`"-5/7"`, but `repr` emits `(-5 : Rat)/7`
(`Init/Data/Rat/Basic.lean:47–51`). Both ACL2 value printers must use an ACL2
rational rendering inside `#C(...)`, not the default `Repr Rat`.

Reflection is feasible without trusting the construction code. In
`reflection-and-parser.lean:34–46`, an elaborator emits a `fromParts` call
whose rational components are explicit `mkRat` calls with integer/natural
literals. The resulting reflected value is proved equal to its intended
value by `rfl`; both declarations have the accepted
`[propext, Classical.choice, Quot.sound]` receipt. The isolated file exits 0;
output is `reflection-and-parser.out`.

An initial alternative using core `ToExpr Rat` did not close with ordinary
`decide` or `rfl`: its nonintegral components are emitted as division
expressions (`Lean/ToExpr.lean:52–68`), and core `Rat.inv` is irreducible at
ordinary transparency (`Init/Data/Rat/Basic.lean:191`). Failure artifacts:
`reflection-generic-toexpr-fails.lean` and
`reflection-and-parser-rfl.out`. That failed scratch theorem has `sorryAx`
in its error-recovery declaration; it is **not** a successful proof receipt.
This is not a kernel-soundness or representation failure: the actual driver
already reduces ground decisions at `.all` transparency
(`Replay/Driver/Reflect.lean:114–120`). The explicit `mkRat` emission provides
a checked simple route and avoids relying on default Rat pretty-printing or
ordinary tactic transparency. Performance on large actual reflected literals
remains unmeasured.

## What remains unverified

- No implementation of the proposed complex arithmetic, reader, count,
  type-set changes, or migrated proofs was available to validate. Source
  agreement and executable ACL2 examples are requirements for that work.
- The review does not prove all round-trip, arithmetic, ordering, or
  canonicity theorems for the proposed representation. The type argument and
  scratch checks are narrower evidence.
- Full replay, emitted numeric descent, source-dependency closure, preserved
  coverage/products, and the selected BVCHOP mirrors are outside this C0
  numeric review. The second reviewer covers migration effects; neither
  review replaces the actual C1–C4 checks.
- Reader acceptance was measured against this saved ACL2 image and host.
  Rejected inputs were inspected in their transcripts. No exhaustive reader
  equivalence or random differential run is claimed.
- No full baseline gate result, final proof receipt, comparator result,
  nanoda result, or NS1 completion is asserted here.
