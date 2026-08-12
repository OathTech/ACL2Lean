# Differential test corpus — Lean interpreter vs ACL2

**Goal.** The Lean ACL2-logic interpreter (`evalOpt` + `Logic`, our trusted
core) should behave *exactly* like real ACL2. This corpus pins that down: the
same forms are fed to both interpreters and their output value streams are
compared.

**Why it matters (fidelity).** `evalOpt` is the semantic model that *defines*
what our replayed statements mean. If it diverges from ACL2, a kernel-checked proof
can certify the wrong statement (see the trust note in the repo `CLAUDE.md`).
So the interpreter's agreement with ACL2 is a load-bearing, non-negotiable
property — this corpus is its acceptance gate.

**Long-term objective — total masquerade.** The endgame is that the Lean
interpreter is indistinguishable from ACL2 as a black box: feed *randomly
generated* ACL2 programs to both and string-compare the output, with no
divergence. We are far from that today (unmodeled builtins, symbol-case
rendering, no defun/defthm evaluation in stream mode), but every entry here is
a step toward it, and the design deliberately keeps the two interpreters as
peers with the *same interface* — forms in on stdin, one value per form out —
so the comparison stays a plain string diff rather than bespoke test plumbing.

## Architecture — two peer interpreters + an external comparator

Neither interpreter knows it is being tested. Each is just "an ACL2": a stream
of forms in, a stream of values out.

- **ACL2 interpreter:** `acl2/saved_acl2 < forms.lisp` — the reference.
- **Lean interpreter:** `lake exe acl2lean eval < forms.lisp` (empty world) or
  `lake exe acl2lean eval-in <book.lisp> < forms.lisp` (forms against a book's
  world). This is plain batch evaluation — an interpreter capability, carrying
  **no** test/expectation logic.
- **Manager** (`scripts/diff-test.sh`): feeds a corpus file to both, joins the
  two value streams by form index, consults the corpus metadata to decide
  whether each (dis)agreement is expected, and reports. ALL test-awareness
  lives here, outside both interpreters.

## Corpus format

Category files live in `corpus/*.lisp`. Each is a sequence of **tests**. A test
is exactly one metadata comment line followed by exactly one ACL2 form (which
may span multiple lines):

```lisp
;@ match
(binary-+ '2 '3)

;@ unsupported
(append '(1 2) '(3 4))

;@ known-bug lean NIL
(equal '5 '5/1)
```

- The `;@` line is a normal Lisp `;` comment, so **both** interpreters skip it;
  it exists only for the manager. Every form MUST have exactly one preceding
  `;@` line — the manager checks that the number of `;@` lines equals the
  number of value lines each interpreter emits (an alignment self-check).
- Ordinary `;` comments (without `@`) and blank lines are free-form.
- A file may begin with a `;@world <name>` directive (before the first test)
  selecting the book world all its forms evaluate in; default is the empty
  world. (`<name>` maps to a `.lisp` book — see the manager.)

### Expectation classes (the `;@` verdicts)

An OUTCOME is either a printed value, or `<stuck>` (Lean's evaluator did not
converge) / `<refused>` (a read/translate/parse error). `<stuck>` and
`<refused>` both count as "produced no value".

| class                      | meaning                                                            | manager rule |
|----------------------------|--------------------------------------------------------------------|--------------|
| `match`                    | evalOpt models this; Lean and ACL2 MUST agree                      | FAIL if they differ, or Lean produces no value |
| `unsupported`              | evalOpt does NOT model this yet (target surface); ACL2 has a value | FAIL if Lean produces any value (now modeled → reclassify to `match`) |
| `known-bug lean <outcome>` | KNOWN divergence: Lean's outcome (a value, or `<refused>`) differs from ACL2 | FAIL if Lean's outcome ≠ `<outcome>` (behavior changed — likely fixed → reclassify) |
| `refuse`                   | ill-formed / rejected form; BOTH interpreters must decline         | FAIL if either produces a value (ACL2 not actually refusing, or Lean too permissive → known-bug) |

`refuse` is a **both-decline** check, not a **same-reason** check: ACL2 refuses
at translate time (arity/syntax) while Lean may decline as `<stuck>` (no rule /
fuel) or `<refused>` (parse error) — the harness does not require the reasons to
match, only that neither produces a value. Tightening this to reason-matching
would need the Lean interpreter to distinguish "rejected" from "did not
converge" per form (an interpreter change, deferred).

The gate stays **green** while `unsupported`/`known-bug`/`refuse` merely
*document* the not-yet-faithful surface, but goes **red** on any *change* — a
regression, a new fidelity bug, or a coverage gain that needs the annotation
updated. That is how the corpus doubles as a live, checked inventory of exactly
how far the masquerade currently extends.

### Per-form isolation (`;@isolate`)

A file whose first directive is `;@isolate` is run ONE form per
interpreter-invocation (own ACL2 session, own Lean process), and read/translate/
parse errors map to the `<refused>` outcome. This is required for
BOUNDARY/ill-formed forms that a batched session cannot survive: a float literal
(`5.0`) halts the ACL2 session, and a radix literal (`#xFF`) aborts Lean's parse
stream. In an `;@isolate` file every test is one SINGLE-LINE form. See
`corpus/boundary.lisp`. Regular files stay batched (two processes per file).

Note: a `refuse` entry does NOT by itself require isolation. The batched path
reconstructs one outcome per ACL2 prompt and maps an `ACL2 Error [...]` block to
`<refused>`, so RECOVERABLE ill-formed forms (arity, unknown fn, malformed
`if`/`quote`) can be `refuse`-tested in an ordinary batched file. Isolation is
only for forms that HALT the session or abort a parse stream (floats, radix).

## Adding a test

Append two lines to the relevant `corpus/<category>.lisp`: a `;@ <class>` line
and the form. New builtin not modeled yet? `;@ unsupported` + the form pins the
target (the manager will show ACL2's value). Found a fidelity bug? `;@ known-bug
lean <the wrong outcome>` records it so a future fix is detected. An ill-formed
form both interpreters reject? `;@ refuse`. Boundary forms that break a batched
session go in an `;@isolate` file.

## Running

    just diff-test              # all categories
    scripts/diff-test.sh corpus/int-arith.lisp   # one file

Needs `acl2/saved_acl2` (build with `just build-acl2`). See the manager script
header for details.
