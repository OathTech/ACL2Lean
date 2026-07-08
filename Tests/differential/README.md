# Differential test corpus — Lean interpreter vs ACL2

**Goal.** The Lean ACL2-logic interpreter (`evalOpt` + `Logic`, our trusted
core) should behave *exactly* like real ACL2. This corpus pins that down: the
same forms are fed to both interpreters and their output value streams are
compared.

**Why it matters (fidelity).** `evalOpt` is the semantic model that *defines*
what our mirror theorems mean. If it diverges from ACL2, a kernel-checked proof
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

;@ stuck
(append '(1 2) '(3 4))

;@ diverge lean NIL
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

| class                 | meaning                                                            | manager rule |
|-----------------------|--------------------------------------------------------------------|--------------|
| `match`               | evalOpt models this; Lean and ACL2 MUST agree                      | FAIL if they differ, or Lean is `<stuck>` |
| `stuck`               | evalOpt does NOT model this yet (target surface); ACL2 has a value | FAIL if Lean produces any value (surface grew → reclassify to `match`) |
| `diverge lean <val>`  | KNOWN fidelity gap: Lean produces the wrong `<val>`, ACL2 differs  | FAIL if Lean ≠ `<val>` (the divergence changed — e.g. was fixed → reclassify) |

The gate stays **green** while `stuck`/`diverge` merely *document* the
not-yet-faithful surface, but goes **red** on any *change* — a regression, a
new fidelity bug, or a coverage gain that needs the annotation updated. That is
how the corpus doubles as a live, checked inventory of exactly how far the
masquerade currently extends.

## Adding a test

Append two lines to the relevant `corpus/<category>.lisp`: a `;@ <class>` line
and the form. New builtin not modeled yet? `;@ stuck` + the form pins the target
(the manager will show ACL2's value). Found a divergence? `;@ diverge lean <the
wrong value>` records it so a future fix is detected.

## Running

    just diff-test              # all categories
    scripts/diff-test.sh corpus/int-arith.lisp   # one file

Needs `acl2/saved_acl2` (build with `just build-acl2`). See the manager script
header for details.
