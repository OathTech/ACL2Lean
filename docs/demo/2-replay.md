# Part 2 — What you do to replay a book

The user manual. This is the end-to-end recipe for taking an ACL2 book you care
about and coming out the other side with a native Lean theorem, catalogued and
gated. The worked example throughout is insertion sort.

Prerequisite: a built instrumented ACL2 (`just build-acl2` — the `acl2/`
submodule, branch `acl2-lean-output`).

---

## Step 0 — the ACL2 source

`acl2/books/sorting/isort.lisp`, upstream ACL2's own sorting book:

```lisp
(defun insert (e x)
  (if (endp x) (cons e x)
    (if (lexorder e (car x)) (cons e x)
      (cons (car x) (insert e (cdr x))))))

(defun isort (x)
  (if (endp x) nil (insert (car x) (isort (cdr x)))))

(defthm orderedp-isort (orderedp (isort x)))
```

Nothing about the book has to be written for us; the point is to import ACL2's
own libraries as they are.

## Step 1 — capture the proof log

```sh
just capture-proof-log acl2/books/sorting/isort.lisp
# or, for everything in the manifest:  just capture-all-logs
```

Our instrumented fork records the waterfall as it runs — runes, rewrite steps
with their substitutions, induction schemes, type-prescription corollaries —
into `acl2_samples/sorting/isort.proof-log` (a generated, gitignored artifact,
stamped with a provenance sidecar that `just check-log-provenance` verifies
against the current submodule HEAD).

Look at what came out before going further:

```sh
lake exe acl2lean dump-proof-tree acl2_samples/sorting/isort.proof-log
just replay acl2_samples/sorting/isort.proof-log orderedp-isort
```

```
• isort  (world: 27 defun(s), 3 theorem(s))
    ORDEREDP-ISORT → REPLAYED ✓ cond[tp:INSERT]
    TRUE-LISTP-ISORT → REPLAYED ✓ cond[tp:INSERT]
    HOW-MANY-ISORT → REPLAYED ✓ cond[tp:HOW-MANY, rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0]
```

`cond[…]` lists the row's **kept conditions**: facts ACL2 used that the replay
cannot yet construct, which will arrive either as another replayed statement or
as registered debt. A row that does not say `REPLAYED` stops here — the driver
hard-fails at a named frontier rather than guessing, and the fix is more ACL2
instrumentation, never Lean-side inference.

## Step 2 — load the development and derive the world

In a mirror module (`ACL2Lean/Imported/Mirrors/Isort.lean`):

```lean
private def isortLog : String :=
  include_str "../../../acl2_samples/sorting/isort.proof-log"

def isortDev : Development := load_development% isortLog

derive_world isortWorldD from isortDev
```

`load_development%` parses and reconstructs at **compile time**, so a malformed
or truncated log is a build error, not a silent empty development.
`derive_world` builds the `World` (the `defun` environment) from the log's own
`:DEFUN` events.

## Step 3 — get the replayed statement

```lean
def orderedpIsortReplayedCond := driver_replayed% isortDev isortWorldD
  "orderedp-isort"
```

This is the whole replay: the driver walks the reconstructed clause tree and
emits a Lean `Expr`, node by node, which the kernel then checks. What you get
is a deep-embedded proposition — "under the world derived from this log, the
goal formula evaluates to something non-`nil`" — with one hypothesis per kept
condition. True, kernel-checked, and unreadable.

Discharge the kept conditions to get the unconditional form:

```lean
theorem orderedpIsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f isortWorldD env
      Worlds.Sorting.orderedp_isortFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpIsortReplayedCond env
    (Worlds.Sorting.dis_insert_tp isortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
```

Each `by decide` is a world fact ("this world's `INSERT` has exactly this
body"). `dis_insert_tp` is an entry of `Demo/Sorting/Assumptions.lean` — this
is exactly where the debt attaches, and why the receipt in part 1 carries
`sorryAx`.

## Step 4 — write your native definition

In `Demo/Sorting/TCB.lean`, in ordinary Lean, with no evaluator vocabulary:

```lean
def insertL (e : SExpr) : List SExpr → List SExpr
  | [] => [e]
  | a :: t => bif lexorderB e a then e :: a :: t else a :: insertL e t

def isortL : List SExpr → List SExpr
  | [] => []
  | a :: t => insertL a (isortL t)
```

This is the *only* place you exercise judgement about meaning: the native
definition is what the final theorem is about, so it must be the function you
mean. It is also the only new content that lands in the trust base.

The ACL2 side of the pair — the macroexpanded body as an `SExpr` — goes in
`Demo/Sorting/AclSource.lean`, transcribed from the log's `(:DEFUN …)` event.

## Step 5 — connect the two: `derive_exec%` + `derive_sim%`

Two generated stages, in `Imported/Sorting/Iso.lean`:

```lean
-- stage 1: the ACL2 call converges to a total Lean function
derive_exec% isortExec corr isort_exec_corr for isort_sym
  formals [xS] body isortBody measured 0

-- stage 2: that function, on ENCODED inputs, computes the native reading
derive_sim% isortExec_enc for "ISORT"
  vars (xs : list)
  exec [xs]
  native (enc (isortL xs))
  simp [isortL]
  induct functional (isortL xs)
```

Callee simulations resolve through a kit registry, so books compose: `isort`'s
iso reuses `insert`'s. Where the recursion is not on the template (`msortExec`,
`qsortExec`, `bnextExec`) the exec is hand-written; the generated route is the
default and the hand route the exception.

## Step 6 — decode

In `Imported/Sorting/Decode.lean` (or `DecodeSorts.lean`) — the **only** layer
allowed to mention a replayed statement. The decode takes the replayed
statement as a hypothesis and transports it, using the stage-2 isos, into the
native form:

```lean
theorem orderedp_isort_native_of_replayed (w : World) …
    (hreplayed : ∀ env : Env, …) :
    orderedpRec (isortL xs) = true := …
```

Then apply it at the concrete world in the mirror module:

```lean
theorem orderedp_isort_native_driver (xs : List SExpr) :
    Worlds.Sorting.orderedpRec (Worlds.Sorting.isortL xs) = true :=
  Worlds.Sorting.orderedp_isort_native_of_replayed isortWorldD (by decide) …
    orderedpIsortReplayed_uncond xs

#print axioms orderedp_isort_native_driver
```

## Step 7 — the catalog entry

Every green row of the corpus sweep needs exactly one decision in `liftCatalog`
(`Imported/Mirrors/Catalog.lean`), or the build fails:

```lean
("sorting/isort", "ORDEREDP-ISORT",
  .nativeSorried ``orderedp_isort_native_driver ``orderedpIsortReplayedCond
    "tp:INSERT (dis_insert_tp; unlock: TP-replay discharge)"),
```

The three statuses are `.native` (clean), `.nativeSorried` (native, with named
debt), and `.replayedOnly` (nothing non-vacuous to lift, with the reason).
Registering the pair also wires the entry into the seam and axiom gates — see
part 3.

## Step 8 — put it on the page (optional)

If the result is a headline, restate it in `Demo/Sorting/Statements.lean` as a
bare application of the catalog constant, with a `#guard_msgs` axiom receipt:

```lean
theorem isort_sorts (xs : List SExpr) : LexSorted (isortL xs) :=
  orderedp_isort_isChain_driver xs

/-- info: 'ACL2.Imported.Showcase.isort_sorts' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_sorts
```

## Step 9 — gate it

```sh
just ci
```

which runs, among others: the static checks (`check-trust-imports`,
`check-file-weight`, `check-dark-files`, `check-log-provenance`), the build and
unit tests, the corpus-wide `driver-coverage` sweep against
`Tests/driver-coverage.golden`, and `check-golden-current` (a hand-edited
golden fails). A newly green row with no catalog decision fails the build, so
"replayed but never lifted" cannot accumulate silently.

---

Next: **[Part 3 — how it works](3-internals.md)**. Back to
**[Part 1 — what's the TCB](1-tcb.md)**.
