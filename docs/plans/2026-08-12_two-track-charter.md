# The two-track charter (drafted 2026-08-12, for Mike's review)

The restart plan from main @ 2f04bcf, under the two-category model:
replaying ACL2 notions into ACL2-like Lean is the METRIC (useful as a
scoreboard, forbidden as a result); the PRODUCT is MIRRORS —
Lean-idiomatic, zero-ACL2-notion theorems mirroring book properties,
proved via replay. The demo work of 2026-08-11/12 is archived
(`archive/demo-2026-08`); nothing of it is on main.

## STEP 0 — the north star (DONE on this branch, for review)

`ACL2Lean/Mirrors/Sorting.lean`: the sorting book's mirror spec.
- The four algorithms in pure idiomatic Lean, polymorphic over OUR
  OWN minimal `TotalOrder` class (insertionSort, alternation-split
  mergeSort, quickSort, bubbleSort — recursing as the book's
  functions recurse). The file imports NOTHING — core prelude only.
- SELF-CONTAINED predicate vocabulary — our own `Sorted` (adjacent
  chain), `count`, `Permuted` (the book's mem+erase recursion),
  `permWitness` — so no Mathlib/Batteries lemma can close mirror
  content; the properties arrive via replay or not at all.
  The order class is ours (Mathlib removed entirely — off the purity
  allowlist; re-admitting it is a ruling).
- 14 target properties as named `Prop`s (sorted ×4, permuted ×4,
  sorted-perm uniqueness, four-sorts-agree, the abstract
  any-sorter-is-insertionSort capstone, perm↔counts, witness
  completeness). No sorry; the only proofs are kernel-demanded
  termination measures.
- `just check-mirrors-pure` (ci): the Mirrors/ imports are pinned to
  Std/Batteries at most (Mathlib EXCLUDED; the sorting spec imports
  nothing at all) — an ACL2 notion in a mirror is definitionally a
  bug, so this one is a claims-tier build gate.

Every future book gets the same shape: `Mirrors/<Book>.lean`, spec
first, THE definition of done.

## THE THREE-SOURCE PROVENANCE RULE (Mike, 2026-08-12)

Use as much of what ACL2 gives us as is viable, without knots:
1. REPLAYED — everything an ACL2 BOOK proves. If a defthm exists,
   its content enters via replay, never re-proved. Maximal.
2. CORE-LOGIC — ACL2's axiomatic base (axioms.lisp ground-zero
   rules, primitive behavior) is never PROVED by ACL2; our
   interpreter's implementation obligations are to PROVE the model
   satisfies it (LexorderOrder.lean, gz agreement, D5 content).
   Proved once in the interpreter layer, differential-tested,
   bounded by axioms.lisp enumerability (the ratified
   predefined-only line). Backs interface instances for
   replay-reachable fragments — no ceremony order-books for facts
   ACL2 never proves anyway.
3. MIRROR-SIDE GLUE — minimized, never content.
Track FREE ledger item: the CORE-LOGIC scoreboard (which axioms.lisp
entries are satisfied-by-proof vs assumed; the differential harness
is its QA).

## TRACK REAL — the mirror buildout (the actual work)

Per-book, user-authored (industrialized where patterns emerge):
1. The isomorphisms from the mirror definitions down to the
   ACL2-like layer (mirror `insertionSort` ↔ waypoint `isortL`/
   `isortExec` — through the order instance: our `lexorder`
   restricted to the relevant atom fragment realizes OUR `TotalOrder`
   interface, backed by CORE-LOGIC theorems (source 2); design note needed on the instance
   architecture: which α (Int first? the SExpr-atom fragment as a
   TotalOrder instance?) and how polymorphic targets are reached
   from a fixed-universe replay — likely: prove at the instance the
   replay supports, state the polymorphic Prop's instance-closure
   honestly, generalize as the machinery grows).
2. Deriving the 14 mirror theorems from replayed content through
   those isos. DISCIPLINE (product-level ornamental-import ban):
   mirror content is closed from replayed facts — never by Mathlib
   lemma application, never by direct Lean induction on the mirror
   defs; glue (rewriting, projections, arithmetic on indices) is
   fine. Eventually gated seam-style (a mirror theorem's proof must
   consume replayed constants); audit-enforced until that gate
   exists.
3. First increment: `insertionSort_sorted` + `insertionSort_perm`
   end-to-end — the route proven on the simplest sort before
   fan-out.

## TRACK FREE — category 1 to actually-zero-work

The metric layer should cost NOTHING per book ("entirely schematic,
extracted automatically from our machinery"). Everything hand-written
there today is a machinery gap:
1. Log-derived bodies/formulas replace the hand transcriptions
   (AclSource-class content auto-extracted; the by-decide checks
   become generated consistency canaries).
2. Generator coverage: the M3 measure shapes (retire the hand exec
   kits), the decode-assembly generator (retire the ~43 hand decode
   proofs).
3. The debt routes (unchanged from the previous charter, now in
   metric-layer terms): with_termination admission coverage
   (REQUIRED class), the TP-replay route (tp: 195), the R-lane
   (PERM-TLFIX), the linear class design. Debt retirement improves
   the METRIC and unblocks Track REAL's route breadth; it is not
   itself the product.

## NAMING SWEEP (EXECUTED 2026-08-12, mechanical)

The machinery's co-opted "mirror" vocabulary is renamed:
`Imported/Mirrors/` → `Imported/Waypoints/` (+ namespace
`ACL2.Imported.Mirrors` → `ACL2.Imported.Waypoints`),
`Imported/NativeMirrors.lean` → `Imported/WaypointCatalog.lean`,
`Tests/MirrorCensus.lean` → `Tests/WaypointCensus.lean`,
`scripts/mirror-metrics.sh` + `just mirror-metrics` →
`waypoint-metrics`; doc language "native mirror" → "waypoint".
The golden was unaffected (no Lean names in it) and the coverage
numbers are unchanged. Historical records (docs/audits, dated
docs/notes, older docs/plans) were NOT rewritten — the two
consulted-in-anger files (TODO.md, the thin-Lean boundary note)
carry a one-line TERMINOLOGY header instead. `mirror` is now
reserved for the product layer (`ACL2Lean/Mirrors/`).

## Standing constraints

Thin-Lean boundary (metric layer); the two-standard rule; mirror
purity (check-mirrors-pure) + self-contained vocabulary + the
product-level ornamental-import discipline; two-tier gating; goal
escape hatches; the canary relabeling (statement pins detect drift,
they are not trust anchors).

## Sequencing

Step 0 review → the iso-instance design note (Track REAL 1, needs a
ruling on the instance architecture) → Track REAL 3 (insertionSort
end-to-end) as the pathfinder arc, with Track FREE items pulled in
exactly when the pathfinder hits them (a hand-written thing on the
path = a Track FREE work item, not a workaround). The naming sweep
rides whichever arc first touches the machinery broadly.
