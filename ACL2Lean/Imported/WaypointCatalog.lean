/-
  THE CATALOG OF REPLAY WAYPOINTS (task #62; design doc §6).

  A WAYPOINT is the ACL2-like Lean restatement of a replayed fact: Lean
  notions over `SExpr`/`lexorderB` — the ACL2 value universe in Lean
  clothes. Waypoints are the replay METRIC's scoreboard (how far the
  machinery reaches) and are NEVER a result. The PRODUCT is the MIRROR
  layer (`ACL2Lean/Mirrors/`): Lean-idiomatic, zero-ACL2-notion theorems
  mirroring a book's properties. (Naming restored 2026-08-12 — this
  catalog and the narrative below long mis-used "mirror" for waypoints;
  read every such occurrence as WAYPOINT.)

  One section per corpus theorem: the waypoint stated in ACL2-like Lean
  terms, proved THROUGH the ACL2 replay — the driver's conditional replayed statement, its
  hypotheses discharged for the log-derived world, decoded to the waypoint
  statement via the `enc`/`corr_*` simulation layer. Each PROVED entry is a
  build-enforced regression; each PENDING entry names the blocking frontier.
  The accumulated patterns are the seed of a future standard lifting library
  (polymorphic `α ↪ SExpr` statements are deliberately deferred — TODO.md).

  ── THE LIVE SCOREBOARD IS `liftCatalog` (Waypoints/Catalog.lean) ───────────
  (Correction 2026-08-06, overall-project audit P2-11: this header's table
  below stops at entry 18 and predates the sorting-book waypoints — it is
  HISTORY, not status. The catalog module holds one decision per green
  sweep row, gated build-failing: lift-coverage/seam, axioms, and the
  waypoint criterion. Count entries there, not here.)

  ── HISTORICAL SCOREBOARD (first 18 entries, kept as narrative) ───────────
  PROVED (via the driver's replayed statement):
    1. my-len-my-app   (xs ++ ys).length = xs.length + ys.length  [List SExpr]
    2. app-assoc       (xs ++ ys) ++ zs = xs ++ (ys ++ zs)        [List SExpr]
    3. ground-arith    (1 + (2 + 3) : Int) = 6                    [ground decode]
    4. sq-of-3         (3 * 3 : Int) = 9                          [defn unfold]
    5. cdr-cons-refl   Logic.cdr (cons u v) = v                   [symbolic-value]
    6. equal-symm      u = v → v = u                              [hypothesis decode]
    7. equal-trans     u = v → v = w → u = w                      [hypothesis + if]
    8. app-cons-car    Logic.car (cons u v) = u                   [nested unfold +
                                                                   symbolic-value]
    9. perm-cons       a ∈ xs → (xs ~ a::ys ↔ xs.erase a ~ ys)    [UNCONDITIONAL
                                                                   replayed stmt; List.Perm]
   10. perm-symmetric  isPerm symm (+ Perm corollary)             [decode kit]
   11. memb-rm         contains survives erase                    [decode kit]
   12. comm-rm         erase_comm (LIST equality via enc_inj)     [decode kit]
   13. perm-memb       membership transports across isPerm        [and-cond decode]
   14. perm-rm         isPerm preserved by erase (+ corollary)    [decode kit]
   15. perm-transitive isPerm trans (+ Perm corollary)            [and-cond decode]
   16. perm-refl       isPerm refl, peeled from the defequiv
                       tower; + isPerm_equivalence_driver bundle  [replayed_peel_guard]
  THE WHOLE PERM BOOK IS IMPORTED: 8 unconditional replayed statements, 8 native facts,
  zero hypotheses (lifter sprint 2026-07-06).
   17. p7-cong-collapse (l.map (fun _ => '0)).length = l.length
                        [FIRST VALIDATION-BOOK waypoint — rung 2's ground
                        truth; tp:LN discharged BY THE DRIVER (the TP
                        prover's return-path arm) + corr_mapconst_enc,
                        validator/lifter arc inc-0; TP-replay arc inc-1]
   18. p5-or-shape-flipped  duppRec (e::tl) → duppRec (e::e::tl)
                        [chain2 schematic (comparison-generic) + boolEnc +
                        implies decode + junk-disjunct elimination,
                        validator/lifter arc inc-1]
  PROVED (via the HAND replayed statement — driver upgrade pending):
    -  my-len-my-app   ACL2Lean/Imported/SimpleWorld.lean (the original)
    -  nat-refl        Tests/DriverTests.lean `native_nat_refl` (trivial, driver)
  WAYPOINT-ONLY (replayed by the driver — DriverCoverage regression — but the
  decode is REFLEXIVE: our own evaluation of both sides computes the same
  value, so no non-vacuous native fact exists to extract):
    -  sq-rewrites, idf-rewrites, count-down-zero, my-evenp-3-is-nil,
       my-oddp-3-is-t
  PENDING:
    -  app-nil          xs ++ [] = xs                        [G5: multi-literal
                        pushed clause induction]
    -  rev-rev          xs.reverse.reverse = xs              [G5 + rev corr]
    -  len2-app family  length_append via len2               [needs the len2
                        world's dischargers (totality inductions + TP) — the
                        entry-1 recipe over the 01 world]
    -  linear-chain     Int order transitivity               [#50 DP tactic]
    -  len2-nonneg      0 ≤ (xs.length : Int)                [decode; the Nat
                        form is type-absorbed; needs len2 dischargers]
    -  true-listp-*     type-absorbed natively (List is well-formed by type) —
                        documented, replayed-only
  ──────────────────────────────────────────────────────────────────────────

  ── MODULE LAYOUT (split 2026-08-02) ──────────────────────────────────────
  This file is now a FACADE. The catalog itself lives in per-book modules
  under `ACL2Lean/Imported/Waypoints/`, so Lake confines rebuilds to the book
  actually edited and elaborates the books in PARALLEL across cores:

    Waypoints.Macro          the `driver_replayed%` elaborator (+ `depsClauseDR`)
    Waypoints.Basics         entries 1–8 (simple / 02-rev / 00-direct /
                             08-equality-reasoning / 01-multi-theorem)
    Waypoints.PermBook       entries 9–16, the perm book + its `List.Perm`
                             corollaries
    Waypoints.Tree           entry 17, true-listp-flatten
    Waypoints.Validation     the p7/p5 validation-book waypoints
    Waypoints.ConvertPerm    the convert-perm-to-how-many DEPENDENCY dev
                             (tree source only — no `derive_world`)
    Waypoints.OrderedPerms   the ordered-perms book (incl. the ORDERED-PERMS
                             capstone; `deps [permDev]`)
    Waypoints.Isort          the isort book
    Waypoints.Qsort          the qsort book
    Waypoints.Msort          the msort book
    Waypoints.IsChain        `LexSorted` + the `List.IsChain` corollaries
    Waypoints.Catalog        `liftCatalog` + the build-failing gates
                             (lift-coverage/seam, axioms, criterion-1,
                             provenance, hreplayed-usage) — and
                             THE WAYPOINT CRITERION text, which now sits next
                             to the gates that mechanize it.

  Entries are grouped by the DEVELOPMENT/WORLD constants they use, not by
  the old section headers: `driver_replayed%` consumes the waypoint registry
  in ELABORATION ORDER, so every invocation over a given world stays in one
  module, in its original relative order.
-/
import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Waypoints.Basics
import ACL2Lean.Imported.Waypoints.PermBook
import ACL2Lean.Imported.Waypoints.Tree
import ACL2Lean.Imported.Waypoints.Validation
import ACL2Lean.Imported.Waypoints.ConvertPerm
import ACL2Lean.Imported.Waypoints.OrderedPerms
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Qsort
import ACL2Lean.Imported.Waypoints.Msort
import ACL2Lean.Imported.Waypoints.IsChain
import ACL2Lean.Imported.Waypoints.EquisortParametric
import ACL2Lean.Imported.EquisortWitness
import ACL2Lean.Imported.Waypoints.P8ClausifyDetail
import ACL2Lean.Imported.Waypoints.Catalog
