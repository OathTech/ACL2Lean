/-
  THE NATIVE MIRROR CATALOG (task #62; design doc §6).

  One section per corpus theorem: the result stated in NATIVE Lean terms,
  proved THROUGH the ACL2 replay — the driver's conditional replayed statement, its
  hypotheses discharged for the log-derived world, decoded to the native
  statement via the `enc`/`corr_*` simulation layer. Each PROVED entry is a
  build-enforced regression; each PENDING entry names the blocking frontier.
  The accumulated patterns are the seed of a future standard lifting library
  (polymorphic `α ↪ SExpr` statements are deliberately deferred — TODO.md).

  ── SCOREBOARD ────────────────────────────────────────────────────────────
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
                        [FIRST VALIDATION-BOOK mirror — rung 2's ground
                        truth; name-generic drv_tp_len + corr_mapconst_enc,
                        validator/lifter arc inc-0]
   18. p5-or-shape-flipped  duppRec (e::tl) → duppRec (e::e::tl)
                        [chain2 schematic (comparison-generic) + boolEnc +
                        implies decode + junk-disjunct elimination,
                        validator/lifter arc inc-1]
  PROVED (via the HAND replayed statement — driver upgrade pending):
    -  my-len-my-app   ACL2Lean/Imported/SimpleWorld.lean (the original)
    -  nat-refl        Tests/DriverTests.lean `native_nat_refl` (trivial, driver)
  MIRROR-ONLY (replayed by the driver — DriverCoverage regression — but the
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
  under `ACL2Lean/Imported/Mirrors/`, so Lake confines rebuilds to the book
  actually edited and elaborates the books in PARALLEL across cores:

    Mirrors.Macro        the `driver_replayed%` elaborator (+ `depsClauseDR`)
    Mirrors.Basics       entries 1–8 (simple / 02-rev / 00-direct /
                         08-equality-reasoning / 01-multi-theorem)
    Mirrors.PermBook     entries 9–16, the perm book + its `List.Perm`
                         corollaries
    Mirrors.Tree         entry 17, true-listp-flatten
    Mirrors.Validation   the p7/p5 validation-book mirrors
    Mirrors.ConvertPerm  the convert-perm-to-how-many DEPENDENCY dev
                         (tree source only — no `derive_world`)
    Mirrors.OrderedPerms the ordered-perms book (incl. the ORDERED-PERMS
                         capstone; `deps [permDev]`)
    Mirrors.Isort        the isort book
    Mirrors.Qsort        the qsort book
    Mirrors.Msort        the msort book
    Mirrors.IsChain      `LexSorted` + the `List.IsChain` corollaries
    Mirrors.Catalog      `liftCatalog` + the three build-failing gates
                         (lift-coverage/seam, axioms, criterion-1) — and
                         THE MIRROR CRITERION text, which now sits next to
                         the gates that mechanize it.

  Entries are grouped by the DEVELOPMENT/WORLD constants they use, not by
  the old section headers: `driver_replayed%` consumes the mirror registry
  in ELABORATION ORDER, so every invocation over a given world stays in one
  module, in its original relative order.
-/
import ACL2Lean.Imported.Mirrors.Macro
import ACL2Lean.Imported.Mirrors.Basics
import ACL2Lean.Imported.Mirrors.PermBook
import ACL2Lean.Imported.Mirrors.Tree
import ACL2Lean.Imported.Mirrors.Validation
import ACL2Lean.Imported.Mirrors.ConvertPerm
import ACL2Lean.Imported.Mirrors.OrderedPerms
import ACL2Lean.Imported.Mirrors.Isort
import ACL2Lean.Imported.Mirrors.Qsort
import ACL2Lean.Imported.Mirrors.Msort
import ACL2Lean.Imported.Mirrors.IsChain
import ACL2Lean.Imported.Mirrors.Catalog
