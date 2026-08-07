/-
  Driver coverage AGGREGATE (perf arc item 1, 2026-08-07).

  The former monolith is now 29 per-book modules (Tests/Coverage/*, see
  Tests/Coverage/Harness.lean for the semantics-preservation argument);
  each book checks its own section of Tests/driver-coverage.golden
  BYTE-EXACTLY at its own elaboration, in parallel across cores, with
  per-book incrementality. THIS module is the roll-up gate: it sums the
  per-book counts, re-renders the golden's two HEADER lines, and checks
  the sections TILE the golden (header + Σ section lines = the whole
  file — no orphan or missing section can hide).

      lake build Tests.DriverCoverage      (the `just driver-coverage` gate)
-/
import Tests.Coverage.BSimple
import Tests.Coverage.BN00Direct
import Tests.Coverage.BN01MultiTheorem
import Tests.Coverage.BN02Rev
import Tests.Coverage.BN03Linear
import Tests.Coverage.BN04MultiCaseInduction
import Tests.Coverage.BN05Hints
import Tests.Coverage.BN06Measure
import Tests.Coverage.BN07MutualRecursion
import Tests.Coverage.BN08EqualityReasoning
import Tests.Coverage.BN09DefnUnfold
import Tests.Coverage.BN10TreeInduction
import Tests.Coverage.BN11CustomMeasure
import Tests.Coverage.BN12MultiController
import Tests.Coverage.BN13MultiMeasuredVar
import Tests.Coverage.BN14Accumulator
import Tests.Coverage.BN15NestedInduction
import Tests.Coverage.BN16ThreeWay
import Tests.Coverage.BN17RuleApplication
import Tests.Coverage.BSperm
import Tests.Coverage.BSconvertPermToHowMany
import Tests.Coverage.BSisort
import Tests.Coverage.BSbsort
import Tests.Coverage.BSorderedPerms
import Tests.Coverage.BSequisort
import Tests.Coverage.BCovEncapsulate
import Tests.Coverage.BSmsort
import Tests.Coverage.BSqsort
import Tests.Coverage.BSsortsEquivalent
import Lean

open Lean Lean.Elab Lean.Elab.Command

namespace ACL2.Tests.Coverage

elab "coverage_aggregate%" : command => do
  let all : List CovCounts :=
    [covCounts_simple,
     covCounts_00_direct,
     covCounts_01_multi_theorem,
     covCounts_02_rev,
     covCounts_03_linear,
     covCounts_04_multi_case_induction,
     covCounts_05_hints,
     covCounts_06_measure,
     covCounts_07_mutual_recursion,
     covCounts_08_equality_reasoning,
     covCounts_09_defn_unfold,
     covCounts_10_tree_induction,
     covCounts_11_custom_measure,
     covCounts_12_multi_controller,
     covCounts_13_multi_measured_var,
     covCounts_14_accumulator,
     covCounts_15_nested_induction,
     covCounts_16_three_way,
     covCounts_17_rule_application,
     covCounts_sorting_perm,
     covCounts_sorting_convert_perm_to_how_many,
     covCounts_sorting_isort,
     covCounts_sorting_bsort,
     covCounts_sorting_ordered_perms,
     covCounts_sorting_equisort,
     covCounts_cov_encapsulate,
     covCounts_sorting_msort,
     covCounts_sorting_qsort,
     covCounts_sorting_sorts_equivalent]
  let sum := fun (f : CovCounts → Nat) => all.foldl (fun a c => a + f c) 0
  let hdr1 := s!"Driver coverage — REPLAYED {sum (·.replayed)}/{sum (·.total)} \
({sum (·.replayed) - sum (·.replayedCond)} unconditional + \
{sum (·.replayedCond)} conditional)"
  let hdr2 := s!"Standalone DP probes (assumeFact — informational, NOT replay): \
✓{sum (·.dpReplayed)} ◌{sum (·.dpAssumed)} \
✗{sum (·.dpTotal) - sum (·.dpReplayed) - sum (·.dpAssumed)} of \
{sum (·.dpTotal)}:"
  let golden ← IO.FS.readFile "Tests/driver-coverage.golden"
  let glines := (golden.splitOn "\n").filter (· ≠ "")
  match glines with
  | g1 :: g2 :: rest =>
    unless g1 == hdr1 do
      throwError "coverage aggregate: header line 1 mismatch\n  golden: \
{g1}\n  summed: {hdr1}"
    unless g2 == hdr2 do
      throwError "coverage aggregate: header line 2 mismatch\n  golden: \
{g2}\n  summed: {hdr2}"
    unless rest.length == sum (·.lineCount) do
      throwError "coverage aggregate: the per-book sections do not TILE \
the golden ({rest.length} body line(s) vs Σ sections \
{sum (·.lineCount)}) — a section is missing, duplicated, or orphaned"
  | _ => throwError "coverage aggregate: golden has no header"
  -- assemble Tests/driver-coverage.actual (the re-pin flow +
  -- scripts/golden-diff.sh keep working unchanged)
  let sections ← corpusOrder.mapM fun k => do
    IO.FS.readFile s!"Tests/coverage-actual/{covSanitize k}.section"
  IO.FS.writeFile "Tests/driver-coverage.actual"
    (hdr1 ++ "\n" ++ hdr2 ++ "\n" ++ String.join sections)
  logInfo s!"{hdr1}"
  logInfo s!"aggregate OK: {all.length} books, sections tile the golden"

coverage_aggregate%

end ACL2.Tests.Coverage
