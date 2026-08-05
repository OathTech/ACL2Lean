/-
  Driver coverage harness over the whole sample corpus.

  For every `.proof-log` in the corpus, this parses → reconstructs → projects the World
  (`Development.toWorld`) → runs the replay driver on each local theorem, recording per
  theorem whether it REPLAYED (the driver emitted a kernel-valid proof Expr) or the exact
  failure message. Most theorems fail-closed at a frontier today (induction, type-set,
  multi-arg unfold, exec-counterpart, …) — those are EXPECTED clean failures; the value is
  (1) exercising the new derive-on-demand / `toWorld` / `reflectWorld` code across diverse
  worlds (incl. `simple.proof-log`, two defuns), surfacing any real bug as a non-frontier
  message, and (2) a live coverage table that fills in as node kinds / the induction
  scaffold land.

  ON DEMAND (not in the `just ci` aggregate — it runs the driver over the whole corpus):
      lake build Tests.DriverCoverage
  reads the table from the build output.

  LEGEND — the two columns of a row can legitimately disagree (fold-back audit
  F8, dp-premises): a row's `cond[…]` reflects the COMPOSED conditional replay
  (`replayProofConditional` — rule/linear/equivrefl premise machinery in
  scope), while its `[DISCHARGE: …]` detail is the STANDALONE per-leaf probe
  (`tryDischarge` → `replayDischargeLeaf`, no ambient telescope, no premise
  machinery, `assumeFact := true`). A leaf can therefore read `◌ assumed …
  ASSUMED:dp-fact` in the detail while the composed row carries no ASSUMED
  cond at all — the composed row is the claim that matters; the probe column
  measures telescope-independent leaf strength. ENFORCED (consumer-queue
  audit 2026-08-05 S1/S4): a composed replay whose kept conds contain
  ASSUMED:dp-fact renders `ASSUMED ◌`, never `REPLAYED ✓`, and is never
  registered as a consumable mirror (`tryReplay`'s single choke point) —
  the assumed obligation is stated over independently-quantified opaques
  and can be FALSE, making the ✓ vacuous.

  NO SILENT SKIPS: each log is `include_str`'d, so an ABSENT log is a HARD compile
  error naming the file (never silently skipped). CAVEAT (audited 2026-06-10): Lake
  does NOT track the embedded files as dependencies — a CHANGED log does not trigger
  a rebuild, and the stale embedded copy survives in the .olean. The capture script
  (`scripts/capture-proof-log.sh`) therefore force-invalidates every include_str
  consumer's build artifacts after recapture; regenerate the corpus with it (never
  by hand) before building this.
-/
import ACL2Lean.Replay.Runner
import Lean

open ACL2 ACL2.Replay.Runner Lean Lean.Elab Lean.Elab.Command Lean.Meta

namespace ACL2.Tests.Coverage

/-- The corpus as `(name, log-content)` pairs. Each log is `include_str`'d (a missing one
    is a hard compile error here — no silent skip — and lake re-runs on change). -/
def corpus : List (String × String) :=
  [("simple",                  include_str "../acl2_samples/simple.proof-log"),
   ("00-direct",               include_str "../acl2_samples/recon-tests/00-direct.proof-log"),
   ("01-multi-theorem",        include_str "../acl2_samples/recon-tests/01-multi-theorem.proof-log"),
   ("02-rev",                  include_str "../acl2_samples/recon-tests/02-rev.proof-log"),
   ("03-linear",               include_str "../acl2_samples/recon-tests/03-linear.proof-log"),
   ("04-multi-case-induction", include_str "../acl2_samples/recon-tests/04-multi-case-induction.proof-log"),
   ("05-hints",                include_str "../acl2_samples/recon-tests/05-hints.proof-log"),
   ("06-measure",              include_str "../acl2_samples/recon-tests/06-measure.proof-log"),
   ("07-mutual-recursion",     include_str "../acl2_samples/recon-tests/07-mutual-recursion.proof-log"),
   ("08-equality-reasoning",   include_str "../acl2_samples/recon-tests/08-equality-reasoning.proof-log"),
   ("09-defn-unfold",          include_str "../acl2_samples/recon-tests/09-defn-unfold.proof-log"),
   ("10-tree-induction",       include_str "../acl2_samples/recon-tests/10-tree-induction.proof-log"),
   ("11-custom-measure",       include_str "../acl2_samples/recon-tests/11-custom-measure.proof-log"),
   ("12-multi-controller",     include_str "../acl2_samples/recon-tests/12-multi-controller.proof-log"),
   ("13-multi-measured-var",   include_str "../acl2_samples/recon-tests/13-multi-measured-var.proof-log"),
   ("14-accumulator",          include_str "../acl2_samples/recon-tests/14-accumulator.proof-log"),
   ("15-nested-induction",     include_str "../acl2_samples/recon-tests/15-nested-induction.proof-log"),
   ("16-three-way",            include_str "../acl2_samples/recon-tests/16-three-way.proof-log"),
   ("17-rule-application",     include_str "../acl2_samples/recon-tests/17-rule-application.proof-log"),
   -- The DRIVING CORPUS (sorting roadmap R0a): leaf books with theorems only.
   -- orderedp/how-many are defun-only (0 theorems) — the integrity net cannot
   -- distinguish a theorem-less book from a TRUNCATED capture, so they stay
   -- out until R2 consumes their defuns via include-book composition.
   ("sorting/perm",            include_str "../acl2_samples/sorting/perm.proof-log"),
   -- 2a: the dependency book carrying the include-book theorems the later
   -- sorting books cite (NOT-MEMB-IMPLIES-HOW-MANY-IS-0 & co.) — placed
   -- BEFORE its consumers so its trees are in the cross-book offer.
   -- KNOWN MISMATCH (pre-merge seams audit F1, 2026-08-02): corpus order
   -- is NOT the include graph — isort/bsort actually include
   -- ordered-perms (which sits AFTER them here), so they never see its
   -- offers (a silently missed capability, fail-closed), while every
   -- sorting book sees the 19 unrelated recon-test books' rules
   -- (over-offer; measured impact nil — deps=perm-only vs deps=all give
   -- byte-identical rows). Reordering changes golden rows, so it rides
   -- the include-book provenance gate (close-out arc Phase 7 debt)
   -- rather than a quiet edit here.
   ("sorting/convert-perm-to-how-many",
    include_str "../acl2_samples/sorting/convert-perm-to-how-many.proof-log"),
   -- R2: the first include-book composition — included defuns re-emit with
   -- :INCLUDED T (justification, no termination clauses → total: stays
   -- hypothesis-backed, D6) and included theorems with :SOURCE :INCLUDE-BOOK
   -- (statement + rules, no proof tree — rule:<thm> citations stay
   -- hypothesis-backed until cross-book proof import).
   ("sorting/isort",           include_str "../acl2_samples/sorting/isort.proof-log"),
   -- J5: ordered-perms reconstructs (its revert wall fell).
   -- J6: the type-set-derived equivalence source class lets msort
   -- reconstruct; its rows sit on named decrease-fragment frontiers.
   -- 2e (bsort-recon): the clausify-stream RECON wall fell — expand-and-or
   -- detail steps now attach to their expansion markers — so bsort enters
   -- the corpus (fold-back audit F3). Its rows sit on named replay
   -- frontiers (μ-registry, detail-chain replay); the corpus entry is what
   -- exercises the detail recon + the never-ignore guard in-sweep (F2).
   ("sorting/bsort",           include_str "../acl2_samples/sorting/bsort.proof-log"),
   ("sorting/ordered-perms",   include_str "../acl2_samples/sorting/ordered-perms.proof-log"),
   -- Phase 4 (R6): equisort ENTERS on the witness-scoping recon (BUG-019
   -- by structure — witnesses recorded scoped, excluded from the world).
   -- Its rows are HONESTLY RED until the parametric-statement machinery
   -- lands: the constraint theorems' trees reference the scoped witness
   -- fns and the strong/weak theorems the constrained fns, both opaque in
   -- the certified world (P1 progress: the row-bearing book is in the
   -- sweep; the rows are the Phase-4 build's scoreboard).
   ("sorting/equisort",        include_str "../acl2_samples/sorting/equisort.proof-log"),
   -- BUG-019 GATE VISIBILITY (equisort-r6 audit F1): the pin book was
   -- outside the sweep, so a regression re-greening its rows (the vacuous
   -- constrained-telescope greens, caught NOT-READY and reverted) was
   -- invisible to `just ci`. Its two rows are pinned HONESTLY RED (opaque
   -- CF — the constrained fn has no world definition); any green here is
   -- a statement-vacuity/substitution alarm, not progress.
   ("cov-encapsulate",         include_str "../acl2_samples/pattern-tests/cov-encapsulate.proof-log"),
   ("sorting/msort",           include_str "../acl2_samples/sorting/msort.proof-log"),
   -- J7: the dotted-rune parse (multi-rule events, (:REWRITE FOO . k)) lets
   -- qsort and sorts-equivalent — the D7 consumer — reconstruct.
   ("sorting/qsort",           include_str "../acl2_samples/sorting/qsort.proof-log"),
   ("sorting/sorts-equivalent", include_str "../acl2_samples/sorting/sorts-equivalent.proof-log")]

/-! NOTE (seams audit F7): `termination:<fn>` rows are pushed as display
    lines but NOT counted in `res.total` — the header's N/M counts
    theorem rows only (101 status rows vs the 80/100 header is by
    construction, not drift). -/

/-- The committed GOLDEN coverage table (audit-debt item, #37 full audit): the
    whole report — every per-theorem status line and the summary counts — is
    diffed against this checked-in baseline, so a refactor's "coverage
    unchanged" claim is a build-enforced diff against a saved artifact, not a
    re-asserted number. `include_str` makes an absent golden a hard compile
    error. A mismatch FAILS elaboration, so no stale .olean caches the old
    embed — the re-run after updating the golden re-reads the file. -/
def goldenTable : String := include_str "driver-coverage.golden"

/-- Where the freshly computed table is written on every run (gitignored), so
    an INTENDED coverage change is updated by
    `cp Tests/driver-coverage.actual Tests/driver-coverage.golden`. -/
def actualTablePath : System.FilePath := "Tests/driver-coverage.actual"

elab "#driver_coverage" : command => do
  liftTermElabM do
    -- The per-book harness lives in ACL2Lean/Replay/Runner.lean (shared with
    -- the focused CLI `acl2lean-replay`); this elab only aggregates across
    -- the corpus and enforces the gates. Reconstruction-INTEGRITY failures
    -- (parse-fail / recon-fail / zero-theorem capture) and EMISSION-FRONTIER
    -- failures (black-box PROVED leaves, Track B gap) HARD-FAIL the build
    -- below — never a silent skip.
    let mut agg : BookResult := {}
    -- 2a: prior books' theorem trees, accumulated in corpus order — the
    -- CROSS-BOOK dependency offer for each subsequent book
    let mut priorTrees : List (String × ClauseProof) := []
    -- P3 cross-rules: prior books' STORED RULES, same corpus-order
    -- accumulation — a dep tree re-replayed at a consumer world can cite
    -- rules the consumer's log never re-emits
    let mut priorRules : List ACL2.RuleSpec := []
    -- per-file wall times, logged SEPARATELY from the golden-compared report
    -- (timings vary run to run; the baseline must stay deterministic)
    let mut timings : Array String := #[]
    for (name, content) in corpus do
      let tFile0 ← IO.monoMsNow
      let (r, trees, rules) ← runBook name content (crossTrees := priorTrees)
        (crossRules := priorRules)
      agg := { lines := agg.lines ++ r.lines,
               total := agg.total + r.total,
               replayed := agg.replayed + r.replayed,
               replayedCond := agg.replayedCond + r.replayedCond,
               dpTotal := agg.dpTotal + r.dpTotal,
               dpReplayed := agg.dpReplayed + r.dpReplayed,
               dpAssumed := agg.dpAssumed + r.dpAssumed,
               integrityFails := agg.integrityFails ++ r.integrityFails,
               emissionFrontiers := agg.emissionFrontiers ++ r.emissionFrontiers }
      priorTrees := priorTrees ++ trees
      priorRules := priorRules ++ rules.filter
        (fun r => !priorRules.any (fun o => o.runeKey == r.runeKey))
      let tFile1 ← IO.monoMsNow
      timings := timings.push s!"  {name}: {tFile1 - tFile0} ms"
    let lines := agg.lines
    let (replayed, replayedCond, total) := (agg.replayed, agg.replayedCond, agg.total)
    let (dpTotal, dpReplayed, dpAssumed) := (agg.dpTotal, agg.dpReplayed, agg.dpAssumed)
    let integrityFails := agg.integrityFails
    let emissionFrontiers := agg.emissionFrontiers
    let report := s!"Driver coverage — REPLAYED {replayed}/{total} ({replayed - replayedCond} unconditional + {replayedCond} conditional); DP-discharge leaves ✓{dpReplayed} ◌{dpAssumed} ✗{dpTotal - dpReplayed - dpAssumed} of {dpTotal}:\n{"\n".intercalate lines.toList}"
    logInfo report
    logInfo m!"per-file wall times (informational — NOT golden-compared):\n{"\n".intercalate timings.toList}"
    -- GOLDEN-TABLE GATE: write the fresh table, then diff against the committed
    -- baseline. Runs BEFORE the integrity/emission gates so the .actual file is
    -- always produced, but only THROWS after them (their failures are the
    -- primary signal; a golden mismatch alongside them is a symptom).
    IO.FS.writeFile actualTablePath (report ++ "\n")
    let goldenLines := goldenTable.trimAsciiEnd.toString.splitOn "\n"
    let reportLines := report.splitOn "\n"
    let tableDrift : Option String :=
      if goldenLines == reportLines then none
      else
        let n := max goldenLines.length reportLines.length
        let diffs := (List.range n).filterMap fun i =>
          let g := goldenLines.getD i "<absent>"
          let r := reportLines.getD i "<absent>"
          if g == r then none else some s!"  line {i + 1}:\n    golden: {g}\n    actual: {r}"
        some ("\n".intercalate diffs)
    unless integrityFails.isEmpty do
      throwError m!"Reconstruction-integrity failures (not the replay frontier):\n{"\n".intercalate integrityFails.toList}"
    unless emissionFrontiers.isEmpty do
      -- HARD RED until the Track B emission lands (docs/plans/2026-06-09_direct-proof-emission.md).
      -- A black-box PROVED leaf has no emitted proof structure to replay; treating it as
      -- handled would be a fidelity lie. These FAIL the build deliberately.
      throwError m!"Unhandled EMISSION FRONTIER — {emissionFrontiers.size} theorem(s) discharged by an uninstrumented preprocess/eval/type-set path (black-box PROVED leaf, no replayable structure emitted). This is the Track B emission gap (docs/plans/2026-06-09_direct-proof-emission.md), deliberately failing until that instrumentation lands:\n{"\n".intercalate emissionFrontiers.toList}"
    if let some drift := tableDrift then
      throwError m!"Coverage table DIFFERS from the committed golden (Tests/driver-coverage.golden) — coverage changed. If UNINTENDED, this is a regression: fix it. If intended, review the diff and update the baseline:\n  cp Tests/driver-coverage.actual Tests/driver-coverage.golden\nDiffering lines:\n{drift}"

-- Unlimited at the command level: per-leaf budgets are enforced INSIDE
-- `tryDischarge` (withRealMaxHeartbeats, ~1M-unit runaway guards), so one expensive leaf cannot
-- poison the rest of the sweep.
set_option maxHeartbeats 0 in
#driver_coverage

end ACL2.Tests.Coverage


