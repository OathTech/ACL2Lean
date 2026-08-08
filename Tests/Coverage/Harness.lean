import ACL2Lean.Replay.Runner
import ACL2Lean.Replay.ParametricInstantiate
import ACL2Lean.Imported.Sorting
import Lean

/-! # Per-book coverage harness (perf arc item 1, 2026-08-07)

The former monolithic `Tests/DriverCoverage.lean` elaborated all 30
corpus books SEQUENTIALLY in one module (~15 min, one core). Each book
is now its own Lake module invoking `coverage_book%`, so Lake gives
parallelism across independent books AND incrementality (a one-book
recapture rebuilds that book + its dependents only). Semantics are
UNCHANGED by construction:

- the golden stays the single `Tests/driver-coverage.golden`; each book
  checks BYTE-EXACT equality of its own section (the aggregate module
  checks the header and that the sections tile the file);
- cross-book offers replicate the sweep exactly: each book's dep list
  (`covDeps`) was DERIVED as {edges in its own log} ∩ {books EARLIER in
  the canonical corpus order} — the same set the corpus-order
  accumulation ∩ include-DAG gate produced (the ordering limitation —
  ordered-perms after its consumers — is deliberately preserved; fixing
  it is a separately-reviewed promotion);
- dep trees/rules are re-derived by PARSE ONLY (`Runner.bookTrees` /
  `Runner.allBookRules` on the dep's own log — no dep re-replay).
  CROSS-RULES NOTE: the old sweep offered rules from ALL earlier books
  (over-offer, measured impact nil — DriverCoverage's old F1 note);
  this harness offers dep-books' rules only. Byte-identical goldens are
  the proof the restriction is behavior-free; any row change fires the
  arc's escape hatch.

Logs are read with `IO.FS.readFile` at elaboration (repo-root
relative). Lake does NOT track them as deps — same caveat as the old
`include_str` corpus — and `scripts/capture-proof-log.sh` derives its
invalidation list from the `"….proof-log"` references in source, which
matches the `covLogPath` literals below via the book-name convention. -/

open ACL2 ACL2.Replay.Runner Lean Lean.Elab Lean.Elab.Command Lean.Meta

namespace ACL2.Tests.Coverage

/-- The canonical corpus order (the golden's section order). -/
def corpusOrder : List String :=
  ["simple", "00-direct", "01-multi-theorem", "02-rev", "03-linear",
   "04-multi-case-induction", "05-hints", "06-measure",
   "07-mutual-recursion", "08-equality-reasoning", "09-defn-unfold",
   "10-tree-induction", "11-custom-measure", "12-multi-controller",
   "13-multi-measured-var", "14-accumulator", "15-nested-induction",
   "16-three-way", "17-rule-application", "sorting/perm",
   "sorting/convert-perm-to-how-many", "sorting/isort", "sorting/bsort",
   "sorting/ordered-perms", "sorting/equisort", "cov-encapsulate",
   "sorting/msort", "sorting/qsort", "sorting/sorts-equivalent"]

/-- Book name → log path (repo-root relative). -/
def covLogPath (name : String) : String :=
  if name == "simple" then "acl2_samples/simple.proof-log"
  else if name == "cov-encapsulate" then
    "acl2_samples/pattern-tests/cov-encapsulate.proof-log"
  else if name.startsWith "sorting/" then
    s!"acl2_samples/{name}.proof-log"
  else s!"acl2_samples/recon-tests/{name}.proof-log"

/-- Each book's cross-book dependency offer set — DERIVED (2026-08-07)
    as {include edges in its own log} ∩ {earlier in corpusOrder}; books
    absent here have no offers. Re-derive with the arc's dep script if
    the corpus or the include structure changes. -/
def covDeps : List (String × List String) :=
  [("sorting/convert-perm-to-how-many", ["sorting/perm"]),
   ("sorting/isort",
    ["sorting/perm", "sorting/convert-perm-to-how-many"]),
   ("sorting/bsort",
    ["sorting/perm", "sorting/convert-perm-to-how-many"]),
   ("sorting/ordered-perms", ["sorting/perm"]),
   ("sorting/equisort",
    ["sorting/perm", "sorting/convert-perm-to-how-many",
     "sorting/ordered-perms"]),
   ("sorting/msort",
    ["sorting/perm", "sorting/convert-perm-to-how-many",
     "sorting/ordered-perms"]),
   ("sorting/qsort",
    ["sorting/perm", "sorting/convert-perm-to-how-many",
     "sorting/ordered-perms"]),
   ("sorting/sorts-equivalent",
    ["sorting/perm", "sorting/convert-perm-to-how-many",
     "sorting/isort", "sorting/bsort", "sorting/ordered-perms",
     "sorting/equisort", "sorting/msort", "sorting/qsort"])]

/-- The per-book result summary the aggregate sums (small data only). -/
structure CovCounts where
  total : Nat
  replayed : Nat
  replayedCond : Nat
  dpTotal : Nat
  dpReplayed : Nat
  dpAssumed : Nat
  lineCount : Nat
  deriving Repr, Inhabited

def covSanitize (name : String) : String :=
  name.map (fun c => if c.isAlphanum then c else '_')

/-- The golden's section for one book: the lines from `• <name>  ` up to
    (excluding) the next `• ` line. -/
def goldenSection (golden : String) (name : String) : Except String (List String) := do
  let lines := (golden.splitOn "\n").filter (· ≠ "")
  let hdr := s!"• {name}  "
  let rec go (ls : List String) : Except String (List String) :=
    match ls with
    | [] => .error s!"goldenSection: no section '• {name}' in the golden"
    | l :: rest =>
      if l.startsWith hdr then
        .ok (l :: rest.takeWhile (fun x => !x.startsWith "• "))
      else go rest
  go lines

/-- Parse a dep book's log to its offer payload — PARSE ONLY. The DEV
    itself rides along (R7b 2c W4: the usefi discharge rebuilds the
    cited theorem's parametric statement from it). -/
def depPayload (dep : String) :
    TermElabM (String × Development × List (String × ClauseProof)
      × List ACL2.RuleSpec) := do
  let content ← IO.FS.readFile (covLogPath dep)
  let log ← match ProofLog.parse content with
    | .ok l => pure l
    | .error e => throwError "coverage_book%: dep {dep} PARSE-FAIL {e}"
  let dev ← match ClauseTree.buildDevelopment log with
    | .ok d => pure d
    | .error e => throwError "coverage_book%: dep {dep} RECON-FAIL {e}"
  return (dep, dev, bookTrees dev, allBookRules dev)

/-- Run ONE corpus book with the sweep's exact semantics and check its
    golden section byte-exactly; emits `covCounts_<sanitized>`. -/
elab "coverage_book% " nameLit:str : command => do
  let name := nameLit.getString
  liftTermElabM do
    let content ← IO.FS.readFile (covLogPath name)
    let deps := (covDeps.lookup name).getD []
    let payloads ← deps.mapM depPayload
    let crossTreesByBook := payloads.map (fun (n, _, t, _) => (n, t))
    let crossRules := payloads.flatMap (fun (_, _, _, r) => r)
    let crossDevs := payloads.map (fun (n, d, _, _) => (n, d))
    let t0 ← IO.monoMsNow
    let (r, _, _) ← runBook name content
      (crossTreesByBook := crossTreesByBook) (crossRules := crossRules)
      -- R7b 2c W4f: the usefi discharge composition is FULLY BUILT and
      -- WIRED but DISABLED — in-sweep runs SIGABRT on term depth
      -- despite the kernel-route decides, the constant-declaration
      -- pattern, and hint-only gates (three remediations, all
      -- committed); the remaining debugging campaign (trace-symbol
      -- profiling + composition bisection) is the Phase 3 close-out's
      -- top continuation item. Enable by swapping none for:
      --   some (fun dev cfg ctx spec =>
      --     ACL2.Imported.Mirrors.mkUseFiDischarger crossDevs
      --       [``ACL2.Worlds.Sorting.dis_pce_total,
      --        ``ACL2.Worlds.Sorting.dis_how_many_tp] dev cfg ctx spec)
      (usefiDischarge := some (fun dev cfg ctx spec =>
        ACL2.Imported.Mirrors.mkUseFiDischarger crossDevs
          [``ACL2.Worlds.Sorting.dis_pce_total,
           ``ACL2.Worlds.Sorting.dis_how_many_tp] dev cfg ctx spec))
    let t1 ← IO.monoMsNow
    unless r.integrityFails.isEmpty do
      throwError "coverage_book% {name}: integrity failures \
        {r.integrityFails.toList}"
    let golden ← IO.FS.readFile "Tests/driver-coverage.golden"
    let want ← match goldenSection golden name with
      | .ok ls => pure ls
      | .error e => throwError "coverage_book% {name}: {e}"
    let got := r.lines.toList
    -- Audit A4 (2026-08-07): the actual-section artifact is written
    -- BEFORE the golden compare (the old monolith's deliberate
    -- property) — a differing book still updates its section, so the
    -- assembled .actual is exactly what the re-pin flow needs.
    IO.FS.createDirAll "Tests/coverage-actual"
    IO.FS.writeFile s!"Tests/coverage-actual/{covSanitize name}.section"
      (String.intercalate "\n" got ++ "\n")
    unless got == want do
      let diff := (got.zipIdx.filterMap fun (l, i) =>
        if want.getD i "" != l then some s!"  line {i}:\n    want: \
          {want.getD i "<absent>"}\n    got:  {l}" else none)
      throwError "coverage_book% {name}: section DIFFERS from the \
        committed golden (Tests/driver-coverage.golden). If unintended \
        this is a regression; if intended: rebuild the aggregate \
        (Tests.DriverCoverage) to assemble Tests/driver-coverage.actual, \
        review with `just golden-review`, then `just coverage-repin` \
        (NEVER a hand edit or bare cp — the repin recipe also \
        invalidates the IO-read caches; audit A3).\n\
        {String.intercalate "\n" diff}\n\
        (want {want.length} line(s), got {got.length})"
    logInfo s!"coverage {name}: {r.replayed}/{r.total} replayed; \
      {t1 - t0} ms"
  -- the small-data counts def for the aggregate, computed from the
  -- just-verified golden section (byte-identical to the live run)
  let golden2 ← IO.FS.readFile "Tests/driver-coverage.golden"
  let lines ← match goldenSection golden2 name with
    | .ok ls => pure ls
    | .error e => throwError "coverage_book% {name}: {e}"
  let rows := lines.filter (fun l => l.startsWith "    " && (l.splitOn " → ").length > 1)
  let thmRows := rows.filter (fun l => !(l.trimLeft.startsWith "termination:"))
  let replayedRows := thmRows.filter (fun l => (l.splitOn " → REPLAYED ✓").length > 1)
  -- the COMPOSED row's cond only — strip the [DISCHARGE: …] suffix
  -- first (probe leaves carry their own cond[ text)
  let condRows := replayedRows.filter (fun l =>
    ((((l.splitOn "  [DISCHARGE:").headD l)).splitOn " cond[").length > 1)
  let dpMarks := lines.flatMap (fun l => (l.splitOn "[DISCHARGE: ").drop 1)
  let count := fun (pat : String) =>
    dpMarks.foldl (fun a m => a + ((m.splitOn pat).length - 1)) 0
  let dpR := count " ✓"
  let dpA := count " ◌"
  let dpF := count " ✗"
  let cid := mkIdent (Name.mkSimple s!"covCounts_{covSanitize name}")
  let mk := fun (n : Nat) => Syntax.mkNumLit (toString n)
  elabCommand (← `(command|
    def $cid : ACL2.Tests.Coverage.CovCounts :=
      { total := $(mk thmRows.length),
        replayed := $(mk replayedRows.length),
        replayedCond := $(mk condRows.length),
        dpTotal := $(mk (dpR + dpA + dpF)),
        dpReplayed := $(mk dpR), dpAssumed := $(mk dpA),
        lineCount := $(mk lines.length) }))

end ACL2.Tests.Coverage
