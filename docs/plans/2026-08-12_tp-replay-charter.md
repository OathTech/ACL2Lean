# TP-replay arc — charter (master plan B1)

Branch `mdd/tp-replay` off main @ 5048e0a. DEMAND-DRIVEN: the first
mirror with debt is on mainline — `len_app_int` carries `sorryAx`
via `drv_tp_mylen` — and the TP-replay gap is the single biggest
lever in the census (`tp:` = 195 kept conditions; 14 of the 20
registered debt sorries are TP-class). The arc kills that gap.

THE DELIVERABLE: the TP discharge route — `proveTp`'s shape coverage
extended over the named frontiers until the TP debt class retires.
Every retirement is FORCED VISIBLE by the standing gates: a debt
entry whose sorry goes stale fails the provenance gate until deleted
in favor of the replay route; a `.nativeSorried` whose debt retired
fails the axiom gate until promoted. The demand-side headline:
`len_app_int`'s receipt flips to the clean trio (update its pinned
receipt + docstring — the FIRST debt retirement observed at the
product layer).

## Queue

1. **Frontier inventory off the real artifact.** Read `proveTp`
   (`Replay/Driver/Provers.lean`) and enumerate its named frontiers
   (known set at drafting: arity > 2; multi-formal measured subset;
   non-`(acl2-count formal)` measures; non-`O<` well-founded
   relations; the args-valued corollary shape (G1) kept
   hypothesis-backed in `Harness`). For EACH of the 14 TP debt
   entries + the `tp:` census classes, identify WHICH frontier
   blocks it — the work list is measured, not guessed.
2. **Extend shape by shape, demand-ordered**: `drv_tp_mylen` first
   (the mirror's debt), then `dis_how_many_tp`/`dis_insert_tp` (the
   sorting waypoints' most-consumed), then the rest by census
   weight. Each extension: the walker generalizes a SHAPE (never a
   per-function special case — the anti-specialization rule); the
   affected debt entries' sorries retire by DELETION + consumer
   rewiring to the discharge route; the catalog promotions and
   receipt updates ride the same increment; goldens re-pinned ONLY
   where rows legitimately gain discharges (row-by-row review; any
   unexpected flip is a mandatory stop).
3. **The emitted-corollary ground truth**: every discharge consumes
   the EMITTED `:TYPE-PRESCRIPTION` corollary (type facts come from
   ACL2, never Lean inference); a corollary shape the emitter does
   not record is a FORK round-trip item (scout first, standard fork
   discipline), not a Lean-side workaround.
4. **Exit audit** (one adversarial claims reviewer + verification):
   the retirements are genuine (each former debt fact now arrives
   via the discharge route from emitted corollaries — no Lean-side
   re-derivation slipped in); the census delta is real; the
   `len_app_int` receipt flip is load-bearing (re-run the
   pathfinder's glue-only-closure check on it). Fix round,
   TRUE_EXIT=0, exit report + merge proposal.

## Discipline

Two-tier gating; goldens row-by-row with diagnosis-before-repin;
the thin-Lean boundary (retirement = deletion + replay route, never
a Lean re-proof — the provenance gate enforces); the
anti-specialization rule on every walker extension; fork changes (if
item 3 triggers) under the full fork sequencing discipline
(commit-fork → build → recapture-all → provenance).

## Exit criterion + escape hatch

Done = the TP debt class EMPTY (or every survivor blocked on a
named, logged frontier — honest deferral is success), the census
`tp:` delta reported, `len_app_int` trio-clean (or its blocker
named), audit + fix round + TRUE_EXIT=0, exit report with merge
proposal. ESCAPE HATCH (binding): early exit at any time, for any
reason or none; fidelity rules override completion pressure.
MANDATORY-EXIT triggers: any per-function specialization in the
walker; any Lean-side re-derivation of a TP fact; any golden flip
without diagnosis; a fork item proceeding without the scout.

## ARC LOG — item 1 complete: THE MEASURED WORK LIST (2026-08-12)

The scout's inventory (empirical — every entry probe-verified against
the real devs/worlds) CORRECTS this charter's assumptions:
- C1: the real census target is **76** (main-row kept conds routed
  through `proveTp`); the other 119 `tp:` conds live on standalone
  informational DP probes (`replayDischargeLeaf` emits them
  unconditionally — a separate optional lever, needs a ruling, not
  taken here).
- C2: the DOMINANT frontier is the RETURN-PATH CALL restriction
  (`tpWalk`, Provers.lean:433-439) — not the charter's named
  measure/WF frontiers, which bind ZERO entries. Three sub-shapes:
  BINARY-+ over the IH value (46 census / 6 entries incl. the
  len_app_int headline), CONS (17 / 4), callee-TP (5 / 2, downstream
  of CONS). Plus arity-3 (7 / 1) and the args-valued G1 routing
  (1 / 1). 1+2+3 = 12/14 entries; +4+5 = 76/76.
- C3: NO FORK NEEDED — the emission's `:TYPE-PRESCRIPTION` events
  carry `:LEAVES` (per-return-path-leaf terms + ACL2's type-set
  verdicts), parsed (ProofLog.lean:1134) and stored (ClauseTree:97)
  but not exposed (a one-line Development accessor). THE DESIGN
  SPINE: the return-path extension consumes ACL2's own emitted leaf
  verdicts — emitted-data-driven, never Lean-side type derivation.
- Sequencing: dis_acl2_count_tp is the hardest (compound blockers
  incl. non-destructor self-calls) — LAST. dis_bnext_size_tp needs
  the callee shape too. The Provers.lean:649 throwError (unreached)
  should become throwFrontier in passing (asymmetry with
  proveTotality's tagged twin).
- Open proof risk (the scout could not verify): that the extensions
  CLOSE — the Logic-primitive preservation obligations
  (P(plus '1 v) from P(v) for the emitted corollary shapes).
  Increment 1 answers it empirically.

## ARC LOG — increments 6+7 ruled in (Mike, 2026-08-13)

The two candidate survivors are CLOSED IN THIS ARC, both in general
form — "no messy patches":
- **Increment 6 — ACL2-COUNT** (after the 4+5 batch): two
  generalizations, no per-function anything. (a) The IH family
  generalizes from THE MEASURED POSITION to ANY self-call whose
  argument is a destructor chain — the strong consCount induction
  already justifies every such position; subsumes the existing
  single-position case; every future tree recursion rides free.
  (b) The callee arm's corollary source becomes OFFER-TABLE ∪
  GROUND-ZERO TABLE — recon confirmed the emission already carries
  gz TP events for NUMERATOR/DENOMINATOR/INTEGER-ABS (source-1 all
  the way; the gzTps channel exists; no fork, no core-logic
  fallback needed). The nested-sum composition is expected to close
  once every leaf position is quote / IH-covered self-call /
  table-backed callee; if not, named report.
- **Increment 7 — the ZIP2 class**: the branch-fact tracker learns
  ACL2's IF-normalization DECOMPOSITIONS — `(IF a a b) = NIL` yields
  both `a = NIL` and `b = NIL` (the or-shape), dually the and-shape
  when true — one principled rule about ACL2's own boolean normal
  forms, enriching the fact set every downstream matcher (incl. the
  shared decrease matcher) consults. General by construction; the
  multi-controller book family (zip2/zip3/interleave) inherits a
  working matcher. CAUTION: the seam is shared termination
  machinery — wider blast surface than the TP walker; goldens
  row-by-row with extra care; if less contained than it looks,
  report and move to the book-family arc's opening item.
- Revised exit target: TP debt class EMPTY (7 → 0 through incs 4-6);
  main-row `tp:` → 0 expected (ZIP2's cond clears via inc 7's
  decomposition feeding the decrease matcher).
