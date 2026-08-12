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
