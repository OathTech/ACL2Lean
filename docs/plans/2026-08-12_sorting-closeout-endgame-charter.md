# Sorting closeout endgame — the remaining technical work (charter draft)

Drafted 2026-08-12 during the demo-v2 build, for Mike's review. Scope:
everything between HERE (demo v2, 110/116, 49 natives, 20 debt
sorries, 3 sorting pendings) and the sorting family being DONE —
plus the named demo follow-ups. Out of scope (separate tracks, listed
at the end): the masquerade/differential roadmap, the gen-world
independent frontend, the non-sorting backlog book families.

The through-line: every remaining item is a DEBT-RETIREMENT or
FRONTIER arc. The mirror layer is complete and gated; what remains is
wiring the replay routes the debt names. Each arc below retires a
named class MECHANICALLY (the promotion-forcing gates turn each
retirement into build-enforced catalog promotions — no per-book
work).

## Arc 1 — with_termination coverage + the usefi lift
**(the REQUIRED class: the ruling says wired, not sorried)**

Goal: the admission-replay route (`with_termination` / `termByFn`)
covers MERGE2, MSORT, O<, PCE, BNEXT (+ BSORT/O-P when arc 4 lands
their kits) — retiring the 5 REQUIRED-class sorries
(`dis_*_total`) — and the usefi alias-world discharge consumes the
resulting `total:` facts, re-greening the three `*-IS-ISORT`
capstone rows (ASSUMED → REPLAYED, 110→113) and resurrecting their
retired statement pins + parked catalog entries from git history.
Payoff: the headline capstones return, on the honest route this
time. Census target: `total:` 172 → the residue the kits can't reach
(each named). Exit: the REQUIRED class is EMPTY or every survivor
has a named frontier ruled acceptable; the capstone rows green or
their blockers named. ESCAPE HATCH: standard (any wall, any doubt,
any needed ruling → report and stop).

## Arc 2 — the TP-replay discharge route
**(the census's dominant lever: `tp:` = 195 kept conditions)**

Goal: extend `proveTp`'s shape coverage (the named frontiers in
`Replay/Driver/Provers.lean`: arity > 2, multi-formal measured
subset, non-`acl2-count` measures, args-valued corollaries) until
the TP debt class retires — 14 sorries (12 original + the 2 minted)
— and the `tp:` kept-condition census falls to the shapes genuinely
outside the emitted corollaries. Every retirement is forced visible:
the provenance gate fails any debt entry whose sorry is gone, the
axiom gate demands promotion of every `.nativeSorried` whose debt
retired. Exit: TP class empty or every survivor named; the census
delta reported. ESCAPE HATCH: standard. NOTE: this arc should also
take the DECODE-ASSEMBLY generator if it falls out (the deferred
item-2 follow-on: all ~43 decodes are a six-step fold with four
enders) — it halves the hand cost of every future book.

## Arc 3 — the R-lane (PERM-TLFIX → the CONVERT-PERM capstone)

Goal: the G1 frontier — replaying a rewriting-equivalence rune under
user equivalence `perm` (the L2 R-parameterized recipe) — lands;
PERM-TLFIX's row greens; `rule:PERM-TLFIX` + `tp:TLFIX` discharge;
CONVERT-PERM-TO-HOW-MANY (the book's capstone) greens and takes its
native (the perm ↔ counts-agree-at-the-witness mirror — the tight
mirror, per the tightest-available ruling); `dis_convert_perm` (the
R-lane debt) retires. Sorting reaches 78/78. Exit: the capstone row
+ native or a named wall inside the R-recipe. ESCAPE HATCH:
standard; the R-lane has prior design work (the L2 invariant) — any
divergence from it is a mandatory stop for a ruling.

## Arc 4 — the linear unlock + the bsort finish

Goal: a discharge route for `linear:` kept conditions (the class
with NO route today — ACL2's linear-arithmetic corollaries as
premises; expected shape: the DP-leaf carve-out's `omega` discharge
at the premise site, consuming the emitted linear corollary — a
DESIGN to rule on before building), plus the bsortExec/bsortL kit
(P2 bubble-size measure — the decrease facts already exist as
`bnextSizeL` natives). Lands ORDEREDP-BSORT + HOW-MANY-BSORT as
natives; the sorting `.pending` census reaches ZERO. Exit: both rows
dispositioned or the linear design ruled infeasible-for-now.
ESCAPE HATCH: standard; the linear design goes to Mike BEFORE build.

## Arc 5 — demo polish (small, after the debt arcs move)

- The Lifting ENCODER SPLIT (encoders out of the EvalLemmas import
  cone) — upgrades the machinery-layer import pins to the design's
  original strong claim.
- The Perm split + section-marker cleanup (deferred v1 items), IF
  the demo cadence warrants.
- Debt.lean/Assumptions.lean shrinks arc-by-arc as classes retire;
  each retirement updates the Statements page's tier-3 count (the
  receipts force it).

## Standing constraints (all arcs)

The thin-Lean boundary (P1/P2/P3; win states; never mint outside
existing classes without a ruling); the two-standard rule (gates are
speedbumps — deletion over hardening; adversarial review reserved
for semantics/claims/records); the tightest-available-mirror
principle; two-tier gating with TRUE_EXIT=0 at claim points; the
per-book-family provenance audit cadence (the next book family —
accumulator/zip — triggers one); goal escape-hatches per the
CLAUDE.md rule.

## Out of scope (separate tracks, not forgotten)

- The MASQUERADE roadmap (H3): growing the differential corpus /
  trusted-core primitives — the evalOpt-fidelity track.
- The gen-world INDEPENDENT FRONTEND: wiring `WorldGen`/`Translator`
  as the statement-derivation path (the certified-pipeline TODO).
- The non-sorting backlog books (accumulator, zip2/3, interleave,
  nested-induction, rule-application, len2 family): a BOOK-FAMILY
  arc with its own charter — `derive_sim%` is ready for it, the
  family audit cadence applies, and the accumulator books are its
  designed first test (the template gate's decisive case).
- The G2 EvTrue migration (when it lands: DELETE the usage gate per
  its tripwire).

## Sequencing rationale

1 before 2 only because the capstone re-green is the visible payoff
and the REQUIRED class carries the ruling's "must be wired"
obligation; 1 and 2 share machinery (both are driver discharge
routes) and could merge into one arc if scoping favors it. 3 is
independent of 1/2 (parallelizable if ever useful). 4 depends on
nothing but its own design ruling (the bsort kit's decrease facts
exist). 5 rides behind whichever arc touches its files.
