# Induction-generality arc — close-out (2026-07-18)

Branch `mdd/induction-generality`, commits `71fc3a6..c0464cc` over main
`0802802`; fork `acl2-lean-output` commits `0895996`, `15f25bf`,
`ddbf3ef05f`. Governing design: `docs/plans/2026-07-15_induction-generality-design.md`
(ratified). Pre-merge audit: 5 adversarial Opus reviewers + verification
pass, 2026-07-18 — record below.

## What the arc actually delivered (stated mechanically)

The pre-merge audit's outside reviewer correctly called out that the
per-WP commit messages used verbs ("closes", "reaches replay", "enters the
corpus") that connote more than the scoreboard shows. The corrected record:

- **Replay: +2 theorems.** `TRUE-LISTP-APP` and `TRUE-LISTP-FLATTEN`
  (both `recon-tests/10-tree-induction`) — genuine multi-IH WF-induction
  mirrors, audit-verified against the real trees as faithful node-chain
  replays, not shortcuts. Scoreboard 26/50 → 28/79 (23 unconditional).
- **Reconstruction: the sorting corpus now reaches the driver.** msort,
  ordered-perms, qsort, sorts-equivalent (and 15-nested-induction's
  revert) all RECONSTRUCT — previously hard-fails at the tree-building
  layer. All 29 new sorting rows still FAIL, each at a precisely named
  DRIVER frontier. That is the real J5–J7 product: walls moved from
  "cannot build the tree" to "named replay frontier".
- **Of the design's five named scaffold targets** (TRUE-LISTP-FLATTEN,
  LEN-ZIP2, LEN-INTERLEAVE, LEN-ZIP3, NESTED-INDUCTION): one replays;
  four sit at named driver frontiers (path-tracking ×2, clausify bridge,
  builtin-LEN TP fact).
- **Arc exit (J8, T5 criterion): met.** `true_listp_flatten_native_driver`
  (NativeMirrors entry 17): the imported FLATTEN program, on ANY input,
  converges to the encoding of a genuine Lean `List`. Unconditional,
  kernel-checked, axioms `{propext, Classical.choice, Quot.sound}`,
  build-failing axiom gate. The outside reviewer judged the statement
  honest (the env-quantification is a strengthening; keeping `evalOpt` in
  a recognizer-class statement is reasoned, not rationalized) while noting
  it is the softest achievable exit — the one target that already
  replayed.
- **Infrastructure that will outlive the arc:** the env-level strong
  induction scaffold (`measure_strong_induction`), the μ-registry, the
  emitted-termination-clause covering join, revert reconstruction,
  the `Rune` index identity, the fmt-margins emission fix, the two-valued
  recognizer registry, and the core-boolean rule-hyp decode.

## Audit record (2026-07-18)

Five dimensions, all read-only, decorrelated; findings independently
spot-checked by the synthesizer.

**Soundness: zero defects, unanimous.** Both dedicated soundness
reviewers (scaffold, discharge-routes) confirmed no route can produce a
false theorem; every unsupported shape fails closed and loud. Key
verified claims: the scheme check is bidirectional with per-child replay;
the covering join cannot accept an un-emitted obligation and the decrease
is independently kernel-proven; the J8 registry/decode routes are gated
by kernel-decided no-shadow facts (a world-shadowed `TRUE-LISTP` makes
them hard-fail, not assume builtin semantics); the revert transform keeps
exactly the succeeded proof; branch-fact scoping is kernel-enforced.

**Findings and disposition:**

| # | Finding | Severity | Disposition |
|---|---------|----------|-------------|
| 1 | Commit verbs overstated the board (outside) | — | Corrected by this note |
| 2 | Decrease discharge = 3 hardwired fragments, the design's REJECTED per-shape tiers; design I4 specified the #37 admission-decrease prover | med | Follow-up (top of backlog): route through the #37 prover — also unblocks the 7 fragment rows |
| 3 | fmt margin is a threshold, not a guarantee; VERIFIED: the whole sorting corpus wraps at ~10k cols (qsort max line 9999), hyphen-split hazard live | med | Follow-up: capture-harness max-line assertion (+ consider `write-for-read`) |
| 4 | `typeSetDerived` is classification BY ELIMINATION (no positive marker in the log; linker bug and type-set verdict indistinguishable); stale doc claimed hard-fail | med | Doc corrected in this commit; follow-up: emit a positive type-set-verdict marker and consume it (the proper J6b) |
| 5 | `checkCoveringClause` silently mapped a non-list clause to `[]` (no-silent-skip violation, fail-closed in effect) | low | FIXED this commit (hard-fail) |
| 6 | Normal push without `:POOLNAME` silently unregistered | low | FIXED this commit (hard-fail, symmetric with abort path) |
| 7 | Rule-spec rune parse lost symbol-name strictness (J7 refactor) | low | FIXED this commit (parse-time hard-fail restored) |
| 8 | Spike headers falsely claimed live `sorry`s | low | FIXED this commit |
| 9 | `callBuiltin` keys on symbol NAME only, dropping package (pre-existing, inherited) | — | FILED as BUG-017 this commit |
| 10 | No corpus witness for a dotted STEP rune selecting its stored rule (only `(:RULES)` entries carry indices today) | info | Backlog: constructed sample when a multi-corollary rule fires in a captured proof |
| 11 | Covering check does not match emitted-clause guards to the case's ruling tests (soundness-safe — decrease independently proven) | low | Backlog note |
| 12 | Pool-shaped (clause-list) motive unimplemented (single-clause only) | low | Tracked in design (latent, hard-fails) |
| 13 | `gz-termination-clauses` recomputation-as-emission not differentially verified against original admissions | info | Backlog: differential check |
| 14 | ◌ headline undersells "19 of 36 DP leaves held as hypotheses" | info | Noted; ◌ semantics verified honest (obligation in the type, never smuggled into a REPLAYED row) |

Refuted in verification: the suspicion that
`(STRINGP (TO-BE-FOUND …))` is a reconstruction artifact —
`arithmetic-3/bind-free/normalize.lisp:128` legitimately reuses the
function name as its fourth formal (separate namespaces); the frontier is
genuine.

## Follow-up queue (order reflects the audit's weight)

1. Decrease discharge via the #37 admission-decrease prover (finding 2) —
   design conformance + likely unblocks the 7 decrease-fragment rows.
2. Positive type-set-verdict emission + consumption (finding 4, J6b).
3. Capture-harness line-length assertion (finding 3).
4. STRINGP DP-lift primitive (16 qsort/sorts-equivalent rows; genuine
   frontier per the refuted-artifact check).
5. Focused-run CLI + perf round 2 (TODO, MDD-requested).
6. Items 10, 11, 13 above as opportunities arise.
