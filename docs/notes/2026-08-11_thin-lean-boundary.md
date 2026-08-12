# The thin-Lean boundary, restated (RULED — Mike, 2026-08-11)

TERMINOLOGY (2026-08-12): 'mirror'/'native mirror' below means the ACL2-like WAYPOINT layer, not a mirror in the product sense (ACL2Lean/Mirrors/). The layer's files moved in the 2026-08-12 naming sweep: `Imported/Mirrors/` → `Imported/Waypoints/`, `Imported/NativeMirrors.lean` → `Imported/WaypointCatalog.lean`.

Mike ratified the post-purge framing review's package in full
("Agree on all points", 2026-08-11). This note is the binding
restatement of the mirror-layer boundary and the adoption record for
the mechanization items. It supersedes the one-principle phrasing in
`docs/audits/2026-08-11_mirror-provenance-audit.md` (which remains the
purge's disposition record); the mirror-criterion memory points here.

## The three principles

The mirror layer's allowed Lean content rests on three DIFFERENT
justifications. Judgment calls are decided by the applicable principle
— never by analogy to whichever exception looks closest.

- **P1 — no capturable record.** ACL2 records only a verdict, so
  there is nothing to replay. Covers: gz/predefined rule content (the
  D5 carve-out, `Imported/GzPrelude.lean`), the ratified
  decision-procedure LEAF carve-out, and admission decrease verdicts.
  **D5 and the DP-leaf carve-out are THIS SAME principle at two
  layers** and share one drift metric (the carve-out drift test:
  per-case custom proofs/checkers = no longer mirroring). P1 is
  self-limiting: as instrumentation grows, it shrinks — an emission
  arc can always retire a P1 instance, and should.
- **P2 — Lean-metatheoretic necessity.** Lean's kernel demands its own
  termination artifact for a recursive definition to EXIST; no ACL2
  artifact can stand in. KNOWN, ACCEPTED consequence: P2 sometimes
  re-proves a theorem ACL2 also proved and we replay — e.g.
  `evensExec_consCount_le/lt` (Sorting.lean) vs the green
  `ACL2-COUNT-EVENS-WEAK/STRONG` rows (the MEASURE-ABSORBED doctrine,
  MDD 2026-08-02). This is a named exception, not drift. P2 covers
  ONLY what the definition's existence requires — never a theorem
  ABOUT the defined function beyond its admission.
- **P3 — untranslatable statement.** Isomorphism theorems
  (`fooExec (enc xs) = enc (fooL xs)` and the decode transport) are
  about Lean objects; ACL2 cannot state them, so there is nothing to
  replay. UNLIKE P1/P2, P3 has no intrinsic bound on proof difficulty
  — it is the drift channel — so P3 content is legal ONLY under the
  template gate below.

Everything else ACL2-derivable is forbidden in Lean: route it through
a replayed statement or carry it as visible FORBIDDEN-DEBT `sorry`.
The win states are unchanged (conditional replay with clear sorry iff
the hypothesis cannot be replayed yet; unconditional via replay
REQUIRED where it can).

## Adopted mechanization (all ruled 2026-08-11; sequencing binding)

1. **`derive_sim%` with TEMPLATE-FAILURE-AS-GATE** — MUST land before
   any accumulator-class book is imported (`14-accumulator`, zip2/3,
   interleave — the `.pending` backlog). The user supplies only the
   Lean-native def; the macro emits the exec, the `_exec_corr`, AND
   the `_enc` iso by the two observed templates (T1 aligned structural
   recursion; T2 measure change). **Template failure is a HARD ERROR,
   not a fall-back to hand proof**: it detects that the chosen native
   reading reassociates the recursion, i.e. the iso would smuggle
   content ACL2 proves. The legal escape is an ACL2 BOOK theorem for
   the bridging fact (e.g. `(equal (rev-acc x acc) (append (rev x)
   acc))`), routed through replay. Named hard frontiers: mutual
   recursion, non-`enc`/`boolEnc`/`intRep` readings, non-computable
   subjects. Follow-on in the same arc if cheap: the decode-assembly
   generator (all 36 decodes are a six-step fold over the `Formula`
   with the four enders already in `Lifting.lean`).
2. **The shape gate + the `hreplayed`-usage check** (closes the two
   probe-confirmed evasions). Every mirror-layer theorem must
   classify as SIM / ISO-corr / ISO-enc / DECODE / registered SUPPORT
   (an enumerated allowlist with one-line justifications, like
   `d5Allowed`); unclassifiable fails the build. Each DECODE proof
   must actually use its `hreplayed` binder. In-Lean `run_cmd` style,
   deterministic, no term-size heuristics.
3. **Delete `prepareUseFi`'s `totsNames` parameter**
   (`Replay/ParametricInstantiate.lean`) — behavior-preserving (sole
   call site passes `[]`); the replayed-admission channel (`termByFn`)
   becomes the only totality route, making the purge's drift class
   unrepresentable.
4. **Metric change.** The headline is the kept-condition census by
   class from the golden header (bucketed `total:`/`tp:`/`rule:`/
   `usefi:`/`dp:`), NOT unconditional-native count. WRITTEN INVARIANT:
   no constant defined in the mirror layer may be injected into the
   coverage sweep. Secondary tell: hand-written lines per catalog
   native (~145 at ruling time) — must fall as books land. `usefi:`
   joins the debt registry as the third unlock class.
5. **`.parametric` LiftStatus** for constraint-introduced subjects
   (`defchoose`, `defun-sk`, encapsulate signatures, metatheory/
   `defevaluator` books): the first-class artifact is the parametric
   constant with visible assumptions; a witness-level native is the
   banned masquerade (generalizes the R6 equisort doctrine). Land
   with the first such book.
6. **Audit cadence:** one adversarial provenance sweep (the
   two-classifier pattern) per BOOK FAMILY imported, at the family
   boundary — not per arc.
7. **F6 housekeeping:** bring `Mirrors/P8ClausifyDetail.lean`'s
   native under the catalog gates.

## Endgame-arc leftovers ratified in the same ruling

- **M1**: the 2e value-equality substitution design — RATIFIED as
  built.
- **M2**: fn-granular tau gating — ACKNOWLEDGED.
