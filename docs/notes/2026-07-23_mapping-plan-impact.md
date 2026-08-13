# Mapping-arc outcomes — impact on the standing plans (2026-07-23)

The mapping arc (branch `mdd/mapping-arc`; the map:
`docs/notes/2026-07-22_pattern-map.md`, ci-gated by
`check-pattern-map`) changes the PLANNING picture in ways the standing
documents predate. This note is the delta — it layers on, and does not
rewrite, the ratified generality plan
(`docs/plans/2026-06-10_generality-design.md`).

## What changed

1. **The frontier's location moved.** Pre-mapping, all sequencing
   assumed the binding constraint was REPLAY support (recipes). The
   map shows the pipeline's generality gradient runs the other way:
   reconstruction handles ~90% of the situation frame while the
   CAPTURE layer is the narrowest — three event forms kill the
   instrumented session outright (defattach, top-level local, ratio/
   #c literals in defthms, plus both exotic rule classes), untagged
   prose leaks break parsing (the forcing round), and verify-guards
   runs whole proofs the log never sees. Session death is the worst
   failure mode: everything downstream silently doesn't exist.

   > **CORRECTION (2026-07-26, full-pipeline audit F10 — measured, not
   > estimated):** this premise is INVERTED by fresh-book data. After
   > the S1 capture hardening, 7/7 upstream books the map never
   > authored CAPTURE cleanly, while RECONSTRUCTION hard-fails on 4/7
   > (two named crash sites: `ProofTree.lean:339` "collectClausify:
   > expected split/out" and `:281` "unexpected clause-structure event
   > inside a literal"). The narrow layer is reconstruction. The
   > "~90% of the situation frame" figure was measured on the authored
   > pattern corpus, which by construction contains only known
   > families. Sequencing derived from this paragraph should be
   > re-weighed against the audit's measurement.
2. **LET/lambda is core-path-blocking and was in no plan.** Plain
   `let` — absent from every sample until the gap audit — hits the
   LAMBDA path-frame parse frontier immediately. Every realistic
   import target uses `let`. This silently gated the whole import
   roadmap and now must be treated as near-core work, not an exotic
   frontier.
3. **L2 is now data-backed.** The design invariant (R-parameterized
   judgment) has concrete requirements artifacts on disk: the
   defequiv/defcong OBLIGATION multi-bridge shape (6 theorems, 3
   books, one clausify class), a recorded `with-lemma` step under
   `:EQUIV SAME-LEN2`, the or-opt iff identity, and the wild
   ORDERED-PERMS/PERM-IMPLIES rows. The L2 design step can start from
   captured shapes instead of speculation.
4. **A standing direction: principled replay over reconstruction.**
   The driver fake-replay inventory (map §Driver inventory; 13
   mechanisms graded [bridge]/[rederive]/[mirror]) plus the MDD rules
   ("no silent normalization — un-instrumented emission sites";
   "pattern-mongering means we aren't logging enough") set the
   default for ALL future support work: prefer fork emission +
   recorded-step replay; retire bridges/rederivations as their
   emissions land (golden-verified); `:TYPESET`/`:TRUETS` decoding
   over re-derivation.

## Revised support sequencing (derives from the map's MDD triage)

Ranking rule: corpus-need > obvious-deficiency > ACL2-importance;
**missing features acceptable, baked-in bad design not** — inventory
kills outrank new features.

- **S1 — DONE (2026-08-13).** capture/emission hardening (one fork batch). The halt
  family (defattach, local, ratio/#c-in-defthm, the two exotic rule
  classes — likely one shared emitter defect), untagged-prose
  suppression (fixes the forcing-round parse), guard-obligation
  emission, backchain-limit field, plus the emission-arc queue
  (:TA-RUNES/DEFAULT-CDR threading, FC-contradiction discharge nodes,
  strip-branches conjunction split). One build+recapture cycle
  covers corpus rows AND the P2 pins.
- **S2 — DONE (2026-08-13).** LET/lambda. Parse-layer LAMBDA path frames + the
  dpValExpr/world lambda story. Gates every real-book import;
  elevated to near-core.
- **S3 — the L2 lane, designed from the captured artifacts.** MDD
  review first (design-parked); the map's P11 + the obligation
  multi-bridge class are the requirements list.
- **S4 — corpus singles per demand:** branch-substitution class,
  NFIX μ-measure, :use hints; registry one-liners (RATIONALP, FORCE,
  PICK) as they block replays.
- Deferred (unchanged): stobjs, defattach semantics, complex values
  beyond the reader pin, :program mode.

## What did NOT change

The governing plan's architecture and invariants (L1 judgment
interface, L2 abstract R, L3 world-parametricity) are VALIDATED, not
revised — the mapping's iff/user-equivalence artifacts are exactly
the situations L2 anticipated. The fidelity rules, the carve-out
(with its two MDD-ratified extensions), and the trust note stand.
Native lifts and differential families remain committed follow-ups,
deferred to support-side arcs and visible in the map.

## For the next agent

Consult the MAP before building support: if the thing you're about to
build re-derives something ACL2 could emit, it belongs in S1's
emission style, not in Lean. The map is ci-gated — if you change a
book, a log, or a pinned claim, `just check-pattern-map` must stay
green, and characterization changes belong in the map text itself.
