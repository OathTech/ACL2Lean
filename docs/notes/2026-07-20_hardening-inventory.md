# Pipeline-hardening inventory — agent-resilience sprint

Date: 2026-07-20. Framing (MDD-ratified): the system is built out by
NON-MALICIOUS BUT ERROR-PRONE agents. The infra should be deeply
redundant at catching errors of all kinds — so the buildout gets FASTER
and more autonomous, not slower. Don't over-engineer: guard the classes
we have actually hit, at the cheapest joint that catches them.

## Existing guard inventory (what already catches errors)

| Guard | Joint | Catches |
|---|---|---|
| `just ci` (lint-sh, check-bugs, check-no-shadow, check-acl2-tags, check-proof-logs, build, test, driver-coverage) | pre-push gate | build breaks, index rot, shadowing, tag drift, missing logs, golden drift |
| Golden reviewed-promotion (byte diff before `cp`) | coverage change | unintended row changes (WEAK: churn can mask flips — see G3) |
| `just diff-test` (389 match / 8 known-bug / 0 FAIL) | interpreter vs real ACL2 | evalOpt divergence; known bugs pinned so they can't rot |
| Runner: `Meta.check` + axiom collection per replayed theorem | proof admission | sorry/native_decide/extra axioms in replays |
| Native-axiom gate (build-failing) | Imported/ | axiom leakage into native facts |
| `#guard` registry invariants (dpLiftHeads↔dpUnary/dpBinary, d4DefFacts⊆dpUnary∧builtinNames) | compile time | registry desync between meta walkers and verified lift |
| TamperTests | test suite | statement tampering detection |
| Typed frontier errors (`throwFrontier`) + fail-closed parsers | runtime | malformed input mistaken for capability gap (and vice versa) |
| Audit protocol (adversarial reviewers before merge) | merge | reasoning errors, misdiagnoses, silent-weaker-proof class |
| TRACE-LOG tagging + round-trip check | fork | untracked fork drift vs upstream |

## Incident classes actually hit (2026-06..07) and their status

| # | Incident class | Example | Guard status |
|---|---|---|---|
| I1 | ACL2 image build failed but LOOKED green; recapture silently used the stale image | msort arc: make failed, notification read "exit 0" | **UNCHECKED** → G1 |
| I2 | Partial recapture: corpus recaptured but recon-tests/simple left stale | expand-and-or S1 | caught only by luck (parser hard-required new fields) → G2, G4 |
| I3 | No binding between a .proof-log and the image/submodule that produced it | any capture | **UNCHECKED** → G2 |
| I4 | Golden error-message churn masking a status flip | every big sweep review | manual eyeballing only → G3 |
| I5 | Silent-weaker-proof: helper proves a defeq-coincident but WRONG Prop | proveNotSpecial lowercase literals (audit N1) | caught by audit, not by tests → G5 |
| I6 | Specific-target `lake build` passing on stale oleans while full build broken | conspT ambiguity (expand-and-or S3) | `just ci` catches; agent loop discipline — doc'd in the sweep lesson; inherent to focused loops |
| I7 | Misdiagnosis-driven code (fix built for the wrong cause) | segment-variant (msort audit); "abbrev-path off-by-one" | audit protocol + drive-off-real-artifact doctrine; process, not infra |
| I8 | Editing-tool text corruption (substring replace hitting the wrong site) | clausifyPure_lifts case11 | re-read + build catches; process |
| I9 | Conditional replay's assumed obligations unsatisfiable → vacuous cond ✓ | none observed; structural risk | **UNCHECKED** → deferred (vacuity item, TODO.md) |

## Sprint scope — guards implemented (G1–G5)

- **G1 `build-acl2` success-marker check.** The recipe now hard-fails
  unless make output contains ACL2's "Initialization complete" success
  marker AND `saved_acl2` was actually refreshed (mtime). Kills I1.
- **G2 capture provenance stamps.** `capture-proof-log.sh` writes a
  sidecar `<log>.meta` (acl2 submodule SHA + image mtime + capture
  time); new `scripts/check-log-provenance.sh` (in `ci`, static)
  hard-fails if any corpus log's stamped SHA ≠ the current submodule
  HEAD, or a sidecar is missing. Kills I3 and makes I2 (partial
  recapture) detectable the moment the submodule moves.
- **G3 structural golden diff.** `scripts/golden-diff.sh` classifies
  golden→actual changes into STATUS FLIPS (REPLAYED↔FAIL, cond-set
  changes, header/DP-tally changes) vs MESSAGE-ONLY churn, so review
  reads the flips first; wired as `just golden-review`. Kills I4's
  masking risk.
- **G4 `just recapture-all`.** One target recapturing the WHOLE log
  surface (sorting corpus + recon-tests + simple), so agents cannot
  partially recapture by accident. With G2, a partial recapture is also
  detected. Kills I2.
- **G5 negative guard tests** for the special-form helper class
  (Tests/DriverTests.lean): `proveNotSpecial` must THROW on symbols
  named IF/QUOTE/LET/LET* and SUCCEED on ordinary heads — pinning the
  uppercase-invariant so the I5 class breaks tests, not just audits.

## Deferred (tracked in TODO.md's hardening item — design-flavored)

- Vacuity/premise-satisfiability: witness-evaluation smoke test per
  imported theorem; TamperTests premise-tamper extension (I9).
- In-log provenance (parser-visible header) if sidecars prove lossy.
- Check-joint enumeration for the remaining stages (translator,
  WorldGen) — the table above covers capture/replay/coverage joints.
