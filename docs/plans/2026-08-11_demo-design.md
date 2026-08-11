# The sorting demo — design (FOR RULING, charter item 4)

Goal (Mike, 2026-08-11): "someone can look at a particular area and
see exactly what they need to trust, and have the untrusted pieces
cleanly factored. Make this the nicest demo we can make it." The
buildout ball-of-mud is fine while building; this is the presentation
layer. Everything below is behavior-preserving (statements, axiom
sets, goldens, pins byte-identical); the demo build is GATED on this
design's ruling (charter mandatory-exit).

## (a) Trust-legible factoring — imports ARE the trust boundary

Split each per-book ball of mud (`Imported/Sorting.lean`, 4575 lines)
into a directory whose module layering IS the trust story, so "what
must I trust?" is answered by `import` lines, not by reading proofs:

```
Imported/Sorting/
  Sims.lean    — the Lean-idiomatic defs (isortL, msortL, qsortL, …),
                 the exec sims, the P2 termination measures.
                 IMPORTS: the semantic core + Lifting's encoders ONLY.
                 Nothing here knows replay exists. A visitor reads
                 THIS file to know what the theorems are about.
  Iso.lean     — the _exec_corr + _enc correspondence layer
                 (generated where the generators cover it).
                 IMPORTS: Sims + the eval lemmas.
  Decode.lean  — the *_native_of_replayed transports: the ONLY layer
                 that touches replayed statements.
  Debt.lean    — the FORBIDDEN-DEBT sorries, quarantined: one file =
                 the complete list of assumed facts, each with its
                 unlock. A visitor auditing "what is assumed?" reads
                 exactly this file (and `#print axioms` agrees).
```

Enforcement (simple, deterministic, in the existing gate style): a
`check-trust-imports` script — `Sims.lean` files must not import
`Replay.*`/`ProofLog`/driver modules; `Decode`/`Debt` are the only
mirror-layer files whose import closure may reach `driver_replayed%`
machinery. Runs in ci next to `check-file-weight` (which this split
also satisfies — every new module under the norm; the grandfathered
giant disappears from the baseline).

Perm/EquisortWitness/SimpleWorld/AppAssoc get the same split only
where they exceed the norm or the demo path touches them (Perm yes;
the two tiny books stay single-file with section markers).

## (b) The capstone showcase — one page, receipts on the page

New `ACL2Lean/Imported/Mirrors/Showcase.lean` — the demo's front
door, restating the headline sorting results FROM the catalog
constants (zero new proof content — it may only apply existing
natives) with the receipts inline:

1. A header docstring: the TRUST MAP in five lines —
   - TRUSTED: the Lean kernel; the semantic core (`SExpr`, `Logic`,
     `evalOpt`); the encoders (`enc`/`boolEnc`/`intRep`); the
     STATEMENTS on this page.
   - UNTRUSTED BUT KERNEL-CHECKED: all of ACL2, our instrumentation,
     the parser, the tree reconstruction, the replay driver — a bug
     anywhere there fails to typecheck; it cannot prove a false
     statement on this page.
   - VISIBLE DEBT: premises carried as `sorryAx`, enumerated in
     `Debt.lean`, each with its named unlock. Nothing else is
     assumed.
2. The headline natives, one `#guard_msgs`-pinned axiom receipt each,
   e.g.:
   - `orderedp_isort`: `isChain lexorderB (isortL xs)` — trio-clean.
   - `how_many_qsort`: `(qsortL xs).count e = xs.count e` — trio.
   - `perm_qsort`: `(qsortL xs).isPerm xs` — trio + sorryAx (debt
     named in the entry).
   - the sorts-equivalence capstones — presented HONESTLY as
     conditionals (the ASSUMED rows): stated with their named
     premises, marked "retires with the R-lane / TP-replay arcs".
3. A closing pointer: the full scoreboard is the catalog (113
   entries, five gates); the sweep is `just ci`'s golden.

## (c) The reader path

`docs/DEMO.md` (top-level, linked from the README): a four-stop tour —
1. `Showcase.lean` — what is proved, what you trust (5 minutes);
2. `Imported/Sorting/Sims.lean` — the objects of study, plain Lean;
3. `Imported/Mirrors/Catalog.lean` — the scoreboard + the gates that
   keep the trust story true (the seam/axiom/provenance/shape/usage
   gates each get one sentence);
4. (optional, downward) one worked replay: the proof log →
   `dump-proof-tree` → the driver → the replayed statement → the
   decode — the untrusted pipeline made concrete.

## Sequencing + cost

1. Showcase + DEMO.md first (pure addition, no restructure risk) —
   the demo exists after one increment.
2. The Sorting/ split second (mechanical moves, one file per commit,
   statements/axioms byte-identical, `check-trust-imports` lands with
   it).
3. Perm split third; the small books stay put.

Rulings sought: (R1) the four-layer split incl. Debt.lean
quarantine; (R2) the import-discipline script as a ci gate; (R3) the
Showcase restating capstones from catalog constants (zero new proof
content) with on-page axiom receipts incl. honest conditionals; (R4)
DEMO.md as the canonical reader path.

## RULED (Mike, 2026-08-11): APPROVED as a first pass — build it.
Sequencing as proposed (Showcase first). Ruled in the same round:
reuse-vs-mint ALLOWED capped to existing unlock classes (the bsort
four land as .nativeSorried on minted debt); the derive_sim% ELEMENT
reading APPROVED (PCE unlocks); the witness-free shape DECLINED as a
mirror — the principle is the TIGHTEST AVAILABLE Lean-idiomatic
mirror, with derived restatements as Showcase-level corollaries above
an honest mirror, never as the mirror itself.
