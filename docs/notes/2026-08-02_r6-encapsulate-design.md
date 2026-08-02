# R6 — encapsulate / equisort (DESIGN, for MDD ratification)

Drafted 2026-08-02 as the close-out arc's Phase 0. Grounded in the
real artifact (`acl2_samples/sorting/equisort.proof-log`) — read
before the design, it reshapes the problem favorably.

## Ground truth

- The fork ALREADY marks encapsulate-local defuns:
  `:SOURCE :LOCAL-WITNESS` (equisort log lines 103-111, 13134-13142 —
  SORTFN1/SORTFN2/SSORTFN1/SSORTFN2 and their inserts, with WITNESS
  bodies). The reader hard-fails on them (BUG-019 fail-closed) — that
  is the current wall, and it is a parse decision, not missing data.
- equisort's 41 defthms are all emitted WITH proof trees.
- The constrained names' emitted bodies are the WITNESSES (insertion
  sort); the exported theorems' recorded proofs are proofs ABOUT the
  witnesses — that is what ACL2 actually ran.
- The exported theorems' proofs are dominated by `:use` hints with
  TRIVIAL constraint clauses (`:CONSTRAINT-CL ('T)`, e.g. lines
  13124, 26149) — the plain-`:use` class (R7a), not functional
  instantiation. Much of equisort needs R7a + ordinary machinery, not
  R6.
- MISSING emission: the encapsulate BOUNDARY (which defuns/defthms
  belong to which encapsulate) and the per-signature CONSTRAINT list
  (which formulas constrain SORTFN1/SORTFN2 …). ACL2 stores exactly
  this (`constraint-lst` on the constrained fns) — the emission is a
  read-off of ACL2's own record, no new computation.

## The justificatory logic (validated against the source + logs)

ACL2's encapsulate, logically: (1) the theory is extended by the
non-local formulas mentioning the signature fns AS AXIOMS (the
`constraint-lst` — for equisort, the six property theorems); (2) the
witnesses are a META-LEVEL conservativity argument — pass 1 proves
the six about the witnesses, exhibiting a model, and the witnesses
are then DISCARDED from the logical world; (3) the strong/weak
theorems sit OUTSIDE the encapsulate (equisort.lisp:59,104) — they
are ORDINARY theorems of the constrained theory, proved by the
ordinary waterfall from the constraint axioms + include-book content
(`:use ORDERED-PERMS`), in a world where no witness content exists;
(4) functional instantiation is a derived rule whose obligations are
the instantiated constraints — exactly the six-conjunct
`:CONSTRAINT-CL` in the sorts-equivalent log.

## Design — JUSTIFIED THEORY EXTENSIONS (general machinery, MDD
direction 2026-08-02: "not a special case")

A development is a sequence of JUSTIFIED EXTENSIONS; a world is a
MODEL of one. One schema for every event form:

- defun: definitional axiom, justified by admission replay (the
  existing totality machinery — already this shape).
- encapsulate: constraint axioms over fresh symbols, justified by a
  MODEL EXISTING — the witness sub-development satisfies the
  constraints (pass 1, replayed kernel-checked).
- include-book: splices the included book's extensions.
- future kinds ride the same schema: defchoose (choice axiom,
  witness-model justification), defaxiom (UNJUSTIFIED — flagged
  loudly), partial-encapsulate.

Machinery consequences:

1. **Parser/Development**: scoped extensions become the primitive. An
   encapsulate is a CONSTRAINED SCOPE containing a witness
   sub-development (`:LOCAL-WITNESS` defuns — already marked) and its
   exported constraint theorems (`:ENCAPSULATE` boundary tags + the
   `:CONSTRAINTS` event, verbatim from ACL2's constraint-lst).
2. **`toWorld` = the canonical model**, uniformly: definitional
   scopes contribute bodies; constrained scopes contribute their
   WITNESS bodies (the witness IS the canonical model of the scope).
   The sweep replays at the canonical model — simultaneously pass 1
   (the constraint theorems' recorded trees) and the ordinary
   post-encapsulate proofs. Nothing encapsulate-specific in the
   replay path.
3. **One generic parametric statement builder** — "abstract over a
   scope": for any scope S and theorem Φ, emit
   `∀ w, ScopeHolds S w → ∀ env, EvTrue w env Φ`, with `ScopeHolds`
   generated uniformly (definitional scope → definition-pinning
   facts, the shape the hand world-parametric dischargers already
   use; constrained scope → the constraint EvTrues + arity facts).
   The R7-ratified `ConstraintsHold` is the constrained-scope
   instance, not a bespoke form. Existing concrete-world statements
   are RE-UNDERSTOOD as instantiations at the canonical model — no
   migration; the builder is invoked where a consumer needs
   abstraction (today: the post-encapsulate theorems R7b
   instantiates).
4. **Conservativity, object-level**: `ScopeHolds S witnessModel`
   proved by replaying the constraint theorems' recorded trees at the
   canonical model — ACL2's meta argument made kernel-checked. This
   is what makes the parametric statements non-vacuous.
5. **The post-encapsulate theorems' parametric replay is DIRECT**:
   their recorded proofs already live in the constrained theory
   (witnesses were gone), so replaying over abstract w replays
   exactly what ACL2 ran. A witness-dereference in such a tree is a
   sanity-check hard-fail, not an expected frontier. The constraint
   theorems themselves need no parametric form — they ARE
   ScopeHolds' components.
6. **R7b = the general "apply at another model" move**: instantiate
   the parametric statement at the concrete world via the ratified
   alias-world commutation lemma; obligations = the recorded
   constraint chains (already replaying).

### Emission (the fork delta — unchanged, small)

`(:CONSTRAINTS :FNS (…) :FORMULAS (…))` verbatim from constraint-lst
+ `:ENCAPSULATE <id>` boundary tags on the scope's events. Witness
marking already exists.

### Catalog doctrine for equisort (pre-ratifying)

- Re-proof rows: `.replayedOnly` pointing at the original book's
  mirror — no duplicate natives.
- Post-encapsulate constrained theorems: the parametric constant is
  the first-class artifact.
- Capstone native shapes (Phase 5): `msortL xs = isortL xs`,
  `qsortL xs = isortL xs`, bsort's trueListp-absorbed variant — each
  seam-gated through its replayed statement.

## Ratification questions

1. Approve the JUSTIFIED-EXTENSIONS design: scoped extensions as the
   Development primitive; `toWorld` = canonical model (witness bodies
   for constrained scopes, provenance-tagged); the sweep replays at
   the canonical model; ONE generic scope-abstraction statement
   builder (encapsulate = the constrained-scope instance, nothing
   special-cased)?
2. Approve the emission shape (`:CONSTRAINTS` verbatim from ACL2's
   constraint-lst + `:ENCAPSULATE` boundary tags)?
3. Approve the equisort catalog doctrine (re-proofs `.replayedOnly`
   pointing at originals; parametric constants as the post-
   encapsulate theorems' artifact; the three capstone native shapes)?
4. BUG-019 interaction: admitting `:LOCAL-WITNESS` defuns into the
   canonical model (provenance-tagged) resolves the equisort instance
   of BUG-019 — the tag + the scope structure replace the fail-closed
   parse wall. The general bug stays open for UNMARKED-witness
   scenarios. Confirm.
