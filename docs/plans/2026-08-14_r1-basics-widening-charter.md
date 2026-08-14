# R1 charter — Basics 6/6 + generator widening (2026-08-14)

Branch `mdd/r1-basics-widening` off main @ 631c282. Second arc of the
R-sequence (`docs/plans/2026-08-13_r-arcs-roadmap.md`); executes the
master plan's A4 prep. Governing findings: over-spec audit F1/F3
(persisted 2026-08-13); the fork audit's verdict that the three
remaining Basics rows are GREEN + UNCONDITIONAL (no emission work —
mirror-side decode only).

## Goal

1. **A — Basics 6/6.** The three remaining mirrors of
   `Mirrors/Basics.lean` — `app_nil`, `rev_app`, `rev_rev` — proved at
   `Int` via `mirror_iso%`/`mirror_transport%`, trio-clean receipts
   (`#print axioms` = {propext, Classical.choice, Quot.sound}; no
   sorryAx, no native_decide), THE LIST in `MirrorProofs/Basics.lean`
   updated. Blockers are decode-layer only: the REV exec/iso kit
   (the revAcc slice from the Basics close-out is the template) and
   APP-NIL's TRUE-LISTP hypothesis absorption (every `List Int` enc
   image is a true list — a machinery-side kernel-checked fact, the
   sanctioned route per the trust story).
2. **B — F1: `mirror_iso%` per-argument readings.** Port SimGen's
   raw/list reading table up one level (the audit's noted irony: the
   layer below already has it); the hom builder applies `e.enc` at
   element positions and `List.map e.enc` at list positions.
   **Demand anchor (anti-"infrastructure now, wire later"):** each
   widening lands in the same increment as a REAL square declaration
   read off `Mirrors/Sorting.lean` — the acceptance witnesses are the
   audit F1 rejects: `insertOrd` (element arg), `howMany` (element
   arg + Nat result), `filterRel` (function arg — may adjudicate to a
   named frontier if the reading table doesn't extend honestly; a
   frontier message stating the real bound is a legal outcome).
   These squares are R4's consumers; declaring them now IS the wiring.
3. **C (stretch) — F3: transport instance threading + the order
   bridge.** `mirror_transport%` threads typeclass instances through
   the crossing (today: none — sorting's `TotalOrder` transport is
   unreachable); plus the restriction lemma
   (`lexorderB` on int-atom encodings ↔ `Int.≤` — a concrete
   kernel-checked machinery-side lemma, R4's named bridge). Stretch:
   drop without ceremony if A+B consume the arc.

### B design scout (2026-08-14, read-only, pre-execution)

Verified shapes: `derive_sim%`'s reading table is USER-DECLARED syntax
(`(x : raw) (xs : list)`, SimGen.lean:176-247) — necessary there
because the waypoint layer is untyped SExpr. At the mirror level the
reading is INFERABLE from the spec's Lean binder types:
`mirrorFnShape` (IsoGen.lean:285-293) already walks the telescope and
collapses to an `allList` boolean; F1 = return a per-binder reading
vector instead (`.list` for `List α`, `.elem` for the embedded `α`,
hard-error with the observed binder type for anything else), and the
hom builder wraps `.elem` vars in `e.enc`, `.list` vars in
`List.map e.enc`. No new user syntax. `filterRel`'s `keep : α → Bool`
is outside this table by construction — expected outcome is a named
frontier stating the real bound (function-valued arguments), unless
the book side turns out to use fixed-predicate filters that adjudicate
it differently. `howMany`'s `Nat` RESULT is a result-class question
(hom-scalar already exists) — check whether the scalar class's codec
covers `Nat` or only `Int` before claiming the witness.

### C design scout (2026-08-14, read-only, pre-execution)

The restriction lemma is concrete and small:
`Worlds… lexorderB` is `lexorder · · == SExpr.t` over the trusted-core
`lexorder` (Lexorder.lean:91; two-valuedness already proved,
Imported/Sorting.lean:26); on `intEmbed.enc` images (integer atoms,
IsoGen.lean:106) `lexorder` reduces to the number-comparison arm, so
the statement is `∀ m n : Int, lexorderB (intEmbed.enc m)
(intEmbed.enc n) = decide (m ≤ n)` — machinery-side, kernel-checked,
no new definitions. Instance threading in `mirror_transport%` remains
the substantive part of C.

## Discipline

- Real-artifact first: read the replayed statements off the live rows
  (`dump-proof-tree` / the coverage modules), never off memory; the
  revAcc slice is the template for the REV kit.
- One increment = one mirror or one widening + its witness; fast-gate
  each (build of touched targets + focused checks + the statics the
  diff touches); full `just claim-gate` once at exit.
- Vocabulary practice binds (own-definition readings; the collision
  linter); golden must stay byte-identical (this arc is mirror-side —
  any row movement means something went wrong: STOP and diagnose).
- F1 is a generator change: the 15 retired hand-square byte-identity
  checks from the Basics close-out must keep passing (the regression
  net for exactly this edit).

## Escape hatch (mandatory early-exit)

Stop and report immediately if remaining work gates on: a user ruling
(e.g. an unforeseen reading-table design fork with product-layer
consequences), a fork round-trip, or a ratified design boundary; or if
an A-item turns out NOT to be decode-only (i.e. the fork audit's
green+unconditional verdict fails on contact — that contradicts a
persisted audit and must be reported, not worked around).

## Exit

A complete (6/6 trio-clean) + B landed with witnesses (or honestly
frontiered per-witness) + C explicitly landed-or-dropped; claim-gate
TRUE_EXIT=0; ARC LOG appended here; merge candidate presented for
sign-off.
