# Sorting-completion II — arc charter

**Status: RATIFIED (MDD conversation 2026-07-30 — "yes, that sounds great,
let's work that arc"). Branch `mdd/sorting-completion-2`, opened at main
a1c25c2 (post validator/lifter tranche 1).**

## Goal

Every SWEEP sorting row green + ORDEREDP-QSORT's `rule:ORDEREDP-APPEND`
condition discharged. Explicitly OUT of scope (the following arc, R6/R7
character — recon/statement-builder work): the bsort book's
clausify-region recon wall (p4-pinned), equisort's encapsulate
(BUG-019-refused, roadmap R6), functional instantiation (R7).

## The red inventory (from the golden at a1c25c2), classed by machinery

### Class A — the type-alist relief family (4 rows; FIRST — highest leverage)

- `ORDEREDP-APPEND` — rule LEXORDER-TRANSITIVE's marker-relieved hyp
  `(LEXORDER A3 (CAR A4))`, `:TA-RUNES ["LEXORDER"]`, no falsity fact in
  scope, no registered FC relief.
- `ORDEREDP-MEMB` — `type-alist: no spine falsity fact for E`.
- `ORDERED-PERMS` — needs `(PERM (CDR (CDR A)) (CDR (CDR A)))` truthy — a
  REFLEXIVITY fact on the type-alist (the equivalence-rule entry class).
- `TRUE-LISTP-MSORT` — `type-alist: no spine falsity fact for MT`.

Shared semantics (pinned by the perm-lane outside audit, F6):
`rewrite-clause-type-alist` = rewritten earlier literals + ORIGINAL later
literals + FORWARD-CHAINED conclusions (`select-forward-chained-concls…`,
acl2/simplify.lisp:5002). The later-literal half is covered by the
demand-hoist machinery (perm-lane inc-1); the FC-conclusion third is
unreachable by case-splitting — expected landing: EMITTED type-alist-entry
provenance (the fork already computes `:TA-RUNES`; emit the entry/its
derivation) + a bounded relief-registry extension (the LEXORDER-TOTAL
registry precedent, rule-of-three watched). Per the project rule: type
facts come from ACL2 — if insufficient, EMIT MORE, never re-derive.
Discharges ORDEREDP-QSORT's biggest kept condition as a side effect.

### Class D — HOW-MANY-QSORT (1 row; SECOND — self-contained named frontier)

`solidify: type-set-derived equivalence (EQUAL (CAR X) E) — not in the
clause context's equation closure; value-level type-set discharge not
implemented (J6)`.

### Class C — msort internals (3 rows; THIRD — three distinct record classes,
ground-truth read each before building)

- `ACL2-COUNT-EVENS-STRONG` — branch-substitution justifying literal
  `(not (equal (ACL2-COUNT (CDR X)) '0))` neither in clause nor segment.
- `ACL2-COUNT-EVENS-WEAK` — ran out of items with no closer at *1/2.2'
  (a silent close the taut arm does not cover).
- `ORDEREDP-MSORT` — literal 9 chain reached 'NIL, recorded result
  `(NOT (CONSP (MERGE2 MT0 (CONS MT3 MT4))))` (chain divergence —
  possibly an emission gap; suspect any stage).

### Class B — the sorts-equivalent walls (3 rows; FOURTH — likely 2 causes)

- `MSORT-IS-ISORT` + `QSORT-IS-ISORT` — one shared message (emitted
  `:PATH` misnavigates to `(HOW-MANY E (ISORT X))`; frames
  `[(1 . IF), (1 . EQUAL)]` land on X) — suspect one emission/alignment
  bug.
- `BSORT-IS-ISORT` — node lhs is a DIFFERENT theorem's formula
  (`(IMPLIES (TRUE-LISTP X) (TRUE-LISTP (ISORT X)))`) — the `:use`-hint
  class (apply-top-hints; `LEN2-APP-VIA-USE` recon-05 is the same
  family). A real feature gap, not a bug.

## Discipline

The standing rules apply: drive off the real artifact (dump the tree
before reasoning); emitted evidence over Lean-side reconstruction;
hard-fail at frontiers; each class lands with decorrelated validation
where it generalizes (pattern books through real ACL2 + capture);
byte-identical sweep outside the intended flips; small verifiable
increments, commit at checkpoints; pre-merge audit at the merge point.

Adjacent debt that may fold in if a class touches it (else stays queued):
the linear-in-simplify emission gap (p6's tripwire), the perm-lane
audit-disclosed items (taut-close commuted-IFF/double-neg/dedup arms,
branch-substitution condition/remove-flg/lit-position emission, the
:RULES cr-rune per-step emission).
