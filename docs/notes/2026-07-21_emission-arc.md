# Emission arc: FC type-alist provenance + fertilize-clause (2026-07-21)

Branch `mdd/emission-arc` off main bc7f767. First phase of the agreed
post-qsort sequencing: BATCH both known emission gaps into ONE fork
rebuild + recapture cycle (fork changes serialize globally), then build
the two Lean consumers, then the CAR-APPEND investigation.

## Fork changes (one batch)

1. **emit/step FERTILIZE detail** (prove.lisp): `:FERTILIZE` gains
   `:LITERAL` (the justifying clause literal `(not (equiv lhs rhs))`),
   `:CROSS-FERT-FLG`, `:DELETE-LIT-FLG` — all already in
   fertilize-clause's ttree; previously only :BULLET/:TARGET/:EQUIV were
   serialized, leaving the substitution unlinked from its justification.
   Direction is NOT emitted: it is structurally determined (which side of
   :LITERAL's equality :BULLET is) — matching, not inference.
2. **emit/relieve-hyp/free-type-alist :TA-RUNES** (rewrite.lisp): when
   the instantiated hyp is literally a type-alist entry, the marker
   carries that entry's ttree runes. A DERIVED entry (forward-chaining,
   e.g. LEXORDER-TOTAL) is otherwise unreplayable — the fact is not any
   clause literal's falsity. Absent when no literal entry matches
   (fail-closed downstream unchanged).
3. **infra/gz-fc-rules + (:GROUND-ZERO-FC-RULES …)** (ld.lisp): the
   cited-closure snapshot now also emits FORWARD-CHAINING-class
   ground-zero rules as `(rune trigger hyps concls match-free)` entries
   in a SEPARATE event (the rewrite entries' 6-field shape is pinned by
   the D5 consumer). Book-level FC rules (none in this corpus) would
   need the per-defthm (:RULES) flush extended — deferred until a
   corpus row demands it.

## Planned Lean consumers

- **Fertilize recipe** (replayClauseWith): a FERTILIZE-CLAUSE step —
  byCases on the :LITERAL's value (truth closes the disjunction; falsity
  gives the equiv equality), substitute :TARGET → :BULLET per the
  recorded flags across the clause (diffCollapse transport, mirroring
  the branch-substitution machinery), recurse the child, handle
  :DELETE-LIT-FLG like the trivial-literal deletion. EQUAL-equiv only at
  first (IFF/PERM route through L2 later — fail-closed on non-EQUAL).
  Rows: HOW-MANY-ISORT, REV-APP.
- **FC-derived relief recipe** (NodeCore marker arm): when the
  marker-relieved hyp has no (not …)-falsity fact in scope but carries
  :TA-RUNES naming an FC rule, instantiate the rule's snapshot
  (unify a concl with the hyp — deterministic structural matching,
  ambiguity fails closed), check each instantiated rule hyp against
  in-scope falsity facts, and conclude via a new FC-rule hypothesis
  species in the telescope (mirror statement from the snapshot, like
  gz rewrite rules / D5). Rows: HOW-MANY-FILTER-1, ORDEREDP-ISORT,
  ORDEREDP-MSORT, TRUE-LISTP-MSORT(?), HOW-MANY-EVENS-AND-ODDS.

## Status

- Fork changes written, tag-check OK; image rebuild in flight.
