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

## Increment log

- **1** (9e56ae6): fork emissions (submodule 5bef37550d) + parse layer.
  Two incidents caught by the gates: (a) the raw delete-lit-flg pool
  entry dragged the APPLY$ :?-measure clique into the cited closure and
  HARD-ERRORED the snapshot emitter — flags normalized to T/NIL, and the
  capture script's failure grep now matches "HARD ACL2 ERROR" (it
  post-dated every :QED and evaded all three detectors); (b) the fork
  commit must precede the FINAL recapture or provenance stamps go stale
  (re-ran the cycle in the right order).
- **2**: the FERTILIZE-CLAUSE recipe (Waterfall/Fertilize.lean) — EQUAL
  equiv + delete-lit T + cross-fert NIL (the induction shape; everything
  else fail-closed): byCases the justifying literal; truth closes via
  evtrueOfLitTrue; falsity gives the equality (logic_not_equal_nil_eq),
  the literal's if-frame folds out (castConvToNil + re_if_false lifted
  through preceding frames), diffCollapse transports target→bullet onto
  the RECORDED output clause (computed == recorded checked), the child
  closes it. REV-APP ✓ (47→48/79). CLI print arms for the new events.

- **3** (eb638e3): FC-derived type-alist relief — the marker arm consumes
  :TA-RUNES; LEXORDER-TOTAL registry entry (snapshot shape-pinned,
  concl-unified, source falsity from litFacts, closed by the
  kernel-proved ACL2.lexorder_total). Zero flips; four rows advanced
  past the FC wall.
- **4**: MULTI-RECORD elim rounds (Waterfall/Elim.lean rewritten) — a
  round's records nest as guard splits; ground-truthed reorder rule:
  applying a record ERASES the eliminated var's (not (consp v)) literal
  (first occurrence; absent for fresh vars), PREPENDS its σ-image, σ's
  the rest — the recompute validates every output clause (guards +
  final) against the emitted :NEWCLAUSES; composition = per-level
  byCases with guard-child peel (nil side), substN bridge + diffCollapse
  + front-peel (fuel_eq_symm) + positional re-insert (success side).
  Also: the marker arm accepts NOT-wrapped hyps whose ATOM's falsity is
  in scope (logic_not_t_of_nil — DEFAULT-CAR/CDR reliefs in guard-child
  walks); elim guard literal no longer required to be the clause head.
  ORDEREDP-RM + ORDEREDP-ISORT now funnel into the runout class;
  ORDEREDP-MSORT → a MERGE2 TP-hypothesis wall in its guard child.

## Emission refinement queue (next fork batch)

- :TA-RUNES misses NOT-wrapped hyps stored positively on the type-alist
  (assoc-equal on the instantiated hyp only): HOW-MANY-EVENS-AND-ODDS'
  DEFAULT-CDR marker has :TA-RUNES [] — extend the emitter to also try
  the stripped atom (and record polarity).

## Runout-pass investigation (parked evidence, next target)

HOW-MANY-ISORT (post-fertilize) + REV-REV now share one signature:
`navigated to (CONSP <tail>), expected redex (CONSP (CONS <hd> <tail>))`.
Ground truth gathered: ACL2's rewrite-fncall for RECURSIVE fns REWRITES
THE REWRITTEN BODY a second time (rewrite.lisp:20613, gstack frame
'rewritten-body); the raw log carries the runout nodes with
`(REWRITTEN-BODY . fn)` boundary path frames, but the BEGIN/END-INNER
block instrumentation emits only KIND BODY/RHS/HYP blocks — an
END BODY / BEGIN BODY adjacency appears where the runout pass starts, so
the block reconstruction mis-adopts the outer unfold's children under
the runout's inner node (the dump shows the outer fncall/recursive node
separated from its body-pass children). Likely fix: emit a
REWRITTEN-BODY-kind inner block around the runout pass (fork) and teach
the definition recipe to chain it as a continuation of the substituted
body (Lean); same class as the LEN-ZIP2/3 off-frame rows.
