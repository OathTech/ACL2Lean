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
- **5** (6c6d636, fork 9a35048a13): the RUNOUT pass SOLVED — the fork fix
  is ONE WORD (`rewritten-body` joins rewrite-entry's inner-block bkptr
  kinds, rewrite.lisp), so the runout pass gets a proper BEGIN/END inner
  block and reconstruction adopts its children correctly; Lean side: the
  chain-root strip does NOT apply past a REWRITTEN-BODY boundary
  (Reflect.lean exemption) + per-level elim pinning. REV-REV,
  HOW-MANY-ISORT, ORDEREDP-RM ✓ (48→51/79).
- **6** (1c23189): the clausify-alongside class — a preprocess split
  whose same-clause-id simplify walk was merged into one node routes
  through the spine walker (arm a: in-node spine, single-out), plus a
  whole-clause discharge arm (b'). TLP-APP-NIL-TWICE, LEN2-CDR-SMALLER,
  LINEAR-CHAIN ✓ (51→54/79).
- **7**: the unicity-of-0 builtin class — `(BINARY-+ '0 (LEN v)) ⇒ (LEN v)`
  needs an int-shaped value for a BUILTIN app (LEN is not world-defined,
  so no tp: hypothesis and no pin). `builtinIntVal?` derives it LOCALLY
  at the two use sites (unicity recipe, acl2-numberp recognizer): gated
  on the development's EMITTED gz `:TYPE-PRESCRIPTION` corollary matching
  the registered nonneg-int shape exactly (drift hard-fails), value =
  structural `Logic.len` + kernel `logic_len_integerp` + choose-refined
  int atom. Deliberately NOT a `pinTermOpaques` arm: a shared pin makes
  every later `dpValExpr` of the term opaque and breaks structural
  consumers (first attempt failed exactly there — the `definition:LEN`
  unfold vs `gz_def_len`). LEN-INTERLEAVE, LEN-REV-ACC,
  NESTED-INDUCTION ✓ (54→57/79).

- **8+9** (one commit): three chain-walker faithfulness mechanisms, each
  ground-truthed in rewrite.lisp. (a) PASS-LOCAL strip tagging — strip
  entries carry the appending node's innermost consumed boundary kind
  (`innermostConsumedKind`) and apply only to same-block nodes; replaces
  the inc-5 blanket REWRITTEN-BODY exemption (which was too broad: it
  also skipped the runout pass's OWN root-collapse strips —
  HOW-MANY-EVENS-AND-ODDS advanced to its :TA-RUNES fork item). (b) the
  rewrite-if SWAPPED-P bridge (rewrite.lisp:17726-37): a negation-shaped
  rewritten test `(IF c 'NIL 'T)` makes ACL2 strip the negation and SWAP
  branches, unrecorded — `bridgeIfNegTestSwap` emits the normalization
  (`re_if_neg_test_swap`, incl. divergence case) deterministically when
  a frame descends into such an if OR the node sits ON it (recorded lhs
  == swapped, exact). (c) recognizer ATOM-from-CONSP-false branch fact
  (`logic_atom_of_consp_nil`) + the lenNat DP bridge
  (`logic_len_eq_lenNat`, the acl2Count pattern, tactic-local simp only)
  so len-linear-arith DP leaves close. LEN-ZIP2, LEN-ZIP3 ✓ (57→59/79;
  DP ✓24→✓29, ◌12→◌7). (d) EQUAL-COMMUTED stored-rule match: ACL2's
  one-way-unify1 tries both argument orders for EQUAL patterns — the
  rule-recipe matcher recompute-and-checks the commuted node lhs and
  prepends the `re_equal_comm` bridge (joint-strictness eval symmetry,
  no-shadow hypothesis). CAR-APPEND ✓ (59→60/79).

- **10**: ORDEREDP-MEMB layers — three mechanisms landed, row parked on
  a fourth. (a) the induction clean-up mirror: `remove-trivial-clauses`
  (induct.lisp:7047) / `trivial-clause-p` / `tautologyp` /
  `if-tautologyp` recomputed (`tautExpand` boot-strap bodies + `ifTaut`
  propositional check with EQUAL/IFF commutation) — LAZILY, only when
  the cheap complement layer leaves an excess vs the emitted :SCHEME
  (ifTaut is compiled code the heartbeat guard can't interrupt; eager
  runs blew up on large cross-product clauses — first attempt hung).
  A trivially-dropped clause's walk branch is discharged by the
  carve-out's closed-form check on the FULL dropped clause
  (`replayDischargeNode`) + the same literal peels as a linked child
  (shared via restructure). (b) `gz_def_not` + d4 entry (definition:NOT
  unfolds). (c) if-finish JOINT swap normalization
  (`normalizeSwapsToward` + shared `liftNegTestSwap`): a NOT unfold
  inside a test position makes ACL2 swap the enclosing if between the
  children and the recorded rhs. Row now parks at the
  TRIVIAL-EQUIV/BRANCH-SUBST class (`:BRANCH-SUBSTITUTION` E ↦ (CAR
  (CDR A)) from an equality literal's falsity + type-set solidify on
  the substituted var) — the long-known type-alist substitution class;
  BACKLOGGED (shares the wall with TRUE-LISTP-MSORT's bare-var fact).

## Emission refinement queue (next fork batch)

- :TA-RUNES misses NOT-wrapped hyps stored positively on the type-alist
  (assoc-equal on the instantiated hyp only): HOW-MANY-EVENS-AND-ODDS'
  DEFAULT-CDR marker has :TA-RUNES [] — extend the emitter to also try
  the stripped atom (and record polarity).

## Runout-pass investigation (RESOLVED in increment 5 — kept as evidence)

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
