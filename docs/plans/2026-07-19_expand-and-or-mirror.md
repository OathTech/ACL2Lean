# Expand-and-or clausify mirror — plan

STATUS: DRAFT, awaiting MDD ratification. Branch `mdd/expand-and-or`.
Source: the msort-frontiers close-out (the sole remaining wall for
TRUE-LISTP-MSORT, HOW-MANY-MERGE2, HOW-MANY-MSORT); 5 clausify-bridge
rows in the golden; the corpus-wide "(expand-and-or fired — replay
frontier)" annotation.

## The wall (real artifact)

`clausifyPure` (ClausifyBridge.lean) mirrors ONLY the pure fragment of
ACL2's `clausify-input1` — the if-splits, `dumb-negate-lit`, and the
checkpoint validation. When ACL2's `expand-and-or` fires inside
clausification (a definition/rewrite expansion chosen by the ens, under
GENEQV-IFF), the recompute diverges from the recorded checkpoints and the
bridge hard-fails: recomputed `(ENDP MT0)` vs recorded `(NOT (CONSP MT0))`.

The instrumentation ALREADY marks each firing (`emit/clausify/expand`,
induct.lisp:856): `(:CLAUSIFY-EXPAND :BOOL b :TO term)` — the
POST-expansion term and polarity, in clausify-input1's deterministic
depth-first order. Census: 3,185 events across the sorting corpus
(qsort 1,158, msort 607, bsort 303, …; even perm has 184 on paths its
replay does not traverse). Sample (the msort wall): `(ENDP X)` with
bool=T → `:TO (IF (CONSP X) 'NIL 'T)` — ENDP's non-recursive def-body,
which then clausifies purely into the recorded `(NOT (CONSP X))` shape.

## Design (consume, never recompute the ens choice)

**D1 — extend the event, don't infer.** `expand-and-or`'s three arms
(lambda-body beta when and-orp; non-recursive enabled def-body when
and-orp; `find-and-or-lemma` rewrite rules) are ens-ordered choices the
checker must NOT re-derive. Extend the emission with `:FROM` (the
pre-expansion term — in scope at the emit site) and the fired rune(s)
(from the ttree delta). The event becomes a complete instruction:
FROM ⇒ TO under bool, by rune.

**D2 — `clausifyChecked`.** A variant of `clausifyPure` threading the
clause record's ORDERED expansion list: at each recursion point, if the
head expansion's `:FROM` matches the current term (and bool matches),
step to `:TO` (recording the proof obligation) and continue; otherwise
recurse purely. Hard-fail on: expansions left unconsumed, a `:FROM`
matching nowhere, order violations. The recorded NEG/SPLIT/OUT
checkpoints remain the validated truth exactly as today.

**D3 — the proof bridge per expansion** (an SIff/eval-equality between
FROM and TO at the clause's truthiness level — the SIff kit exists):
- def-body arm (the msort class): the definition-unfold machinery —
  world/gz defuns via the defn lemmas, builtins via the D4 route.
- lambda arm: beta via the substitution lemmas (`evalOpt_substTerm_*`).
- and-or LEMMA arm: the cited rule's `rule:` hypothesis under IFF — the
  R-parameterized judgment (invariant L2); a non-equal/iff equivalence
  hard-fails.
Every arm keyed by the EMITTED rune — no arm selection by search.

**D4 — reconstruction attachment.** `ClauseTree` currently reduces the
expand events to a boolean "fired" flag (the frontier display). Attach
the ordered event list to the clausify record instead; the linker's
no-skip rule applies (an expansion event with no consuming record
hard-fails).

## Expected outcome

The 5 clausify-bridge rows unblock directly; the 3 msort rows flipping
would ALSO deliver the outstanding kernel-checked consumers for the #37
S4 sim-lemma registry and the generalize head-drop (closing both audits'
known-WIP items). Rows behind clausify walls elsewhere (perm's 184
untraversed events, qsort's 1,158) surface honestly as the replay reaches
them. Golden changes at each landing, reviewed per increment.

## Stages (each gate-checked: ci + reviewed golden + diff-test + zero
## warnings; commits at green increments)

- S1 — DONE (2026-07-19): fork emits `:FROM` + `:RUNES` (ttree delta;
  NOTE the delta dedupes runes already in the incoming ttree — 1,248 of
  2,237 censused events carry NIL runes for that reason; tolerable
  because the def-body bridge keys on the FROM head's unique world
  unfold with TO as the checked target). Parser hard-requires the new
  fields (stale logs fail closed). Corpus recaptured.
- S0 — census DONE: 2,229/2,237 events are the DEF-BODY arm on exactly
  three builtins — NOT (1,943), ENDP (280), ATOM (6); 8 are the and-or
  LEMMA arm (EQUAL-headed, CONS-EQUAL/EQUAL-CONS); NO lambda arm in the
  corpus. S3 covers 99.6%.
  DESIGN CONFIRMATION for S3: `clausifyPure_sound` is a PROVED theorem
  by functional induction over the dpLift value layer — so
  `clausifyChecked` extends the FUNCTION with the threaded expansion
  list and `clausifyChecked_sound` adds one hypothesis family (value-
  level FROM = TO per consumed expansion). For the def-body arm these
  facts are near-definitional (`Logic.not/endp/atom` are their ACL2
  def-bodies), discharged by a small per-builtin lemma registry.
- S2 — ClauseTree ordered attachment (D4).
- S3 — `clausifyChecked` + the def-body arm bridge (unlocks the ENDP
  class → the msort rows).
- S4 — lemma/lambda arms as the corpus census demands; anything else
  stays fail-closed with a named frontier.
- S5 — close-out: golden review, TODO sync, honest status of the S4/#37
  consumers.

## Risks

- The SIff-level composition through `clausifyChecked`'s recursion is the
  novel proof plumbing (the pure walk's bridge lemmas compose eval-equal
  steps; expansions inject iff steps mid-walk). If the existing SIff
  ladder does not compose cleanly at split boundaries, S3 may need a new
  bridge lemma family — surfaced early by driving the msort wall first.
- Event volume (3,185): attachment and checked-walk must stay linear;
  the WP1 focused loop keeps iteration cheap.
- `:FROM` emission must capture the term BEFORE `expand-and-or` (the call
  site binds it); rune extraction from the ttree delta needs care (tag
  `lemma` objects only).
