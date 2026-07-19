# Expand-and-or clausify mirror — plan

STATUS: RATIFIED; S1–S3 LANDED (S3 green a62d5fd — every clausify-bridge
wall in the corpus fell). Update 2026-07-19: the HOW-MANY-{MERGE2,MSORT}
follow-on wall was NOT an abbrev-path off-by-one — it was two missing
hyp-relief recipes in `replayNodeWith` (NodeCore): (1) a negated hyp
`(NOT atm)` is relieved by ACL2's `relieve-hyp` on the ATM (no gstack
frame) — the recorded chain is atm-rooted, must land on `'nil`, and is
lifted through the `not` by unary congruence + exec-ground fold, the
`replayLiteralChain` recipe; (2) a `SYNP` (syntaxp) hyp is relieved
meta-level and recorded as `(:DEFINITION SYNP)` in the ttree — in the
logic `synp` ignores its args and returns `t` (its defun is in the gz
snapshot), so the discharge is the ground definitional evaluation,
gated on that rune being in the node's recorded runes. Both rows now
REPLAY ✓ (30/79). Branch `mdd/expand-and-or`.

Second increment (bc1a7ee + fork f3bd188c09): (1) a multi-literal
preprocess-clause PROVED with no children routes its clause-level chain
over the disjoined formula (the type-set-fc verdict leaf spans the full
clause) — TRUE-LISTP-{ISORT,MSORT} advance to their REAL frontiers
(type-alist derived entries; ◌-class assumed-fact discharge
composition — both known deep items, out of this arc's scope);
(2) `abbreviation-expansion` rewrite-rule steps (rules applied by
expand-abbreviations) are consumed by the with-lemma recipe: origin
accepted, hyp-freedom enforced (ACL2's `abbreviation` subclass), and
the fork now emits `:SUBST` on the push (corpus recaptured) —
LEN2-APP-{VIA-INDUCT,NO-HELPER} REPLAY ✓. Scoreboard 32/79
(24 unconditional + 8 conditional).

S4 status (2026-07-19): NO current consumer — the corpus's 6 lemma-arm
clausify-expand events (bsort CONS-EQUAL ×4, ordered-perms EQUAL-CONS,
qsort composite) all sit in rows that fail UPSTREAM on other frontiers
(non-identity-literal-alongside-clausify, STRINGP lift class). Per this
plan's own "as the corpus census demands" and the no-unwired-infra
rule, the lemma arm stays fail-closed (named frontier) until a row
actually demands it.
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
- S3 — IN PROGRESS. `clausifyChecked`/`clausifyCheckedStep` (fuel-
  indexed mutual, theory-side `CExp := SExpr × SExpr × Bool` triples,
  computable `cSize`/`clausifyFuel`) LANDED and compile. SOUNDNESS BY
  REDUCTION, not by mirroring the 300-line `clausifyPure_sound`:
  (a) `expandTerm fuel exps t pos : Option (SExpr × List CExp)` — splice
      each consumed expansion at its walk position, producing the fully
      expanded term t′;
  (b) correspondence (syntactic, fuel induction): a successful
      `clausifyChecked` run equals `clausifyPure t′ pos` with the same
      leftovers — REQUIRES side condition C1: no expansion's toTerm is
      `quoteT`/`quoteNil` (else a sibling guard could flip arm selection);
      C1 is validated at the DRIVER (hard-fail) and hypothesized in the
      lemma;
  (c) lift-preservation: `dpLiftF vars opq t′ = dpLiftF vars opq t` given
      the expansion lift-equalities (hexp);
  (d) transport: `ClausifyGoal w env t′ pos → ClausifyGoal w env t pos`
      from lift-equality (via dpLiftF_sound + val_unique /
      ne_nil_of_evtrue_conv);
  then `clausifyPure_sound` applies to t′ UNCHANGED. The driver-side
  hexp facts for the def-body arm are per-builtin value lemmas
  (Logic.not/endp/atom vs their if-form def-bodies — near-definitional),
  discharged from a small registry keyed by the FROM head.
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
