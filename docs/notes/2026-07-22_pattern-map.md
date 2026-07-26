# The pattern map — anchored circles over the ACL2 situation space

Created 2026-07-22 (mapping arc increment 1; the arc spec is the TODO.md
top block, MDD-ratified 2026-07-21). **Scope correction (MDD,
2026-07-22): the arc maps COVERAGE of ACL2's situation/proof space —
how to SUPPORT a construct is a secondary, downstream question, and
the map must never limit itself to what the replay can handle today.**
A book that fails at a named frontier, or does not even reconstruct,
is a SUCCESSFUL mapping outcome: it pins where the frontier is with a
real captured artifact. The replay scoreboard is recorded per book but
is NOT the arc's metric; situation-space coverage is.

## The coverage frame (top-down, from ACL2's own inventory)

Enumerated from ACL2's documented structure — NOT from what we have
built (the P1–P11 entries below were seeded bottom-up from conquered
mechanisms and are the survivor-biased half of the picture). Status
per item: `corpus` (wild anchor exists), `books` (pattern books
authored), `frontier-pinned` (book captured, observed failure
recorded), `UNCOVERED` (no artifact at all — the priority).

**Event forms:** defun `corpus`; mutual-recursion `corpus`
(recon-07); defthm `corpus`; include-book `corpus` (isort);
encapsulate/constrained-fns `frontier-pinned` (cov-encapsulate — REFUSED
at parse since the 2026-07-26 BUG-019 fix: the local witness's :DEFUN is
tagged :SOURCE :LOCAL-WITNESS and hard-fails — the pre-fix "reconstructs"
was the audit-F1 false green, a 2/2 replay ABOUT THE WITNESS);
defun-sk (quantifiers) `frontier-pinned` (cov-defun-sk — recon fails, -suff shape); defchoose `books` (cov-defchoose); defconst `books-partial` +
local `frontier-pinned` (cov-defconst-local — the top-level LOCAL
defthm logs with :SOURCE :LOCAL, then the session HALTS before the
next event; capture-layer pin);  defequiv/defcong `books` (cov-congruence — obligations reconstruct; consumption-side book queued); defattach `frontier-pinned`
(cov-defattach — CAPTURE halt at the event); verify-guards `frontier-pinned` (cov-verify-guards — the defun/TP
events emit but the GUARD OBLIGATION PROOF is entirely absent from
the log; an emission-coverage gap pinned).

**Rule classes:** :rewrite `corpus+books`; :definition `corpus`;
:type-prescription `corpus`; :elim `corpus`; :forward-chaining
`corpus`; :compound-recognizer `corpus` (CD2-BOUND);
:induction `corpus` (12-multi-controller); :linear `books` (cov-linear); :congruence `books`;
:equivalence `books`; :refinement `books` (cov-refinement); :meta `frontier-pinned`
(cov-meta-rule — REFUSED at parse since the BUG-019 fix: defevaluator's
MEV witnesses are :SOURCE :LOCAL-WITNESS; the S2-era 3/16 replays were
audit-F1 false greens over the witness world); :clause-processor
`frontier-pinned` (cov-clause-processor — same, CPEV witnesses; was
4/16); :built-in-clause `books` (cov-built-in-clause);
:tau-system `corpus` (discharge leaves only); :generalize-rule `books` (cov-generalize-rule); :well-founded-relation
`books` (cov-wf-relation — the defun event emits :WFREL MY-LT with
termination clauses in the custom relation).

**Waterfall processors:** preprocess `corpus`; simplify `corpus`;
settled-down `corpus`; fertilize `corpus`; generalize `corpus`
(msort); eliminate-destructors `corpus`; eliminate-irrelevance
`corpus` (thin — one wild row class); push/induct `corpus`; apply-top-hints-clause `books` (cov-by-hint —
a processor MISSING from this frame until the book surfaced it; :by
discharges through it as a PROVED step with no rewrites).

**Rewriter situations:** geneqv equal `corpus+books`; geneqv iff
`frontier-pinned` (p1-or-opt-probe); user geneqv `books` (cov-cong-consume — a with-lemma step recorded
with :EQUIV SAME-LEN2, the L2 lane's core artifact);
free-var hyp relief `corpus`; FORCING / case-split `frontier-pinned` (cov-force-round — the ROUND
captured incl. (:QED :FORCED 1); untagged prose leaks into the log —
a fork SUPPRESS gap, per the 2026-07-23 audit correction);
backchain limits `books` (cov-backchain-limit — EMISSION pin: stored
rules carry no limit field); syntaxp/bind-free `corpus`
(SYNP relief); rewrite-cache effects `books`
(cov-rewrite-cache — ONE recorded unfold for TWO occurrences);
linear-pot integration `books` (cov-linear-pot —
(:FAKE-RUNE-FOR-LINEAR NIL) captured).

**Hints:** :use `corpus` (LEN2-APP-VIA-USE, recon-05, frontier);
:induct `corpus` (recon-05?); :expand `books` (cov-expand-hint); :cases `books` (cov-cases-hint); :by `books` (cov-by-hint); :in-theory `corpus` (implicit);
computed hints `books` (cov-computed-hint).

**Value/interpreter surface:** integers `corpus`; rationals
`frontier-pinned` (NUMERATOR rows, design-parked); complex numbers `frontier-pinned` (cov-complex — CAPTURE-layer halt); characters/strings `corpus` (STRINGP lift); symbols/
packages `corpus` (BUG-002 family); guard-vs-logic-mode distinctions
`books` (cov-guard-logic — guards leave no proof-surface trace).

Priority for book authoring: the `UNCOVERED` items above, breadth
first — one minimal book each, captured through real ACL2, observed
behavior catalogued here (capture / parse / reconstruct / replay
frontier), REGARDLESS of support status. **This branch does NOT wire
books into the replay sweep, add pipeline code, or build support of
any kind — coverage only.** Sweep wiring, emission fixes, recipes,
and native lifts are all support-side follow-ups sequenced AFTER the
map is good.

## Frontier tier (captured; observed behavior catalogued)

Breadth batch 1 (2026-07-22, `cov-*.lisp` — 9 books authored, all
through real ACL2):

- `cov-complex` — **CAPTURE-layer halt**: ACL2/instrumentation stops
  at the first event (log = banner + `(:BEGIN-PROOF-LOG)` only; the
  capture integrity net flagged INCOMPLETE). The complex-number value
  surface's frontier starts at the fork's emitters, before parse or
  replay. Pins: instrumentation cannot yet log a book containing `#c`
  literals.
- `cov-defun-sk` — captures (1 QED) but **RECONSTRUCTION fails**:
  `theorem 'EXISTS-DOUBLE-SUFF' has no closing (:QED) before included
  theorem 'EXISTS-DOUBLE-SUFF'` — defun-sk's generated `-suff` rule is
  admitted without the standard proof-log shape. Pins the defun-sk
  event structure.
- `cov-encapsulate` — REFUSED at reconstruction (BUG-019 fix,
  2026-07-26): the encapsulate's local witness `(:DEFUN CF … :SOURCE
  :LOCAL-WITNESS)` hard-fails the parse with the statement-substitution
  explanation. Pre-fix state (the audit-F1 false green): the witness
  entered the World unconditionally and BOTH theorems replayed 2/2
  about `λx. 0` — with the same world validating `(EQUAL (CF X) '0)`,
  which real ACL2 explicitly refuses. sig-pinned on the witness tag.
- `cov-congruence` — RECONSTRUCTS, including the defequiv-generated
  equivalence obligation and the defcong congruence theorem as
  ordinary defthms. The rule-class CONSUMPTION side (rewriting under
  the user equivalence) is not exercised by this book — follow-up
  book needed where a later theorem rewrites UNDER `same-len`.
- `cov-defchoose`, `cov-linear`, `cov-cases-hint`, `cov-expand-hint`
  — all RECONSTRUCT; observed tree shapes catalogued by capture.
- `cov-force` — reconstructs, but NO forcing round fired (the forced
  hyp relieved immediately by type-set in both theorems). The
  forcing-ROUND proof structure is still unpinned — stronger probe
  queued (a forced hyp not relievable at use time, e.g. via a
  constrained function).

Breadth batch 2 (2026-07-22, 11 more books):

- `cov-meta-rule`, `cov-clause-processor` — **PARSE frontier**: both
  defevaluator-based books (16 generated internal theorems each, all
  captured, 7k-line logs) fail parse on `:PATH frame fn not a symbol
  (lambda/quote unsupported)` — the generated evaluator proofs rewrite
  inside LAMBDA applications and the path frames carry the LAMBDA
  term. Pins the lambda-path event shape (parse-layer sibling of the
  known dpValExpr LAMBDA frontier).
- `cov-cong-consume` — the L2 core artifact: a with-lemma step
  recorded `:EQUIV SAME-LEN2` (a rewrite under a USER equivalence
  inside a defcong-blessed argument position), plus the `(:RULES …)`
  storage of a SAME-LEN2-equiv rule. **Behavioral pin from the first
  version**: a HYP-FREE user-equivalence rule loops ACL2's
  PREPROCESSOR (call-depth hard error) — preprocess classes it
  "simple"/abbreviation and IGNORES loop-stoppers; the syntaxp guard
  routes it through the full rewriter.
- `cov-defconst-local` — **CAPTURE-layer pin**: the top-level LOCAL
  defthm runs and logs (`:SOURCE :LOCAL`), then the ACL2 session
  halts before the next event (k-fixed never starts). defconst itself
  substitutes fine at translate (the formula shows `(+ 42 0)`).
- `cov-verify-guards` — the defun/TP events emit but the GUARD
  OBLIGATION PROOF is entirely absent from the log — verify-guards
  runs a real proof our instrumentation does not see. Emission-
  coverage pin.
- `cov-by-hint` — `:by` discharges through APPLY-TOP-HINTS-CLAUSE
  (`:RESULT :PROVED`, no rewrites) — a waterfall processor missing
  from this frame until the book surfaced it.
- `cov-wf-relation` — custom well-founded relation flows through
  admission emission: `:WFREL MY-LT`, termination clauses stated in
  MY-LT. Reconstructs.
- `cov-refinement`, `cov-built-in-clause`, `cov-generalize-rule`,
  `cov-computed-hint` — all reconstruct; shapes catalogued.

Breadth batch 3 (2026-07-22, 5 books):

- `cov-force-round` — **the forcing ROUND captured for the first
  time** (iteration 2; iteration 1 was defeated by the rule fn's own
  :TYPE-PRESCRIPTION closing the goal by type-set — probe finding).
  A forced hyp needing INDUCTION → unrelievable at use time → round:
  3 QEDs for 2 defthms, clause-ids `[1]Goal`, `[1]Subgoal *1/1`,
  `[1]Subgoal *1/2`, and a structured `(:QED :FORCED 1)`. **Frontier
  pinned — CORRECTED by the gap audit (2026-07-23)**: the parse error
  `Unknown proof log event: MODULO` is NOT new round vocabulary — it
  is ACL2's untagged English prose ("Modulo the following forced
  goal…") LEAKING into the log, a fork suppress/emit gap. The fix is
  a suppression patch, not a parser extension.
- `cov-backchain-limit` — reconstructs; **EMISSION pin**: the stored
  (:RULES …) entry `((:REWRITE BFN-RULE) ((INTEGERP X)) EQUAL (BFN X)
  '0)` carries NO backchain-limit field — limits are invisible to the
  replay.
- `cov-trivial-drop` — probe MISSED (proved without induction; and the
  flattened clause shape would land in the add-literal complement-fold
  (i)-class anyway — the (ii) :SCHEME-DROPPED route needs the
  *1-REVERT structure keeping the IMPLIES literal whole). ORDEREDP-
  MEMB remains the wild anchor; a revert-shaped retry is queued.
- `cov-equal-nil-norm` — reconstructs; records the (EQUAL X 'NIL) vs
  (IF X 'NIL 'T) orientations for inventory entry 1.
- `cov-typeset-decode` — reconstructs; three distinct `:TYPESET`
  values captured (3072, 40, 6) — the decode probes for inventory
  entry 6.

Breadth batch 4 (2026-07-22, 6 books + 2 iterations — the frame's
last UNCOVERED items):

- `cov-trivial-drop2` — **the (ii)-class :SCHEME-DROPPED reproduced
  STANDALONE** (iteration 2, via the *1-revert route keeping the
  IMPLIES literal whole): the emitted record carries exactly the
  merged-base-case tautology clause. Quirk-backlog item closed;
  reconstructs (2.9k-line inductive proof).
- `cov-rewrite-cache` — **cache semantics pinned** (iteration 2;
  iteration 1 was closed by the constant fn's own TP): a subterm
  occurring TWICE gets ONE recorded unfold — the cache suppresses the
  second occurrence's steps. Load-bearing for any future replay of
  repeated redexes.
- `cov-linear-pot` — **`(:FAKE-RUNE-FOR-LINEAR NIL)` captured**
  (iteration 2; iteration 1 was swallowed whole by
  (:EXECUTABLE-COUNTERPART TAU-SYSTEM)): the pot list's contribution
  is visible — another verdict-only source the carve-out family will
  meet. Reconstructs.
- `cov-defattach` — **CAPTURE-layer halt**: the encapsulate theorem +
  its gz snapshot emit, then the session dies at the defattach event
  (the following theorem never logs). Same halt family as top-level
  LOCAL.
  UPDATE 2026-07-26: the book now captures further but REFUSES at parse
  (its locals tag :SOURCE :LOCAL-WITNESS — BUG-019 fix); either way
  fail-closed, as the audit's blast-radius note recorded.
- `cov-complex-defun` — completes the `#c` boundary at THREE layers:
  defthm-with-#c halts CAPTURE (cov-complex); a defun BODY with #c
  captures and emits fine (`:BODY (BINARY-+ X '#C(0 1))`); and OUR
  PARSER then fails closed (`unrecognized reader macro: #C`).
- `cov-guard-logic` — reconstructs; pins that guards leave no trace
  in the proof surface (logic-mode car nil = nil, no guard events).

**Probe-craft rule (earned three times over):** before authoring,
check what TYPE-SET/TAU/the fn's own :TYPE-PRESCRIPTION can conclude
about the probe's functions — degenerate (constant/boolean-obvious)
values get the goal closed without ever exercising the target
machinery (force-round v1, rewrite-cache v1, linear-pot v1).

Breadth batch 5 (2026-07-23, the GAP-AUDIT batch — 11 books from the
Opus auditor's ranked findings; audit corrections applied):

- `cov-let-lambda` — **A1 confirmed, the map's biggest blind spot**:
  plain `let` (the commonest binding construct, ZERO prior usage in
  any sample) reproduces the LAMBDA-frame parse frontier standalone:
  `:PATH frame fn … (LAMBDA (Y) (BINARY-* Y Y))`. `cov-mv-let` pins
  the MV encoding the same way (`(LAMBDA (MV) (CONS (MV-NTH …)`).
- `cov-or-hint` — **NEW parse pin**: the `:or` hint's log trips
  `single-colon or malformed package marker unsupported` — a token
  shape no other book produces.
- `cov-number-literals` — **capture-halt family extended**: a negative
  ratio literal (`-1/2`) in a defthm halts the session at the first
  event, exactly like `#c`. `cov-quoted-constant-rule` and
  `cov-type-set-inverter` — both exotic rule classes halt the session
  at their admission (frame rows now complete for all 19 rule-class
  tokens, two as halt-pins).
- `cov-do-not-hints`, `cov-nonlinear`, `cov-elim-irrelevance`,
  `cov-induct-hint`, `cov-deftheory` — all reconstruct (dedicated
  books for the auditor's B items).
- Audit disposition: C1 corrected above (untagged PROSE leak, not
  round vocabulary); D-sorting resolved (sources ARE tracked — in the
  acl2 submodule, per books.txt — invisible to the repo-only check).

## The REPLAY dimension (2026-07-23, MDD)

Coverage now records how DEEP the pipeline reaches per book — the
focused replay CLI run over every reconstructing pattern book
(observation only; nothing wired into the sweep). Result: **26
pattern theorems REPLAY end-to-end kernel-checked; 23 fail at NAMED
frontiers**, clustering into ~7 classes:

1. `clausify multi-bridge: splits/out/proofs mismatch` — ALL six
   defequiv/defrefinement/defcong OBLIGATION theorems (three books,
   one frontier class: the boolean-equivalence obligation's multi-way
   split shape).
2. `preprocess chain with child clauses at Goal` — the :use-hint
   class (known) + user-equiv rule admissions.
3. DP leaf tactic FAILED — nonlinear arithmetic; bare boolean-var
   shapes (z1-decides).
4. Registry one-liners — RATIONALP (two-valued recognizers), FORCE
   (DP-lift), PICK/defchoose (builtin registry).
5. `no literal or step items in clause Goal` — the :cases/:or
   apply-top-hints Goal shape.
6. branch-substitution — `cov-trivial-drop2` reproduces ORDEREDP-
   MEMB's ENTIRE journey to the same wall (the minimal book's full
   validation).
7. if-finish mismatches — the or-opt iff identity (P11) and forced
   contexts.

## Prioritization (MDD, 2026-07-23 — do not eat the whale)

Ranking rule: (1) what the TARGET CORPUS needs, (2) what is OBVIOUSLY
deficient, (3) what matters to ACL2 broadly. **Missing features are
acceptable; baked-in bad design is not** — where a new feature and a
fake-replay-inventory kill conflict, the kill wins.

- P1 (corpus-needed): branch-substitution class; the fork-batch
  emissions (:TA-RUNES threading, FC-contradiction discharge,
  conjunction split, untagged-prose suppression); NFIX μ-measure;
  :use hints.
- P2 (obviously deficient): ~~LET/lambda path frames~~ (LANDED S2,
  2026-07-24 — see the S2 section); the CAPTURE-HALT family (defattach,
  local, ratio literals, #c, the two exotic rule classes — session
  death is the worst failure mode); guard proofs unlogged.
- P3 (ACL2-important): L2/user-equivalence lane (obligation
  multi-bridge + :EQUIV consumption — also corpus-adjacent via
  ORDERED-PERMS); forcing rounds; defun-sk; nonlinear; meta rules.
- Deliberately deferred: stobjs, defattach semantics, complex
  numbers beyond the reader pin, :program mode.

## S1 correction — the "capture-halt family" dissolved (2026-07-23)

S1's first diagnosis (unsuppressed reruns): **every "capture halt" was
an ordinary ACL2 event failure** — illegal ground rewrite rules
(cov-complex, cov-number-literals, cov-defconst-local's K-FIXED),
unverified-guard defattach, malformed exotic-rule forms — rendered
invisible because :structured mode inhibits the error channel. The
fork now emits `(:EVENT-FAILED :CTX …)` at print-failure (fork
6f44ace078), so a failed event is self-describing; and the
forcing-round prose is replaced by `(:FORCING-ROUND :ROUND r :GOALS n
:ASSUMPTIONS n0)`. The books were corrected (`:rule-classes nil` on
ground facts; guard-verified defattach; correct exotic-rule forms —
`:TYPE-SET 3` is {0,1} in this encoding, predicate on the left) and
all six surfaces now CAPTURE fully:
- radix/ratio literals RECONSTRUCT (ACL2 prints them in normal form);
- local + defconst RECONSTRUCT; defattach RECONSTRUCTS;
- both exotic rule classes RECONSTRUCT (all 19 rule-class tokens now
  genuinely captured);
- #c narrows to exactly OUR `#C` reader macro (parse);
- the forcing round is a NAMED parse frontier (its structured event)
  instead of a prose crash.
The mischaracterized pins below (batches 1/4/5 "halt" entries) are
retained as written for the probe-history record — THIS section is
authoritative.

## S1.2 — three emission pins LANDED (2026-07-23, fork 8d1cf3dbef)

- **verify-guards wrapper**: `(:VERIFY-GUARDS :NAMES … :CLAUSES …)`
  wraps the guard-obligation waterfall (its steps were ORPHANS; the
  gplus-trivial case emits nothing, as before). Book iterated to a
  REAL obligation (gsum). Replay = named parse frontier until guard
  support lands.
- **backchain-limit field**: capture-time `(:RULES …)` entries carry
  the stored backchain-limit-lst as a 6th element, parsed into
  `RuleSpec.backchainLimit` (gz snapshots: tracked follow-up).
- **conjunction split**: `(:CLAUSIFY-CONJUNCTION :LEFT p :RIGHT q)` at
  strip-branches' and-shape (the ORDEREDP-ISORT pin). Parsed;
  flattened out of the decision stream (documented — reproduces the
  pre-marker trace exactly, zero corpus drift); the spine consumer
  that READS it is the tracked follow-up (P8). Build note: the
  raw-code coverage check required registering strip-branches in
  *initial-program-fns-with-raw-code*.
- Also: the S1.1/S1.2 events (:EVENT-FAILED, :FORCING-ROUND,
  :VERIFY-GUARDS, :CLAUSIFY-CONJUNCTION) all have fail-closed parser
  arms; the corpus sweep is golden byte-identical across the whole
  cycle.

## S2 — LET/lambda: the REWRITE-FNCALL beta path LANDED (2026-07-24, fork
b48faff962; audit-corrected 2026-07-25 — see the four-site table below)

The map's biggest blind spot (A1) is closed FOR THE REWRITER'S MAIN BETA
PATH. `let`/`mv-let` translate to `((LAMBDA (formals) body) actuals)`, so
this was core-path-blocking: any book binding a local hit it. ACL2
beta-reduces lambdas at FOUR sites; the 2026-07-25 3-Opus audit established
the true coverage:

| site | status (fork batch 2026-07-25) |
|---|---|
| `rewrite-fncall` lambda branch (`rewrite.lisp` ~20397) | EMITTED (S2) — `cov-let-lambda` replays through it |
| `rewrite` all-quoteps fast path (~17337) | EMITTED — origin `REWRITE/LAMBDA-BODY-QUOTED`, adopts the block; pin `p2-beta-quoted-actuals` |
| preprocess `expand-abbreviations` — FOUR arms: all-quoted actuals (`induct.lisp` ~314), abbreviation body, open-expanded-abbreviation body, lambda-survives | first three EMIT entry-style (origin `EXPAND-ABBREVIATIONS/LAMBDA-BODY`, rhs = the PLAIN substitution — `structured-sublis-var-plain`; `sublis-var`'s cons-term const-folding jumped ahead of the recorded steps — further expansion as own steps); `:equiv` is ALWAYS `equal` (re-audit F1: an entry-style beta IS the substitution, an EQUAL fact regardless of the ambient geneqv — the context label under-claimed pure betas as IFF and cost coverage; pin `p2-beta-iff-context`, which REPLAYS); the HIDE arm emits `(:hide-normalize nil)` when sublis-var folds inside a hide (re-audit F2; pin `p2-beta-hide`); the survives arm is a DOCUMENTED no-emit (byte-identity audit-verified against `mcons-term`/`cons-term1`); the OPEN body expansion pushes a `(lambda-body . fn)` boundary frame (SYMBOL anchor, nested case included — and the gstack twin got the same anchor fix, re-audit F3); arm B (open-expanded-abbreviation) is UNEXERCISED — `abbreviationp` with `lambda-flg nil` sends lambda-headed bodies to arm A (audit could not construct a reaching book); pins `p2-beta-preprocess` (REPLAYS 2/2, DriverTests-gated with `p2-beta-iff-context`) |
| `:expand … :lambdas` (`rewrite-with-lemmas` lambda arm ~20860) | EMITTED — origin `EXPAND-HINT/LAMBDA-BODY` (rune/hyp nil by the arm's own assert$); pin `p2-beta-expand-hint`. NOTE: the named-fn `fncall/expand-permission` site keeps its pre-existing `:rune rune` (nil for plain :expand hints — unexercised, out of scope) |

The `:EQUIV` fix (ratified option B + re-audit amendment 2026-07-26,
`structured-geneqv-equiv`): nil → EQUAL; a SINGLETON → its record's
`:equiv` symbol (ACL2's congruence essay: "the relation denoted by {e1} is
e1" — the earlier structural check against `*geneqv-iff*` missed
world-sourced singleton iff geneqvs with real :CONGRUENCE runes, the
cov-defchoose `(IFF)` catch); a MULTI-element geneqv → the verbatim
equiv-name list, parsed CANONICALLY to a compound string that every equiv
reader treats as an unknown relation (node-granularity fail-closed; a
parser reject had book granularity). Applied to the EXIT-style beta sites
(1/2/4) AND the three `fncall/*` keep-arm twins + `fncall/expand-permission`
(their rhs is the REWRITTEN body under the ambient geneqv; the hardcoded
'equal was the audit's false-claim defect). STANDING POLICY (re-audit
verified sound, exhaustive trace): at COMPOSITE nodes
(`definition`/`lambda-body`) the replay knowingly proves EQUALITY where
ACL2 claimed only the geneqv relation — the equiv label never enters any
proof or assumed statement; the recipes compose the recorded child chain
and hard-check the recorded rhs, and every assumed hypothesis
(`total:`/`tp:`/`rule:`) is built from separate events behind independent
equal-only gates. Non-composite steps under non-equal equivs gate by name
(the S3 lane's frontier). The audit's
three probes are PROMOTED to pinned books (S2b increment 1, 2026-07-25 —
captured from the committed fork, pins reproduce the findings from clean
state):
- `p2-beta-quoted-actuals` — reaches site 2 (the actual `(k a)` becomes
  quoted only inside the rewriter): a `KIND LAMBDA-BODY` block with NO
  `(:LAMBDA-BODY NIL)` beta step (nosig-pinned — fixing site 2 fails the
  pin loudly).
- `p2-beta-preprocess` — site 3: abbreviation-expansion to the lambda,
  const-folds after, NO lambda markers at all (nosig-pinned).
- `p2-beta-equiv-iff` — the false-equiv defect: an `:EQUIV IFF` child
  under the beta step's hardcoded `ORIGIN REWRITE-FNCALL/LAMBDA-BODY
  :EQUIV EQUAL` (sig-pinned; the fork fix changes this signature).
- `p2-beta-expand-hint` (added with the fork batch) — site 4: an
  `:expand (:lambdas)` hint preempting rewrite-fncall; origin
  `EXPAND-HINT/LAMBDA-BODY`.
- `p2-beta-iff-context` (re-audit F1 probe, promoted) — a `let` in an IF
  TEST: the entry-style beta is an EQUAL fact despite the iff context;
  REPLAYS (was a spurious preprocess-gate frontier pre-fix).
- `p2-beta-hide` (re-audit F2 probe, promoted) — HIDE inside a let body:
  pins the `(:hide-normalize nil)` fold-recording step; replay stops at
  the named HIDE registry frontier (S4 queue). Until it lands,
"LET/lambda support" means: books whose betas all go through the
rewrite-fncall path.

**RESOLVED (fork batch 2026-07-25):** the false-`:EQUIV` defect above is
fixed by `structured-geneqv-equiv` at all body-rewrite emissions;
`p2-beta-equiv-iff` now pins the HONEST state (`:EQUIV IFF` on the beta
step; nosig on any `LAMBDA-BODY :EQUIV EQUAL`).

**S2b replay status (close-out 2026-07-25).** `p2-beta-preprocess`
REPLAYS 2/2 (the site-3 arm: plain-substitution rhs emission +
`proveConv`'s beta-descent + `findOccurrences`' lambda-ACTUALS descent);
`p2-beta-expand-hint` REPLAYS 1/1. Named frontiers, deliberately open:
- `p2-beta-quoted-actuals` — "folded constant-test collapse … node rhs
  is '4": the site-2 chain shape (constant-IF collapse composed with a
  nested exec-counterpart inside a lambda body) needs a chain-recipe
  extension; emission is correct.
- `p2-beta-equiv-iff` — reaches convergence of the constrained stub
  `(BAR Y)` (proveConv frontier): the theorem genuinely needs
  iff-reasoning (S3 lane).
- `cov-mv-let` — the NESTED-let class: a rewrite inside an UNOPENED
  lambda body (the boundary-frame case) has no body-congruence PathStep
  (`findOccurrences` deliberately skips bodies; the needed lemma is a
  quantified-premise congruence: ∀env' eval body = eval body' ⇒ apps
  equal). The inner-beta step now EMITS (was silent), so the failure
  moved from the masked MV-NTH point to this earlier, more honest one.
- Also fixed in-batch: emitters' `:RHS` instantiation is now PLAIN
  substitution (`structured-sublis-var-plain`) — `sublis-var`'s
  cons-term const-folds ground calls, which made entry-style rhs values
  jump AHEAD of the recursion's own recorded steps (an incoherent
  chain; hit the pre-existing `abbreviation-expansion` emitter too);
  and the open-body boundary frame anchors as the SYMBOL `lambda` when
  the body is itself a lambda application (nested case — the raw term
  in fn position was unparseable and killed cov-mv-let at parse).

- **Interpreter** (S2.1, committed cb54a6c): `evalOptStep`'s
  LAMBDA-application arm — actuals in the outer env, body in the outer
  env EXTENDED by formals↦values. Semantics DECIDED BY DIFFERENTIAL
  PIN (`Tests/differential/corpus/lambda.lisp`, 9/9): the fresh-env
  (`ev` pairlis) variant DIVERGED on a nested open lambda, because
  ACL2's translate closes lambdas over their lexical scope. The
  formals extraction is now the shared `lamFormals?` (one definition
  for interpreter and replay).
- **Parse** (S2.2, cb54a6c): `PathFrame.argLam` (numeric bkptr, the
  lambda term in fn position); body descents arrive as
  `.boundary LAMBDA-BODY <head>`.
- **Scoping lemma pack** (S2.3): `freeVars`/`NoLet`/`substTerm` are
  binder-aware — a lambda application is admitted exactly when ACL2's
  own translate invariant holds (well-formed formals, body free vars ⊆
  formals), and substitution rewrites only the ACTUALS. The four
  induction lemmas (`evalOpt_freevar_congr`, `evalOpt_substTerm_quote`
  / `_eq` / `_conv`) gained real lambda cases.
- **EMISSION, not reconstruction** (fork): ACL2 fires no rune for the
  beta step, so the `LAMBDA-BODY` block had NO adopting step and the
  tree builder attached its nodes to the NEXT chain step — a genuine
  mis-parent. `rewrite-fncall`'s lambda case now emits
  `(:REWRITE-STEP :RUNE (:LAMBDA-BODY NIL) :ORIGIN
  REWRITE-FNCALL/LAMBDA-BODY :LHS <app with rewritten actuals> :RHS
  <rewritten body>)`, which adopts the block exactly as a `:DEFINITION`
  unfold adopts its body block. The same site gained the
  speculative-rollback checkpoint the fncall path already had (a
  too-many-ifs-rejected lambda expansion used to leave orphan events).
- **Replay**: `PathStep.lamHead` + arity-1/2 lambda argument
  congruences (the `(k LAMBDA …)` frame); `replayLambdaBody` (the
  beta node, structurally the definition-unfold recipe); the DP-lift
  value walkers descend into the beta-reduct (`re_lam_beta*_val`).
  Beta needs NO closedness side condition — `bindArgsOver` extends,
  so an open body reads the same outer bindings on both sides.
- Status: `cov-let-lambda` REPLAYS end-to-end (ci-gated:
  `fsq_unfolds_real_mirror` in Tests/DriverTests.lean pins the replay,
  the kept-hypothesis set, and the axioms). The lambda wall fell in
  the other three pinned books too — they now stop at unrelated
  frontiers (`cov-mv-let`: MV-NTH is not a DP-lift primitive;
  cov-meta-rule/cov-clause-processor (SINCE REFUSED whole — BUG-019
  witness fix, 2026-07-26): SYMBOLP recognizer cells and the
  SYNP preprocess shape, 3/16 and 4/16 replaying). Corpus golden stays
  62/79; correction (audit F7): the S2 branch's golden delta was NOT
  purely message-only — cb54a6c's single-child preprocess arm
  (Core.lean) moved 05-hints/LEN2-APP-VIA-USE from the clausify-split
  frontier to a deeper preprocess mismatch (still FAIL; that book has
  no lambdas). Binder arities >2 hard-fail by name in the congruence
  walk and the beta recipe; the DP-lift walkers frontier them.
- Follow-ups: DONE 2026-07-25 — `NoLet` renamed `WellScoped` (it admits
  a binding form) and the `envUpdate`/`bindArgsOver` clone collapsed;
  both golden byte-identical. Sites 2–4 of the table above
  (CORRECTION 2026-07-25: the earlier claim here that site 2 "would
  hard-fail" was wrong at the tree layer — the audit's probe shows
  silent mis-parenting in the reconstructed tree; only the driver
  fails closed).

## Driver inventory — candidate fake-replay infrastructure (pin now, kill later)

MDD directive (2026-07-22): mechanisms in the CURRENT driver that
RE-DERIVE what ACL2 could emit are candidate fake-replay
infrastructure. This branch pins each with coverage; the kill-path
(principled emission + recorded-step replay) is future support work.
Graded: [bridge] = reconstructs an unlogged rewrite at a mismatch
point; [rederive] = recomputes a resolution ACL2 made from data we do
not consume; [mirror] = deterministic recompute of a documented ACL2
function validated against emitted output (most defensible, still
listed).

1. [bridge] `bridgeEqualNilNorm` — rewrite-equal NIL/EQUALITYP forms.
2. [bridge] `bridgeIfNegTestSwap` / `normalizeSwapsToward` /
   `liftNegTestSwap` — rewrite-if swapped-p. (Books: p1-swap-descend, p1-swap-joint, p1-swap-double-neg.)
3. [bridge] display-folded constant-test collapse arms
   (`mkConstTestCollapse` on folded records) — sublis-var folds.
4. [rederive] `collapseEval` symbolic-test resolution — "re-derives
   the resolution from the SAME facts if-interp consulted".
5. [rederive] the test-resolution reconciliation arm (unemitted
   type-alist lookups, if-interp-assumed-value2).
6. [rederive] recognizer registry derivations (ATOM-from-CONSP-false,
   ZP-from-INTEGERP-false, two-valued registries) — NOTE: the log
   already carries `:TYPESET`/`:TRUETS` integers on recognizer steps
   that we DO NOT consume; principled replay would decode the emitted
   type-set instead of re-deriving membership.
7. [rederive] `collectContextDemands` demand hoisting — re-derives
   what ACL2's type-alist had in scope (incl. the commuted-lexorder
   special case).
8. [rederive] FC-relief registry (LEXORDER-TOTAL) — consumes the
   emitted snapshot but re-derives the relief chain.
9. [mirror] chain-root strip / pass-local tagging — re-derives gstack
   frame residue from bkptr paths (structure not emitted).
10. [mirror] elim reorder recompute (erase+prepend+σ) — validated vs
    emitted :NEWCLAUSES.
11. [mirror] induction clean-up recompute (trivial-clause-p/ifTaut) —
    now validated vs emitted :SCHEME-DROPPED; the (i)-class
    add-literal complement folds are still recompute-only.
12. [mirror] pool-subsumption witness recompute (`subsumeWitness`),
    `dumbNegateLit`/`substTerm` mirrors, clausify mirror
    (`expandTerm`/`clausifyChecked`).
13. [rederive] `clause-context-resolution` verify-then-drop markers.

Each [bridge]/[rederive] entry needs: (a) a book pinning the
underlying ACL2 mechanism (quirk-derived backlog below), (b) a named
future emission that would retire it. The [mirror] class is retained
by design where the emitted artifact fully validates the recompute —
graded acceptable, but listed so the boundary stays visible.

## Quirk-derived book backlog

From the emission arc's bespoke mechanisms (each pins one inventory
entry): equal-NIL normalization shapes; EQUAL-commuted rule match
(one-way-unify1); display-folded collapses; a MINIMAL trivial-clause
drop (ORDEREDP-MEMB's is embedded in a big book); free-var relief via
type-alist (:TA-RUNES); strip-branches and-shape union; elim
multi-record rounds; clause-context-resolution marker; runout
minimal book; :TYPESET-decode probes (books whose recognizer verdicts
exercise distinct type-set bits). Plus follow-ups from batch 1:
forcing-round-for-real, congruence-consumption, defun-sk variants
(forall; nested), complex-number minimal repro for the fork.

This document is the arc's SPINE:
one entry per replay mechanism ("pattern"), each recording

- **source**: the generating ACL2 code site — the ground truth whose
  branch structure defines the circle's axes (never imagination);
- **axes**: what that code actually branches on — each axis point is a
  candidate synthetic book;
- **anchor**: the wild corpus row(s) that prove the pattern is real;
- **books**: the authored pattern-corpus books covering the axes
  (`acl2_samples/pattern-tests/`, each through real ACL2 + capture, each
  with a native lift where feasible — the anti-mangling guard);
- **status**: `recipe-landed` / `emission-pending` / `design-parked`,
  and per-axis coverage.

Method (the amended CLAUDE.md rule): synthetic BOOKS yes, synthetic
ARTIFACTS never. An axis point ACL2 refuses to reach from a small book
is recorded as `unreachable-by-construction`, not silently skipped.
Books whose natural native statement is Logic-bound (ACL2-quirk
circles) are FLAGGED as such — lack of a lift must be visible.

**Generalize-before-baking (MDD, 2026-07-22).** A quirk a probe
surfaces is treated as a SIGN of a more general rule until shown
otherwise: locate the family's generating structure in the ACL2
source and probe THAT — the map's unit is the family, not the
instance.

**There is no "silent normalization" (MDD, 2026-07-22).** The emission
format is entirely OUR design; a rewrite the log does not show is an
UN-INSTRUMENTED EMISSION SITE — the project's top-level rule applied
again (find where reconstruction lacks information → instrument the
fork there, in FUTURE support work). The map's job is only to
enumerate and pin those sites with books.

### P0 — un-instrumented emission sites (future fork instrumentation)
- the sites where our current instrumentation does not record what the
  rewriter did, enumerable by reading the rewriter source:
  rewrite-equal's NIL/EQUALITYP forms (rewrite.lisp:18089-98),
  rewrite-if's swapped-p (17726-37) and the or/and *T*/left-copy
  identities beside it, the if-interp call-stack folds (3742-3849),
  strip-branches' and-shape union (4318), sublis-var display folds,
  rewrite-time FC contradictions, primitive type-set entries'
  provenance.
- coverage task (THIS arc): source-sweep the rewriter for the full
  site list; give each a book pinning its observed log shape.
- support task (FUTURE, not this branch): instrument each site;
  today's replay-side reconstructions of some of them then become
  redundant and can be retired.

### P11 — the geneqv landscape
- source: ACL2's geneqv computation (`geneqv-lst`, congruence-rule
  application) — which argument positions rewrite under which
  equivalence.
- coverage task: books that put the same redex under equal-geneqv vs
  iff-geneqv vs user-geneqv positions and catalogue the recorded
  chains. The observed shapes are the requirements data for the
  (future, design-parked) L2 support work.

Seeded from the emission arc's conquered mechanisms (each source site
was read during implementation; see
`docs/notes/2026-07-21_emission-arc.md` for the increment evidence).
No pattern books exist yet — authoring them is the arc's work.

## Rewriter-core patterns

### P1 — rewrite-if SWAPPED-P normalization
- source: `acl2/rewrite.lisp:17726-37` (negation-shaped rewritten test
  `(IF c 'NIL 'T)` → strip + swap branches, unrecorded).
- axes: firing position (frame descends into the if / node ON the if /
  at the if-finish JOINT); nested double-negation (swap fires twice);
  interaction with the or-optimization directly below it in the source
  (`(if x x y)` with `unrewritten-test == left` → `*t*` under iff);
  swap inside hyp-relief vs body vs rhs blocks.
- anchor: LEN-ZIP2/3 (descend+target), ORDEREDP-MEMB (joint).
- books (first circle, 2026-07-22 — `acl2_samples/pattern-tests/`):
  - `p1-swap-descend` (or-guard base case) — REPLAYS ✓;
  - `p1-swap-joint` ((NOT (EQUAL …)) body test) — REPLAYS ✓;
  - `p1-swap-double-neg` (iterated swap ×2) — REPLAYS ✓. Probe finding:
    a (NOT (NOT …)) DEFUN body is normalized at admission
    (unreachable-by-construction); the THEOREM-hypothesis route reaches
    it.
  - `p1-or-opt-probe` — axis PINNED by a real captured shape: ACL2
    replaces the or-test's then-copy by *T* under IFF geneqv
    (`(iff (if x x y) (if x t y))`, the identity directly below the
    swap site). Row FAIL (named if-finish mismatch) — this is the L2
    frontier in miniature; note: at a TEST position the identity IS
    eval-sound (`(IF (IF x x y) a b) ≡eval (IF (IF x 'T y) a b)`), so a
    positional bridge is designable short of full L2. Design note for
    the L2 ladder.
- status: 4/4 axes have captured books (observed via focused replay:
  3 replay under existing support, 1 pins the iff-identity shape).
  Native lifts and any sweep wiring: support-side, future.

### P2 — the RUNOUT pass (rewritten-body)
- source: `acl2/rewrite.lisp` ~20613 (`rewrite-fncall` re-rewrites the
  rewritten body, gstack `'rewritten-body`); fork: the bkptr
  inner-block kind list.
- axes: recursive vs non-recursive fn; runout children carrying their
  own root collapses (the pass-local strip case); nested unfolds inside
  the runout; runout under a rule RHS block.
- anchor: REV-REV, HOW-MANY-ISORT, ORDEREDP-RM;
  HOW-MANY-EVENS-AND-ODDS (pass-local strip).
- books: none yet. status: recipe-landed.

### P3 — chain-root strip / pass locality
- source: ACL2's gstack branch-frame residue per rewrite pass
  (`rewrite-if` keeping the if on the gstack while rewriting a branch).
- axes: block kind (BODY/RHS/HYP/REWRITTEN-BODY); two same-kind blocks
  under one parent (audit-refuted as unobserved — an axis point to
  probe deliberately); collapse selecting then vs else; folded vs
  unfolded recorded lhs.
- anchor: HOW-MANY-EVENS-AND-ODDS.
- books: none yet. status: recipe-landed (kind-tagged); the same-kind
  collision axis is exactly what a book should try to construct.

### P4 — EQUAL-commuted stored-rule match
- source: `acl2/translate.lisp:6916-31` (`one-way-unify1` EQUAL
  special case).
- axes: direct vs commuted; ambiguity (both orientations matching
  DIFFERENT stored rules — must stay hard-fail); commuted match with
  hyps; non-EQUAL equivalences (must NOT commute).
- anchor: CAR-APPEND.
- books: none yet. status: recipe-landed.

### P5 — rewrite-equal built-in normalizations
- source: `acl2/rewrite.lisp:18089-98` (NIL forms, EQUALITYP form);
  if-interp call-stack folds `:3742-3849`.
- axes: each normalization form; chain-end vs mid-chain occurrence.
- anchor: qsort-arc rows (ALL-REL family).
- books: none yet. status: recipe-landed (`bridgeEqualNilNorm` et al).

## Clause/waterfall patterns

### P6 — induction clean-up (trivial-clause drops)
- source: `acl2/induct.lisp:7047` → `trivial-clause-p`
  (simplify.lisp:6808) → `tautologyp`/`if-tautologyp`
  (rewrite.lisp:5852-5960) + SINGLE-PASS `expand-some-non-rec-fns`;
  fork `:SCHEME-DROPPED` (a291c2ec22).
- axes: each expansion fn (implies/iff/eq/eql/=/zerop/…— note the
  audit's single-pass subtlety: introduced EQL stays opaque);
  EQUAL/IFF commutation depth; complement folds (add-literal, never
  emitted) vs trivial drops (emitted in :SCHEME-DROPPED); base-case vs
  IH-selection drops.
- anchor: ORDEREDP-MEMB.
- books: none yet. status: recipe-landed + emission-landed.

### P7 — multi-record ELIM rounds
- source: `eliminate-destructors-clause` (the per-record erase/prepend/σ
  reorder rule, validated vs :NEWCLAUSES).
- axes: record count; fresh vs occurring elim vars; guard-literal
  position; per-level pinning.
- anchor: msort rows.
- books: none yet. status: recipe-landed.

### P8 — strip-branches conjunction split
- source: `acl2/rewrite.lisp:4318` (`(IF p q 'NIL)` unions the two
  sides' clause sets — NO if-interp test event).
- axes: and-shape at literal root; nested and-shapes; and-shape whose
  p side itself splits.
- anchor: ORDEREDP-ISORT (Subgoal *1.1/3').
- books: none yet. status: EMISSION-PENDING (fork queue: emit a
  conjunction-split event), then a spine-walker arm.

### P9 — FC-derived type-alist facts
- source: forward-chaining rules feeding the type-alist
  (`:TA-RUNES` provenance, fork); `type-alist-clause` contradictions.
- axes: relief via a single FC rule (LEXORDER-TOTAL, landed); the
  commuted-source demand (landed); FC CONTRADICTION closing a whole
  clause (S1.3: `simplify-clause/fc-contradiction` +
  `rewrite-clause/type-alist-contradiction` discharge emitters,
  `*true-clause*`-gated; HOW-MANY-FILTER-1 replays via the DP lexorder
  order theory); DEFAULT-CDR-style clause-context relief (S1.5: the
  `(NOT atom)` demand orientation + hoist; `relieve-hyp/known-true`
  markers thread `:TA-RUNES` + `:PARENTS` from the verdict ttree —
  HOW-MANY-EVENS-AND-ODDS replays). Transitive type-alist EQUIVALENCE
  (a solidify `:EQUIV-TERM` composing across clause equations) is
  derived as the deterministic equation closure — MDD-ratified
  2026-07-23: ACL2 stores classes, never a chain; emit what ACL2
  records, derive in Lean what it doesn't.
- anchor: qsort ALL-REL rows; HOW-MANY-FILTER-1;
  HOW-MANY-EVENS-AND-ODDS.
- books: none yet (both anchors replay from the wild logs).
  status: LANDED (S1.3–S1.5); remaining sub-frontier: type-set-derived
  solidify verdicts BEYOND the equation closure (J6 residue, e.g. both
  sides nil under ¬consp) — named throw in the solidify arm.

### P10 — verdict-class recognizers and TP pins
- source: type-set recognizer resolution (`rewrite-recognizer`,
  assume-true-false); compound-recognizer rules; gz TP corollaries.
- axes: recognizer × fact-source matrix (litFact / segFact /
  branchFact / TP hypothesis / builtin TP via emitted gz corollary /
  compound-recognizer rule); the registered kernel derivations
  (ATOM-from-CONSP-false, ZP-from-INTEGERP-false, unicity int pins).
- anchor: LEN-INTERLEAVE class, LEN-ZIP2, CD2-BOUND.
- books: none yet. status: recipe-landed for the exercised cells; the
  matrix's unexercised cells are the book targets.

## Interpreter-layer twin (differential families)

Each trusted-core primitive pinned WITH a differential family
(`Tests/differential/`), H3 made systematic. Queue seeded by the
corpus: NUMERATOR/DENOMINATOR (H3 pin-first, design-parked), the
lexorder total-order surface (partially pinned), `zp`/`nfix` numeric
coercions (newly load-bearing via P10/the NFIX measure single).

## Design-parked circles (MDD review before any build)

L2 equivalence ladder (IFF→PERM congruences), encapsulate/functional
instantiation, admission-waterfall replay, `:use`-hint Goal structure,
NFIX μ-measure + decrease-prover arm, trivial-equiv branch
substitution (the type-alist substitution class).
