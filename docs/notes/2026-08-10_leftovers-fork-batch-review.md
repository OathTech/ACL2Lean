# Leftovers fork batch — item-by-item review request

For: Mike (the standing rule: fork batches get item-by-item review
before the rebuild). Assembled per the equal-descent restructure
charter's item 4; ONE rebuild+recapture round-trip, sequenced
commit-fork → build → recapture per the provenance discipline.

## Item E — `emit/dedup-drop` at add-literal's member-term branch
## (the close-out audit's D1 remedy)

Site: `acl2/simplify.lisp:154`, the `((member-term lit cl) cl)` branch
of the same `cond` whose member-complement-term sibling carries
`emit/complement-close` (user-ruled 2026-08-06). The Lean side
currently INFERS the drop from the clause shape (`dedupSkipClose`,
HELD UNDER EXPIRY with the audit's marker). Proposed record:

    ; TRACE-LOG[emit/dedup-drop]: the add-literal DUPLICATE drop —
    ; the incoming literal is already among the clause's literals
    (push (list :dedup-drop :origin 'dedup-drop :lit lit)
          (cdr *structured-rewrite-log*))

Consumer: `dedupSkipClose`'s trigger becomes a read-off of the
recorded drop (the arm's byCases composition stays; the expiry
marker retires). Retires the last inference-from-absence at this
`cond`.

## Item F — type-alist entry-derivation provenance for the
## LEXORDER-ORDER class (retires that rung's expiry)

The `equal/type-alist-nil` verdict basis (R1 retirement, landed
2026-08-07) records the ENTRY (`:TA-ENTRY`) but not the entry's own
derivation when it was built during type-alist construction from
order-axiom reasoning (HOW-MANY-BAD-PAIRS-BNEXT's
`(EQUAL (CAR X) (CADR X)) := nil` from the false LEXORDER literal —
`:TA-RUNES` empty). The Lean rung currently supplies the
justification (kernel `lexorder_refl`, HELD UNDER EXPIRY). Proposed:
instrument the entry-construction site to record the source fact the
disequality entry derives from (shape parallel to the landed
`(:TA-SUBST …)` records; exact site to be pinned during the build —
the assume-true-false/type-set-rec path that binds equality entries
from order facts). If the site turns out diffuse, we present the
find-out before editing.

SCOUT RESULT (endgame arc, 2026-08-10): **item F DROPS from the
batch — no fork edit needed.** The order-derived theory is REFUTED
by the artifact: both rung-serving witnesses (HOW-MANY-BAD-PAIRS-
BNEXT Subgoals *1/6.1 and *1/5.1, bsort.proof-log 11518 / 14145,
`:TA-RUNES NIL`) have the `:TA-ENTRY (EQUAL (CAR (CDR X)) (CAR X))`
appearing VERBATIM as positive clause literal 6 of the input clause,
while the verdict fires at literal 5. Upstream
`rewrite-clause-type-alist` (simplify.lisp:5065) assumes "(a) the
falsity of every literal in tail except the first" — the entry is a
plain TAIL-LITERAL assumption, already fully recorded (the input
clause + the entry term). The gap is CONSUMER-side: the driver's
`falsitySources` = processed `litFacts` only, so tail literals are
out of scope and the lexorder rung compensated with an order-axiom
justification ACL2 never used (exactly the expiry's complaint).
Remedy (joins the consumer wave in place of F's emission): tail-
literal falsity in scope via byCases on the tail literal in the
spine composition, gated on the recorded `:TA-ENTRY` matching a
clause literal verbatim; the LEXORDER-ORDER rung then RETIRES. Any
future record whose entry matches no clause literal is a frontier —
if one appears, a real entry-provenance emission item can be
designed then.

## Item G (CONDITIONAL — only if item 2's negative side becomes
## consumable): split `equal/cdrs-decision` origins

The audit-C3 asymmetry (a negative-side cdrs `*t*` is discarded by
ACL2) is now mirrored at the OUTCOME level in `replayEqualDescent`,
and the shared origin is verdict-consistent per phase — so this split
is NOT currently needed. Listed so the review covers it in principle;
it joins only if a future consumer must distinguish the sides
record-side.

## Item H — the admission-clause RUNE CHANNEL (restructure-audit
## DEFECT 2's emission half; user-agreed for this batch 2026-08-10)

The emitted `:TERMINATION-CLAUSES` are verdict-only with NO rune
channel, so the DP linear-premise supply cannot be leaf-rune-gated on
the admission path (the ruled direction for the DP-scan question).
SCOUTED + RULED (2026-08-10): the admission ttree is ALREADY in scope
at the emit/defun site and discarded (`(declare (ignore ttree))`) —
the edit is ~one line (`all-runes-in-ttree` alongside the clauses).
Granularity ruled PER-ADMISSION (the ttree is not per-clause);
premise gating on the admission's cited rune set. Consumer: the
linear/rule premise passes gate injection on the recorded runes
wherever the channel exists.

## Item I — the TAU RULE-SET-BASIS emission (the ruled tau middle
## path's fork half; user-agreed for this batch 2026-08-10)

Per the 2026-08-10 tau ruling: for verdict-only tau leaves, emit the
rule set the verdict rested on (the ta-nil-basis/fc-derivations
precedent); the existing DP kit then takes exactly those runes'
instances as premises — read-off, not matcher selection.
SCOUTED + RULED (2026-08-10): the verdict site is clean
(tau-clausep → tau-clause1p, induct.lisp, where the discharge node
already emits); the basis SHAPE is ruled the FN-RESTRICTED
TAU-DATABASE SLICE (the pos/neg-implicants + signature rules for
exactly the clause's fn symbols — deterministic read-off at the
verdict site; exact-fired threading stays available as a later
tightening if the slice proves too coarse). Unblocks
HOW-MANY-RM-GENERAL's *1/3.2 leaf (the row's ✓).

## The ask

Approve/amend items E, F, H, and I for ONE fork edit + rebuild +
recapture-all round-trip (item G explicitly deferred unless ruled
otherwise). BATCHING AGREED (Mike, 2026-08-10) — the four items ride
one round-trip; the item-by-item content review of each edit's exact
site+shape still happens here before the rebuild (H and I carry
scout-first caveats above). Expected recapture surface: corpus-wide
records of the new classes appear wherever the sites fire; goldens
reviewed row-by-row; expected row-status changes from E/F/H NONE
(their consumers become read-offs of what the replay already
concluded) and from I the HOW-MANY-RM-GENERAL tau-leaf advance —
any OTHER status drift is a mandatory stop.

BATCH AS EXECUTED (endgame arc, 2026-08-10): **E + H + I** — item F
dropped per its scout result above (the charter's pre-authorized
drop class: the artifact already carries the derivation; the fix is
consumer-side). E/H/I sites and shapes are all pinned and ruled;
the review is complete. Fork 497b21a6b3; ingestion-first tolerance
landed at 19caaed BEFORE the recapture.

ROUND-TRIP DRIFT (mandatory stop, DIAGNOSED, fixed 2026-08-10):
the first recapture ballooned every TAU-BASIS-carrying world by
~90 defuns (ordered-perms 21→105, equisort 31→104,
sorts-equivalent 214→279) and regressed MSORT/QSORT-IS-ISORT to
ASSUMED (usefi prepare over maxRecDepth in the bloated world).
Cause: the slice printed the GROUND-ZERO implicant universe (CONSP's
pos/neg-implicants name ZPF, DFP, BAD-ATOM, …) through the
cited-symbol collector (infra/cited-symbols), whose def-closure then
gz-snapshot-emitted every named predicate clique. Fix (fork
f9d4a99b68, the fertilize :DELETE-LIT-FLG remedy class —
emission-side payload normalization): PREDEFINED fns contribute
their tau-pair identity only (:GZ T); world-entering fns keep the
full ruled slice. DEVIATION NOTE vs the ruled shape: gz fns' tau
data is world-CONSTANT and lives Lean-side as ground-zero knowledge
(fail-closed at any use site that lacks it) — the fn-restriction
and the user-fn payload are exactly as ruled; flagged for the exit
audit + Mike's review.
