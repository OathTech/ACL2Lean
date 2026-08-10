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
Proposed: extend the defun emission to carry, per termination clause,
the rune set ACL2's admission machinery consulted (site pinned during
the build — the measure-conjecture proof path; presented before the
edit if diffuse). Consumer: the linear/rule premise passes gate
injection on the recorded runes wherever the channel exists.

## Item I — the TAU RULE-SET-BASIS emission (the ruled tau middle
## path's fork half; user-agreed for this batch 2026-08-10)

Per the 2026-08-10 tau ruling: for verdict-only tau leaves, emit the
rule set the verdict rested on (the ta-nil-basis/fc-derivations
precedent); the existing DP kit then takes exactly those runes'
instances as premises — read-off, not matcher selection. FIRST
INCREMENT IS THE SCOUT: confirm the tau verdict site can cheaply
report its fired rule set (upstream tau is deliberately ttree-free);
the scout's find-out comes back before the fork edit. Unblocks
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
