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

## The ask

Approve/amend items E and F for one fork edit + rebuild +
recapture-all round-trip (item G explicitly deferred unless ruled
otherwise). Expected recapture surface: corpus-wide records of the
two new classes appear wherever the sites fire; goldens reviewed
row-by-row; expected row-status changes NONE (both consumers become
read-offs of what the inference already concluded) — any status
drift is a mandatory stop.
