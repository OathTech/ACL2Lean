# R-lane (rung 3) decision brief — the PERM-TLFIX gate

For: Mike. The sorting final close-out charter models this as the
arc's single USER GATE (queue item 5): the arc exits honestly at
77/78 if unruled, 78/78 if the build is approved and lands. This
brief assembles the already-pinned design record so the ruling needs
no new investigation.

## The row and the class

`PERM-TLFIX` (convert-perm-to-how-many book) fails at:

    replayNode: rune (rewriting-equivalence, NIL) applied under
    equivalence perm — R-parameterized recipe pending (G1 frontier)

The artifact (dump-proof-tree, Subgoal *1/2' literal 3): a solidify
R-rewrite `(TLFIX (CDR X)) => (CDR X)` under `PERM`, justified by the
IH literal `(NOT (PERM (TLFIX (CDR X)) (CDR X)))`, runes citing
`equivalence:PERM-IS-AN-EQUIVALENCE` and NO defcong — ACL2's built-in
geneqv license: an :EQUIVALENCE rune doubles as congruence at the
relation's own argument positions. This is the ONE remaining sorting
red that is neither bsort-emission nor convert-machinery class.

## What the build is (the 2026-08-04 artifact-anchored record, TODO)

Lean side (the L2 discipline governs — R stays an abstract relation;
the recipe is the equivalence rule itself, never an enum):
(a) R-frames for equivalence-rune-licensed positions; (b) the
solidify decode for an R-source literal ((NOT (PERM A B)) assumed
false ⇒ EvTrue (PERM A B)); (c) value-level composition from the
defequiv statement's conjuncts + the R-fact; (d) the reflexive close
rides the existing equivrefl arm. The threading runs through the
literal-chain composer (`rec.rewrites` + `chainReqEq` currently
reject non-equal chains) with the one-frame collapse
(`equivOwnPosCongr`, already built) at the parent R-application.

FORK PREREQUISITE (audit-corrected 2026-08-04 F12, and itself a
fidelity FIX independent of the R-lane): the current emission
HARDCODES `:equiv 'equal` at the solidify site, and the enclosing
with-lemma step records a false EQUAL equation (its :RHS is the rule
rhs AFTER the R-solidify — true only up to R). The fix is the true
per-step relation at both sites. CAVEAT for sequencing: this changes
recorded fields consumers currently read — a recapture with the new
emission needs a consumer-compat check across the EXISTING green
corpus before the golden re-pin (the charter's recapture discipline
covers this).

## Options

1. **BUILD in this arc** — the emission fix rides the bsort fork
   batch (one round-trip instead of two), then the Lean-side lane.
   Outcome: 78/78. Cost: the emission item + the literal-chain
   composer threading (the driver's most-trodden path — the reason
   this was made a checkpoint rather than just built).
2. **EMISSION-ONLY in this arc** — land the per-step-relation
   emission fix in the batch (it is a fidelity correction on its own
   merits and the long-pole round-trip), defer the Lean-side lane to
   its own charter. Outcome: 77/78 now; the future R-lane arc starts
   with its prerequisite already captured.
3. **DEFER both** — PERM-TLFIX stays gate-logged; the R-lane gets its
   own arc end-to-end. Outcome: 77/78; the future arc carries its own
   fork round-trip.

Recommendation: **option 2** unless you want 78/78 out of this arc —
the emission fix is worth doing while the fork is open regardless of
the lane decision, and it decouples the composer threading (the risky
part) from the batch (the slow part). Option 1 is honest and fully
designed if you prefer the complete close-out now.

Ruling needed: 1 / 2 / 3 (or your own variant). The arc proceeds on
all other queue items meanwhile; this gates only PERM-TLFIX.

## RULED (Mike, 2026-08-09): option 2 — emission-only

The per-step-relation emission fix (item D) joins the approved fork
batch; the Lean-side composer threading is DEFERRED to its own
charter. PERM-TLFIX stays red this arc (the charter's exit criterion
counts this as success — the gate-log is this brief + the ruling).
