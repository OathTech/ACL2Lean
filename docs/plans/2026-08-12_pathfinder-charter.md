# Pathfinder arc — charter (the first mirror, unconditionally)

Branch `mdd/pathfinder` off main @ 77cced1. Baseline: the mirror
specs exist (`Mirrors/Basics.lean`, zero-import, six Props); the
APP-ASSOC waypoint is `.native` with the CLEAN TRIO (unconditional,
zero debt) — the one Basics example pushable through with no
inherited `sorryAx`. Master plan Phase A1; the lexicon governs all
vocabulary.

THE DELIVERABLE: `app_assoc` proved VIA REPLAY at a genuine Lean
instance — the first MIRROR theorem in the project's history —
with a trio-clean `#print axioms` receipt. Target instance: `Int`
(a real Lean type; `SExpr` itself is an ACL2 notion and would
violate mirror purity). The polymorphic Prop is instance-scoped
honestly (the master plan's route 1); nothing pretends otherwise.

## Queue

1. **PLACEMENT DESIGN (present to Mike BEFORE building past it).**
   The spec files in `Mirrors/` are zero-import by gate; a proof of
   `app_assoc Int` must import machinery, so it cannot live there.
   Proposed: `ACL2Lean/Proofs/Basics.lean` — imports machinery,
   states ONLY `theorem <name> : ACL2Lean.Basics.<prop> <instance>`
   (statement-level purity: the statement mentions Mirrors constants
   + instance types and NOTHING else — extend check-mirrors-pure
   with that statement pin for Proofs/, deterministic). The reader
   story: the spec file is what you read; the proof file is one line
   of statement per Prop + a receipt. Alternative shapes welcome —
   this is the arc's one open design point.
2. **The refinement-relation core (machinery-side, minimal).**
   `Acl2Embed α` (element injection `α → SExpr` + injectivity) —
   ONLY what app_assoc needs, no order field (that arrives with
   sorting); the `Int` instance over int atoms (injectivity is a
   core-logic-adjacent lemma; `intRep` exists waypoint-side); the
   list encoding `encVia e = enc ∘ map e`.
3. **The squares** (each template-shaped BY HAND this once — the
   transfer kit's spec, per the master plan):
   (a) `map e (Basics.app xs ys) = Basics.app (map e xs) (map e ys)`
   (same-skeleton square); (b) the definitional-agreement square
   between `Basics.app` on `List SExpr` and the waypoint's append
   vocabulary (read the actual APP-ASSOC waypoint statement first —
   drive off the real artifact, not the remembered one).
4. **Theorem transport**: waypoint APP-ASSOC (replayed-backed,
   trio-clean) + squares + injectivity → `app_assoc Int`. The proof
   consumes the waypoint constant (which consumes its
   `driver_replayed%` seam — attribution chain intact end-to-end).
5. **THE LIST**: every hand-written artifact from 2–4 logged at the
   moment of writing as a Phase B/C work item (the arc's second
   deliverable — the transfer kit's requirements, measured not
   guessed).
6. **Stretch (only if the route generalizes without new design):**
   `len_app Int` — adds the Nat-result transport and the FIRST
   honest debt inheritance (`drv_tp_mylen` → the receipt carries
   `sorryAx`, stated on the theorem, retiring with B1). If it needs
   new design, log and stop — the milestone is app_assoc.
7. **Exit audit** (small arc, one reviewer + verification): an
   adversarial CLAIMS reviewer on the one question that matters —
   is the mirror theorem genuinely proved VIA replay? Specifically:
   does the proof term transitively consume the replayed constant,
   and is there NO Lean induction closing mirror content (a direct
   induction proving app_assoc would typecheck and be worthless —
   the product-level ornamental-import failure, and the exact thing
   the pathfinder exists to prove we don't need). Then the fix
   round, TRUE_EXIT=0, exit report + merge proposal.

## Discipline

Two-tier gating; goldens/pins untouched (this arc adds no waypoint
work); the product ornamental-import ban (mirror content from
replayed facts only — squares and transport are the allowed glue;
template-shaped, no content smuggling); check-mirrors-pure stays
green throughout; the lexicon's vocabulary in everything new.

## Exit criterion + escape hatch

Done = app_assoc Int proved via replay with a trio-clean receipt,
THE LIST delivered, the audit run + fix round gated TRUE_EXIT=0,
exit report with merge proposal. Item 6 is optional; deferring it
with a log entry is success. ESCAPE HATCH (binding): early exit at
any time, for any reason or none — an honest interim report is a
success outcome; fidelity and the boundary rules override
completion pressure. MANDATORY-EXIT triggers: the placement design
proceeding without Mike's look (item 1); any Lean induction closing
mirror content; any purity-gate weakening to land a theorem; any
golden/pin change at all.

## ARC LOG — early exit at the item-1 wall (2026-08-12)

Recon complete (the waypoint verified off the real artifact:
`app_assoc_native_driver` over core `++`/`List SExpr`, unconditional,
trio-clean). The item-1 checkpoint DELIVERED to Mike: the placement
design (`Proofs/Basics.lean` + the Proofs/ statement-purity pin) and
the content-flow design (Square A vocabulary alignment at SExpr; the
waypoint as associativity's SOLE entry point; the Acl2Embed-Int lift
by homomorphism square + injectivity), including the honesty note
that core `List.append_assoc` makes a dishonest three-line proof
available at all times — which is exactly what the exit audit checks
against. Items 2–7 are gated on Mike's ruling per this charter's own
mandatory-exit trigger ("the placement design proceeding without
Mike's look"). EARLY EXIT declared per the goal's exit condition:
the remaining work gates on a user decision. Resuming = Mike's go on
the design (or an amended design), then items 2–4 execute as
presented.

RULING RECEIVED (Mike, 2026-08-12 — closing the item-1 wall; recorded
here per exit-audit CONCERN-1, which rightly noted the ruling
previously existed only in agent prose): (1) the placement directory
is `ACL2Lean/MirrorProofs/` (not the proposed `Proofs/`); (2) the
proposed statement-purity pin is NOT adopted — "we are going to avoid
doing the lazy thing by setting expectations right, rather than
aggressive gating. These are small demos, easy enough to keep
straight"; the content-flow shape approved as presented. The
EXPECTATIONS header in MirrorProofs/Basics.lean implements (2); the
exit audit's NOTE-2 speedbump suggestion is DECLINED under the same
ruling (recorded for future reconsideration if MirrorProofs grows
beyond small demos).

ARC COMPLETION (2026-08-12): items 2–6 executed as designed — both
mirror theorems landed first-try (app_assoc_int trio-clean;
len_app_int with the honest drv_tp_mylen sorryAx receipt); the exit
audit returned ZERO DEFECTS with the decisive checks (glue-only
closure content-free; unplug test leaves exactly the waypoint
statement; the transport is a complete reduction to the waypoint;
hreplayed genuinely consumed one level down). NOTE-4 (credit): the
proof is generic over any Acl2Embed α — the Int scoping is WEAKER
than what is proved, the honest direction.
