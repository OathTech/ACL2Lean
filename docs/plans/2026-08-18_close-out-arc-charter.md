# Close-out arc charter — the sorting shop window to 15/15 (2026-08-18)

Branch: from main AFTER the r4-collect merge (which itself awaits explicit
sign-off — this charter presumes nothing about it). Mike's direction
(2026-08-18, verbatim): "our next arc should be fixing bsort_is_isort (and
then we're done!)" — plus two same-day rulings folded in: (a) sorter_unique
is defensibly REMOVED from the mirror (an encapsulate-internal
instantiation device, not a book export); (b) permWitness_complete's block
is solved by the Option refinement route ("morally the same theorem" —
Mike), not rested. End state: a 15-Prop shop window with every Prop a
proven-via-replay theorem — no structural asterisks.

This arc CLOSES the sorting line. The survey's product-first targets
(Runs/compress, Fringe/samefringe, no-dups-qsort + the IFF-decode
broadening) are a separate future arc, deliberately out of scope here.

## Item 0 — sorter_unique reclassified out (spec change, ruled)

> **THE PRE-CHECK FIRED (2026-08-18) — the asymmetry stated below is
> FALSE and the removal stands on a DIFFERENT argument.** Half (i) is
> refuted by the book, the captured artifact and the 75-row inventory
> alike; Mike re-ruled on the corrected facts ("still remove, this
> seems fine") on the EXPORTED-BUT-AN-INSTANTIATION-DEVICE argument.
> See ARC LOG J-0-1 and reshape note Part 8. The bullet about moving
> the catalog entry "to the constraints tier" is also void — the row is
> RESULT TIER and stays there, annotated represented-by-instances.

- **Pre-check (binding, before touching the spec):** verify from the
  75-row inventory (docs/notes/2026-08-18_sorting-spec-reshape.md) and the
  book source that (i) the uniqueness theorem's correspondent is
  encapsulate-internal — consumed only via :functional-instance to mint
  the concrete X-IS-ISORT exports — and (ii) permWitness_complete's
  correspondent IS a book-exported top-level defthm (the asymmetry that
  justifies keep-vs-remove). If the inventory contradicts either half,
  STOP and report before any edit.
- Remove sorter_unique from Mirrors/Sorting.lean (16 → 15 Props). No
  tombstone (shop-window rule); the reclassification is recorded as a
  dated part in the reshape doc (the same treatment the four phantom
  Props received). Catalog entry moves to the constraints tier; the
  concrete instance products (msort/qsort/bsort_is_isort) are and remain
  the book's external face.

## Item 1 — bsort_is_isort (RETARGETED 2026-08-18: driver-side, NO fork round-trip)

**The original framing is withdrawn.** It said the fork emits a
verdict with no discharge record and the fix is at emission. The
binding ground-truth pass refuted all three of its load-bearing
claims (full diagnosis in the ARC LOG, J-1-1; the wave-2g entry it
came from carries a dated correction):

1. the fork HAS emitted `:TAU-BASIS` at `emit/preprocess/tau` since
   fork-batch item I (user-ruled 2026-08-10), and the BSORT leaf's
   slice names the `TRUE-LISTP-BSORT` signature rule;
2. the citation consumer is LIVE and the leaf DISCHARGES in the real
   replay by citing that already-replayed dependency theorem
   (instrumented measurement: gate passes, match succeeds,
   `proveDpFact` + `dischargeSpine` both OK — for all SIX tau-basis
   leaves in the sorting corpus, zero fallbacks; see the count
   correction under J-1-1);
3. the N1 guard never fired on this row: the golden's `REPLAYED ✓`
   with no trailing `cond[…]` means UNCONDITIONAL, and the `cond[…]`
   that was read as the row's belongs to the standalone informational
   DP probe, which has no `ReplayCtx` and so always reports `◌`.

**Mike's ruling (2026-08-18, verbatim): "we should ALWAYS replay ACL2
when we have the material at hand."** Dep-theorem CITATION is the
route; the DP-leaf carve-out is LAST RESORT, for genuinely
verdict-only leaves with no proof record. That principle is already
what the tau-basis path implements, which is why no fix was needed
there.

- **No fork change, no recapture, no golden repin** — the emission
  side is complete and the logs are untouched, so the golden must
  stay byte-identical. ANY golden movement in this item is a STOP.
- The real blocker is the `usefi` (functional-instance) bridge at the
  waypoint layer — the second, secondary observation in J-2g-1, which
  was the accurate one.
- Then re-land the preserved decode (J-2g-2) → the `bsort_is_isort`
  product, receipts pinned. Scoreboard 14/15.
- Records corrected as part of the item: the N1 guard's error text
  (it advised "fix the leaf's emission", which is what mis-aimed the
  wave), the wave-2g ARC LOG entry, and this charter.

## Item 2 — the Option refinement row + permWitness_complete re-spell

> **THE SPEC-CHANGE BULLET BELOW IS SUPERSEDED — all three of its
> predictions were refuted by the landed outcome (block added
> 2026-08-19, audit round; items 0 and 1 got theirs in place at the
> time and this one did not, which left the section reading as though
> it had been executed as written).** What actually landed is recorded
> in `docs/notes/2026-08-18_sorting-spec-reshape.md` **Part 7**:
>
> 1. *"permWitness re-spelled with an `Option α` witness"* — REFUTED at
>    two layers. The witness is UNCHANGED; a crossing is stated at
>    `SExpr`, where `Option SExpr → SExpr` is not injective (`none` and
>    `some nil` share an image), so an `Option`-VALUED spec definition
>    cannot cross at all. What moved was the ELEMENT TYPE, not the
>    witness: the `Option` row is applied to `α`, giving the product at
>    `Option Int`.
> 2. *"the junk arm and its `[Inhabited α]` instance eliminated"* —
>    REFUTED with (1). Both are still there, and the junk arm is now
>    load-bearing in the honest direction: `Option`'s own `default` IS
>    `none`, which the row sends to `nil`, which is exactly what
>    discharges the element-result square's hypothesis generically.
> 3. *"the Int product landed"* — REFUTED. There is NO `Int` product
>    and there cannot be one: the element-result square is FALSE at
>    `Int`, kernel-refuted by `conditional_elem_square_false`
>    (`MirrorProofs/Sorting.lean`, live theorem). The product is
>    `permWitness_complete_optint` at `Option Int`, approved by Mike as
>    THE product for that `Prop`. Scoreboard 15/15 as predicted — at a
>    different type than predicted.
>
> [Also corrected 2026-08-19: the `Prop`'s spurious `[TotalOrder α]`
> binder came off in the post-merge audit round — `CONVERT-PERM-TO-
> HOW-MANY` is order-free — taking with it the `TotalOrder (Option Int)`
> instance and the order pin this item had landed to satisfy it.]

- **Generic machinery (not a shim):** an Option row in the
  data-refinement calculus — Lean `Option α` refines ACL2's value-or-nil
  idiom (`none ↦ nil`, `some a ↦ enc a`). This is the rendering of
  ACL2's single most pervasive return shape (member/assoc/every search
  function), witnessed here first; it lands as a table row with the same
  fail-closed shape checks as every prior row. Acceptance: ALL existing
  transports byte-identical (regression net + receipts re-pass), golden
  untouched.
- **Spec change — draft returns for Mike's bless before landing (the
  established shop-window flow):** permWitness re-spelled with an
  `Option α` witness (the junk arm and its `[Inhabited α]` instance
  eliminated — the Option form is the TIGHTEST idiomatic correspondent
  of the book's element-or-nil witness); permWitness_complete restated
  in the Option form; the crossing re-derived; the Int product landed.
  Scoreboard 15/15.
- Note the prior record honestly: the J-2e-6 kernel refutation killed a
  DIFFERENT repair (the precondition quarantine) and stands; the Option
  route was named-not-taken in the reshape era and is now taken by
  Mike's direction.

## Order

0 → 1 → 2. Item 2 is independent of item 1's fork round-trip and MAY run
as a parallel lane while capture cycles block item 1; item 0 is a
half-day spec increment done first (it changes the denominator every
later receipt cites).

## Law

Four-line canon; golden protocol as above; never push; merge only with
explicit sign-off at the moment of merge; fast-gate intermediates labeled
as such, ONE full claim-gate TRUE_EXIT=0 at the arc exit; J/O-numbered
logging; the five ask-first classes; receipts pinned; sorries 0; spec
drafts return for the bless before landing.

## Escape hatch (per the goal-design rule)

Stop and report if:
- ~~the tau leaf's obligation cannot be stated from what ACL2 itself
  possesses at emission time~~ — RESOLVED 2026-08-18: it is stated,
  emitted, and cited. Replaced by: the `usefi` bridge's gap turns out
  to need a SECOND fork round-trip or a ratified-boundary change;
- ANY golden row moves at all in item 1 (there is no recapture, so
  the golden must be byte-identical);
- the Option row cannot keep the existing transports byte-identical;
- the item-0 pre-check contradicts the classification asymmetry;
- any remaining work gates on a user decision, a ratified design
  boundary, or a SECOND fork round-trip.

## Definition of done

Mirrors/Sorting.lean holds exactly 15 Props; 15 products with trio-clean
receipts ({propext, Classical.choice, Quot.sound}); the reshape doc
carries the item-0 record; full claim-gate TRUE_EXIT=0 recorded in the
exit commit; the merge candidate presented for explicit approval.

## ARC LOG

### Items 0 and 1 (2026-08-18, branch `mdd/close-out`)

* **J-0-1 — THE BINDING PRE-CHECK FIRED, AND THE CHARTER WAS THE THING
  THAT WAS WRONG.** Item 0's stated justification was an ASYMMETRY:
  `sorter_unique`'s correspondent "encapsulate-internal … not a book
  export" vs `permWitness_complete`'s "book-exported top-level defthm".
  Half (ii) held. Half (i) was refuted by all three sources the charter
  itself named — the book (`equisort.lisp`: the encapsulate closes at
  line 102, `strong-ssortfn1-is-ssortfn2` is at line 104, top level, not
  `local`), the captured artifact
  (`sorts-equivalent.proof-log:187` carries it `:SOURCE :INCLUDE-BOOK`
  and installs it as an active `:REWRITE` rule at `:189` — the identical
  export test `CONVERT-PERM-TO-HOW-MANY` passes), and the 75-row
  inventory (RESULT TIER, never in the ENCAPSULATE CONSTRAINTS tier the
  charter said to move it to). No edit was made. Mike re-ruled on the
  corrected facts — "still remove, this seems fine" — with the argument
  that actually holds (EXPORTED-BUT-AN-INSTANTIATION-DEVICE), and the
  removal landed on that basis. Record: reshape note Part 8.
* **J-1-1 — THE bsort "EMISSION GAP" DOES NOT EXIST; THE CITATION ROUTE
  WAS ALREADY LIVE.** Measured with temporary instrumentation at the
  eligibility gate (`Totality.lean:803`), then fully reverted. The fork
  has emitted `:TAU-BASIS` at `emit/preprocess/tau` since fork-batch
  item I (2026-08-10); the BSORT leaf's slice decodes to exactly the
  `TRUE-LISTP-BSORT` spec; that rule IS in `ctx.ruleHyps`; the gate
  passes; `oneWayMatch` succeeds; `proveDpFact` and `dischargeSpine`
  both succeed. ALL SIX tau-basis leaves in the sorting corpus
  discharge by citation, with ZERO fallbacks. The leaf was already
  doing what Mike's principle asks ("we should ALWAYS replay ACL2 when
  we have the material at hand").
  **[COUNT CORRECTED 2026-08-19 — post-merge audit round.]** This entry,
  the item-1 framing above, the ARC EXIT below and TODO.md all said
  "FIVE tau-basis leaves". Re-counted directly from the corpus
  (`grep -c TAU-BASIS acl2_samples/**/*.proof-log`): there are **SIX**,
  across **FIVE books / five golden rows** — `convert-perm-to-how-many`,
  `equisort`, `sorts-equivalent`, `bsort` one each, and
  `ordered-perms.proof-log` **TWO** (Subgoal *1/6 and Subgoal *1/4 of
  the same theorem). The finding is unchanged: every one of them
  discharges by citation with zero fallbacks; only the count was wrong.
  Commit `e9fa5b1`'s message carries the same miscount ("All FIVE
  tau-basis leaves") and is immutable — this is its correction.
  **The `◌` that started the wave is a SCOREBOARD-READING error.** The
  `[DISCHARGE: … ◌ assumed cond[…]]` annotation is the STANDALONE
  informational DP probe's (`Runner.lean:855-878`), which by
  construction (`Totality.lean:479-483`) receives no `ReplayCtx` — no
  rules to cite — and so reports `◌` on every leaf whose discharge
  needs one, forever. The ROW's own verdict, `REPLAYED ✓` with no
  trailing `cond[…]`, means UNCONDITIONAL. All SIX `ASSUMED:dp-fact`
  rows in the golden are of this kind; none is blocked, none is
  `sorryAx`-class debt.
  Consequence: NO fork round-trip, NO recapture, NO golden repin — and
  the golden verified BYTE-IDENTICAL at the end.
* **J-1-2 — THE REAL BUG: A CACHED-CONDS SHORTCUT IN THE `usefi`
  PRE-PASS** (which is J-2g-1's second, accurate observation, correctly
  attributed at last). `Waypoints/Macro.lean` recorded `[]` as the
  condition list on both CACHE branches of its termination pre-pass.
  BSORT's is the corpus's one CONDITIONAL admission — its decrease is
  licensed by `HOW-MANY-BAD-PAIRS-BNEXT`, a `:LINEAR` rule ACL2 proves
  before it admits the defun — so `usefi_term_…_BSORT` carries a premise
  binder, and applying it with no condition arguments is a type error.
  It surfaced as `depReplayedProofAt: dependency ORDEREDP-BSORT's replay
  failed (frontier)` — an error naming a DIFFERENT THEOREM, which is why
  wave 2g read it as a dependency frontier. Latent because msort/qsort
  never need BSORT's totality; the first row that does is BSORT-IS-ISORT.
  Fixed with the device `crossBookRegistry` has always used for exactly
  this: a companion `_conds : List String` constant written alongside and
  read back, fail-closed (constant without companion hard-fails).
* **J-1-3 — WHAT THE MIS-AIM COST, and where it was corrected.** One
  wave recorded a fork round-trip as the remedy, one charter item was
  written around it, and three records repeated it (the N1 guard's own
  error text said "fix the leaf's emission instead", which is the most
  likely origin). All three are corrected in place with dated blocks
  rather than quietly re-aimed: the guard text, the wave-2g ARC LOG
  entry, and this charter's item 1. The catalogue's `.pending` text for
  the row is replaced by `.native` with the correction noted.
* **J-1-4 — DISCLOSED, not silenced: a toolchain PANIC in the sweep
  log.** `Lean.LibrarySuggestions.SymbolFrequency` hits a heartbeat
  timeout while writing the `BSsortsEquivalent` module. It is a
  Lean-internal symbol-indexing pass, non-fatal — the sweep completed
  116/116 with exit 0 and the golden byte-identical. Recorded because it
  is noise in the gate log that a later reader should not have to
  re-diagnose; not investigated further, and not ours.

### Residuals at this point

* Item 2 ran as a parallel lane on `mdd/close-out-item2`; the merge of
  the two lanes is the arc's collection step and is where the header
  scoreboard reaches FIFTEEN Props / FIFTEEN proven.
* The full claim-gate (`TRUE_EXIT=0`) is owed at the arc exit, after
  collection — the two commits here are FAST-GATE labelled.

## ARC EXIT (2026-08-19)

Full claim-gate **TRUE_EXIT=0 on a1bb171** (artifact:
`.gate-runs/a1bb171-20260819T000915Z.log`). **THE SORTING SHOP WINDOW
IS CLOSED: FIFTEEN Props, FIFTEEN proven-via-replay theorems** —
fourteen at `Int`, `permWitness_complete` at `Option Int` (the
value-or-nil element type; the `Int` refutation stands as the reason).
Zero structural asterisks; the products page's scoreboard section that
listed "the ones that are not, with their real distance and no
euphemism" is retired EMPTY — every `Prop` now has a product.
[Phrasing corrected 2026-08-19, audit round: this line said "the
products page's 'not yet' section", and no section of that name ever
existed on the page. The retired section is the one quoted above.]

How each of the three closed, against the charter's own predictions —
all three of which were corrected by measurement:
- **item 0**: the binding pre-check REFUTED the charter's
  encapsulate-internal premise (book source, artifact, inventory all
  three); Mike re-ruled removal on the corrected
  instantiation-device argument (reshape Part 8).
- **item 1**: NO fork round-trip — the emission was complete since
  fork-batch item I (2026-08-10) and the citation route was already
  live (all six tau-basis leaves, zero fallbacks — count corrected
  2026-08-19, see J-1-1); the `◌ assumed`
  reading belonged to the standalone informational DP probe (J-1-1);
  the real bug was the usefi pre-pass's cached-conds shortcut vs
  BSORT's one conditional admission (J-1-2, fixed fail-closed).
  Golden BYTE-IDENTICAL throughout.
- **item 2**: the Option-VALUED re-spell was REFUTED at two layers
  (reshape Part 7); the Option ROW landed generically and the product
  lives at the honest element type per Mike's three approvals.

Mike's principle, ruled this arc and recorded durably: "we should
ALWAYS replay ACL2 when we have the material at hand" — the DP
carve-out yields to dep-theorem citation wherever a proof record
exists.

Also collected: `docs/notes/2026-08-18_project-history.md` (the
retrospective, written at Mike's request on the eve of the close).

The branch is the merge candidate awaiting explicit approval.
POST-MERGE SEQUENCE (Mike, 2026-08-18): the final adversarial audit
(two Fable auditors — trust-chain inside + statement-fidelity outside —
plus a records auditor, plan pre-presented), then the public README
rewrite, then the champagne.

## POST-MERGE AUDIT ROUND + FIX BATCH (2026-08-19, branch `mdd/audit-fixes`)

The post-merge sequence above, executed. **Three auditors** ran against
the closed arc — a trust-chain reviewer (inside: is the TCB story what
the tree actually implements?), a statement-fidelity reviewer (outside:
do the Props say what the ACL2 books say?), and a records reviewer
(claims, counts, provenance) — followed by orchestrator spot-checks of
every falsifiable finding. **No finding touched soundness**: no product
lost a receipt, no statement was found unfaithful, the golden never
moved. What the round DID find was one spurious binder, one claim that
was true of a probe and false of the page that cited it, and a scatter
of miscounts and stale prose — i.e. exactly the class the two-standard
rule reserves adversarial review for (claims and records), landing on
the records rather than on the proofs.

The batch, in the order it landed (each commit carries its own receipts):

0. **The spec change (Mike-blessed).** `permWitness_complete` loses its
   `[TotalOrder α]` binder — `CONVERT-PERM-TO-HOW-MANY` is order-free
   and so is everything the `Prop` is stated in. Consequence chased and
   reported deleted-vs-kept: `instTotalOrderOption`, the two
   LEXORDER-against-`nil` facts and the order pin all go (they existed
   only to satisfy the binder — item 2's own report said "nothing
   consumes the order"); `intEmbed_enc_ne_nil` and `optIntEmbed` stay
   (the product consumes them). The product re-derived unchanged.
1. **The refutation elaborates.** `conditional_elem_square_false` had
   been sitting inside a fence inside a docstring while the page said
   "the refutation is kernel-checked rather than argued" — true of wave
   2e's probe, false of the page. It is now a live theorem on that page
   with a pinned receipt.
2. **SIX tau-basis leaves, not five** (`ordered-perms.proof-log` carries
   two) — corrected here and in TODO.md; `e9fa5b1`'s message is
   immutable and its correction is recorded under J-1-1.
3. **Seven prose/docstring corrections**, each verified against the
   primary source: the junk arm's TRUE case set (every permuting pair,
   not just `[] []`); `permuted_equivalence`'s THREE replayed seams (not
   one); wave 2g's "sorting 11 → 13" (truly 9 → 13); this charter's "not
   yet section" phrasing; item 2's missing superseded block (added
   above); the P2 carve-out DISCLOSED in the spec header (audit B's
   signing condition — `howManySmaller_bnext` and
   `howManyBadPairs_bnext_lt` ARE the book's two lemmas, proved
   natively because Lean's kernel demands the decrease before `bsort`
   exists); BUG-020's present-tense body under a `fixed` status.
4. **The retrospective** gets a dated closing addendum (its live counts
   were true at writing; the close landed hours later) plus four
   in-place count corrections.
5. **The README rewrite** (added to the batch by Mike mid-round): the
   295-line README moves to `docs/OVERVIEW.md` with two stale claims
   re-measured, and the root `README.md` becomes a short front page.

**GATE.** Full claim gate `TRUE_EXIT=0` on `8d934b9`, artifact
`.gate-runs/8d934b9-20260819T060913Z.log`: 13 statics green (incl. the
submodule triple — 91 logs stamped at `e8d78e513d68`), `lake build`
zero warnings, `just test`, sweep **116/116** (116 unconditional, 0
conditional), `check-golden-current: golden matches the live assembly`,
zero `sorry` / `native_decide` in the log. The coverage golden is
BYTE-IDENTICAL to the arc's — nothing in this batch touches the driver,
the logs or the corpus. Disclosed, as in J-1-4: the log again carries
the non-fatal toolchain PANIC from Lean's own
`LibrarySuggestions.SymbolFrequency` background pass (a heartbeat
timeout in the toolchain, not in our elaboration); the build completes
successfully around it.

The branch is a merge candidate. NOT merged, NOT pushed — awaiting
explicit approval at the moment of merge.

## EXTERNAL REVIEWER ROUND + FIX BATCH (2026-08-19, branch `mdd/reviewer-fixes`)

An EXTERNAL reviewer (outside the arc, outside the audit round above) was
pointed at the repository's public top-level claims — principally the new
front-page `README.md` — and read them against the live declarations, the
ACL2 sorting books, the provenance/proof-log gates, the mirror assembly, and
this project's own canonical trust model. The report is committed VERBATIM,
before any fix, as `docs/audits/2026-08-19_top-level-claims-audit.md`
(commit `24b075f`), so the claim and the response stay separable in history.

**Nothing it found touched soundness.** It re-established mechanically, and
we did not dispute: fifteen sorting `Prop`s with fifteen `mirror_transport%`
products and fifteen guarded receipts, the products ACL2-free, the seam gate
reporting 21 products each with a replayed-statement witness, 91 logs stamped
at the pinned submodule commit with all four negative fixtures failing closed,
`just test` exit 0. Every finding landed on the CLAIMS and the RECORDS — the
two classes the two-standard rule reserves adversarial review for — and the
harshest of them was ours: a binding document that had gone stale under a
result it was supposed to describe.

The batch, Mike-triaged, docs-only, in one commit (`755f3cb`):

1. **`README.md` — three sentence replacements, Mike-blessed verbatim, plus
   one count.** The fifteen products are INSTANCE products (fourteen at
   `Int`, `permWitness_complete_optint` at `Option Int`) and one of them —
   `permuted_equivalence_int` — bundles THREE replayed theorems, so
   "the corresponding `defthm`" became "the corresponding theorem" with the
   bundle disclosed. The trust paragraph now separates what the kernel
   certifies (the theorems) from what is enforced one level down (generated
   templates, provenance hashes, seam gates — named as strong engineering
   evidence, "deliberately distinguished from the kernel's guarantee").
   "No `sorry` … anywhere" became "in anything checked", with the native
   termination lemmas described as they are: a handful, two of which are
   themselves named ACL2 book theorems. The Learn-more bullet's
   "seven-stage pipeline" is now NINE, matching the document it names.
2. **`CLAUDE.md` — the P1, and the one that mattered.** Its trust note still
   said the bridge "reaches only the WAYPOINT layer" and called the product
   layer a north star — text that had been false since the arc exit above,
   in the file that binds every agent. Refreshed and dated: for the
   DEMONSTRATED CORPUS the fully-untrusted property is LIVE (21 products,
   receipts pinned, seam-gated), and the caution is re-aimed at the two
   places it still binds — BREADTH beyond that corpus, and
   ATTRIBUTION/FIDELITY, where statement authenticity and replay fidelity
   are engineering-evidenced and never kernel-certified ("Never report it as
   one"). "Suspect any stage" is kept, pointed at every new import. The
   Current-status paragraph now records the 2026-08-19 close-out.
3. **`docs/plans/2026-08-12_master-plan.md` — a disposition note, not a
   rewrite.** The dated plan keeps its text; a header note marks its
   "13 Props" figure and its still-open sorting description superseded (the
   reshape's fifteen, the close-out's 15/15) and states what still governs:
   the two-category model and Track FREE / Track REAL.
4. **`docs/OVERVIEW.md` — the fresh-clone instruction was WRONG, and the
   reviewer proved it from the build graph.** The reduced capture (simple +
   recon-tests) cannot build the default targets: `defaultTargets` → `Main`
   → the root `ACL2Lean` library → the sorting mirror proofs, and the
   waypoint modules `include_str` their books' logs at compile time.
   `just recapture-all` is now the instruction. The reduced path was not
   kept on faith — the one genuinely smaller cone was MEASURED (import
   closure of `ACL2Lean.Replay.Runner`: 66 modules, zero `Imported/`, one
   compile-time log, `simple.proof-log`) and is documented as the focused
   `acl2lean-replay` dev loop, explicitly not a way to build the library.
   Separately, the quoted 2026-08-16 TCB passage keeps its wording as dated
   history and gains a current-disposition line: the mirror-level seam gate
   it records as ABSENT now exists and finds 21 products mechanically — and
   its conclusion ("strongly-evidenced engineering, not mathematics") is
   unchanged and still governs.
5. **The PANIC (P2) — investigated, then DOCUMENTED, because no switch
   exists.** Lean's own `LibrarySuggestions.SymbolFrequency` runs its
   `exportEntriesFnEx` over a module's constants AT EXPORT and blows its
   heartbeat budget on our heaviest coverage modules. There is no
   project-local way to turn it off: the extension is
   `builtin_initialize`-registered in the shared library, carries no
   `register_builtin_option` gate and no `lean` CLI flag, and its budget is
   unreachable — `Environment.unsafeRunMetaM` builds a FRESH `Core.Context`
   with `options := {}` and `maxHeartbeats` defaults off THOSE options
   (`Lean/CoreM.lean:217,225`, v4.28.0 source), so neither `set_option
   maxHeartbeats` nor `-DmaxHeartbeats=…` reaches it. Classified instead in
   `docs/OVERVIEW.md` § *Building and commands* (post-elaboration pass, no
   olean / receipt / `#guard_msgs` pin / golden row / gate reads it, gate
   `TRUE_EXIT=0` alongside) and tracked in `TODO.md`, with the line that
   matters written down: it is never a licence to wave through a real proof,
   replay or gate failure.

**GATE.** Full claim gate `TRUE_EXIT=0` on `755f3cb`, artifact
`.gate-runs/755f3cb-20260819T070120Z.log`: statics green (shellcheck clean,
`check-log-provenance` 91 logs at `e8d78e513d68`, `check-pattern-map` 61
books, `check-mirrors-pure`, `check-dark-files` 183 sources, the provenance
gates failing closed), `lake build` **zero warnings**, `just test`, sweep
**116/116** (116 unconditional, 0 conditional), `check-golden-current: golden
matches the live assembly`, zero `sorry` / `native_decide` in the log. The
diff is documentation ONLY — no `.lean`, no build configuration, no corpus —
so the coverage golden is byte-identical by construction as well as by cmp.
Disclosed, unchanged and now classified above: the log carries the same three
non-fatal `LibrarySuggestions.SymbolFrequency` panics; the build completes
successfully around them.

The branch is a merge candidate. NOT merged, NOT pushed — awaiting explicit
approval at the moment of merge.
