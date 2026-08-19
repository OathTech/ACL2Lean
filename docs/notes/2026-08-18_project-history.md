# ACL2Lean: A History
### From a one-line README to a sorting book that mirrors

*Written 2026-08-18, on the eve of the sorting close-out, at Mike's request.
Sources: git log (998 commits, 2025-12-17 → 2026-08-18, 74 distinct working
days), docs/plans/, docs/notes/, docs/audits/, docs/BUGS.md, docs/LEXICON.md,
README.md, CLAUDE.md, TODO.md, and the mirror layer itself. Everything below
is quoted or counted from those; nothing is reconstructed from memory.*

---

## Chapter 0 — Prehistory: the transpiler (2025-12-17 → 2026-01-07)

The repository opens on 17 December 2025 with a commit by Alok Singh:
"Initial ACL2Lean structure: parser, syntax, and workbench." It is a
transpiler. Parser.lean reads s-expressions, Syntax.lean holds an AST,
Workbench.lean prints event histograms. ACL2_SPEC.md reports the corpus
census — 113 defuns, 73 defthms, 5 defmacros — and its "Next Steps" end with
the modest ambition to "Define a proof-oriented semantics (World.step) once
function bodies are elaborated into Lean equivalents." The README is one
line long: `# ACL2Lean`.

Over three weeks it grows a DSL (#acl { }), tactics (acl2_simp, acl2_grind,
acl2_induct), stobjs, bitvectors. Then, on 7 January 2026, it stops.
Seventeen commits, and silence for ten weeks.

## Chapter 1 — The handover, and the day sorting arrived (2026-03-19 → 03-21)

On 19 March 2026 a second author appears — septract — and never leaves; of
the 998 commits, 981 are his. The first week is inventory work: closing
seven sorry stubs in Logic.lean, proving lexorder_total, acl2Count,
append/len/trueListp, full rational arithmetic.

On 20 March, two things happen on the same day that decide the next five
months.

First, commit 79388bf: "Add ACL2 fork submodule and sorting corpus samples"
— ten .lisp files copied into acl2_samples/sorting/: bsort, isort, msort,
qsort, perm, orderedp, how-many, ordered-perms, convert-perm-to-how-many,
sorts-equivalent. J Moore's classic sorting development, the one every ACL2
course teaches.

Second, docs/plans/2026-03-20_acl2-book-replay.md — the earliest artifact in
the record that names the sorting book as the target. Its goal line reads,
verbatim:

> **Goal:** Import any ACL2 book and replay its proofs in Lean, using ACL2
> as an untrusted proof-search oracle with Lean's kernel as the sole trust
> anchor.

And its Phase 3 names the first four targets by their ACL2 runes:
orderedp-isort, true-listp-isort, how-many-isort, perm-isort.

**An honest caveat about "the original goal":** that plan also records that
the ambition predates this repository — a legacy prototype at
~/Projects/acl2-lean already carried Acl2Lean/Manual/Sorting.lean and the
ACL2 fork's books/sorting/, both listed as "Not yet imported". So sorting
was Mike's target before the first line of this repo was written; the
2026-03-20 plan is simply the earliest place the record can show it.

The plan is also, read from today, wonderfully wrong in exactly the ways the
project would later forbid. Its Phase 5 replay tactic ends in a fallback
chain — acl2_grind → omega → simp_all → sorry — with the note "Graceful
degradation: sorry'd subgoals, not failures", and its deliverable is a
tactic that "closes >50% of sorting corpus theorems automatically." Every
one of those three ideas — heuristic fallback, sorry as degradation,
percentage-of-goals as success — is banned by name in today's CLAUDE.md.
The project spent five months earning the right to that ban.

## Chapter 2 — The design pivot and the instrumentation sprint (2026-03-22 → 03-23)

Tactic replay hit a wall almost immediately. The walkthrough that killed it
is blunt about where (docs/plans/2026-03-22_simple-example-walkthrough.md:175):
"ACL2's built-in arithmetic rules (UNICITY-OF-0, COMMUTATIVITY-OF-+, FIX)
operate at a high level. Our Lean Logic.plus implements the low-level
rational arithmetic. There's no bridge." Commit f6279a1, 22 March: "Design
pivot: verified ACL2 rewriter; remove stale .claude tooling." Then 13f2545
deletes 1071 lines of tactic machinery. New premise: ACL2 terms stay as
SExpr **data**, an interpreter gives them meaning, and a rewriter replays
ACL2's trace on the data.

The design doc of that day states the trust argument that has never since
changed a word in spirit:

> A bug anywhere in the pipeline — wrong interpreter, broken rewriter, bad
> trace, incorrect correspondence lemma — results in a type error, never a
> false theorem.

The same week produced the project's only outward-facing document,
docs/comms/2026-03-22_acl2-lean-bridge.md, an architecture letter addressed
to ACL2's own developers — proposing upstreaming, asking whether there were
better hooks than patching rewrite-with-lemma, and reporting that the trace
had been tested on "the ACL2 sorting textbook corpus (~60 inductions, ~900
waterfall steps across the 7 standalone files that produce substantive
proofs)." Its "First target" is a single theorem: my-len-my-app,
"end-to-end from ACL2 proof trace to kernel-checked Lean theorem with no
sorry."

Then an instrumentation sprint of remarkable intensity — 26 commits on 22
March alone, walking the fork's coverage from 87% to 96%: IF simplification,
equal-self, recognizer logging, depth guards, scope-aware logging ("70%
smaller proof traces"), context substitution, rewriting-equivalence. On 23
March: "TRACE-LOG tags on all 32 logging points" — the convention (emit/ /
suppress/ / infra/) that still governs the fork today, now spanning 228 tags
across 12 files.

## Chapter 3 — The soundness detour, and the first pivot point (2026-03-24 → 04-04)

The plan was: build a rewriter, prove it sound once, replay forever. A
two-day spike produced the decision that outlived the plan — evalOpt, the
fuel-bounded Option-returning evaluator, chosen over an Except version
because `∀ f, eval f lhs = eval f rhs` is *false* at intermediate fuel while
`none = none` makes the quantification work. That evaluator is still the
semantic heart of the system.

By 28 March the shape had changed again: not a verified rewriter but a
**sound checker** — a Bool function that accepts ACL2's steps and never
infers. Its manifesto (docs/plans/2026-03-28_sound-checker.md, 525 lines)
contains both the joke and the doctrine:

> **Corollary: the easiest checker to prove sound is one that always
> rejects** (trivially sound, but useless). We build upward: every check we
> add expands the set of cases the checker *soundly accepts*.

Commit 7542316 the same day strips the checker's own cleverness — "Remove
all heuristic inference from the checker (simplifyTerm, resolveIfTests,
hypothesis free-variable search)" — and writes into CLAUDE.md the direct
ancestor of today's rule: "The proof checker does NOT do inference… The
checker follows instructions; it does not improvise." Baseline that day:
595 of 649 theorems pass across the sorting corpus.

On 4 April, twenty-one commits in one day, ending at 62fc20b: "Pivot point:
hand proof validates architecture, moving to proof-producing checker." The
hand proof had done its job — discovered the lemma inventory, validated
composition — and was now "fighting tactic mode." The checker would stop
returning Bool and start returning Expr.

Then, again, silence. Two months.

## Chapter 4 — The reset (2026-06-05)

The project's defining failure is commit b0ea0fb, 5 June 2026, and it is
worth quoting at length because everything the project now *is*
procedurally was written in its wake:

> main was reset to 2f180d1 … The 2026-06-05 proof-producer work was
> built/validated against synthetic nodes and a hand proof whose step case
> did not follow the reconstructed proof tree; run against the real tree it
> replayed 0 nodes and lacked the recursive driver entirely.

The postmortem (docs/audits/2026-06-05_producer-reset-postmortem.md),
addressed "to the next agent picking up Track B — read this first,"
enumerates four failure modes. The proof had been modelled as flat and
independent **three separate times** when it is a recursive tree. Node
handlers had been unit-tested on synthetic ProofNodes "with bare variables —
shapes that do not occur in real trees. Green synthetic tests gave false
confidence." The hand proof's step case had computed both sides and equated
them with native arithmetic instead of replaying the node chain: "It proved
the theorem but did NOT demonstrate the replay — so it was useless as a
template." And there was a rewrite handler for cdr-cons that only matched
(cdr (cons VAR VAR)) — "a shape that never occurs."

One thing survived intact, and the postmortem says so with evident relief:
no sorry, no fallback, had ever been introduced. "This discipline WAS
respected throughout … keep it that way."

The very next day, commit 9c1dc68 rebuilt CLAUDE.md from scratch and added,
**in a single commit**, the entire Fidelity section and the entire
Working-discipline section that still govern the project:

> Proof construction here is long-cycle work that has **failed more than
> once** by building plausible pieces in isolation and only discovering they
> don't fit after a large investment. The failure mode is structural, not a
> knowledge gap — guard against it structurally.

> **A green lemma in isolation is a non-signal.** The only progress that
> counts is a sorry discharged *in the real theorem*.

> **Banned anti-pattern: "build the infrastructure now, wire it into the
> real proof later."** There is no "later" where it gets validated; the
> wiring *is* the work, and skipping it is exactly what has caused the
> repeated failures.

The same week also killed the *previous* pivot's descendant:
RewriterSoundness.lean was deleted as "abandoned legacy approach,
**known-false sorry**", and a de-claiming pass dropped a false "Zero sorry
in this theorem" comment and marked the checker's accept-on-gap fallbacks
KNOWN-UNSOUND — "**a ✓ certifies nothing.**"

## Chapter 5 — The architecture week (2026-06-08 → 06-12)

Five days, 136 commits, and the system acquires its permanent skeleton.

**8 June** — the driver replays its first real ACL2 proof tree end-to-end
(sq-rewrites), reading a captured log rather than a hand-built value. The
same day, commit 9589988: the coverage sweep is born, at **1/27**.

**9 June — the carve-out.** ACL2 closes many clauses by procedures that
record only a verdict: tau, type-set/forward-chaining, linear arithmetic.
There is nothing to replay because ACL2 wrote nothing down. The ratified
answer (docs/plans/2026-06-09_direct-proof-emission.md) is the project's
single deliberate exception: emit a discharge node, lift the leaf's
precisely-stated obligation, and close it with kernel-checked omega. The
doc is careful about why this is not a cheat —

> Fidelity framing: **faithful at clause granularity** — the clause tree
> (which IS ACL2's proof) is mirrored exactly, and decision-procedure
> leaves are discharged the way ACL2 itself regards them (a closed-form
> check).

— and equally careful about the cost, deliberately turning just ci red
until the emission landed: "Consequence acknowledged: just ci is not a
green gate again until this gap closes — **that pressure is the point**."
The same day added the merge rule, worded as a correction to inferred
permission: "Approval is never inferred from an earlier 'merge it' or from
the branch being green."

**10 June** — an eight-surveyor read of ACL2's own sources produces the
architecture survey, and from it the generality design with the three
invariants that still bind every module written since: **L1** the open
interface is the judgment layer (a monolithic Derivation inductive is
*prohibited*); **L2** the rewrite relation R is abstract, never an enum;
**L3** mandatory world-parametricity. The doc's judgment on the
Milawa-style alternative is a single line: "Milawa is evidence, not a
ceiling."

**12 June — sorting becomes the method, not just the target.** Verbatim,
from docs/plans/2026-06-12_sorting-corpus-roadmap.md:

> **Decision (MDD, 2026-06-12):** instead of the grep-sweep version of G6,
> adopt ONE real book development as the driving target:
> acl2/books/sorting/ — the classic J Moore *sorts-equivalent* development.
> Every gap that matters for a real book surfaces in dependency order;
> "what to build next" is whatever the corpus needs next.

The corpus is measured for the first time: 11 books, ≈75 own theorems,
qsort alone 6931 rewrite steps. An R0–R7 ladder is laid out, ending at
sorts-equivalent. The same doc contains the first statement of the finish
line: "The end-state test of the whole pipeline is theorems LIFTED into
Lean." Coverage that week: **17 of 37**.

## Chapter 6 — The long climb, book by book (June – July 2026)

This is the project's middle passage: five weeks of walking up the
dependency graph, one wall at a time, each wall named before it was
crossed.

The **perm** book fell first — perm-cons on 3 July, perm-transitive on the
5th, perm-rm and comm-rm on the 6th, and then, the same day, "the perm book
is 8/8" and "THE WHOLE PERM BOOK IS IMPORTED." Coverage 23/47.

Immediately after, the project turned around and attacked its own
foundations. evalOpt was rebuilt as an **ACL2 peer** — same interface,
forms in on stdin, values out — and differentially tested against real
ACL2. What came back was humbling and is now docs/BUGS.md, the single
canonical index: 27 numbered fidelity bugs, 16 fixed outright, 8 open, 3
partial. Characters were modelled as symbols (BUG-001). The parser
lowercased bare symbols where ACL2 upcases (BUG-002). lexorder had the
wrong order class for keywords and no class for characters (BUG-006/007).
The reader ignored Common Lisp's terminating macro characters, silently:
ACL2 reads (A B;C D) as (A B D), we read B;C as one token — "the reader's
one fail-open gap, and it becomes a live soundness hole the moment
gen-world output is wired into the certified pipeline" (BUG-020).

Most instructive, BUG-012, found by a spike on 10 July: SExpr admitted
non-canonical numbers *outside ACL2's value space* — .rational 2 4 and
.rational 1 2 were two representations of one value. Two countermodels were
executed rather than argued: **lexorder transitivity was false over all
SExpr**, and the replayed statement of a true ACL2 theorem was false —
(equal (* 1 q) q) evaluated to NIL at q = .rational 2 4. The fix made the
junk unrepresentable by construction.

Then the machinery walls: multi-variable induction measures and the
generalized scaffold (J1–J8, 15–17 July) which brought msort, qsort and
sorts-equivalent into reconstruction at 27/79; the emission arc (21–22
July) which walked 47/79 → 60/79 by teaching the fork to say more rather
than teaching Lean to guess; the **pattern map** (22–23 July), a top-down
frame over ACL2's situation space with 61 deliberately authored books run
through real ACL2, whose governing insight inverts the usual scoreboard:
"A book that fails at a named frontier … is a SUCCESSFUL mapping outcome."

**The end goal gets its first full statement here**, in
docs/plans/2026-07-06_long-term-roadmap.md:

> **Deliverable/headline at R7**: the classic J Moore sorts-equivalent
> development imported end-to-end — every theorem kernel-checked in Lean,
> the flagship facts (four sorts sort, and are equivalent) as native
> Mathlib-idiomatic statements.

And then, on 26 July, the audit that inverted the project's self-image.
Seven never-authored upstream books, 144 defthms, run end-to-end
(docs/audits/2026-07-26_full-pipeline-audit.md:529-535):

> | REPLAY | **10/144 (7%)**, 0 unconditional | … against the reported
> **62/79 (78%)**.
> **Every failure was fail-closed at a named frontier** — across 144
> defthms and 4 reconstruction crashes, no silent wrong answer, no
> swallowed event, no plausible-looking bad proof. That is a real and
> substantial positive result.

The same audit inverted the governing sequencing premise ("the narrow layer
is reconstruction," not capture), and found that the **tamper suite — the
soundness regression net — had been dark since the day it landed**, 179
commits earlier, with three of its four tampers no-ops: "So T1 removes
nothing, T2 tampers nothing, T3 matches nothing … because **no tamper
occurred**."

And its finding F1 became **BUG-019**, which is the whole trust note in one
incident. Every .defun event entered the World unconditionally, including
an encapsulate's *local witness* — so a constrained function was bound to
its discarded witness body, and the pattern book cov-encapsulate reported
**2/2 REPLAYED, unconditional and axiom-clean, about λx. 0**, while the
same world validated (EQUAL (CF X) '0), which real ACL2 refuses as a
theorem. Nothing false was kernel-certified; every replayed statement was
true *about the witness world*. The defect was statement substitution. The
BUGS entry's own summary is the line to remember: **"it failed GREEN."**
It regressed nine days later, gate-invisibly, because the pin book sat
outside the sweep — "docs/BUGS.md's BUG-019 evidence was false as written
at HEAD."

## Chapter 7 — Drift, and the rules that caught it (late July – 2026-08-11)

Late July opens the sorting arcs proper, and on 31 July a burst of fifteen
commits lands what were then called "sorting mirrors": ORDEREDP-ISORT
("insertion sort always sorts"), HOW-MANY-ISORT, ORDEREDP-APPEND
("quicksort's assembly step"), then PERM-QSORT — "QUICKSORT PERMUTES (the
flagship)" — and ORDEREDP-QSORT — "QUICKSORT SORTS (the headline)."

They were not mirrors. That is Chapter 8.

Four course-corrections cluster in this fortnight, and each produced a rule
still in force.

**The masked red build (2 August).** The Justfile comment that created
claim-gate fuses two events. On 21 July, self-caught:
`just ci | tail -2 && git commit` — $? after a pipeline is tail's status,
so && fired on a red ci and "a doc-only commit landed on a red build (the
very green-looking-failure class G1 guards against)." Then on 2 August,
commit 3c3255d claimed "GOLDEN BYTE-IDENTICAL" and recorded SWEEP_EXIT=0 —
*a sub-step's exit code in place of ci's*. The emission-cluster audit's
blocking finding F1: "just ci exit 1 at the 'COMPLETE' commit … **PROCESS
FAILURE: the completion commit claimed 'GOLDEN BYTE-IDENTICAL' against a
red build.**" The first remedy was just claim-gate on 3 August
(set -o pipefail; … TRUE_EXIT=$?). The second came on 7 August, when the
~30-minute gate began serializing every increment: the **two-tier split**,
in which intermediate commits must say fast-gate and may never say
TRUE_EXIT=0, "**so the tiers cannot masquerade**." Evidence it held:
8298966 (4 Aug) — "RED BUILD, claim-gate TRUE_EXIT=1 (recorded honestly)",
with the body amendment "An earlier version of this message claimed
TRUE_EXIT=0 from an unchecked pipeline — amended to the truth before any
build" — and 2931618 (7 Aug), "RECORD CORRECTION … 0ec18cb's closing-gate
claim was FALSE."

**The vacuous-green class (4–9 August).** Three times in five days: green
rows whose *hypotheses were refutable*. On the 4th, "evalOpt diverges, so
the hypothesis is UNSATISFIABLE (the reviewer proved totalHyp → False in a
scratch Lean file) … the BUG-019 failure mode one level up (statement
vacuity)." On the 5th, named as a recurrence in its own audit title line.
On the 9th, a row whose kept hypothesis *was its own goal*; corpus
107 → 106. It produced the ASSUMED choke point in the runner, and it is
the best answer anyone has to "why so many audits."

**The carve-out drift scare (2–6 August).** The rule had been ratified on
2 August, and it is Mike's, verbatim: "if we find ourselves writing custom
proofs or checkers per case, we are no longer mirroring ACL2 — we are
building custom search to replace it." On 5 August, chasing **one** row
through roughly nine successive frontier classes in a single session, the
executing agent declared the stop-early condition **on itself**: "the drift
test's question is live and **not self-certifiable**." Mike then
commissioned an outside review of 80 commits. Its verdict
(docs/audits/2026-08-05_branch-drift-audit.md):

> **The branch's direction is right; its tail accreted.** … Counting
> per-case (non-general) discharge mechanisms added on this branch:
> **nine**, of which **six have zero dependent green rows**. The test says
> "a growing count fails the test", and this count is growing.
> The most consequential single item is R1 … because of how it arose: **a
> fork recapture broke three previously-green rows and the response was a
> Lean-side search rather than an emission question. That is the exact
> inversion the mission forbids.**

Two kill rounds followed — "infra-mirror pieces KILLED, replay pieces
kept" — and the survivors carry DRIFT MARKER comments in the driver to
this day, each with an expiry tied to a queued fork emission. It also
produced the **goal escape-hatch rule**, whose rationale names the trap
precisely: "a completion-only goal-keeper combined with an exit that
requires user sign-offs converts 'no legal work remains' into open-ended
grinding on whatever is still touchable."

**The thin-Lean purge and the two-standard rule (11 August).** Mike ruled
the mirror layer down to sims plus isomorphism theorems, on three
principles (docs/notes/2026-08-11_thin-lean-boundary.md): P1 — no
capturable record; P2 — Lean-metatheoretic necessity (the kernel demands a
termination artifact for a definition to *exist*); P3 — untranslatable
statement, "the drift channel," legal only under the template gate.
Everything else ACL2-derivable is forbidden in Lean, "or carry it as
visible FORBIDDEN-DEBT sorry." The same week brought the two-standard
rule: adversarial review is for semantics, claims and records; gates are
reviewed only to the deterrent standard, because hardening a gate against
a motivated adversary "manufactures infinite hardening — **gate
whack-a-mole**, where each hired adversary's escape breeds the next, more
fragile gate."

## Chapter 8 — The restoration (2026-08-12)

The word "mirror" had drifted through three senses. It first meant the
deep-embedded EvTrue theorem. On 30 July that was corrected (3f600ed) —
"a MIRROR is only and exclusively the Lean-idiomatic native theorem … The
deep-embedded EvTrue-over-evalOpt theorem is a REPLAYED STATEMENT" — with
a surgical rename (driver_mirror% → driver_replayed%, hmirror →
hreplayed). But the corrected sense had itself been captured: "mirror" now
named the ACL2-shaped Lean restatements — SExpr lists, lexorderB chains,
isortL — which were being presented as results.

On 12 August Mike's original meaning was restored wholesale.
Imported/Mirrors/ became Imported/Waypoints/ (16 modules),
NativeMirrors.lean became WaypointCatalog.lean, and docs/LEXICON.md was
written as the canonical glossary — its preamble noting that the three
terms come first "because each has historically been used for the others'
referents":

> **Replayed statement** — the deep-embedded theorem the driver produces …
> the unit of the replay METRIC. Never user-facing.
> **Waypoint** — an ACL2-like Lean restatement decoded FROM a replayed
> statement … **Never a result**: presenting a waypoint as a top-level
> theorem is forbidden — *the historical failure this lexicon exists to
> prevent*.
> **Mirror** — the PRODUCT, and the only thing the word means: a
> Lean-idiomatic theorem with ZERO ACL2 notions … A user of mirrors knows
> nothing about ACL2 and never needs to.

The scoreboard had been mistaken for the score. Naming it stopped that.

The same day, the master plan set the two-track end state and pointed at a
file that did not yet contain a single theorem: "The mirror spec
(ACL2Lean/Mirrors/Sorting.lean, 13 Props) is the definition of done for
sorting." And hours later, the pathfinder arc delivered **THE FIRST
MIRROR** — app_assoc_int, proved via ACL2 replay, #print axioms clean at
{propext, Classical.choice, Quot.sound}. Not sorting. Deliberately the
smallest possible slice, "the project's original examples," so the route
could be proved before the aperture widened.

Two days later Mike wrote the four-line canon: no Lean-side theorems
specific to each example; all mirrors proved completely; mirrors are
idiomatic Lean with zero ACL2 taint; the proofs are accomplished by
replaying the ACL2 theorems. It was cited as a binding priority rank in
charters from that day — and, the end-of-branch audit found on the 16th,
**defined nowhere**. It was persisted into CLAUDE.md that day.

## Chapter 9 — The sprint (2026-08-14 17:10 → 2026-08-16 14:49)

Forty-five and a half hours, twelve parallel executor lanes, one goal:
close every replay frontier and every piece of qualification debt.

| metric | sprint start | sprint end |
|---|---|---|
| golden | 113/116 (84 uncond + 29 cond) | **116/116 (116 uncond + 0 cond)** |
| FAIL rows | 6 | **0** |
| row conditions (tp:/total:/rule:/linear:) | 106 | **0** |
| sorries | 6 | **0** |

Somewhere around 19:38 on 15 August, a cross-book transfer landed and the
log records the line Mike had named as the win state two days earlier:
**ZERO SORRIES IN THE REPOSITORY.** The class has been empty ever since.
Two of the sprint's own premises were refuted mid-flight by measurement —
one "emission gap" turned out to be records that a single-line grep had
missed because they were line-wrapped. The trip report files that under
"footguns" rather than "lessons," which is the correct genre.

## Chapter 10 — The last climb, and one very bad morning (2026-08-17 → 08-18)

With the metric layer finished, the product layer could finally run. Waves
2a through 2g, in six days:

- **2a–2b** — the transfer kit's squares: 8 → 19 → 23 live isomorphism
  squares, the complete definition inventory covered.
- **2c (17 Aug)** — **THE FIRST SORTING MIRRORS**: isort_ordered_int and
  msort_ordered_int are theorems, trio-clean, no extra hypotheses.
  Products 6 → 8.
- **2d** — ordered_perm_unique_int, the first hypothesis-carrying product.
  Products 9. The wave also reported something new: "the mirror machinery
  is now AHEAD of the waypoint layer for the first time."
- **2e** — qsort_ordered_int + qsort_perm_int. Products 11.
- **2f — the reshape.** Three waves had reported machinery frontiers; the
  reshape doc found they were one defect in the **spec**. The
  target-property section had accreted to 13 Props "from what each wave
  happened to be aiming at," never checked against the corpus in either
  direction — while being the definition of done, i.e. a claim in its own
  right. A mechanical extraction of every (:DEFTHM …) row from the eleven
  sorting logs — **75 rows, partitioned 16 / 38 / 11 / 8 / 2** into result
  tier, support tier, type-absorbed, encapsulate constraints, and
  collapsed-into-a-result — rebuilt the section as a **bijection** against
  the 16. isort_perm had been blocked not by machinery but because *the
  book does not prove it*. perm_iff_howMany's → direction appears in no
  defthm in the corpus; closing it in Lean would have been
  List.Perm.count_eq, the ornamental-import antipattern. Thirteen Props
  became sixteen; ten rows moved; **five landed as products immediately**.
  Mike: "Agree on all." Products 11 → 15.
- **2g** — the last two generic machinery items (a world-function measure
  row; the functional-instance pre-pass). Sorting 11 → 13 of 16;
  **products 15 → 19**.

And on the morning of 18 August, at 07:15:45, ~/.gitconfig became
unreadable to the sandbox. Lake's git check misread the state, fired its
"URL changed → delete and re-clone" remedy inside a worktree, and deleted
.lake/packages/mathlib — which, because worktrees symlink the packages
directory, was the *main tree's* checkout. The re-clone then failed:
GitHub is not in the sandbox allowlist.
docs/notes/2026-08-18_mathlib-incident.md is a model of its genre — root
cause evidenced, containment verified in-sandbox, recovery commands
written out for a human to run outside, and the honest state at pause:
docs-only work, no build possible. The wave-2d commit made that morning is
labelled a WIP below fast-gate tier, with "re-verification owed the moment
the toolchain is restored." Nobody claimed green. Destruction at 07:20; a
full claim gate green at 20:05 the same evening — about thirteen hours.

## Chapter 11 — The product bar, and the shop window (2026-08-18)

Two more corrections landed the same day, and together they are the last
movement of the story.

**The yank.** In the morning, an eval lane landed two new products, on
rulings Mike had given that same morning. In the afternoon he reversed
himself (docs/notes/2026-08-18_eval-rulings.md, verbatim):

> yes, let's yank the eval things - they don't really fit with this
> philosophy. **The aim is for the top level mirrors here to be truly
> worthwhile Lean theorems (even if small).**

That is the **product bar**, and it was applied retroactively rather than
letting the morning's blesses stand. Two consequences, both binding: *"Is
the book worth admitting" is a PRIOR question to the bijection* — "an
impeccably bijective rendering of a theorem no Lean reader would stop for
is still not a product" — and *books greened for capability stay at the
waypoint layer*. An approved transport-table widening was reverted
byte-identical alongside them, because "a transport-table row with no
consumer is precisely the project's banned anti-pattern." The removal was
a new commit on top of the one that landed them: "**the
blessed-then-yanked sequence is the honest record.**"

It cost the very next lane its output, immediately and by design. The
broadening lane's summary line: "**the MACHINERY and the METRIC landed;
NEITHER candidate product was admitted to the shop window.**" Two Props
were drafted, proved via replay, trio-clean, presented — and refused. What
*did* land was real: LiftingRel.lean took the decode layer past its
EQUAL-only frontier, and five catalog rows went .pending → .native. The
corollary the note draws for future lanes: **"'it greened cheaply' is not
an argument for admission."**

**The reclassification.** The close-out arc charter opens with Mike's
direction, verbatim: "our next arc should be fixing bsort_is_isort (and
then we're done!)" Its item 0 removes sorter_unique — 16 → 15 Props — and
the way it was removed is the project in miniature. The charter's own
justifying premise (that the theorem was encapsulate-internal) was made a
**binding pre-check**, and the pre-check *refuted it*: in equisort.lisp
the second encapsulate closes at line 102 and strong-ssortfn1-is-ssortfn2
sits at line 104, outside it, top level, not local; the consumer book's
log records it as :SOURCE :INCLUDE-BOOK and installs it as an active
rewrite rule; and the reshape doc's own inventory places it in the result
tier. **The asymmetry did not exist. The edit was not made.** Put back to
Mike with the refutation: "still remove, this seems fine" — and the
removal was re-ruled on the argument that actually holds: it is an
*instantiation device*, consumed downstream only via :functional-instance,
and its three instances already have Props.

The reshape doc's closing self-limitation is the last word on gates, and
deserves to be: the bijection "is checked by reading the extracted
(:DEFTHM …) rows against the Props — **by review, not by a gate**… a
census gate over 75 rows is exactly the fragile gate-cruft the
two-standard rule says to delete rather than write."

## Chapter 12 — Where it stands tonight

**Fifteen Props; thirteen are theorems.** Precisely: thirteen
mirror_transport% declarations in MirrorProofs/Sorting.lean, each followed
by a #guard_msgs-pinned receipt reading exactly
[propext, Classical.choice, Quot.sound], plus six in Basics.lean —
**nineteen products** in the layer. Zero sorry anywhere in ACL2Lean/ or
Tests/.

The two outstanding are not the same kind of thing.

**permWitness_complete** cannot arrive at Int as currently spelled, and
this was settled by kernel refutation rather than argument: the
element-result square is false at the junk arm for *any* embedding
(SExpr's default is nil; intEmbed.enc is never nil), with the disproof
permWitness [1] [1] by decide, and permWitness returning the junk value on
the entire Permuted half. It is not a proof waiting to be found; it is a
*definition* waiting to be refined — item 2's Option α row (none ↦ nil,
some a ↦ enc a), which eliminates the junk arm and the [Inhabited α]
alike. Mike: "morally the same theorem."

**bsort_is_isort** is the last line of the coverage golden: a tau leaf
carrying ASSUMED:dp-fact, which driver_replayed% correctly refuses to
register. Wave 2g wrote the consuming decode, measured that it closes, and
**reverted it rather than ship it unwired**. The charter's plan was a fork
round-trip: go back to the Lisp, instrument the leaf, emit its obligation.

That plan turned out to be wrong, in the best possible way. Today's
diagnosis found that **the fork already emits the record** — :TAU-BASIS,
shipped as part of the fork batch ruled on 10 August. The residual gap is
entirely Lean-side: an eligibility gate that fails to match. And Mike's
ruling on how the leaf should close is the sentence the whole eight months
was built to earn: the obligation discharges by **citing TRUE-LISTP-BSORT,
which the replay has already proved** — *"we should ALWAYS replay ACL2
when we have the material at hand."*

---

## What the finished thing actually is

Open ACL2Lean/Mirrors/Sorting.lean and the first thing you notice is what
isn't there. Five hundred and forty-eight lines, and not one import — not
Mathlib, not Batteries, not the replay machinery; the file elaborates from
Lean's core prelude alone. No SExpr, no lexorder, no evalOpt, no sorry. A
TotalOrder class with five fields, deliberately not Mathlib's LinearOrder.
Seventeen definitions named off the ACL2 book and Lean-cased. Eight
theorems, every one of them a termination obligation Lean's kernel demands
before the definitions may exist — the last being bsort's bad-pair
decrease, which is the same obligation ACL2 discharges to admit BSORT. And
then fifteen named Props, each with a docstring naming the ACL2 theorem it
mirrors: ∀ (xs : List α), Ordered (qsort xs). ∀ (a : α) (xs : List α),
howMany a (msort xs) = howMany a xs. ∀ (xs ys : List α), Ordered xs →
Ordered ys → (xs = ys ↔ Permuted xs ys). Thirteen are theorems today, each
with a pinned receipt reading exactly [propext, Classical.choice,
Quot.sound].

Six hundred and forty lines of product, standing on seventy thousand lines
of machinery — 38,771 in the replay driver alone, 16,372 in the lifting
and waypoint layer, plus 228 instrumentation tags in a forked theorem
prover, 91 captured proof logs, 61 authored pattern books, a 122-row
waypoint catalog with zero entries in the forbidden-debt class, and 27
numbered fidelity bugs found by pointing the interpreter at real ACL2 and
diffing the output. That ratio *is* the result. A reader who wants to use
these theorems reads the one file and trusts Lean's kernel — not the
instrumented prover, not the log parser, not the clause-tree
reconstruction, not the fuel-bounded interpreter, not the driver, none of
it. Because the statements are written in Lean's own vocabulary and the
proofs are kernel-checked terms, all seventy thousand lines are untrusted
by construction: a bug anywhere makes the file fail to compile and can
never make it lie.

Eight months and 74 working days bought that, and not because sorting is
hard. Mathlib already proves most of these; a competent Lean user could
hand-write all fifteen in a week. But hand-writing them would have proved
nothing whatsoever. The point was that they arrived by replaying J Moore's
actual proofs, node by node down the clause tree ACL2's waterfall really
produced — no omega shortcut past a step ACL2 recorded, no library lemma
standing in for content the book proves, no sorry presented as done. Every
rule in CLAUDE.md is scar tissue from a specific day this went wrong and
someone wrote it down: a reset that threw away a day's work because it had
been validated against synthetic nodes and replayed zero real ones; a
green scoreboard that turned out to be about λx. 0; a completion commit
made against a red build with the failure hidden behind a pipe; a coverage
number that fell from 78% to 7% the first time anyone pointed it at
unfamiliar books; two products blessed in the morning and yanked in the
afternoon because "an impeccably bijective rendering of a theorem no Lean
reader would stop for is still not a product."

Which is why nobody is claiming fourteen tonight — and why the last
obstacle is such a fitting one. For a day it looked like a missing
sentence of Lisp in a forked prover. It isn't. ACL2 had already written
the record down; the fork has been emitting :TAU-BASIS since a ruling on
the tenth. What was missing was on our side of the line — a gate that
didn't recognise what it was being handed — and the fact needed to close
the leaf turns out to be a theorem the replay had already proved and set
down a few rows up the same scoreboard. "We should ALWAYS replay ACL2 when
we have the material at hand." Eight months of building a machine that
refuses to guess, and the final step is the machine learning to read what
was in front of it the whole time. When it does, and when the witness gets
its Option, a Lean reader will hold fifteen ordinary theorems about
sorting lists — every one of them proved by a program that was never
trusted for a moment.

---

### Appendix — the rules as strata

CLAUDE.md's sections can be dated by git log -S, and the shape tells the
story better than prose does.

| Date | Stratum |
|---|---|
| 2026-03-21 | **File created** by the silent-failures audit (~82 swallow sites). "Never silently skip malformed input." |
| 2026-03-28 | "The proof checker does NOT do inference." |
| **2026-06-06** | **The big bang** — one commit, the day after the reset: the *entire* Fidelity section and the *entire* Working-discipline section. |
| 2026-06-09 | Carve-out ratified; TRACE-LOG convention; "Approval is never inferred from an earlier 'merge it'." |
| 2026-06-10 | L1 / L2 / L3 invariants. |
| 2026-06-12 | Audit plans need sign-off before spawning subagents. |
| 2026-07-07 | TOTAL ACL2 MASQUERADE; the interpreter as a PEER of ACL2. |
| 2026-07-08 | docs/BUGS.md as the single canonical index. |
| 2026-07-22 | Synthetic **books** yes, synthetic **artifacts** never. |
| 2026-07-28 | Sandbox merge protocol (local just ci, not remote CI). |
| 2026-07-30 | Terminology fix #1: mirror = native theorem; the deep embedding = replayed statement. |
| **2026-08-05** | **Goal escape-hatch rule** ← the drift scare. |
| **2026-08-07** | **Two-tier gating** ← the masked red build. Module-size norm. |
| **2026-08-11** | **The two-standard rule** ← audit inflation / gate whack-a-mole. |
| **2026-08-12** | **Terminology restoration**: replayed statement / waypoint / mirror. |
| 2026-08-13 | Vocabulary practice; the zero-sorryAx win state. |
| **2026-08-16** | **The four-line canon**, finally written down. |

March says *don't swallow input*. One catastrophic June morning writes the
whole fidelity core in a single commit. June and July accrete frontier and
instrumentation rules. Early August is all **process** rules, each
traceable to a specific self-inflicted failure. Mid-August is **vocabulary
and product** rules — the point at which the project stopped policing only
its proofs and started policing what it *calls* things and what it
*counts* as a result.

*Method note: read-only research; every count from files, greps, or
verbatim commit text. Two honest gaps: no document narrates "the masked
red build" as one named incident (the primary sources treat it as two,
separated above), and the 2026-06-09 merge rule and 2026-06-12 audit-plan
rule read as corrections to inferred permission but have no linked
postmortem — that causal story is inferred from wording.*
