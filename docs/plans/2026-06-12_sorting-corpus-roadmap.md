# The sorting corpus as driving target — validation + roadmap (2026-06-12)

**Decision (MDD, 2026-06-12):** instead of the grep-sweep version of G6, adopt
ONE real book development as the driving target: `acl2/books/sorting/` — the
classic J Moore *sorts-equivalent* development. Every gap that matters for a
real book surfaces in dependency order; "what to build next" is whatever the
corpus needs next. The mechanism-frequency sweep is demoted to a later
validation checkpoint before claiming the CORE tier.

## 1. Corpus validation (done, this branch)

**Provenance.** All sample copies were byte-identical to upstream
`acl2/books/sorting/` (and every other non-authored file under `acl2_samples/`
was byte-identical to its upstream book — sorting ×10, workshops-2009 ×2,
apply-model ×2, bakery ×2, die-hard ×2, execloader, gaussian ×2). Per MDD:
duplicates DELETED; the submodule is the canonical source. `acl2_samples/`
now holds only authored content (`simple.lisp`, `recon-tests/`, `books.txt`)
plus captured (gitignored) logs. `capture-proof-log.sh` gained `OUTDIR` so
submodule-sourced books log into `acl2_samples/` without dirtying the
submodule; `books.txt` lists the full include-closure in dependency order;
`Workbench.lean`'s probe list points at the submodule.

**Freshness.** Recaptured every book from the submodule paths with the current
instrumented image. orderedp/how-many/perm/isort/msort/bsort/qsort recaptures
were BYTE-IDENTICAL to the Jun-11 logs (capture is deterministic; those were
fresh). convert-perm-to-how-many / ordered-perms / sorts-equivalent were stale
(March-era) — replaced; equisort was missing — added. A junk
`isort.proof-log.proof-log` was deleted.

**Capture caveat (known, minor):** the capture script's qed/defthm warning
heuristic misfires on include-book books — included theorems emit `:DEFTHM
… :SOURCE :INCLUDE-BOOK` with no `:QED` (include skips proofs), and
commented-out defthms inflate the source count (`perm-isort` is commented out
upstream — isort is genuinely 3/3). Fix: count only `:SOURCE :LOCAL` events
against uncommented source forms. Tracked below (R0c).

## 2. The corpus, measured

| book | own thms | includes | notes |
|---|---|---|---|
| orderedp | 0 (defuns) | — | reconstructs today |
| how-many | 0 (defuns) | — | reconstructs today |
| perm | 8 | — | `(defequiv perm)` — USER EQUIVALENCE (L2's first real exercise) |
| convert-perm-to-how-many | 13 | perm, how-many | the counting argument |
| ordered-perms | 6 | perm, orderedp | |
| equisort | 14 | perm, ordered-perms, convert… | ENCAPSULATE (2 constrained fns) |
| isort | 3 | perm, ordered-perms, convert… | |
| msort | 8 | same | evens/odds split recursion |
| bsort | 8 | ordered-perms, convert… | bubble pass |
| qsort | 12 | same + **arithmetic-3/extra/top-ext** | 6931 rewrite steps; FORCING present |
| sorts-equivalent | 3 | equisort + the four sorts | **functional instantiation** |

≈ 75 own theorems. Forcing rounds appear ONLY in qsort + sorts-equivalent
(G4 is needed exactly there, not before).

## 3. Frontier inventory (measured today, per pipeline stage)

- **Stage 2/3 — the include-book wall (gates 8 of 11 books).** Included events
  arrive with `:SOURCE :INCLUDE-BOOK` and no proof/admission payload; the
  parser correctly hard-fails (`DEFUN rm: recursive … but no
  :TERMINATION-CLAUSES`). The discriminator is already in the log format.
- **Stage 4 — perm reconstruction:** `rewriting-equivalence node (equal x1 a)
  matches no clause hypothesis (assume-true-false…)` — a new linking class
  (hypothesis from the type-alist rather than a clause literal).
- **Stage 5 — translator silently DROPS `include-book`/`encapsulate`**
  (pre-dates the fail-closed rule; isort's generated world has only
  insert+isort while its mirror statements reference orderedp/how-many).
  Discipline fix first: hard-fail on unknown top-level forms.
- **Stage 6 — `lexorder` missing** from the evaluator (insert's comparator;
  ACL2's total order on objects — needs faithful semantics + differential
  tests). Scan for further missing primitives as books open up.
- **Stage 7 — known replay frontiers, now corpus-driven:** G5 induction shapes
  (msort/bsort/qsort schemes), theorems-as-rewrite-rules (pervasive — every
  later book consumes earlier books' lemmas), `(defequiv perm)` congruence
  runes (the L2 abstract-R machinery's purpose), forcing (qsort), the
  arithmetic-3 foreign-rune question (qsort), functional instantiation
  (sorts-equivalent endpoint).

## 4. Roadmap (dependency-honest sequencing)

- **R0 — scoreboard + hygiene (immediate).**
  (a) Wire orderedp/how-many/perm logs into the coverage harness — the gate
  grows its first real-book rows, perm's 8 theorems land as named frontiers.
  (b) Translator: hard-fail on `include-book`/`encapsulate`/unknown top-level
  forms. (c) Include-aware capture warnings (`:SOURCE :LOCAL` only).
- **R1 — perm replayed (first real book).** `lexorder` primitive (+
  differential tests); the assume-true-false linking fix; whatever G5 shapes
  perm's 8 trees actually take; first contact with `defequiv`/congruence
  runes (L2 instantiation at a user relation).
- **R2 — include-book architecture (the big unlock; design doc required
  before building).** Per-book Developments composed in dependency order —
  an included book's theorems are ALREADY-REPLAYED mirror theorems imported
  as rules; included defuns extend the World with identity validated against
  the source book (this mirrors ACL2's own certificate semantics, and L3
  world-parametricity is what makes the composition well-typed). The
  alternative (re-emit admission data at include time, one giant log) is
  rejected: it re-proves nothing and breaks the one-log-one-book model.
- **R3 — the counting argument:** convert-perm-to-how-many + ordered-perms
  (19 theorems; expect `:use`-style hint shapes and G5 growth).
- **R4 — the three elementary sorts:** isort, msort, bsort own theorems
  (G5: evens/odds and bubble-pass schemes).
- **R5 — qsort:** forcing rounds (G4 lands here, driven by real logs) + the
  arithmetic-3 question — replay only the foreign runes that actually FIRE,
  importing each as its own replayed lemma or hard-failing with a named
  frontier (no blanket trust of an uncertified include).
- **R6 — equisort:** encapsulate-as-constraints (CORE-tier item; constrained
  functions enter the World abstractly — the L3 dividend).
- **R7 — sorts-equivalent:** functional instantiation (EXTENDED tier; the
  endpoint). Tier call to ratify when we get here: either build the
  `:functional-instance` recipe or import the four `X-is-isort` theorems
  conditionally.

Each step is measurable on the coverage table; "the corpus needs it" replaces
speculative prioritization. G5 stops being a monolith — it lands incrementally
inside R1/R3/R4 driven by the real schemes; G4 lands inside R5.

## 5. What this corpus does NOT exercise (honest residual)

Guards/`verify-guards`, `defun-sk`/`defchoose`, metafunctions/clause
processors, stobjs, `apply$`/`loop$`, mutual recursion at scale. The
mechanism-frequency sweep (old G6) remains the validation step before any
CORE-tier completeness claim.

## Progress + ratified sequencing (2026-06-12, MDD)

- **R0 DONE** (branch mdd/sorting-r0): perm on the scoreboard (corpus
  37→45; EquivSource reconstruction extension), translator fail-closed,
  include-aware capture warnings.
- **R1 IN PROGRESS:** the multi-case induction scaffold landed (G5 v2,
  docs/plans/2026-06-12_multicase-induction.md — strong induction +
  decision-tree dispatch + N-var IH bridge; all 17 prior REPLAYED rows
  byte-identical). The scheme wall fell; the measured remaining perm
  walls: (a) MULTI-LITERAL PUSHED CLAUSES (4 theorems; P over the pushed
  disjunction, per-(alist×literal) children, disjunctive-IH elimination),
  (b) clausify-on-multi-literal inside case children (perm-cons,
  perm-transitive), (c) executable-counterpart terminal, (d) the
  .segment/.branchTest conditional-congruence machinery
  (perm-is-an-equivalence).
- **(c) PARTIAL — comm-rm split into two walls (2026-06-14, branch
  mdd/perm-exec-counterpart):** exec-counterpart steps + closer DONE
  (commit 7fe4d38; faithful ground re-execution, orthogonal/kept). Behind
  it, comm-rm hit a SECOND wall — `sublis-var` display-folding of if-simp
  branches (logging-only per ACL2's own comment; not a missing-reasoning
  gap) — now **DEFERRED**: the A/B/C fix is a judgment call that can't be
  measured until earlier walls fall (live-branch-fold frequency unknown).
  Full mechanism + options + keep/throwaway rationale:
  docs/notes/2026-06-14_exec-counterpart-and-folding-wall.md. comm-rm
  stands 1-of-2 done at a clean named frontier.
- **NEXT: clausify-on-multi-literal** (perm-cons, perm-transitive) —
  chosen over the 4-theorem multi-literal-pushed induction as the smaller
  next step under the post-Fable buffer-against-mistakes mandate.
- **Lifter industrialization (RATIFIED sequencing):** after perm replays,
  a mirror-library sprint with the perm book as the driving example —
  the NativeMirrors catalog discipline extends to every newly-replayed
  theorem (native entry or explicit PENDING marker), plus the #63 items
  (Rep transformers, lift_decode elaborator, guarded Implements). The
  end-state test of the whole pipeline is theorems LIFTED into Lean;
  the replay→lift loop becomes the per-book cadence from isort onward.
