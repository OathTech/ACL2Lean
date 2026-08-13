# The validator/lifter arc — draft charter

> **TERMINOLOGY (added 2026-08-13).** This is a dated record. "Mirror"
> below means **WAYPOINT** in today's vocabulary (`docs/LEXICON.md`).
> Where this file conflicts with the lexicon, the lexicon wins.
>
> **RETRACTED — item 1's "ground truth" clause.** Its definition of
> *mirror* ("the Lean-idiomatic native theorem … `Imported/`,
> `NativeMirrors`") pointed at what is now the WAYPOINT layer, and a
> waypoint is METRIC, **never a result** and never ground truth for the
> reasoning. The canonical definitions are the lexicon's: a MIRROR lives
> in `ACL2Lean/Mirrors/` with zero ACL2 notions. Item 1 is retained below
> only as the dated record of what was believed on 2026-07-30.

**Status: DRAFT (2026-07-30), to be ratified at arc start. Direction approved
in the MDD conversation of 2026-07-30 ("audit, merge, then do the
validator/lifter industrialization work"); the details below are the working
plan, not yet MDD-pinned.**

## Why this arc

Two threads converged at the perm-lane merge point:

1. **Terminology + ground truth (MDD, 2026-07-30).** A *mirror* is only and
   exclusively the Lean-idiomatic native theorem proved FROM a replayed
   statement (`Imported/`, `NativeMirrors`) — the sole first-class artifact
   establishing that a replayed theorem means what the user intends. A
   *statement pin* anchors the embedded statement TERM to the `.lisp`
   source, but its meaning still lives inside `evalOpt`; only a mirror
   closes the semantic loop. Validation books therefore want mirrors not as
   showcase but as **ground truth for the reasoning** — there is no other
   first-class notion that establishes the theorems are what the user
   intends.
2. **The validation-surface survey (2026-07-30, Explore agent).** Full
   inventory of every validation surface and its anchoring strength. The
   result: 43 of 65 green sweep rows have no statement pin anywhere; the
   native-mirror scoreboard's mirror-only/PENDING lists accumulate
   silently; several structural gaps (below).

## The two workstreams

### W1 — validator (the survey's prioritized gap list)

Verbatim priorities from the survey (each anchored in its report; the agent
transcript has file:line detail):

1. `fsq-unfolds` statement pin — the ONLY gate on the lambda/beta replay
   path pins the cond-set, not the statement.
2. The 8 green `sorting/qsort` dependency rows with no pin (HOW-MANY-APPEND,
   HOW-MANY-FILTER-1, CAR-APPEND, ALL-REL-FILTER-1/2, ALL-REL-RM-1/2,
   PERM-IMPLIES-EQUAL-ALL-REL-2) — the pinned headline rows REST on them.
3. TRUE-LISTP-ISORT + HOW-MANY-ISORT (near-zero marginal cost — the pins
   file already parses that development).
4. msort's 3 green rows (no pin of any kind on the whole book).
5. ordered-perms' 4 green rows.
6. Termination-replayed-statement status pushed into `res.lines` (the class
   is invisible to the golden today; only QSORT has any anchor).
7. Build-failing axiom gate for DriverTests' replayed-statement constants
   (11 informational `#print axioms` — they bypass Runner's axiom filter).
8. Statement pins for the induction-scaffold books 11–16's green rows
   (each the only corpus instance of its scaffold class).
9. 17-rule-application's two rows.
10. Tamper coverage for the emitted `:DEFUN` body / justification joints
    (the axis every statement pin concedes — the gen-world gap's only
    interim control).
11. Message-pin the four `#expect_driver_fails` negatives (TamperTests'
    substring discipline).
12. `diff-test` into local `just ci` (or a fast subset) — the trusted-core
    fidelity gate currently runs only in remote CI.
13. NFIX's gz_def body `#guard` (the one unpinned d4DefFacts fn).
14. A recon-level golden for `recon-tests/*.dump` (recon shape drift that
    still replays is invisible today).
15. Retire or wire `Verify.py` (unreferenced comparator at repo root).

Also from the survey: `check-pattern-map.sh`'s reverse direction only scans
`p1|p2|cov` tokens — p3–p7 books are exempt from the map-mentions-exist
check; the forward direction is satisfied by prose mentions. Tighten.

### W2 — lifter industrialization (#63, sequenced 2026-06-12; triggers now live)

Roadmap H2's metric: **~10 hand-written lines per imported theorem**. The
lift layer is downstream of the kernel-checked replayed statement, so
automation here has ZERO fidelity/soundness surface — a wrong mirror fails
to elaborate or visibly states the wrong thing. Items (from TODO #63):

- (a) **NativeMirrors catalog as a COVERAGE GATE**: every driver-replayed
  theorem gets a native entry or an explicit PENDING(frontier) marker —
  the ratchet that stops "replayed but never lifted" accumulating (the
  survey's headline finding, now enforceable).
- (b) **Rep transformers** (`Rep α → Rep (List α)`) + exec-def GENERATION
  from World bodies.
- (c) **`lift_decode` automation** — the per-theorem formula-spine walk
  composing `Implements` facts is the dominant hand cost (the assembly
  glue); an elab recursing the formula (as `proveConv` does) emits it,
  fail-closed. This is what collapses per-mirror cost from ~300–700 lines
  to ~10 + the irreducible per-NEW-fn `Implements` induction.
- (d) **Guarded `Implements`** (recognizer hypotheses from emitted TP
  facts) for conditional fns — needed beyond the total-list-fn class.

**Driving examples** (the #63 discipline): mirrors for the validation books,
in order p7 (ln/dub — cheapest, and rung 2's ground truth) → p5 (dupp/rep;
implies-headed decode) → p3 (ordd/ins over LEXORDER — native list structure,
trusted-core element order). One meaningful mirror per book (p7's defcong
and equivalence theorems have degenerate native content). Second exercise:
the scoreboard's PENDING natives (app-nil, rev-rev, the len2 family) share
the same function classes and should fall out of the machinery.

## Sequencing within the arc

Suggested (to ratify): W2(c) lift_decode with p7 as the driving example
first (it immediately produces the arc's headline artifact — rung 2's
ground-truth mirror), then W1 items 1–3 + 6–7 (cheap, high-value), then
alternate. W1 items 10/12/14 are larger and may split out.

## Hygiene items folded in

- The naming fix (2026-07-30, commit 3f600ed) left dated docs/notes using
  "mirror" for replayed statements as historical record — no action, but
  new prose must follow CLAUDE.md's terminology note.
- Queued perm-lane leftovers (TODO merge-point pin): the type-alist relief
  class (LEXORDER-TRANSITIVE marker), the linear-in-simplify emission gap
  (p6), HOW-MANY-QSORT's J6 solidify frontier — these are REPLAY-side and
  belong to a separate arc unless one blocks a driving example.

## Inc-0 working state (2026-07-30, ground truth established)

The p7 mirror's ingredients, verified against the artifacts:

- **LN's emitted body is EXACTLY `lenBody "LN"`** — ACL2 normalized the
  source's `endp` away at admission: `(:DEFUN LN :FORMALS (X) :BODY
  (IF (CONSP X) (BINARY-+ '1 (LN (CDR X))) '0))`. So
  `Lifting.corr_len_enc w "LN"` instantiates DIRECTLY (h_fn by decide on
  the derived world; no new schematic needed).
- **DUB's body is a MAP-CONST shape**: `(IF (CONSP X) (CONS '0 (DUB (CDR
  X))) 'NIL)` — needs ONE new name-generic schematic in Lifting:
  `mapConstBody (c : SExpr) (fn : String)` + `corr_mapconst_enc`
  (conclusion: Conv of `(app1 fn a)` to `enc (xs.map (fun _ => c))`),
  template = `corr_append_enc`'s induction, simpler (unary).
- **The tp:LN discharger**: `SimpleWorld.drv_tp_mylen` is the exact
  corollary shape but HARDCODED to MY-LEN (my_len_sym/my_lenBody,
  via `dis_mylen_int_nonneg`) — generalize to a name-generic
  `drv_tp_len (w) (fn)` over `lenBody fn` (industrialization dividend:
  every len-class fn's TP discharges from one lemma; LN and MY-LEN both).
- **Setup pattern** (Entry-1, NativeMirrors:70-135): include_str the p7
  log → `p7Dev` → `derive_world p7WorldD` → `driver_replayed% p7Dev
  p7WorldD "p7-target"` → discharge tp:LN via the generic discharger →
  instantiate at `X ↦ enc l` → Conv both sides via corr_mapconst_enc ∘
  corr_len_enc → `native_of_replayed_equal intRep` →
  **the mirror: `∀ l : List SExpr, (l.map (fun _ => qInt-0)).length =
  l.length`** — stated and proved FROM the replayed P7-TARGET.
- File: `ACL2Lean/Imported/P7Cong.lean` (new), imported by
  NativeMirrors or the Imported root; axiom-gate via the throwing
  `run_cmd` pattern (NativeMirrors:738), NOT bare `#print axioms`
  (survey gap 7).
