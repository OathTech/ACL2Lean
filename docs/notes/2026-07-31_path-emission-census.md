# Path-emission Phase-0 census (WIP — the sub-arc's deliverable 1)

Charter: docs/plans/2026-07-31_path-emission-subarc.md. This census
enumerates (A) every gstack `rewrite`-frame producer the fork's
`structured-rewrite-path` (rewrite.lisp:124) can observe, and (B) every
Lean-side mechanism that bridges gstack coordinates to the replay's
running term. STATUS notes mark what is verified vs still to check.

## How :PATH is produced today

`structured-rewrite-path` walks `*deep-gstack*` innermost-first,
collecting `(bkptr . fn)` for each `'rewrite` frame, where `fn` = head
of the frame's term (a lambda term anchors as `LAMBDA` under a
non-integer bkptr), and an INTEGER bkptr under a
`rewrite-with-lemma`/`rewrite-quoted-constant-with-lemma` parent is
rebadged `HYP`. All frames enter via `push-gframe 'rewrite bkptr term`
inside `rewrite` itself (rewrite.lisp:16946) — so the census reduces to:
who calls `rewrite` with which bkptr, and does the recorded term
coordinate survive into the replay's running term?

## A. Frame producers (rewrite-entry (rewrite … bkptr) sites)

VERIFIED (file:line, bkptr, meaning):
1. rewrite-args (rewrite.lisp:18035, bkptr = arg position int) — plain
   argument descent. Coordinates stable; the replay navigates these
   directly. NO divergence by itself.
2. rewrite's IF handling (rewrite.lisp:17096 via the test rewrite above
   it): test descends with bkptr 1; then `rewrite-if` on the REST.
3. rewrite-if branch descents (rewrite.lisp:17746 left bkptr 2, 17754
   right bkptr 3) — branches rewritten while the ORIGINAL if's frame
   remains on the gstack. DIVERGENCE SOURCE 1: if the test resolved,
   the replay's running term collapses the if but deeper nodes still
   carry the branch frame → the Lean `strip` mechanism.
4. rewrite-if-finish re-entries (CONFIRMED: 17713 left bkptr 2 /
   17718 right bkptr 3 are inside `rewrite-if-finish`,
   rewrite.lisp:17682) — re-rewriting already-rewritten branches.
   DIVERGENCE SOURCE 2: the re-entry walks the REWRITTEN branch under
   frames whose terms are pre-rewrite → the if-finish `strip'`
   arithmetic + or-collapse bridge. NOTE the fncall analog ALREADY has
   an explicit window: `BEGIN-INNER-REWRITE :KIND REWRITTEN-BODY`
   (observed in qsort.proof-log Subgoal 2-family) — the if-finish
   re-entry window is the MISSING twin, strong evidence the window
   idiom is the right extension.
5. rewrite-equal component descents (rewrite.lisp:7235 and
   17713/17718/17906/17907 area — `(rewrite left alist 2)` etc. under
   rewrite-equal; ALSO the synthesized `(car lhs)/(car rhs)`
   components via rewrite-args on the list `'((car lhs) (car rhs))`
   with alist {lhs, rhs} → bkptr 1/2 with SCRATCH redexes never present
   in the literal). DIVERGENCE SOURCE 3 → the Lean scratch-detection in
   `replayRewritesWith` (the rewrite-equal decomposition interpreter).
6. Definition/lemma body descents: rewrite.lisp:20547 (`body` under a
   lambda/let?), 20712 (bkptr 'body — rewrite-fncall's body descent),
   24416 (body, quoted-constant twin), 20858 (`rewritten-body` —
   RE-ENTRY of the rewritten body, the fncall analog of if-finish).
   DIVERGENCE SOURCE 4: body coordinates (`(BODY . IF)` frames) are in
   the DEFINIENS' coordinate space, not the literal's → the Lean
   `relativizeFrames` depth/boundary mechanism.
7. Hyp/RHS windows: bkptr ints under rewrite-with-lemma parents are
   rebadged HYP by structured-rewrite-path; RHS descends via
   rewrite.lisp:21011/21119/21151-family (`new-term`) and is bracketed
   by BEGIN/END-INNER-REWRITE window events (KIND HYP/RHS/BODY) the
   tree builder scopes with. Mostly WINDOWED already — the precedent
   the new emission extends.
8. Special forms (ALL CONFIRMED): HIDE (17153/17188 bkptr 1, in
   `rewrite`); IMPLIES (17216 arg1 / 17225 arg2, `rewrite`'s
   `(eq (ffn-symb term) 'IMPLIES)` branch, geneqv-iff both);
   double-rewrite (17274 bkptr 1 then re-entry with OUTER bkptr);
   'expansion — 17555 (`rewrite`, alist-binding transfer) and
   21012/21067 (`rewrite-with-lemmas`, expansion window incl.
   `(rewrite hyp alist 'expansion)`); lambda-body — 17402 (`rewrite`'s
   lambda application) and 20549 (`rewrite-fncall`); 20547 'body is
   `rewrite-fncall`'s definiens descent, 24416 its quoted-constant
   twin; 21248 arg 1 is `rewrite-linear-term` — its (rewrite … 1)
   frames ARE 'rewrite frames, so linear-context emissions (if any
   fire) carry them; whether the fork emits inside linear contexts
   needs a corpus grep before Phase 1 (replay handling TBD).
9. simplify.lisp:7210 (`atm` — rewrite-atm's literal-top entry, bkptr =
   the literal index) and rewrite.lisp:18751 (`relieve-hyp`'s hyp
   descent — rebadged HYP by structured-rewrite-path's parent check,
   scoped by the BEGIN/END HYP windows).

CONFIRMED ALSO: synp pushes sys-fn 'synp (14722) — invisible to
`structured-rewrite-path` (it collects only 'rewrite frames), so syntaxp
relief cannot perturb paths ✓; scons-term/exec emissions carry
:PATH NIL by design (clause-level folds — windowless, consumed
positionally by the branch-substitution fold loop, harmless ✓);
rewrite-atm's literal-top entry contributes the leading
`(<literal-index> . <literal-head>)` frame (simplify.lisp:7210;
observed as `(3 . O<)` in qsort Subgoal 2), which the tree builder
already strips at the literal boundary. STILL OPEN (pre-Phase-1, not
blocking the prototype): whether any corpus emission fires inside
linear-arithmetic contexts (rewrite-linear-term frames); the
relieve-hyp descent at rewrite.lisp:18751's exact bkptr conventions.

## B. Lean-side bridging mechanisms (to retire in Phase 1)

1. `relativizeFrames` depth/boundary (Reflect.lean ~230-267 + callers):
   consumes BODY-coordinate frames per unfold depth. Retires if body
   windows carry their input term (the window precedent).
2. `strip` lists (NodeCore `replayRewritesWith` root-if collapses +
   `relativizeAndStrip` Reflect.lean ~396): branch frames for
   already-collapsed ifs, matched-and-dropped BY COUNT — the mechanism
   whose composition gap walls ORDEREDP-APPEND.
3. if-finish `strip'` arithmetic (NodeCore ~4185-4210:
   `steps.map (argIdx+1)`) + the or-collapse bridge's test-prefix
   re-composition (chainPrefix scan).
4. `bridgeIfNegTestSwap` path juggling (swapped-p normalization at the
   node's path).
5. The rewrite-equal SCRATCH detection (the `[.arg i CAR/CDR-of-side]`
   shape test in `replayRewritesWith`) — under new emission these
   should arrive in an explicit component WINDOW carrying the
   synthesized redex, killing the shape test.
6. `Preprocess.lean` ~301 pathStepsFromFrames consumer (preprocess
   chains) — same coordinates, same retirement.

## Candidate emission semantics (deliverable 2 — DRAFT, to be written
against every census row before the MDD checkpoint)

Extend the BEGIN/END window idiom (BEGIN-LITERAL / BEGIN-INNER-REWRITE
already scope hyp/rhs/body): emit a window per COORDINATE-SPACE change —
(a) if-branch descent windows carrying the branch's input term and
position (test/left/right); (b) body windows carrying the instantiated
definiens; (c) rewrite-equal component windows carrying the synthesized
component redex; (d) if-finish/fncall re-entry windows carrying the
re-entered (already-rewritten) term. Steps inside a window carry :PATH
relative to THAT window's input term only. The replay then never
computes positions across a collapse: window entry hands it the exact
term the chain walks, verbatim from ACL2.

Cost sketch (deliverable 4 — TO FILL after the prototype): fork —
window push/pop at the 4 window classes (all already have TRACE-LOG
regions nearby); tree builder — nest by the new windows (the BEGIN/END
scoping code exists); replay — navigation becomes window-local
(pathStepsFromFrames unchanged in kind, callers lose the
relativize/strip plumbing).

## Prototype target (deliverable 3)

qsort.proof-log ORDEREDP-APPEND, Subgoal *1/2'-family literal 5: the
`definition:ALL-REL (ALL-REL 'LTE A E) => 'NIL` node inside nested
if-finish children whose frames `[1 IF, 2 IF, 1 ALL-REL]` navigate
pre-collapse structure. Success = the node arrives inside an if-branch
window whose input term contains the redex at the emitted (window-local)
path, and a hand-run of the window semantics over the whole literal-5
chain needs NO strip accounting.

## Deliverable 2 — emission semantics v2 (WINDOWED PATHS), reviewed per row

**Extension point found:** the BEGIN/END-INNER-REWRITE machinery lives in
the `rewrite-entry` macro itself (rewrite.lisp:7475-7560), keyed on the
QUOTED bkptr being one of `(rhs body lambda-body expansion
rewritten-body)`. Windows currently carry NO term payload — the spec
below adds one and extends the kind list. This is a small, uniform
change at ONE macro plus the rewrite-if/rewrite-equal call sites.

Semantics:
1. **`:TERM` payload on every window.** BEGIN-INNER-REWRITE gains
   `:TERM <instantiated input term>` — the term the descent rewrites,
   with the rewrite alist APPLIED (`structured-sublis-var-plain`, the
   same instantiation idiom the constant-test emitter already uses;
   audit 2026-07-26 F3 is the precedent for why plain instantiation,
   not mcons-term folding). The lazy `(term . alist)` pair is the
   correctness risk — fold-back audit Reviewer A's whole brief.
2. **New window kinds, exactly where a divergence class exists** (rows
   3, 4, 5 of the census; minimality keeps unaffected paths
   byte-identical):
   - `if-left` / `if-right` — rewrite-if's branch descents (17746/17754),
     term = the instantiated branch. Retires the `strip` lists (row B2).
   - `rewritten-if` — rewrite-if-finish's re-entries (17713/17718),
     term = the re-entered branch. The REWRITTEN-BODY twin; retires the
     if-finish `strip'` arithmetic (B3).
   - `equal-component` — rewrite-equal's synthesized component descents,
     term = the instantiated `(CAR lhs)`-style component. Retires the
     scratch shape-detection (B5) — the decomposition interpreter keeps
     its kernel lemmas but consumes windows instead of guessing shapes.
3. **Window-local `:PATH`.** A parallel stack records `*deep-gstack*`
   length at each window BEGIN; `structured-rewrite-path` stops
   collecting at the innermost recorded depth. Steps outside any window
   keep full-literal paths (unchanged for the stable rows 1, 2, 8, 9).
4. **Body/rhs/expansion windows** (existing kinds) get the `:TERM`
   payload too — retiring relativizeFrames' depth/boundary (B1): the
   replay stops recomputing the instantiated definiens.
5. **Tree builder:** the existing BEGIN/END nesting code adopts the
   payload; `ProofTree.buildLiteralProofs` threads each window's term as
   the chain anchor. **Replay:** `pathStepsFromFrames` unchanged in
   kind; callers navigate within the innermost window term; the swap
   bridge (B4) and preprocess consumer (B6) migrate mechanically.

Per-census-row check: rows 1/2/8/9 (stable coordinates) — no window,
paths unchanged ✓; row 3 → if-left/if-right ✓; row 4 → rewritten-if ✓;
row 5 → equal-component ✓; row 6 → :TERM on existing body windows ✓;
row 7 (hyp/rhs) — already windowed, gains :TERM ✓. Open rows (linear
contexts, relieve-hyp bkptr detail) do not add window kinds; they are
covered by "outside any window ⇒ unchanged".

## Deliverable 4 — consumer-migration cost estimate (measured)

Lean touchpoints (grep-measured on the current tree):
- `relativizeFrames`/`relativizeAndStrip` call sites: 19 across the
  Driver (Reflect definitions + NodeCore/Core/Preprocess/Elim callers).
- `strip` occurrences in NodeCore alone: 66 (the threading parameter
  through `replayRewritesWith` and every recipe that forwards it) —
  Phase 1 deletes the parameter entirely, a mechanical but WIDE change.
- `innermostConsumedKind`: 7 sites (strip tagging) — deleted with it.
- Parser: `ProofLog.beginInnerRewrite/endInnerRewrite` currently carry
  `kind` only (ProofLog.lean:127-128, parse at :731) — gains the
  optional `:TERM` payload (hard-fail if absent on the NEW kinds,
  tolerated absent on legacy kinds during the one migration commit,
  then mandatory everywhere once the corpus is recaptured).
- Tree builder: ProofTree.lean:211/226 bracket on begin/end — gains
  window nodes carrying the term; `buildLiteralProofs` threads the
  window term as the chain anchor for its enclosed steps.
- Replay: `pathStepsFromFrames` unchanged; every caller drops the
  relativize/strip plumbing and navigates the innermost window term.
  The window's LEADING ENTRY FRAME (the branch's own `(2 . fn)` /
  `(3 . fn)`) is VALIDATED-AND-DROPPED against the window kind
  (if-left ⇒ 2, if-right ⇒ 3) — record-directed, fail-closed
  (implementation decision, recorded during the prototype).

## Prototype (deliverable 3) — implementation notes

Fork changes (rewrite.lisp, tags `infra/path-window`,
`emit/if-window/begin`, `emit/if-window/end`):
- `*structured-window-gstacks*` — gstack-pointer stack; the path walker
  stops collecting at the innermost boundary (`eq` pointer test, O(1)).
- `structured-window-begin/end kind term boundary-gstack` — emit
  `:begin/end-inner-rewrite :origin if-window/* :kind if-left|if-right
  :term <sublis-var alist branch>`; boundary = the LOCAL `gstack`
  formal (NOT `*deep-gstack*`, which is only restored after listed
  callees — the local is the lexically correct boundary).
- All FOUR rewrite-if-finish branch descents wrapped (must-be-true,
  must-be-false, general left, general right); the or-collapse
  shortcircuit `(mv … *t* …)` paths do not descend and get no window.
- Phase-1 hardening noted: balance begin/end under non-local exit
  (unwind-protect) — acceptable risk for the scratch prototype only.

## Prototype VALIDATED (2026-07-31) — Phase 0 complete

Scratch capture of sorting/qsort on the windowed fork (c71b72a628):
- The node that walls ORDEREDP-APPEND arrives inside
  `:ORIGIN IF-WINDOW/BEGIN :KIND IF-LEFT
  :TERM (IF (ALL-REL 'LTE A E) (ALL-REL 'GTE B E) 'NIL)` with
  window-local `:PATH ((2 . IF) (1 . ALL-REL))` — validate-and-drop the
  entry frame (bkptr 2 ⇔ if-left ✓), navigate arg 1 of the window term,
  land EXACTLY on the redex. The success criterion holds: no strip
  accounting anywhere in the chain.
- 719 BEGIN = 719 END (balanced); log size +3.5% (126967 vs 122697
  lines). 14 occurrences of the ALL-REL redex all windowed identically.

Phase 0 deliverables 1-4 all complete → the charter's DECISION
CHECKPOINT (MDD) is next: approve the semantics for the corpus-wide
Phase 1 switch.

## Phase-1 migration log (running)

- Parser: `:TERM` (mandatory on windowed kinds) + `:PATH` on
  BEGIN-INNER-REWRITE; tree builder threads `innerKind/innerTerm/
  innerPath` and decides INLINE-vs-ADOPT by record (an if-branch window
  whose term equals the previous step's rhs continues the chain — the
  constant-test collapse descent; all other windows precede their
  adopting step).
- `relativizeFrames` → uniform drop-one (the entry frame);
  `relativizeAndStrip` → strip is DEAD (no-op shim pending the
  parameter-deletion cleanup).
- if-finish/combined: children partitioned by WINDOW KIND (if-left/
  if-right), tags stripped before the branch sub-walks; non-branch
  children validated at the if and re-rooted by path trimming
  (retargetAtIf — an `if-post` fork window would retire it).
- The walk: INLINE window groups replayed over the window :TERM and
  lifted at the window's entry :PATH alone — the preceding collapse
  already put the branch at the if's position (the branch-frame append
  was an overshoot, caught by the lift validation).
- FORK LEAK FOUND (the big one): the failed-hyp-relief rollback
  (infra/hyp-log-tail) discards the BEGIN-HYPS event but left its
  window BOUNDARY pushed — every failed rule attempt leaked one
  boundary, truncating all later :PATHs in the theorem (the corpus-wide
  1-frame paths). Fix: the rollback pops the boundary stack. The
  general rule recorded for the fold-back audit: EVERY log-tail
  rollback site must restore *structured-window-gstacks* alongside the
  log; currently the only rollback that can fire with an outstanding
  push is the hyp one (the lambda/fncall/rewrite-atm rollbacks wrap
  regions whose windows balance internally before the rollback point).
