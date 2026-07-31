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
4. rewrite-if-finish re-entries (rewrite.lisp:17682's family; 17713
   left bkptr 2 / 17718 right bkptr 3 — TO CONFIRM which defun) —
   re-rewriting already-rewritten branches. DIVERGENCE SOURCE 2: the
   re-entry walks the REWRITTEN branch under frames whose terms are
   pre-rewrite → the if-finish `strip'` arithmetic + or-collapse
   bridge.
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
8. Special forms: HIDE (17153/17188 bkptr 1), IMPLIES-ish geneqv-iff
   pair (17216 arg1 / 17225 arg2 — TO CONFIRM enclosing defun),
   double-rewrite (17274 bkptr 1 then re-entry with OUTER bkptr),
   'expansion (×2 — TO LOCATE), 'body at 20547, lambda-body
   ('lambda-body bkptr at rewrite.lisp:20535-area — the lambda descent),
   linear-arithmetic atoms (21248 arg 1 under add-linear-lemma-ish —
   linear frames are NOT 'rewrite sys-fn so likely invisible to
   structured-rewrite-path; TO CONFIRM).
9. simplify.lisp:7210 (`atm` — rewrite-atm's literal-top entry, bkptr =
   the literal index) and 18751 (TO CONFIRM — likely the built-in
   clausep/tau window).

TO COMPLETE: the 'expansion sites; synp (14722 pushes sys-fn 'synp —
invisible to structured-rewrite-path, confirm); the
rewrite-solidify-family emissions (no rewrite frame of their own —
paths inherited); scons-term/exec emissions (PATH NIL observed in the
corpus — windowless, confirm harmless).

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
