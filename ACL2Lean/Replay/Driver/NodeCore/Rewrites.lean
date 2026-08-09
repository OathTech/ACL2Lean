/-
  Driver/NodeCore/Rewrites — positional slice of the former NodeCore
  monolith (perf arc 3a, 2026-08-07): MOVE-ONLY; the boundaries are the
  file's own def-before-use order, so the import chain IS the
  dependency order.
-/
import ACL2Lean.Replay.Driver.NodeCore.Node

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a chain of rewrite nodes, lifting each through the chain's start term by
    path-directed congruence (window-local paths, drop-one relativization) and
    chaining. Returns the composed `∃N∀f≥N, eval start = eval finalTerm` (or
    `none` if the chain is empty) and the final term. -/
partial def replayRewritesWith (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr)
    (nodes : List ProofNode)
    -- the CURRENT literal chain's already-consumed nodes (G1 rung 1,
    -- inc-2b): the or-collapse bridge re-composes the TEST-position prefix
    -- on the then-copy. Consume-and-continue recursions append; re-process
    -- sites pass unchanged; sub-chain recursions (branch children) start
    -- fresh (the default).
    (chainPrefix : List ProofNode := []) :
    MetaM (Option (Expr × Bool) × SExpr) := do
  match nodes with
  | [] => return (none, start)
  | n :: rest => do
    let (lhs, rhs) := nodeLhsRhs n
    -- fork-batch item A (2026-08-09): an UNRESOLVED equal-descent probe
    -- record (`equal/{cars,cdrs}-decision` with rhs == lhs — the recursive
    -- rewrite-equal left the component equality standing; its windows were
    -- empty, so the cons-decomposition protocol below never engages).
    -- Verdict-only DATA: validate the record names the running equality's
    -- own components and consume it as a no-op. A lone RESOLVED record
    -- (constant rhs, no windowed scratch) stays a loud frontier until a
    -- book exhibits one.
    if nodeOrigin n == "equal/cars-decision" ||
        nodeOrigin n == "equal/cdrs-decision" then
      if rhs == lhs then do
        let pfn := if nodeOrigin n == "equal/cars-decision" then "CAR"
                   else "CDR"
        let mkComp : SExpr → SExpr := fun t =>
          .cons (.atom (.symbol { name := pfn })) (.cons t .nil)
        let ok : Bool := match start, lhs with
          | .cons (.atom (.symbol eqS)) (.cons a (.cons b .nil)),
            .cons (.atom (.symbol eqS')) (.cons ca (.cons cb .nil)) =>
            eqS.name == "EQUAL" && eqS'.name == "EQUAL" &&
            ca == mkComp a && cb == mkComp b
          | _, _ => false
        unless ok do
          throwError "replayRewrites: unresolved {nodeOrigin n} record \
              {repr lhs} does not name the running equality \
              {repr start}'s {pfn} components (frontier)"
        return ← replayRewritesWith rec cfg ctx start rest (chainPrefix ++ [n])
      else
        throwError "replayRewrites: lone resolved {nodeOrigin n} record \
            ({repr lhs} ⇒ {repr rhs}) outside the decomposition protocol \
            (frontier)"
    -- INLINE branch-window group (path-emission Phase 1): nodes tagged
    -- if-left/if-right reaching the walk directly are the surviving
    -- branch's sub-chain after a rewrite-if constant-test collapse (the
    -- tree builder attaches them inline exactly when the window term
    -- equals the collapse step's rhs). Replay the run as a chain over the
    -- window TERM and lift the composite at the window's :PATH plus the
    -- branch position its KIND names. Recipes that consume windows
    -- (if-finish's partition) strip the tag first — reaching here tagged
    -- means the inline case.
    if innerKindOf n == "if-left" || innerKindOf n == "if-right" then do
      let kind := innerKindOf n
      let some wterm := innerTermOf n
        | throwError "replayRewrites: {kind}-tagged node without a window \
            term (pre-Phase-1 log? recapture)"
      let wpath := innerPathOf n
      let wswapped := innerSwappedOf n
      let mut group : List ProofNode := [n]
      let mut restG := rest
      let mut scanning := true
      while scanning do
        match restG with
        | m :: r' =>
          if innerKindOf m == kind && innerTermOf m == some wterm &&
              innerPathOf m == wpath && innerSwappedOf m == wswapped then
            group := group ++ [m]
            restG := r'
          else scanning := false
        | [] => scanning := false
      -- when a RECORDED collapse preceding the window already replaced the
      -- if by its surviving branch in the running term, the window term
      -- sits AT the if's own position: the lift path is the window's entry
      -- path alone (no branch frame)
      let relW := relativizeFrames wpath
      -- The window's gstack entry path can UNDER-DETERMINE the position
      -- (fold-back audit 2026-07-31 V5 redesign; the earlier collapseEval
      -- rung — dead corpus-wide and blind to branchFacts — is deleted).
      -- Two structural facts, both record-directed:
      -- (a) the entry path's FIRST frame is a literal-root DESCRIPTOR when
      --     the enclosing collapses were RECORDED (the running term already
      --     descended with them — drop it: `relW`), but a REAL descent
      --     frame when an enclosing must-be arm collapsed SILENTLY (the
      --     running term still carries the enclosing ifs — keep the full
      --     `wpath`);
      -- (b) the window term either sits AT the navigated position (a
      --     recorded collapse replaced the if), or is the branch of a
      --     still-uncollapsed 3-arg IF there — the branch named by the
      --     window KIND and `:SWAPPED-P` (if-left = arg 2, or arg 3 when
      --     the record says the running if is the pre-swap negation
      --     shape).
      -- Every reading is a TOTAL function of the record + running term
      -- (no search): compute all that CHECK OUT and require them to agree
      -- on the position; disagreement or none → the unique-occurrence
      -- fallback, then hard-fail.
      -- A `:SWAPPED-P` window whose if still has the PRE-swap negation
      -- shape additionally applies ACL2's silent swap normalization
      -- (`re_if_neg_test_swap`) at the if FIRST — the record is the
      -- trigger (BUG-026; the old spurious no-op combined records used
      -- to carry this via `normalizeSwapsToward`, BUG-025's guard fix
      -- removed them). A candidate is (branch frames, pre-swap if base).
      let branchDirect (S : SExpr) : Option Nat := do
        let .cons (.atom (.symbol ifS)) (.cons _ (.cons thn (.cons els .nil))) := S
          | none
        guard (ifS.name == "IF")
        if kind == "if-left" && thn == wterm then some 2
        else if kind == "if-right" && els == wterm then some 3
        else none
      let branchPreSwap (S : SExpr) : Option Nat := do
        guard wswapped
        let .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) := S
          | none
        guard (ifS.name == "IF")
        let .cons (.atom (.symbol ifS2)) (.cons _ (.cons qn (.cons qt .nil))) := c
          | none
        guard (ifS2.name == "IF" && qn == quoteNil && qt == quoteT)
        -- after the swap the if is (IF c els thn): if-left names els
        -- (post-swap arg 2), if-right names thn (post-swap arg 3)
        if kind == "if-left" && els == wterm then some 2
        else if kind == "if-right" && thn == wterm then some 3
        else none
      -- candidates: (branch frames, pre-swap if base, branch anchor).
      -- A BRANCH-anchored window (the if is still uncollapsed — a silent
      -- must-be arm) replays its sub-chain UNDER the branch hypothesis
      -- (ACL2's assume-true-false: arg 2 under test≠nil, arg 3 under
      -- test=nil) and lifts by the conditional branch congruence — the
      -- context the combined partition supplies for ADOPTED windows.
      let mut cands : List (List PathFrame × Option (List PathFrame) ×
        Option (List PathFrame × Nat)) := []
      for base in [relW, wpath] do
        match pathStepsFromFrames start base wterm with
        | .ok _ =>
          -- a DIRECT locate whose LAST frame descends into an IF branch
          -- IS the branch anchor's position (the dedup principle below,
          -- applied at generation): the sub-walk must carry the branch
          -- hypothesis — plain congruence through a then/else position
          -- would demand the sub-chain hold UNCONDITIONALLY, which a
          -- solidify consuming the test does not (HOW-MANY-RM-GENERAL
          -- *1/2' literal 2). Synthesize the anchor from the frames'
          -- own shape; a non-IF tail stays a plain direct locate.
          let anchored? : Option (List PathFrame × Nat) := do
            let lastFr ← base.getLast?
            let bidx ← match lastFr with
              | .arg i _ => if i == 2 || i == 3 then some i else none
              | _ => none
            let pre := base.dropLast
            match (navigateFrames start pre).toOption with
            | some (_, .cons (.atom (.symbol ifS))
                (.cons _ (.cons _ (.cons _ .nil)))) =>
              if ifS.name == "IF" then some (pre, bidx) else none
            | _ => none
          cands := cands ++ [(base, none, anchored?)]
        | .error _ =>
          match (navigateFrames start base).toOption with
          | some (_, S) =>
            match branchDirect S with
            | some bidx =>
              let c := base ++ [PathFrame.arg bidx { name := "IF" }]
              if (pathStepsFromFrames start c wterm).toOption.isSome then
                cands := cands ++ [(c, none, some (base, bidx))]
            | none =>
              match branchPreSwap S with
              | some bidx =>
                cands := cands ++
                  [(base ++ [PathFrame.arg bidx { name := "IF" }],
                    some base, some (base, bidx))]
              | none => pure ()
          | none => pure ()
      let mut start := start
      let mut frames := relW
      let mut preChain : Option Expr := none
      let mut branchAnchor : Option (List PathFrame × Nat) := none
      -- dedupe by POSITION (the frames): the relW and wpath readings can
      -- name the SAME position with different anchoring modes (a direct
      -- locate landing exactly on an if-branch IS the branch anchor's
      -- position) — prefer the BRANCH-anchored reading, the
      -- hypothesis-bearing faithful context (a sub-chain needing no
      -- hypothesis composes under it unchanged)
      let cands' := cands.foldl (fun (acc : List (List PathFrame ×
          Option (List PathFrame) × Option (List PathFrame × Nat))) c =>
        match acc.find? (·.1 == c.1) with
        | some prev =>
          if prev.2.2.isNone && c.2.2.isSome then
            acc.map (fun p => if p.1 == c.1 then c else p)
          else acc
        | none => acc ++ [c]) []
      let mut chosen? : Option (List PathFrame × Option (List PathFrame) ×
        Option (List PathFrame × Nat)) := none
      match cands' with
      | [c] => chosen? := some c
      | [] =>
        match occurrencePaths start wterm with
        | [p] => frames := p
        | [] => throwError "replayRewrites: inline {kind} window term \
            {repr wterm} does not occur in the running term \
            {repr start} (frontier)"
        | ps => throwError "replayRewrites: inline {kind} window term \
            {repr wterm} occurs {ps.length} times in the running term \
            {repr start} (entry path {repr wpath}, swapped {wswapped}) — \
            ambiguous position (frontier)"
      | cs => do
        -- POSITION-CANONICAL uniqueness (the drift round's stated
        -- completion condition, item 15, COMPLETED at the final
        -- close-out): canonicalize ALL THREE components — the frames
        -- (validated PathSteps), preSwap? (navigated steps + subterm),
        -- and branchAnchor (navigated steps + index) — across the
        -- survivors. Distinct SPELLINGS of one reading collapse to
        -- equality and the first is taken (no preference: they are
        -- interchangeable); any canonicalization failure or genuine
        -- disagreement still hard-fails.
        let canonOf : (List PathFrame × Option (List PathFrame) ×
            Option (List PathFrame × Nat)) →
            Option (List PathStep × Option (List PathStep × SExpr) ×
              Option ((List PathStep × SExpr) × Nat)) := fun (f, pre, br) =>
          match pathStepsFromFrames start f wterm with
          | .error _ => none
          | .ok p =>
            let preC : Option (Option (List PathStep × SExpr)) :=
              match pre with
              | none => some none
              | some pf => match navigateFrames start pf with
                | .error _ => none
                | .ok (steps, sub) => some (some (steps, sub))
            let brC : Option (Option ((List PathStep × SExpr) × Nat)) :=
              match br with
              | none => some none
              | some (bf, i) => match navigateFrames start bf with
                | .error _ => none
                | .ok (steps, sub) => some (some ((steps, sub), i))
            match preC, brC with
            | some pc, some bc => some (p, pc, bc)
            | _, _ => none
        let canonPos := cs.map (fun c =>
          (pathStepsFromFrames start c.1 wterm).toOption)
        let posSame := match canonPos with
          | some p0 :: rest => rest.all (· == some p0)
          | _ => false
        let canonMeta := fun (c : List PathFrame × Option (List PathFrame) ×
            Option (List PathFrame × Nat)) =>
          (canonOf c).map (fun (_, pc, bc) => (pc, bc))
        if posSame then
          -- ONE position, several anchoring modes: the BRANCH-anchored
          -- reading is the faithful context (the ratified same-frames
          -- dedup argument, extended along position-canonical equality:
          -- an unanchored reading is the anchored one's hypothesis-free
          -- specialization — a sub-chain needing no hypothesis composes
          -- under the branch congruence unchanged). Multiple anchored
          -- readings must agree on the canonical anchor+preSwap.
          match cs.filter (·.2.2.isSome) with
          | [] => chosen? := some cs.head!
          | [a] => chosen? := some a
          | a :: rest =>
            if rest.all (fun c => canonMeta c == canonMeta a)
                && (canonMeta a).isSome then
              chosen? := some a
            else
              throwError "replayRewrites: inline {kind} window term \
                  {repr wterm}: multiple branch-anchored readings with \
                  differing canonical anchors at one position (genuine \
                  ambiguity — frontier)"
        else
          throwError "replayRewrites: inline {kind} window term \
              {repr wterm} admits {cs.length} distinct anchorings \
              {repr (cs.map (·.1))} in the running term {repr start} (entry \
              path {repr wpath}) — ambiguous position (frontier)"
      if let some (c, preSwap?, br?) := chosen? then
        frames := c
        branchAnchor := br?
        if let some base := preSwap? then
          let (stepsToIf, S) ← ofExcept (navigateFrames start base)
          let .cons (.atom (.symbol ifS))
              (.cons (.cons (.atom (.symbol _))
                  (.cons cIn (.cons _ (.cons _ .nil))))
                (.cons a (.cons b .nil))) := S
            | throwError "replayRewrites: internal — pre-swap candidate \
                lost its negation shape at {repr S}"
          let swapped : SExpr :=
            .cons (.atom (.symbol ifS)) (.cons cIn (.cons b (.cons a .nil)))
          let (pc, root') ← liftNegTestSwap cfg stepsToIf start S cIn a b swapped
          preChain := some pc
          start := root'
      let w := cfg.worldExpr
      let e := cfg.envExpr
      let mkIdEq (t : SExpr) : MetaM Expr := do
        let fn ← withLocalDeclD `f (mkConst ``Nat) fun fV =>
          mkLambdaFVars #[fV] (mkApp4 (mkConst ``evalOpt) fV w e (reflectSExpr t))
        mkAppM ``fuel_eq_refl #[fn]
      match branchAnchor with
      | some (base, bidx) => do
        -- branch-anchored: sub-walk under the branch hypothesis, lift by
        -- the conditional congruence, then through the base frames
        let (stepsToIf, S) ← ofExcept (navigateFrames start base)
        let .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) := S
          | throwError "replayRewrites: internal — branch anchor lost its \
              if shape at {repr S}"
        let ctx ← pinTermOpaques cfg e ctx c
        let vC ← ctxValExpr cfg ctx c
        let pC ← ctxValProof cfg ctx c
        let nilC := mkConst ``SExpr.nil
        let (lamT, lamE, thn', els') ←
          if bidx == 2 then do
            let (lamT, thn') ← withLocalDeclD `hne (← mkAppM ``Ne #[vC, nilC]) fun hNe => do
              let ctx' ← installBranchTrueFacts cfg ctx c vC hNe
              let (chT, thn') ← replayRewritesWith rec cfg ctx' wterm
                (group.map clearWindowTag)
              let chT ← chainReqEq chT
              let prf ← match chT with
                | some p => pure p
                | none => mkIdEq wterm
              pure (← mkLambdaFVars #[hNe] prf, thn')
            let lamE ← withLocalDeclD `hnil (← mkEq vC nilC) fun hNil => do
              mkLambdaFVars #[hNil] (← mkIdEq els)
            pure (lamT, lamE, thn', els)
          else do
            let (lamE, els') ← withLocalDeclD `hnil (← mkEq vC nilC) fun hNil => do
              let ctx' := { ctx with branchFacts := ctx.branchFacts ++ [(c, vC, false, hNil)] }
              let (chE, els') ← replayRewritesWith rec cfg ctx' wterm
                (group.map clearWindowTag)
              let chE ← chainReqEq chE
              let prf ← match chE with
                | some p => pure p
                | none => mkIdEq wterm
              pure (← mkLambdaFVars #[hNil] prf, els')
            let lamT ← withLocalDeclD `hne (← mkAppM ``Ne #[vC, nilC]) fun hNe => do
              mkLambdaFVars #[hNe] (← mkIdEq thn)
            pure (lamT, lamE, thn, els')
        if thn' == thn && els' == els then
          -- no effective rewrites — a no-op group (the swap normalization,
          -- if any, still moves the chain forward)
          let (restProof, finalTerm) ←
            replayRewritesWith rec cfg ctx start restG chainPrefix
          match preChain with
          | none => return (restProof, finalTerm)
          | some pc =>
            return (some (← chainWithR cfg ctx pc start restProof), finalTerm)
        let newIf : SExpr := .cons (.atom (.symbol ifS))
          (.cons c (.cons thn' (.cons els' .nil)))
        let mut inner ← mkAppM ``evalOpt_congr_if_branches_cond
          #[w, e, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
            reflectSExpr thn', reflectSExpr els', vC, pC, lamT, lamE]
        let mut curL := S
        let mut curR := newIf
        for st in stepsToIf.reverse do
          inner ← applyStep w e st curL curR inner
          curL := rebuild st curL
          curR := rebuild st curR
        unless curL == start do
          throwError "replayRewrites: inline {kind} branch-window lift \
              reconstructed {repr curL} ≠ running {repr start}"
        match preChain with
        | none => pure ()
        | some pc => inner ← mkAppM ``fuel_chain_eq #[pc, inner]
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx curR
          restG (chainPrefix ++ [n])
        return (some (← chainWithR cfg ctx inner curR restProof), finalTerm)
      | none => do
        let (chOpt, wfinal) ← replayRewritesWith rec cfg ctx wterm
          (group.map clearWindowTag)
        let chOpt ← chainReqEq chOpt
        let steps ← match pathStepsFromFrames start frames wterm with
          | .ok st => pure st
          | .error e => throwError "replayRewrites: inline {kind} window's \
              entry path does not locate its term in the running chain: {e}"
        match chOpt with
        | none =>
          -- no effective rewrites in the window — a no-op group
          return ← replayRewritesWith rec cfg ctx start restG chainPrefix
        | some chain => do
          let mut inner := chain
          let mut curL := wterm
          let mut curR := wfinal
          for st in steps.reverse do
            inner ← applyStep w e st curL curR inner
            curL := rebuild st curL
            curR := rebuild st curR
          unless curL == start do
            throwError "replayRewrites: inline {kind} window lift \
                reconstructed {repr curL} ≠ running {repr start}"
          let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx curR
            restG (chainPrefix ++ [n])
          return (some (← chainWithR cfg ctx inner curR restProof), finalTerm)
    -- rewrite-if SWAPPED-P bridge: apply ACL2's silent branch swap when this
    -- node's path descends into a negation-test if in the RUNNING term, then
    -- re-process the node on the normalized term. (Skipped for the
    -- clause-context-resolution marker — it never navigates its path.)
    if (runeOf n).ty != "clause-context-resolution" then
      let rel := relativizeFrames (nodePath n)
      match ← bridgeIfNegTestSwap cfg rel start lhs with
      | some (swapEq, start') =>
        let (restAll, finalT) ← replayRewritesWith rec cfg ctx start' (n :: rest) chainPrefix
        return (some (← chainWithR cfg ctx swapEq start' restAll), finalT)
      | none => pure ()
    -- OR-SHAPE IFF node (G1 rung 1, inc-2): rewrite-if-finish's
    -- `(if a a b) ⇒ (if a 't b)` collapse arrives `:EQUIV IFF` (the fork
    -- labels it truthfully now — p3-conj-mid-literal). Its SIff payload is
    -- lifted along the node's path by the R congruence table and MUST
    -- collapse to an eval-equality at a boolean-consumer frame before the
    -- literal root (if-test / implies positions); a root-iff literal chain
    -- is a frontier.
    if nodeEquiv n == "iff" && (runeOf n).ty == "if-simplification" then
      if let .node _ _ _ [] _ := n then
        let .cons (.atom (.symbol ifS)) (.cons a (.cons a2 (.cons bT .nil))) := lhs
          | throwError "replayRewrites: iff if-simplification lhs {repr lhs} is \
              not an if application (frontier)"
        unless ifS.name == "IF" && a == a2 do
          throwError "replayRewrites: iff if-simplification {repr lhs} is not \
              the or-shape (if a a b) (frontier)"
        let expectedRhs : SExpr := .cons (.atom (.symbol ifS))
          (.cons a (.cons quoteT (.cons bT .nil)))
        unless rhs == expectedRhs do
          throwError "replayRewrites: iff or-shape rhs {repr rhs} is not \
              (if a 't b) (frontier)"
        let rel := relativizeFrames (nodePath n)
        let steps ← match pathStepsFromFrames start rel lhs with
          | .ok s => pure s
          | .error e => throwError "replayRewrites: iff or-shape :PATH does \
              not navigate to the redex: {e}"
        let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
        let payload ← mkAppM ``evrel_siff_if_or_shape
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr bT,
            ← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx bT,
            ← ctxValProof cfg ctx a, ← ctxValProof cfg ctx bT]
        let mut inner := payload
        let mut innerIff := true
        let mut curL := lhs
        let mut curR := rhs
        for st in steps.reverse do
          if innerIff then
            let (p, still) ← applyStepSIff cfg ctx st inner
            inner := p
            innerIff := still
          else
            inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
          curL := rebuild st curL
          curR := rebuild st curR
        unless curL == start do
          throwError "replayRewrites: iff or-shape lift reconstructed \
              {repr curL} ≠ running {repr start}"
        if innerIff then
          throwError "replayRewrites: or-shape iff chain still IFF at the \
              literal root (frontier — R-parameterized literal chains)"
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx curR rest (chainPrefix ++ [n])
        return (some (← chainWithR cfg ctx inner curR restProof), finalTerm)
    -- an if-simplification recorded as an IDENTITY (`X ⇒ X`, no children) is
    -- ambiguous: either a true no-op, or a DISPLAY-FOLDED constant-test
    -- collapse (`(if 'c a b) ⇒ branch` logged with the already-collapsed
    -- term on both sides). The RUNNING term at the node's path is the ground
    -- truth: equal to rhs → no-op (replay as reflexivity by skipping);
    -- a constant-test if collapsing to rhs → replay the collapse.
    if lhs == rhs && (runeOf n).ty == "if-simplification" then
      if let .node _ _ _ [] _ := n then
        let rel := relativizeFrames (nodePath n)
        let (_, S) ← ofExcept (navigateFrames start rel)
        if S == rhs then
          return ← replayRewritesWith rec cfg ctx start rest (chainPrefix ++ [n])
        -- SYMBOLIC-test if resolved by an in-scope clause-context fact,
        -- record folded all the way past the constant (observed: 'T ⇒ 'T
        -- with running (IF (EQUAL (CAR X) E) 'NIL 'T) under that segment
        -- literal's falsity — ALL-REL-FILTER-1, Subgoal *1/2'). collapseEval
        -- re-derives the resolution from the SAME facts if-interp consulted;
        -- the rhs equality below fail-closes on any divergence.
        if let .cons (.atom (.symbol ifS')) (.cons c' _) := S then
          let symbolicTest := ifS'.name == "IF" &&
            (match c' with
             | .cons (.atom (.symbol q')) (.cons _ .nil) => q'.name != "QUOTE"
             | _ => true)
          if symbolicTest then
            let (chOpt, S') ← collapseEval cfg ctx [] S
            if let some ch := chOpt then
              if S' == rhs then
                let (lifted, newTerm) ←
                  emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S S'
                    ch
                let (restProof, finalTerm) ←
                  replayRewritesWith rec cfg ctx newTerm rest (chainPrefix ++ [n])
                return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
        let .cons (.atom (.symbol ifS))
            (.cons (.cons (.atom (.symbol q)) (.cons cv .nil))
              (.cons thn (.cons els .nil))) := S
          | throwError "replayRewrites: identity if-simplification's running \
                        subterm {repr S} is neither rhs {repr rhs} nor a \
                        constant-test if (frontier; segFacts: \
                        {repr (ctx.segFacts.map (·.1))}, litFacts: \
                        {repr (ctx.litFacts.map (·.2.1))})"
        unless ifS.name == "IF" && q.name == "QUOTE" do
          throwError "replayRewrites: identity if-simplification's running \
                      subterm {repr S} is not a constant-test if (frontier)"
        let branch := if cv == SExpr.nil then els else thn
        unless branch == rhs do
          throwError "replayRewrites: folded constant-test collapse of \
                      {repr S} selects {repr branch}, node rhs is {repr rhs}"
        let c : SExpr := .cons (.atom (.symbol q)) (.cons cv .nil)
        let (nodeEq, _) ← mkConstTestCollapse cfg ctx c cv thn els
        let (lifted, newTerm) ←
          emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S branch
            nodeEq
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest
          (chainPrefix ++ [n])
        return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
    -- DISPLAY-FOLDED constant-test collapses (docs/notes/2026-06-14_exec-
    -- counterpart-and-folding-wall.md; extended 2026-07-20): a constant-test
    -- if-simplification's recorded lhs went through sublis-var, whose
    -- cons-term folds ground applications inside the branches — (car 'c)/
    -- (cdr 'c) in the DISCARDED branch (data-ratified 2026-07-06), and ground
    -- (EQUAL 'c1 'c2) tests in the SURVIVING branch (the REL-unfold chains,
    -- qsort corpus) — logging-only, per ACL2's own comment. The RUNNING term
    -- is the ground truth: require the SAME test and a SELF-CONSISTENT record
    -- (rhs == the recorded taken branch), and replay the collapse on the
    -- RUNNING term, continuing the chain from the RUNNING surviving branch.
    -- Surviving-branch folds are reconciled by the SUBSEQUENT recorded steps
    -- (the exec-counterpart resolutions ACL2 logs right after), each with its
    -- own fail-closed redex check — a real divergence still throws there or
    -- at the chain's end-result check.
    if (runeOf n).ty == "if-simplification" && lhs != rhs then
      if let .node _ _ _ [] _ := n then
        if let .cons (.atom (.symbol ifS))
            (.cons c@(.cons (.atom (.symbol q)) (.cons cv .nil))
              (.cons thn (.cons els .nil))) := lhs then
          if ifS.name == "IF" && q.name == "QUOTE" then
            let rel := relativizeFrames (nodePath n)
            let (_, S) ← ofExcept (navigateFrames start rel)
            -- take the relaxation ONLY on the folded-collapse shape: same
            -- test, recorded rhs == recorded taken branch. Anything else
            -- falls THROUGH to the normal machinery (if-finish/combined
            -- etc.), which handles or fails precisely.
            let compatible :=
              match S with
              | .cons (.atom (.symbol ifS')) (.cons c' (.cons _ (.cons _ .nil))) =>
                let taken := if cv == SExpr.nil then els else thn
                ifS'.name == "IF" && c' == c && rhs == taken
              | _ => false
            if S != lhs && compatible then
              let .cons _ (.cons _ (.cons thn' (.cons els' .nil))) := S
                | throwError "replayRewrites: internal — compatible running \
                              subterm lost its if shape"
              -- the collapse result is the RUNNING surviving branch (the
              -- recorded rhs may carry surviving-branch folds — see the arm
              -- doc above; nodeEq is exactly `eval S = eval taken'`)
              let (nodeEq, taken') ← mkConstTestCollapse cfg ctx c cv thn' els'
              let (lifted, newTerm) ←
                emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S taken'
                  nodeEq
              let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest
                (chainPrefix ++ [n])
              return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
    -- clause-context-resolution marker: ACL2's rewrite-atm emits this as a
    -- terminal REPORT ("we have proved the original literal … hence the
    -- clause", simplify.lisp) — lhs is the ORIGINAL atom, rhs the NET constant
    -- the preceding chain nodes already produced. It is not a sequential step;
    -- when it is terminal and the running term already equals its rhs, it adds
    -- no reasoning, so verify-then-drop. Fail-closed otherwise.
    if (runeOf n).ty == "clause-context-resolution" then
      unless rest.isEmpty do
        throwError "clause-context-resolution: non-terminal marker (frontier)"
      if rhs == start then
        return (none, start)
      -- GROUND residue (Phase 2, WEAK/STRONG capstones, diagnosed off
      -- the real tree 2026-08-07): rewrite-atm evaluates a GROUND
      -- residual (the chain's (IMPLIES 'T 'NIL)) to the reported net
      -- constant with no recorded step. Recompute toward the RECORDED
      -- rhs at value level — the ratified recompute-dictated-by-the-
      -- recorded-target class; a non-ground or non-matching residue
      -- still hard-fails.
      let .cons (.atom (.symbol qS)) (.cons cv .nil) := rhs
        | throwError "clause-context-resolution: rhs {repr rhs} ≠ running \
            term {repr start} (chain did not reach the reported net \
            result, and the rhs is not a quoted constant)"
      unless qS.name == "QUOTE" do
        throwError "clause-context-resolution: rhs {repr rhs} ≠ running \
            term {repr start} (chain did not reach the reported net \
            result, and the rhs is not a quoted constant)"
      unless (ACL2.Replay.freeVars start).isEmpty do
        throwError "clause-context-resolution: rhs {repr rhs} ≠ running \
            term {repr start} (chain did not reach the reported net \
            result; the residue is not ground — frontier)"
      let conv ← replayExecGround cfg start cv
      let pr ← mkAppM ``re_val_quote
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      let step ← mkAppM ``fuel_eq_of_conv
        #[conv, pr, ← mkEqRefl (reflectSExpr cv)]
      return (some (step, false), rhs)
    -- `if-finish/combined`: rewrite-if FINISHED an if whose test stayed
    -- symbolic. Since the fold-back audit fix (2026-07-31 V2) the recorded
    -- lhs is the ACTUAL input to rewrite-if1 — `(if test rewritten-left
    -- rewritten-right)`, raw cons — i.e. the running subterm AFTER the
    -- branch windows apply; earlier logs carried an UNINSTANTIATED folded
    -- shape (BUG-025). The replay still takes the running term as ground
    -- truth: navigate to the node's position for the redex
    -- `S = (if c thn els)`, chain the node's CHILDREN over the branch each
    -- descends into UNDER that branch's test assumption (ACL2's
    -- assume-true-false — the conditional-congruence lemma discharges the
    -- hypotheses), require the result to be the node's recorded rhs, and
    -- lift by congruence.
    if let .node ⟨"if-simplification", _, _⟩ _ _ children prov := n then
      if prov.origin == "if-finish/combined" then
        let rel := relativizeFrames (nodePath n)
        let (steps, S) ← ofExcept (navigateFrames start rel)
        let _ := steps
        let .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) := S
          | throwError "if-finish/combined: running subterm {repr S} is not a \
                        3-arg if"
        unless ifS.name == "IF" do
          throwError "if-finish/combined: running subterm head {ifS.name} ≠ if"
        -- partition the children by their WINDOW (path-emission Phase 1):
        -- branch rewrites arrive inside if-left/if-right windows
        -- (record-directed — the fork brackets rewrite-if-finish's branch
        -- descents); whole-if FINISHING steps (if1/boolean, same-branches)
        -- fire after the branch windows close, so they carry the ENCLOSING
        -- window's coordinates — their window-local path must equal the
        -- if-finish node's own (`rel`), validated fail-closed, and the walk
        -- below re-roots them at the if by PATH TRIMMING (kept ONLY here;
        -- an `if-post` window at the fork would retire it — noted for the
        -- fold-back audit).
        -- group by WINDOW IDENTITY + recorded order: a child whose window
        -- term IS the then/else branch OPENS that branch's group; following
        -- children (nested windows, post-collapse continuations) stay in
        -- the open group until the other branch's window opens. Children at
        -- the if itself (whole-if finishing steps) close the branch groups.
        -- Only the OWN branch window's tag is cleared for the sub-walk —
        -- nested window tags survive for the recursive inline handler.
        let mut thenCh : List ProofNode := []
        let mut elseCh : List ProofNode := []
        let mut postCh : List ProofNode := []
        let mut cur : Nat := 0  -- 0 = none, 1 = then, 2 = else
        for chN in children do
          if innerKindOf chN == "if-left" && innerTermOf chN == some thn then
            unless postCh.isEmpty do
              throwError "if-finish/combined: branch child after a whole-if \
                          child (frontier)"
            -- :SWAPPED-P consistency (fold-back audit V3): this branch
            -- window and the combined record come from the SAME
            -- rewrite-if-finish invocation — their swap flags must agree
            -- (a mismatch is a tree-shape or emission divergence).
            unless innerSwappedOf chN == prov.swapped do
              throwError "if-finish/combined: if-left window :SWAPPED-P \
                          ({innerSwappedOf chN}) disagrees with the combined \
                          record ({prov.swapped})"
            cur := 1
            thenCh := thenCh ++ [clearWindowTag chN]
          else if innerKindOf chN == "if-right" && innerTermOf chN == some els then
            unless postCh.isEmpty do
              throwError "if-finish/combined: branch child after a whole-if \
                          child (frontier)"
            unless innerSwappedOf chN == prov.swapped do
              throwError "if-finish/combined: if-right window :SWAPPED-P \
                          ({innerSwappedOf chN}) disagrees with the combined \
                          record ({prov.swapped})"
            cur := 2
            elseCh := elseCh ++ [clearWindowTag chN]
          else
            let chRel? := some (relativizeFrames (nodePath chN))
            if chRel? == some rel && innerKindOf chN == "" then
              cur := 0
              postCh := postCh ++ [retargetAtIf chN rel.length]
            else if cur == 1 then
              thenCh := thenCh ++ [chN]
            else if cur == 2 then
              elseCh := elseCh ++ [chN]
            else
              throwError "if-finish/combined: child {repr (nodeLhsRhs chN).1} \
                  (kind {innerKindOf chN}) precedes both branch windows and \
                  is not at the if (frontier)"
        let w := cfg.worldExpr
        let e := cfg.envExpr
        let vC ← ctxValExpr cfg ctx c
        let pC ← ctxValProof cfg ctx c
        let nilC := mkConst ``SExpr.nil
        let mkIdEq (t : SExpr) : MetaM Expr := do
          let fn ← withLocalDeclD `f (mkConst ``Nat) fun fV =>
            mkLambdaFVars #[fV] (mkApp4 (mkConst ``evalOpt) fV w e (reflectSExpr t))
          mkAppM ``fuel_eq_refl #[fn]
        let (lamT, thn') ← withLocalDeclD `hne (← mkAppM ``Ne #[vC, nilC]) fun hNe => do
          let ctx' ← installBranchTrueFacts cfg ctx c vC hNe
          let (chT, thn') ← replayRewritesWith rec cfg ctx' thn thenCh
          let chT ← chainReqEq chT
          let prf ← match chT with
            | some p => pure p
            | none => mkIdEq thn
          pure (← mkLambdaFVars #[hNe] prf, thn')
        let (lamE, els') ← withLocalDeclD `hnil (← mkEq vC nilC) fun hNil => do
          let ctx' := { ctx with branchFacts := ctx.branchFacts ++ [(c, vC, false, hNil)] }
          let (chE, els') ← replayRewritesWith rec cfg ctx' els elseCh
          let chE ← chainReqEq chE
          let prf ← match chE with
            | some p => pure p
            | none => mkIdEq els
          pure (← mkLambdaFVars #[hNil] prf, els')
        let target : SExpr := .cons (.atom (.symbol ifS))
          (.cons c (.cons thn' (.cons els' .nil)))
        -- OR-COLLAPSE BRIDGE (G1 rung 1, inc-2b): an IFF combined node
        -- whose then-branch is the UNREWRITTEN test's copy `A` — ACL2's
        -- rewrite-if replaced it by 'T with no recorded step (the collapse
        -- is guarded by `unrewritten-test == left`). Replay: re-compose the
        -- TEST-position prefix nodes on the then-copy (the branch-children
        -- strip pattern, `(myKind, 1)`), require the result to be the
        -- rewritten test `c`, and bridge with `evrel_siff_if_or_bridge` —
        -- the node's composite becomes IFF (p3-conj-mid-literal's flip).
        let mut bridge? : Option Expr := none
        let mut postStart := target
        if prov.equiv == "iff" && thn' != quoteT then
          if let some pc0 := postCh.head? then
            let (pcLhs, _) := nodeLhsRhs pc0
            if pcLhs == .cons (.atom (.symbol ifS))
                (.cons c (.cons quoteT (.cons els' .nil))) then
              unless thenCh.isEmpty && thn' == thn do
                throwError "if-finish/combined: or-collapse bridge with a \
                    rewritten then-branch (frontier)"
              unless rel.isEmpty do
                throwError "if-finish/combined: or-collapse bridge below the \
                    literal root (frontier — needs the mixed lift)"
              let mut testNodes : List ProofNode := []
              for pn in chainPrefix do
                -- a prefix node whose path does not relativize under THIS
                -- node's frame is at another position — a NON-MATCH, not an
                -- error (audit Q1: deliberate; a wrong selection still
                -- fails closed on the xA == c check below). WINDOW-TAGGED
                -- prefix nodes are excluded outright (fold-back audit
                -- B-F3): their paths are window-local — relative to their
                -- own window's term, not the literal — so a leading
                -- `.arg 1` frame there is a coincidence, not a
                -- test-position descent.
                if innerKindOf pn != "" then
                  continue
                let relPn? := some (relativizeFrames (nodePath pn))
                if let some (.arg 1 _ :: _) := relPn? then
                  -- re-root at the then-copy: drop the test-position frame
                  -- (validated by the .arg 1 filter above) so the sub-walk's
                  -- uniform drop-one navigates within `thn` — the strips this
                  -- replaced retired with gstack-coordinate emission
                  testNodes := testNodes ++ [retargetAtIf pn 1]
              let (chA, xA) ← replayRewritesWith rec cfg ctx thn testNodes
              unless xA == c do
                throwError "if-finish/combined: or-collapse bridge — the \
                    re-composed test chain reached {repr xA}, the rewritten \
                    test is {repr c} (frontier)"
              let chA ← chainReqEq chA
              let hAX ← match chA with
                | some hp => pure hp
                | none => throwError "if-finish/combined: or-collapse bridge — \
                    empty test chain but then-copy {repr thn} ≠ test {repr c}"
              bridge? := some (← mkAppM ``evrel_siff_if_or_bridge
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
                  reflectSExpr els', vC, ← ctxValExpr cfg ctx els',
                  hAX, pC, ← ctxValProof cfg ctx els'])
              postStart := .cons (.atom (.symbol ifS))
                (.cons c (.cons quoteT (.cons els' .nil)))
        -- whole-if finishing steps apply AFTER the branch congruence, on the
        -- rebuilt if
        let (postOpt, final) ← replayRewritesWith rec cfg ctx postStart postCh
        let postOpt ← chainReqEq postOpt
        -- the JOINT may need SWAPPED-P normalizations the children created
        -- (a NOT unfold inside a test position swaps the enclosing if,
        -- unrecorded — ORDEREDP-MEMB)
        let (swapOpt, final) ← normalizeSwapsToward cfg final rhs
        -- rewrite-equal's UNRECORDED nil-normalization inside a branch
        -- (`bridgeEqualNilNormDeep`) — same joint treatment as the swaps
        let (nilNormOpt, final) ← do
          if final != rhs then
            match ← bridgeEqualNilNormDeep cfg ctx final rhs with
            | some h => pure ((some h : Option Expr), rhs)
            | none => pure ((none : Option Expr), final)
          else pure ((none : Option Expr), final)
        unless final == rhs do
          throwError "if-finish/combined: children chains reached {repr final}, \
                      node rhs is {repr rhs}"
        if let some br := bridge? then
          -- the bridged composite S →eq target →SIFF postStart →eq final
          -- (rel = []): inject the eq parts into the SIff lane and transit;
          -- the node's chain contribution is IFF (consumed at the literal
          -- boundary by the spine's test-position collapse)
          let mut comp := br
          if target != S then
            let eqB ← mkAppM ``evalOpt_congr_if_branches_cond
              #[w, e, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
                reflectSExpr thn', reflectSExpr els', vC, pC, lamT, lamE]
            let eqBS ← mkAppM ``evrel_of_fuel_eq
              #[mkConst ``siff_refl, eqB, ← ctxValProof cfg ctx target]
            comp ← mkAppM ``evrel_trans #[mkConst ``siff_trans, eqBS, comp]
          let mut postParts : List Expr := []
          if let some p := postOpt then postParts := postParts ++ [p]
          if let some p := swapOpt then postParts := postParts ++ [p]
          if let some p := nilNormOpt then postParts := postParts ++ [p]
          unless postParts.isEmpty do
            let postEq ← chainEqs postParts
            let postS ← mkAppM ``evrel_of_fuel_eq
              #[mkConst ``siff_refl, postEq, ← ctxValProof cfg ctx final]
            comp ← mkAppM ``evrel_trans #[mkConst ``siff_trans, comp, postS]
          let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx final rest (chainPrefix ++ [n])
          return (some (← chainIffWithR cfg ctx comp finalTerm restProof), finalTerm)
        let mut proofs : List Expr := []
        if target != S then
          proofs := proofs ++ [← mkAppM ``evalOpt_congr_if_branches_cond
            #[w, e, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
              reflectSExpr thn', reflectSExpr els', vC, pC, lamT, lamE]]
        if let some p := postOpt then
          proofs := proofs ++ [p]
        if let some p := swapOpt then
          proofs := proofs ++ [p]
        if let some p := nilNormOpt then
          proofs := proofs ++ [p]
        if proofs.isEmpty then
          -- no effective rewrites: a no-op summary node
          unless S == rhs do
            throwError "if-finish/combined: no effective children but running \
                        subterm {repr S} ≠ rhs {repr rhs}"
          return ← replayRewritesWith rec cfg ctx start rest (chainPrefix ++ [n])
        let nodeProof ← chainEqs proofs
        let (lifted, newTerm) ←
          emitCongruence w e start (nodePath n) S final nodeProof
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest (chainPrefix ++ [n])
        return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
    -- a CONSTANT-TEST if-simplification whose recorded test does not match
    -- the running term's test: the test was resolved by an UNEMITTED
    -- type-alist lookup (a clause/segment fact, possibly through `equal`'s
    -- commutativity — if-interp-assumed-value2's rule). Mirror the
    -- resolution as an explicit test-position rewrite, then replay the
    -- recorded collapse on the reconciled term.
    let reconciled? ← do
      if (runeOf n).ty == "if-simplification" then
        match lhs with
        | .cons (.atom (.symbol ifS))
            (.cons (.cons (.atom (.symbol q)) (.cons cv .nil)) _) =>
          if ifS.name == "IF" && q.name == "QUOTE" && cv == SExpr.nil then
            let rel := relativizeFrames (nodePath n)
            let (steps, S) ← ofExcept (navigateFrames start rel)
            match S with
            | .cons (.atom (.symbol ifS'))
                (.cons T (.cons thn (.cons els .nil))) =>
              if ifS'.name == "IF" && S != lhs &&
                 lhs == SExpr.cons (.atom (.symbol ifS'))
                   (.cons (.cons (.atom (.symbol q)) (.cons cv .nil))
                     (.cons thn (.cons els .nil))) then
                -- derive `value of T = nil` from the in-scope facts: spine
                -- falsity (litFacts/segFacts), an enclosing if-test assumed
                -- FALSE (branchFacts), either through `equal`'s commutativity
                -- (if-interp-assumed-value2's rule), or through a
                -- :CONTEXT-SUBST segment equality pinning one `equal` side
                -- (a false `(not (equal p q))` gives vp = vq; the substituted
                -- test's falsity is then a direct fact)
                -- (litFactByTerm? itself already falls through to segFacts —
                -- the *1.5/2.1 segment fact resolves through it; audit F1
                -- removed a dead third arm that re-searched segFacts)
                let nilFactFor : SExpr → Option Expr := fun u =>
                  (ctx.litFactByTerm? u).orElse fun _ =>
                    (ctx.branchFacts.find? (fun (t, _, sign, _) =>
                      t == u && !sign)).map (·.2.2.2)
                let eqOf : SExpr → SExpr → SExpr := fun x y =>
                  .cons (.atom (.symbol { name := "EQUAL" }))
                    (.cons x (.cons y .nil))
                let directOrFlipped : SExpr → MetaM (Option Expr) := fun u => do
                  match nilFactFor u with
                  | some h => return some h
                  | none =>
                    match u with
                    | .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) =>
                      if eqS.name == "EQUAL" then
                        match nilFactFor (eqOf y x) with
                        | some h => do
                          let vx ← ctxValExpr cfg ctx x
                          let vy ← ctxValExpr cfg ctx y
                          let comm ← mkAppM ``logic_equal_comm #[vx, vy]
                          return some (← mkAppM ``Eq.trans #[comm, h])
                        | none => return none
                      else return none
                    | _ => return none
                let hNil? ← do
                  match ← directOrFlipped T with
                  | some h => pure (some h)
                  | none =>
                    match T with
                    | .cons (.atom (.symbol eqS)) (.cons u (.cons v .nil)) =>
                      if !(eqS.name == "EQUAL") then pure none else do
                      let mut found : Option Expr := none
                      -- equality sources: clausify-branch segment facts AND
                      -- clause-literal falsity facts of the same
                      -- `(not (equal p q))` shape (G2 rung 2: the hoisted
                      -- (NOT (EQUAL X1 (CAR X-EQUIV))) literal's falsity
                      -- pins vX1 = v(CAR X-EQUIV) at *1.5/2.1)
                      let eqSources : List (SExpr × Expr) :=
                        ctx.segFacts ++ ctx.litFacts.map (fun (_, l, h) => (l, h))
                      for (st, hSeg) in eqSources do
                        if found.isSome then break
                        let .cons (.atom (.symbol ns))
                            (.cons pq@(.cons (.atom (.symbol eqS'))
                              (.cons p (.cons q .nil))) .nil) := st
                          | continue
                        unless ns.name == "NOT" && eqS'.name == "EQUAL" do
                          continue
                        -- heq : vp = vq from the false segment literal
                        let vPQ ← ctxValExpr cfg ctx pq
                        -- TYPE-CHECKED (audit F8, the litFactByTermChecked?
                        -- discipline): a fact whose proof lives in ANOTHER
                        -- env context (pool-root/elim crossings) or whose
                        -- opaque pins drifted is SKIPPED, not crashed on
                        let expectedTy ← mkEq
                          (mkApp (mkConst ``Logic.not) vPQ)
                          (mkConst ``SExpr.nil)
                        unless ← isDefEq (← inferType hSeg) expectedTy do
                          continue
                        let hne ← mkAppM ``logic_not_nil_ne #[vPQ, hSeg]
                        let heq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hne]
                        let vu ← ctxValExpr cfg ctx u
                        let vv ← ctxValExpr cfg ctx v
                        -- the four side-substitution variants; each transports
                        -- vT to the substituted test's value, then a direct
                        -- fact finishes
                        let tryVariant (t' : SExpr) (vEq : Expr) :
                            MetaM (Option Expr) := do
                          match ← directOrFlipped t' with
                          | some h' => return some (← mkAppM ``Eq.trans #[vEq, h'])
                          | none => return none
                        let fR ← withLocalDeclD `z (mkConst ``SExpr) fun zV => do
                          mkLambdaFVars #[zV] (← mkAppM ``Logic.equal #[vu, zV])
                        let fL ← withLocalDeclD `z (mkConst ``SExpr) fun zV => do
                          mkLambdaFVars #[zV] (← mkAppM ``Logic.equal #[zV, vv])
                        if v == p then
                          -- T = (equal u p): vT = f vp = f vq = v(equal u q)
                          let vEq ← mkAppM ``congrArg #[fR, heq]
                          found ← tryVariant (eqOf u q) vEq
                        if found.isNone && v == q then
                          let vEq ← mkAppM ``Eq.symm #[← mkAppM ``congrArg #[fR, heq]]
                          found ← tryVariant (eqOf u p) vEq
                        if found.isNone && u == p then
                          let vEq ← mkAppM ``congrArg #[fL, heq]
                          found ← tryVariant (eqOf q v) vEq
                        if found.isNone && u == q then
                          let vEq ← mkAppM ``congrArg #[fL, heq]
                          found ← tryVariant (eqOf p v) (← mkAppM ``Eq.symm #[vEq])
                      pure found
                    | _ => pure none
                let some hNil := hNil?
                  | throwError "replayRewrites: unemitted test resolution — no \
                                in-scope nil fact for the if-test {repr T} \
                                (rewriting {repr start}; \
                                lit-facts {repr (ctx.litFacts.map (·.2.1))}; \
                                seg-facts {repr (ctx.segFacts.map (·.1))}) \
                                (frontier)"
                let pT ← ctxValProof cfg ctx T
                let pQ ← mkAppM ``re_val_quote
                  #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.nil]
                let testEq ← mkAppM ``fuel_eq_of_conv #[pT, pQ, hNil]
                -- lift the test rewrite at the node's path + the test position
                let mut inner := testEq
                let testStep : PathStep :=
                  { fn := ifS', arity := 3, argIdx := 0, siblings := [thn, els] }
                inner ← applyStep cfg.worldExpr cfg.envExpr testStep T
                  (SExpr.cons (.atom (.symbol q)) (.cons cv .nil)) inner
                let mut curL := S
                let mut curR := lhs
                for st in steps.reverse do
                  inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
                  curL := rebuild st curL
                  curR := rebuild st curR
                unless curL == start do
                  throwError "replayRewrites: test-resolution lift \
                              reconstructed {repr curL} ≠ {repr start}"
                pure (some (inner, curR))
              else pure none
            | _ => pure none
          else pure none
        | _ => pure none
      else pure none
    if let some (testChain, start') := reconciled? then
      -- eval start ≡ eval start[T := 'nil]; replay THIS node on the
      -- reconciled term and continue
      let (restAll, finalT) ← replayRewritesWith rec cfg ctx start' (n :: rest) chainPrefix
      return (some (← chainWithR cfg ctx testChain start' restAll), finalT)
    -- REWRITE-EQUAL cons-decomposition (sorting-completion-2, ORDERED-PERMS
    -- Subgoal *1/7'5' literal 10, both polarities): ACL2's rewrite-equal on
    -- (EQUAL s1 s2) rewrites the SYNTHESIZED components
    -- (rewrite-args '((car lhs) (car rhs)) — gstack bkptr 1/2, so the path
    -- frames name redexes that are NOT literal subterms), decides each
    -- component equality (a recorded node at the EQUAL's own path, or a
    -- SILENT type-alist refutation), then — cars equal — repeats for the
    -- cdrs. Verdicts: any component refuted ⇒ 'NIL
    -- (`logic_equal_nil_of_{car,cdr}_components`); both phases equal ⇒ 'T by
    -- cons-extensionality with consp evidence for BOTH sides
    -- (`logic_equal_t_of_components`). Detected at the FIRST scratch step;
    -- the whole remaining chain is the protocol — anything off-shape
    -- hard-fails.
    if (runeOf n).ty != "clause-context-resolution" then
      if let .cons (.atom (.symbol eqS)) (.cons s1 (.cons s2 .nil)) := start then
        if eqS.name == "EQUAL" then
          -- window-tagged detection (path-emission Phase 1): the fork
          -- brackets the component descents in equal-cars/equal-cdrs
          -- windows carrying BOTH synthesized redexes — no shape guessing.
          -- (cdrs-first arises when the cars phase decided with no scratch
          -- rewrite — its window is empty and unseen here.)
          if innerKindOf n == "equal-cars" || innerKindOf n == "equal-cdrs" then do
            -- UNRESOLVED PROBE block (fork-batch item A, 2026-08-09):
            -- classify the descent by its FIRST decision record — an
            -- identity record (rhs == lhs) means the whole descent resolved
            -- NOTHING (ACL2 probed the component equalities, possibly
            -- nesting further descents, and kept the running equality
            -- unchanged; HOW-MANY-BAD-PAIRS-BNEXT *1/6' literal 5). The
            -- honest consumption is the maximal block of window-tagged
            -- scratch + identity decision records as a NO-OP on the running
            -- term — the scratch rewrote SYNTHESIZED redexes only, and the
            -- records are verdict-only data. A RESOLVED record inside such
            -- a block is a frontier (no corpus witness); a resolved FIRST
            -- record falls through to the decomposition protocol below.
            let isDecision : ProofNode → Bool := fun m =>
              nodeOrigin m == "equal/cars-decision" ||
              nodeOrigin m == "equal/cdrs-decision"
            let firstDec? := (n :: rest).find? isDecision
            let unresolvedProbe := match firstDec? with
              | some m => (nodeLhsRhs m).1 == (nodeLhsRhs m).2
              | none => false
            if unresolvedProbe then do
              let mut restP : List ProofNode := n :: rest
              let mut consumed : List ProofNode := []
              let mut scanning := true
              while scanning do
                match restP with
                | m :: r' =>
                  if innerKindOf m == "equal-cars" ||
                      innerKindOf m == "equal-cdrs" then
                    consumed := consumed ++ [m]; restP := r'
                  else if isDecision m then
                    let (l', r'') := nodeLhsRhs m
                    unless r'' == l' do
                      throwError "replayRewrites: resolved {nodeOrigin m} \
                          record ({repr l'} ⇒ {repr r''}) inside an \
                          unresolved probe block (frontier)"
                    consumed := consumed ++ [m]; restP := r'
                  else scanning := false
                | [] => scanning := false
              return ← replayRewritesWith rec cfg ctx start restP
                (chainPrefix ++ consumed)
            let mut ctx ← pinTermOpaques cfg cfg.envExpr ctx start
            let vs1 ← ctxValExpr cfg ctx s1
            let vs2 ← ctxValExpr cfg ctx s2
            let mut nodesLeft : List ProofNode := n :: rest
            -- verdict accumulator: none = still deciding; some hEq = the
            -- final `Logic.equal vs1 vs2 = <const>` fact + the constant
            let mut verdict : Option (Expr × SExpr) := none
            let mut phaseComps : List Expr := []  -- car-, then cdr-phase
            for pfn in ["CAR", "CDR"] do
              if verdict.isSome then continue
              let mut c1 : SExpr := .cons (.atom (.symbol { name := pfn }))
                (.cons s1 .nil)
              let mut c2 : SExpr := .cons (.atom (.symbol { name := pfn }))
                (.cons s2 .nil)
              ctx ← pinTermOpaques cfg cfg.envExpr ctx c1
              ctx ← pinTermOpaques cfg cfg.envExpr ctx c2
              let mut h1 ← mkEqRefl (← ctxValExpr cfg ctx c1)
              let mut h2 ← mkEqRefl (← ctxValExpr cfg ctx c2)
              -- consume this phase's scratch rewrites (either side, any
              -- interleaving; each is a full node replayed by its own
              -- recipe)
              let mut scanning := true
              while scanning do
                match nodesLeft with
                | [] => scanning := false
                | n' :: r' =>
                  let (l', r'') := nodeLhsRhs n'
                  let phaseKind := if pfn == "CAR" then "equal-cars"
                                   else "equal-cdrs"
                  let side? : Option Nat :=
                    if innerKindOf n' == phaseKind then
                      match nodePath n' with
                      | .arg k _ :: _ => some k
                      | _ => none
                    else none
                  match side? with
                  | some 1 =>
                    if l' == c1 then
                      let e ← rec.node cfg ctx n'
                      ctx ← pinTermOpaques cfg cfg.envExpr ctx r''
                      let ve ← mkAppM ``val_eq_of_eval_eq
                        #[e, ← ctxValProof cfg ctx c1,
                          ← ctxValProof cfg ctx r'']
                      h1 ← mkAppM ``Eq.trans #[h1, ve]
                      c1 := r''; nodesLeft := r'
                    else scanning := false
                  | some 2 =>
                    if l' == c2 then
                      let e ← rec.node cfg ctx n'
                      ctx ← pinTermOpaques cfg cfg.envExpr ctx r''
                      let ve ← mkAppM ``val_eq_of_eval_eq
                        #[e, ← ctxValProof cfg ctx c2,
                          ← ctxValProof cfg ctx r'']
                      h2 ← mkAppM ``Eq.trans #[h2, ve]
                      c2 := r''; nodesLeft := r'
                    else scanning := false
                  | _ => scanning := false
              -- the phase decision: a recorded (EQUAL c1 c2) node at the
              -- EQUAL's own path, or a silent type-alist refutation
              let decT : SExpr := .cons (.atom (.symbol { name := "EQUAL" }))
                (.cons c1 (.cons c2 .nil))
              let dec? ← match nodesLeft with
                | n' :: r' => do
                  let (l', rr') := nodeLhsRhs n'
                  if l' == decT && (relativizeFrames (nodePath n')) == [] then
                    pure (some (n', rr', r'))
                  else pure none
                | [] => pure none
              match dec? with
              | some (n', rr', r') =>
                nodesLeft := r'
                let e ← rec.node cfg ctx n'
                ctx ← pinTermOpaques cfg cfg.envExpr ctx decT
                let vDec ← ctxValExpr cfg ctx decT
                if rr' == quoteT then
                  let vq ← mkAppM ``re_val_quote
                    #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
                  let ve ← mkAppM ``val_eq_of_eval_eq
                    #[e, ← ctxValProof cfg ctx decT, vq]
                  -- vDec = t → vc1 = vc2 → component equality
                  let _ := vDec
                  let hc ← mkAppM ``logic_eq_of_equal_t #[ve]
                  let hcomp ← mkAppM ``Eq.trans
                    #[h1, ← mkAppM ``Eq.trans #[hc, ← mkAppM ``Eq.symm #[h2]]]
                  phaseComps := phaseComps ++ [hcomp]
                else if rr' == quoteNil then
                  let vq ← mkAppM ``re_val_quote
                    #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.nil]
                  let ve ← mkAppM ``val_eq_of_eval_eq
                    #[e, ← ctxValProof cfg ctx decT, vq]
                  let lem := if pfn == "CAR" then
                    ``logic_equal_nil_of_car_components
                    else ``logic_equal_nil_of_cdr_components
                  verdict := some (← mkAppM lem #[h1, h2, ve], SExpr.nil)
                else
                  throwError "replayRewrites: rewrite-equal {pfn} decision \
                      node {repr decT} ⇒ {repr rr'} is not a constant \
                      verdict (frontier)"
              | none =>
                -- silent refutation from the in-scope context (the same
                -- facts ACL2's type-set consulted)
                ctx ← pinTermOpaques cfg cfg.envExpr ctx decT
                let hRef ← do
                  match ← typeSetWalk cfg ctx (.isNil decT) with
                  | some h => pure h
                  | none =>
                      throwError "replayRewrites: rewrite-equal {pfn} \
                          phase — no recorded decision and no in-scope \
                          refutation of {repr decT} (frontier)"
                let lem := if pfn == "CAR" then
                  ``logic_equal_nil_of_car_components
                  else ``logic_equal_nil_of_cdr_components
                verdict := some (← mkAppM lem #[h1, h2, hRef], SExpr.nil)
              -- fork-batch item A (2026-08-09): the emitted
              -- equal/{cars,cdrs}-decision record IS this phase's verdict,
              -- recorded at the descent level. When the phase ALSO carried
              -- an internal verdict node (the recursion's own
              -- equal/type-alist-nil, consumed as `dec?` above), the
              -- decision record re-states the same fact — consume it here,
              -- cross-checking agreement; a disagreement is emission
              -- divergence, hard-fail. (A LONE decision record is instead
              -- consumed by `dec?` itself — the matcher is origin-agnostic.)
              match nodesLeft with
              | n' :: r' =>
                let decOrigin := if pfn == "CAR" then "equal/cars-decision"
                                 else "equal/cdrs-decision"
                if nodeOrigin n' == decOrigin then
                  let (l', rr') := nodeLhsRhs n'
                  unless l' == decT do
                    throwError "replayRewrites: {decOrigin} record lhs \
                        {repr l'} ≠ the phase components {repr decT} \
                        (emission divergence)"
                  let expected := if verdict.isSome then quoteNil else quoteT
                  unless rr' == expected do
                    throwError "replayRewrites: {decOrigin} record verdict \
                        {repr rr'} ≠ the phase outcome {repr expected} \
                        (emission divergence)"
                  nodesLeft := r'
              | [] => pure ()
            let (hEq, cst) ← do
              match verdict with
              | some (h, c) => pure (h, c)
              | none => do
                -- both phases component-equal: 'T by cons-extensionality;
                -- consp evidence for BOTH sides from value shape/context
                let [hcompCar, hcompCdr] := phaseComps
                  | throwError "replayRewrites: rewrite-equal decomposition \
                      finished with {phaseComps.length} component proofs \
                      (internal)"
                let some hca ← typeSetWalk cfg ctx (.isConspT s1)
                  | throwError "replayRewrites: rewrite-equal — no consp \
                      evidence for {repr s1} (frontier)"
                let some hcb ← typeSetWalk cfg ctx (.isConspT s2)
                  | throwError "replayRewrites: rewrite-equal — no consp \
                      evidence for {repr s2} (frontier)"
                pure (← mkAppM ``logic_equal_t_of_components
                  #[hca, hcb, hcompCar, hcompCdr], SExpr.t)
            unless nodesLeft.isEmpty do
              throwError "replayRewrites: rewrite-equal decomposition left \
                  unconsumed nodes \
                  {repr (nodesLeft.map (fun m => (nodeLhsRhs m).1))} \
                  (frontier)"
            let pl ← ctxValProof cfg ctx start
            let pr ← mkAppM ``re_val_quote
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr cst]
            let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hEq]
            let resT : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
              (.cons cst .nil)
            return (some (step, false), resT)
    let nodeEq ← rec.node cfg ctx n
    let (lifted, newTerm) ←
      try
        emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) lhs rhs nodeEq
      catch ex =>
        let nch : String := toString (match n with | .node _ _ _ ch _ => ch.length)
        throwError "generic-tail lift for {(runeOf n).ty}/{nodeOrigin n} \
          (kind {innerKindOf n}, {nch} children): {ex.toMessageData}"
    -- an if-simplification AT THE CHAIN ROOT selects a branch; ACL2's rewrite-if
    -- keeps the if on the gstack while rewriting inside that branch, so the
    let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest
      (chainPrefix ++ [n])
    return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)

/- The tied node-level knot — the ONLY remaining mutual at this layer.
   Public names/signatures identical to the pre-WP2 mutual members. -/
mutual

partial def replayNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    : MetaM Expr :=
  replayNodeWith ⟨fun c x n' => replayNode c x n',
                  fun c x s ns => replayRewrites c x s ns⟩ cfg ctx n

partial def replayRewrites (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr) :
    List ProofNode →
    MetaM (Option (Expr × Bool) × SExpr) :=
  fun ns =>
    replayRewritesWith ⟨fun c x n => replayNode c x n,
                       fun c x s' ns' => replayRewrites c x s' ns'⟩ cfg ctx start ns

end

/-- The tied record itself (recipes outside this file recurse through it). -/
def nodeRec : NodeRec :=
  ⟨fun cfg ctx n => replayNode cfg ctx n,
   fun cfg ctx s ns => replayRewrites cfg ctx s ns⟩

end ACL2.Replay.Driver
