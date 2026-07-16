/-
  J1(a) SPIKE — the TRUE-LISTP-FLATTEN mirror BY HAND
  (induction-generality design §6b; RATIFIED 2026-07-16).

  ACKNOWLEDGED WIP: this file carries explicit `sorry` placeholders — one
  per design joint — filled one at a time per the validation strategy. It
  is deliberately NOT imported by the root `ACL2Lean` module until
  sorry-free (build during development with
  `lake env lean ACL2Lean/Imported/FlattenSpike.lean`).

  What this spike validates (and what "done" means): the REAL
  TRUE-LISTP-FLATTEN mirror statement — read off the real tree in
  acl2_samples/recon-tests/10-tree-induction.proof-log, over the world
  derived from that log, with the driver's own telescope hypothesis
  shapes — proved by hand in EXACTLY the shapes the generalized scaffold
  (design I1–I5) will emit:

    - the env-level motive `P env := EvTrue w env ⟪(TRUE-LISTP (FLATTEN X))⟫`
      under strong induction on the μ-registry measure (I1/I2);
    - TWO IH instantiations in the step case — X := (CAR X) and
      X := (CDR X) — from the ONE strong IH (survey axis A1);
    - decrease obligations covered by FLATTEN's EMITTED termination
      clauses (both car and cdr clauses verified present in the log —
      restated C2 for this tree), discharged by the Count library from
      the case's branch fact (I4);
    - the substN bridge relating each IH instance to the substituted
      formula the tree consumes (I3).

  ACCEPTANCE RULE (theory-audit T6): every proof step below is annotated
  `-- [driver: <primitive>]` naming the existing lemma constant or the
  named-new-lemma the driver will mechanically produce for that step. A
  joint that can only be closed by an unannotatable tactic move is a STOP
  TRIGGER (design §6b).

  The tree (dumped 2026-07-16):
    Goal (TRUE-LISTP (FLATTEN X)) → push *1 (SINGLETON pool — the
    degenerate pool case) → INDUCTION on (FLATTEN X), measure
    (ACL2-COUNT X), on: X;
      case [(CONSP X)]: IH X := (CAR X), IH X := (CDR X)   (= Subgoal *1/1)
      case [(NOT (CONSP X))]: base                          (= Subgoal *1/2)
    Subgoal *1/2 (base): FLATTEN unfolds to (CONS X 'NIL) under the
      recognizer/false chain; TRUE-LISTP closes by recognizer/true.
    Subgoal *1/1 (step): simplify cites definition:FLATTEN,
      rewrite:TRUE-LISTP-APP, type-prescription:FLATTEN — so the mirror is
      CONDITIONAL on the rule:TRUE-LISTP-APP hypothesis (TRUE-LISTP-APP is
      itself a red row today), exactly as the driver's telescope offers it.
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.Count

namespace ACL2.Spike.Flatten

open ACL2 ACL2.Replay ACL2.Replay.Driver

/-! ## The real artifact -/

private def flattenLog : String :=
  include_str "../../acl2_samples/recon-tests/10-tree-induction.proof-log"

/-- Parse failure ⇒ `.done` ⇒ the world below is empty and every proof
    fails loudly. -/
def flattenDevelopment : Development :=
  (((ProofLog.parse flattenLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world flattenWorld from flattenDevelopment

-- pin the world really came from the log (not an empty fallback)
#guard (flattenDevelopment.toWorld.defs.get? { name := "FLATTEN" }).isSome
#guard (flattenDevelopment.toWorld.defs.get? { name := "APP" }).isSome

/-! ## Term literals (read off the tree; TRUE-LISTP is a BUILTIN —
    world-absent by the no-shadow exclusion, dispatched to `callBuiltin`) -/

def vX : SExpr := .atom (.symbol { name := "X" })
def vY : SExpr := .atom (.symbol { name := "Y" })

/-- The IH substitution terms from the emitted alists: `(CAR X)`, `(CDR X)`. -/
def carX : SExpr := .cons (.atom (.symbol { name := "CAR" })) (.cons vX .nil)
def cdrX : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons vX .nil)

def flattenT (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "FLATTEN" })) (.cons a .nil)
def appT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "APP" })) (.cons a (.cons b .nil))
def tlpT (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons a .nil)

/-- The pushed `*1` clause — SINGLETON pool, single literal:
    `(TRUE-LISTP (FLATTEN X))`. -/
def goalT : SExpr := tlpT (flattenT vX)

/-! ## The μ-registry instance (design I1)

Measure `(ACL2-COUNT X)`, measured subset {X} (= free vars of the measure
term ⊆ :CONTROLLERS (X) — theory-audit T3 check holds for this scheme).
Registry entry `ACL2-COUNT ↦ SExpr.acl2Count` over the measured
variable's env value. Total and pure; appears in NO statement below. -/

def μ (env : Env) : Nat := ((env.get? { name := "X" }).getD .nil).acl2Count

/-! ## The base case (Subgoal *1/2), as a standalone lemma

Needs NO telescope hypothesis: FLATTEN's unfold takes the non-recursive
else-branch. `flattenBody` is transcribed from the log and PINNED to the
parsed artifact by the `#guard` (recompute-check discipline). -/

/-- FLATTEN's body as emitted:
    `(IF (CONSP X) (APP (FLATTEN (CAR X)) (FLATTEN (CDR X))) (CONS X 'NIL))`. -/
def flattenBody : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
    (.cons (appT (flattenT carX) (flattenT cdrX))
    (.cons (.cons (.atom (.symbol { name := "CONS" }))
      (.cons vX (.cons Replay.quoteNil .nil)))
    .nil)))

#guard flattenDevelopment.toWorld.defs.get? { name := "FLATTEN" }
  == some ([{ name := "X" }], flattenBody)

/-- APP's body as emitted: `(IF (CONSP X) (CONS (CAR X) (APP (CDR X) Y)) Y)`. -/
def appBody : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
    (.cons (.cons (.atom (.symbol { name := "CONS" }))
      (.cons carX (.cons (appT cdrX vY) .nil)))
    (.cons vY .nil)))

#guard flattenDevelopment.toWorld.defs.get? { name := "APP" }
  == some ([{ name := "X" }, { name := "Y" }], appBody)

/-- `Logic.trueListp` is two-valued.
    [driver: named-new J2 lemma (`trueListp_boolean`), the TRUE-LISTP twin
    of `lexorder_boolean` — D4-adjacent builtin two-valuedness] -/
private theorem trueListp_boolean (v : SExpr) :
    Logic.trueListp v = SExpr.t ∨ Logic.trueListp v = SExpr.nil := by
  induction v with
  | cons a b iha ihb => simpa [Logic.trueListp] using ihb
  | nil => exact .inl rfl
  | atom x => exact .inr rfl

/-- BASE: a non-cons measured value — FLATTEN computes `(CONS X 'NIL)`
    (recognizer/false + if-simplification chain), TRUE-LISTP closes
    recognizer/true.
    [driver: replayDefinition unfold (conv_defn_1 + re_if_false) +
     recognizer kit (conv_builtin1/2, re_val_quote, evtrue_of_eq_t)] -/
private theorem base_case (env : Env) (xv : SExpr)
    (hget : (env.get? { name := "X" }).getD .nil = xv)
    (hconsp : Logic.consp xv = SExpr.nil) :
    EvTrue flattenWorld env goalT := by
  -- X converges to xv (at env, and at the unfold's bindArgs env)
  have hvarX : ∃ N, ∀ f ≥ N, evalOpt f flattenWorld env vX = some xv := by
    have h := re_val_var flattenWorld env { name := "X" } (by decide)
    rw [hget] at h; exact h
  have hX' := re_val_var_bind1 flattenWorld { name := "X" } xv
  -- (CONSP X) at the body env computes nil  [driver: conv_builtin1]
  have hc : ∃ N, ∀ f ≥ N,
      evalOpt f flattenWorld (bindArgs [{ name := "X" }] [xv])
        (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
      = some SExpr.nil := by
    have h := conv_builtin1 flattenWorld (bindArgs [{ name := "X" }] [xv])
      { name := "CONSP" } vX xv (Logic.consp xv) (by decide) (by decide) hX'
      (callBuiltin_consp xv)
    rw [hconsp] at h; exact h
  -- (CONS X 'NIL) at the body env computes (cons xv nil)  [driver: conv_builtin2]
  have hcons : ∃ N, ∀ f ≥ N,
      evalOpt f flattenWorld (bindArgs [{ name := "X" }] [xv])
        (.cons (.atom (.symbol { name := "CONS" }))
          (.cons vX (.cons Replay.quoteNil .nil)))
      = some (SExpr.cons xv .nil) :=
    conv_builtin2 flattenWorld (bindArgs [{ name := "X" }] [xv])
      { name := "CONS" } vX Replay.quoteNil xv .nil (SExpr.cons xv .nil)
      (by decide) (by decide) hX'
      (re_val_quote flattenWorld (bindArgs [{ name := "X" }] [xv]) .nil)
      rfl
  -- the body: IF false → else branch value  [driver: re_if_false]
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f flattenWorld (bindArgs [{ name := "X" }] [xv]) flattenBody
      = some (SExpr.cons xv .nil) := by
    obtain ⟨N1, h1⟩ := re_if_false flattenWorld (bindArgs [{ name := "X" }] [xv])
      (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
      (appT (flattenT carX) (flattenT cdrX))
      (.cons (.atom (.symbol { name := "CONS" }))
        (.cons vX (.cons Replay.quoteNil .nil)))
      (SExpr.cons xv .nil) hc hcons
    obtain ⟨N2, h2⟩ := hcons
    exact ⟨max N1 N2, fun f hf =>
      (h1 f (le_trans (le_max_left _ _) hf)).trans
        (h2 f (le_trans (le_max_right _ _) hf))⟩
  -- the unfold: (FLATTEN X) converges to (cons xv nil)  [driver: conv_defn_1]
  have hflat : ∃ N, ∀ f ≥ N,
      evalOpt f flattenWorld env (flattenT vX) = some (SExpr.cons xv .nil) :=
    conv_defn_1 flattenWorld env { name := "FLATTEN" } vX xv { name := "X" }
      flattenBody (SExpr.cons xv .nil) (by decide) (by decide) hvarX hbody
  -- TRUE-LISTP recognizer/true: trueListp (cons xv nil) = t
  -- [driver: conv_builtin1 + evtrue_of_eq_t]
  exact evtrue_of_eq_t
    (conv_builtin1 flattenWorld env { name := "TRUE-LISTP" } (flattenT vX)
      (SExpr.cons xv .nil) SExpr.t (by decide) (by decide) hflat
      (callBuiltin_true_listp (SExpr.cons xv .nil)))

/-! ## The mirror (CONDITIONAL — the driver's own telescope shapes)

Hypothesis types are hand-instantiations of the driver's builders:
`mkTotalityHypType` (total:FLATTEN, total:APP), `mkTpHypType`
(tp:FLATTEN — corollary `(CONSP (FLATTEN X))`, lifted at the application
value), `mkRuleHypType` (rule:TRUE-LISTP-APP — the stored rule verbatim
from the log's `(:RULES)` entry: hyps `((TRUE-LISTP Y))`, `:EQUIV EQUAL`,
lhs `(TRUE-LISTP (APP X Y))`, rhs `'T`). -/

theorem true_listp_flatten_mirror
    -- [driver: mkTotalityHypType FLATTEN 1]
    (htotal_flatten : ∀ (env : Env) (a : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f flattenWorld env a = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f flattenWorld env (flattenT a) = some v)
    -- [driver: mkTotalityHypType APP 2]
    (htotal_app : ∀ (env : Env) (a b : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f flattenWorld env a = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f flattenWorld env b = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f flattenWorld env (appT a b) = some v)
    -- [driver: mkTpHypType FLATTEN [X] (CONSP (FLATTEN X))] — OFFERED by the
    -- telescope (the step's rune summary cites type-prescription:FLATTEN) but
    -- NOT CONSUMED by this hand route (the rule's hyp relieves directly from
    -- the IH fact); the driver's used-filter would likewise drop it
    (_htp_flatten : ∀ (env : Env) (a : SExpr) (v : SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f flattenWorld env (flattenT a) = some v) →
      Logic.consp v = SExpr.t)
    -- [driver: mkRuleHypType (TRUE-LISTP-APP stored spec)]
    (hrule_tlp_app : ∀ env : Env,
      EvTrue flattenWorld env (tlpT vY) →
      ∃ N, ∀ f ≥ N,
        evalOpt f flattenWorld env (tlpT (appT vX vY))
          = evalOpt f flattenWorld env
              (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))) :
    ∀ env : Env, EvTrue flattenWorld env goalT := by
  intro env
  -- ── The scaffold spine (design I2) ─────────────────────────────────
  -- [driver: measure_strong_induction (MeasureImage Nat) — J2's once-proved
  --  scaffold lemma; here inlined as Nat strong induction on μ, exactly the
  --  `acl2Count_strong_induction` generalization pattern]
  generalize hμ : μ env = n
  induction n using Nat.strong_induction_on generalizing env with
  | _ n IH =>
    -- ── Ruling-test case split on the measured variable's VALUE ──────
    -- [driver: the case-tree branch on the ruling test's VALUE — the
    --  existing scaffold's consp split, generalized to emitted tests (I5)]
    match hshape : (env.get? { name := "X" }).getD .nil with
    | .cons a b =>
      -- ═ Subgoal *1/1 (STEP case, tests [(CONSP X)]) ═
      have hn : (SExpr.cons a b).acl2Count = n := by
        rw [← hμ]; simp only [μ, hshape]
      -- IH instantiation 1: X := (CAR X)  (survey axis A1, first of TWO)
      -- decrease: covered by FLATTEN's EMITTED clause
      --   ((NOT (CONSP X)) (O< (ACL2-COUNT (CAR X)) (ACL2-COUNT X)))
      -- [driver: Count.acl2Count_car_lt_of_consp + the I4 covering join]
      have hdec₁ : μ (envUpdate env [{ name := "X" }] [a]) < n := by
        have hupd : μ (envUpdate env [{ name := "X" }] [a]) = a.acl2Count := by
          simp [μ, envUpdate]
        rw [hupd, ← hn]
        exact acl2Count_car_lt a b
      have hIH₁ : EvTrue flattenWorld
          (envUpdate env [{ name := "X" }] [a]) goalT :=
        -- [driver: strong-IH application at the updated env (I3)]
        IH _ hdec₁ _ rfl
      -- IH instantiation 2: X := (CDR X)  (second IH from the SAME strong IH)
      -- [driver: Count.acl2Count_cdr_lt_of_consp + the I4 covering join]
      have hdec₂ : μ (envUpdate env [{ name := "X" }] [b]) < n := by
        have hupd : μ (envUpdate env [{ name := "X" }] [b]) = b.acl2Count := by
          simp [μ, envUpdate]
        rw [hupd, ← hn]
        exact acl2Count_cdr_lt a b
      have hIH₂ : EvTrue flattenWorld
          (envUpdate env [{ name := "X" }] [b]) goalT :=
        IH _ hdec₂ _ rfl
      -- substN bridges: each IH-at-env' IS the substituted formula at env
      -- (the tree's IH literals: (TRUE-LISTP (FLATTEN (CAR X))) etc.)
      -- [driver: evalOpt_substTerm_substN (EvalLemmas:1367), args valued in
      --  the ORIGINAL env — simultaneous-substitution semantics — then
      --  evtrue_of_fuel_eq; arg values via conv_builtin1 + re_val_var]
      have hvarX : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld env vX = some (SExpr.cons a b) := by
        have h := re_val_var flattenWorld env { name := "X" } (by decide)
        rw [hshape] at h
        exact h
      have hcarV : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld env carX = some a :=
        conv_builtin1 flattenWorld env { name := "CAR" } vX (SExpr.cons a b) a
          (by decide) (by decide) hvarX (callBuiltin_car (SExpr.cons a b))
      have hcdrV : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld env cdrX = some b :=
        conv_builtin1 flattenWorld env { name := "CDR" } vX (SExpr.cons a b) b
          (by decide) (by decide) hvarX (callBuiltin_cdr (SExpr.cons a b))
      have hIHf₁ : EvTrue flattenWorld env (tlpT (flattenT carX)) := by
        have hb := evalOpt_substTerm_substN flattenWorld env [{ name := "X" }]
          [carX] [a] goalT (by decide) rfl
          (by intro p hp; simp only [List.zip, List.zipWith, List.mem_singleton] at hp
              rw [hp]; exact hcarV)
        rw [show substTerm [{ name := "X" }] [carX] goalT
              = tlpT (flattenT carX) from rfl] at hb
        exact evtrue_of_fuel_eq hb hIH₁
      have hIHf₂ : EvTrue flattenWorld env (tlpT (flattenT cdrX)) := by
        have hb := evalOpt_substTerm_substN flattenWorld env [{ name := "X" }]
          [cdrX] [b] goalT (by decide) rfl
          (by intro p hp; simp only [List.zip, List.zipWith, List.mem_singleton] at hp
              rw [hp]; exact hcdrV)
        rw [show substTerm [{ name := "X" }] [cdrX] goalT
              = tlpT (flattenT cdrX) from rfl] at hb
        exact evtrue_of_fuel_eq hb hIH₂
      -- ═ the step-case BODY: Subgoal *1/1's recorded simplify chain ═
      -- Pinned values for the two FLATTEN sub-applications
      -- [driver: totality-hypothesis instantiation — the ctx.vals opaque pinning]
      have hcarVex : ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f flattenWorld env carX = some v := by
        obtain ⟨N, h⟩ := hcarV; exact ⟨N, a, h⟩
      have hcdrVex : ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f flattenWorld env cdrX = some v := by
        obtain ⟨N, h⟩ := hcdrV; exact ⟨N, b, h⟩
      obtain ⟨NFC, vFC, hFC⟩ := htotal_flatten env carX hcarVex
      obtain ⟨NFD, vFD, hFD⟩ := htotal_flatten env cdrX hcdrVex
      -- IH₂ at the VALUE level: trueListp vFD = t
      -- [driver: conv_builtin1 + ne_nil_of_evtrue_conv + trueListp_boolean]
      have hTLPfd : Logic.trueListp vFD = SExpr.t := by
        have hconv := conv_builtin1 flattenWorld env { name := "TRUE-LISTP" }
          (flattenT cdrX) vFD (Logic.trueListp vFD) (by decide) (by decide)
          ⟨NFD, hFD⟩ (callBuiltin_true_listp vFD)
        have hne := ne_nil_of_evtrue_conv hIHf₂ hconv
        rcases trueListp_boolean vFD with h | h
        · exact h
        · exact absurd h hne
      -- the RULE instance at env2 := env[X ↦ vFC, Y ↦ vFD]
      -- [driver: the with-lemma :SUBST instantiation at pinned values]
      have hgetX2 : (envUpdate env [{ name := "X" }, { name := "Y" }]
          [vFC, vFD]).get? { name := "X" } = some vFC := by
        simp [envUpdate]
      have hgetY2 : (envUpdate env [{ name := "X" }, { name := "Y" }]
          [vFC, vFD]).get? { name := "Y" } = some vFD := by
        simp [envUpdate]
      have hvarX2 := re_val_var_get flattenWorld _ { name := "X" } vFC hgetX2
      have hvarY2 := re_val_var_get flattenWorld _ { name := "Y" } vFD hgetY2
      -- hyp relief: EvTrue env2 (TRUE-LISTP Y)  [driver: relief from the IH fact]
      have hrelief : EvTrue flattenWorld
          (envUpdate env [{ name := "X" }, { name := "Y" }] [vFC, vFD])
          (tlpT vY) := by
        apply evtrue_of_eq_t
        have h := conv_builtin1 flattenWorld _ { name := "TRUE-LISTP" } vY vFD
          (Logic.trueListp vFD) (by decide) (by decide) hvarY2
          (callBuiltin_true_listp vFD)
        rw [hTLPfd] at h
        exact h
      have hruleEq := hrule_tlp_app _ hrelief
      -- the APP value at env2 (via totality) and its BODY fact (inverse unfold)
      -- [driver: htotal_app pinning + re_body_conv2]
      have hvarX2ex : ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f flattenWorld
            (envUpdate env [{ name := "X" }, { name := "Y" }] [vFC, vFD]) vX
          = some v := by
        obtain ⟨N, h⟩ := hvarX2; exact ⟨N, vFC, h⟩
      have hvarY2ex : ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f flattenWorld
            (envUpdate env [{ name := "X" }, { name := "Y" }] [vFC, vFD]) vY
          = some v := by
        obtain ⟨N, h⟩ := hvarY2; exact ⟨N, vFD, h⟩
      obtain ⟨NA, vAPP, hAPP2⟩ := htotal_app _ vX vY hvarX2ex hvarY2ex
      -- APP's BODY fact at bindArgs [X,Y] [vFC,vFD] (inverse unfold)
      -- [driver: re_body_conv2 — the driver's own body-from-app extractor]
      have hbodyAPP := re_body_conv2 flattenWorld
        (envUpdate env [{ name := "X" }, { name := "Y" }] [vFC, vFD])
        { name := "APP" } { name := "X" } { name := "Y" } appBody vX vY
        vFC vFD vAPP (by decide) (by decide) hvarX2 hvarY2 ⟨NA, hAPP2⟩
      -- decode the rule equation to the VALUE fact: trueListp vAPP = t
      -- [driver: the with-lemma value decode — fuel determinism at shared fuel]
      have hTLPapp : Logic.trueListp vAPP = SExpr.t := by
        have hTLPconv := conv_builtin1 flattenWorld
          (envUpdate env [{ name := "X" }, { name := "Y" }] [vFC, vFD])
          { name := "TRUE-LISTP" } (appT vX vY) vAPP (Logic.trueListp vAPP)
          (by decide) (by decide) ⟨NA, hAPP2⟩ (callBuiltin_true_listp vAPP)
        have hqT := re_val_quote flattenWorld
          (envUpdate env [{ name := "X" }, { name := "Y" }] [vFC, vFD]) SExpr.t
        obtain ⟨N1, h1⟩ := hTLPconv
        obtain ⟨N2, h2⟩ := hruleEq
        obtain ⟨N3, h3⟩ := hqT
        have hf := h1 (N1 + N2 + N3) (by omega)
        have hg := h2 (N1 + N2 + N3) (by omega)
        have hh := h3 (N1 + N2 + N3) (by omega)
        exact Option.some.inj (hf.symm.trans (hg.trans hh))
      -- FLATTEN sub-apps TRANSFERRED to the unfold's body env
      -- bindArgs [X] [cons a b]: invert each at env (re_body_conv1), rebuild
      -- at the body env (conv_defn_1) — the driver's pinning transfer
      have hbodyFC := re_body_conv1 flattenWorld env { name := "FLATTEN" }
        { name := "X" } flattenBody carX a vFC (by decide) (by decide)
        hcarV ⟨NFC, hFC⟩
      have hbodyFD := re_body_conv1 flattenWorld env { name := "FLATTEN" }
        { name := "X" } flattenBody cdrX b vFD (by decide) (by decide)
        hcdrV ⟨NFD, hFD⟩
      have hXB := re_val_var_bind1 flattenWorld { name := "X" } (SExpr.cons a b)
      have hcarB : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld (bindArgs [{ name := "X" }] [SExpr.cons a b])
            carX = some a :=
        conv_builtin1 flattenWorld _ { name := "CAR" } vX (SExpr.cons a b) a
          (by decide) (by decide) hXB (callBuiltin_car (SExpr.cons a b))
      have hcdrB : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld (bindArgs [{ name := "X" }] [SExpr.cons a b])
            cdrX = some b :=
        conv_builtin1 flattenWorld _ { name := "CDR" } vX (SExpr.cons a b) b
          (by decide) (by decide) hXB (callBuiltin_cdr (SExpr.cons a b))
      have hFCB : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld (bindArgs [{ name := "X" }] [SExpr.cons a b])
            (flattenT carX) = some vFC :=
        conv_defn_1 flattenWorld _ { name := "FLATTEN" } carX a { name := "X" }
          flattenBody vFC (by decide) (by decide) hcarB hbodyFC
      have hFDB : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld (bindArgs [{ name := "X" }] [SExpr.cons a b])
            (flattenT cdrX) = some vFD :=
        conv_defn_1 flattenWorld _ { name := "FLATTEN" } cdrX b { name := "X" }
          flattenBody vFD (by decide) (by decide) hcdrB hbodyFD
      -- (APP (FLATTEN (CAR X)) (FLATTEN (CDR X))) at the body env → vAPP
      -- [driver: conv_defn_2 forward with the SAME body fact]
      have hAPPB : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld (bindArgs [{ name := "X" }] [SExpr.cons a b])
            (appT (flattenT carX) (flattenT cdrX)) = some vAPP :=
        conv_defn_2 flattenWorld _ { name := "APP" } (flattenT carX)
          (flattenT cdrX) vFC vFD { name := "X" } { name := "Y" } appBody vAPP
          (by decide) (by decide) hFCB hFDB hbodyAPP
      -- the body's IF: consp (cons a b) = t → then-branch  [driver: re_if_true]
      have hconspB : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld (bindArgs [{ name := "X" }] [SExpr.cons a b])
            (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
          = some SExpr.t :=
        conv_builtin1 flattenWorld _ { name := "CONSP" } vX (SExpr.cons a b)
          SExpr.t (by decide) (by decide) hXB
          (callBuiltin_consp (SExpr.cons a b))
      have hbodyStep : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld (bindArgs [{ name := "X" }] [SExpr.cons a b])
            flattenBody = some vAPP := by
        obtain ⟨N1, h1⟩ := re_if_true flattenWorld
          (bindArgs [{ name := "X" }] [SExpr.cons a b])
          (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
          (appT (flattenT carX) (flattenT cdrX))
          (.cons (.atom (.symbol { name := "CONS" }))
            (.cons vX (.cons Replay.quoteNil .nil)))
          SExpr.t vAPP hconspB rfl hAPPB
        obtain ⟨N2, h2⟩ := hAPPB
        exact ⟨max N1 N2, fun f hf =>
          (h1 f (le_trans (le_max_left _ _) hf)).trans
            (h2 f (le_trans (le_max_right _ _) hf))⟩
      -- the unfold at env: (FLATTEN X) → vAPP  [driver: conv_defn_1]
      have hFXconv : ∃ N, ∀ f ≥ N,
          evalOpt f flattenWorld env (flattenT vX) = some vAPP :=
        conv_defn_1 flattenWorld env { name := "FLATTEN" } vX (SExpr.cons a b)
          { name := "X" } flattenBody vAPP (by decide) (by decide) hvarX hbodyStep
      -- close: TRUE-LISTP recognizer at the rule-derived value
      -- [driver: conv_builtin1 + evtrue_of_eq_t]
      exact evtrue_of_eq_t
        (conv_builtin1 flattenWorld env { name := "TRUE-LISTP" } (flattenT vX)
          vAPP SExpr.t (by decide) (by decide) hFXconv
          (hTLPapp ▸ callBuiltin_true_listp vAPP))
    | .atom av =>
      -- ═ Subgoal *1/2 (BASE case, tests [(NOT (CONSP X))]) ═
      exact base_case env (.atom av) hshape rfl
    | .nil =>
      -- same base case, nil shape (CONSP nil = nil)
      exact base_case env .nil hshape rfl

-- the standing verification (must print exactly the classical trio)
#print axioms true_listp_flatten_mirror

end ACL2.Spike.Flatten
