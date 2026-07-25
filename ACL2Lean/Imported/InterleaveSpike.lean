/-
  J1(b) SPIKE — the LEN-INTERLEAVE mirror BY HAND
  (induction-generality design §6b; RATIFIED 2026-07-16).

  COMPLETE (sorry-free; axioms {propext, Classical.choice, Quot.sound}) —
  a J1 validation artifact, deliberately NOT in the root import graph
  (build standalone with `lake env lean ACL2Lean/Imported/InterleaveSpike.lean`).
  (Header corrected 2026-07-18 — it previously read as WIP; audit F4.)

  What THIS spike validates (the measure joints, complementing J1(a)):
    - the μ-REGISTRY on a SUM measure: `(BINARY-+ (ACL2-COUNT X)
      (ACL2-COUNT Y))`, measured subset {Y, X} — μ = acl2Count(X-val) +
      acl2Count(Y-val) (I1);
    - the SWAP IH `X := Y, Y := (CDR X)` as a SIMULTANEOUS env update,
      with the decrease of the SUM under the swap covered by INTERLEAVE's
      EMITTED termination clause
      `((ATOM X) (O< (+ (acl2-count Y) (acl2-count (CDR X)))
                     (+ (acl2-count X) (acl2-count Y))))` (I3/I4);
    - the 2-formal substN bridge for the swap (args valued in the ORIGINAL
      env — the artifact itself confirms simultaneity: the tree's IH
      literal is exactly substTerm [X,Y] [Y,(CDR X)] goal).

  Tree (dumped 2026-07-16, 13-multi-measured-var.proof-log):
    Goal (EQUAL (LEN (INTERLEAVE X Y)) (BINARY-+ (LEN X) (LEN Y))) →
    push *1 (singleton pool) → INDUCTION on (INTERLEAVE X Y),
    measure (BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y)), on: Y, X;
      case [(ATOM X)]: base                     (= Subgoal *1/1)
      case [(NOT (ATOM X))]: IH X := Y, Y := (CDR X)   (= Subgoal *1/2)
    Step chain cites definition:INTERLEAVE, definition:LEN, CDR-CONS,
    COMMUTATIVITY(-2)-OF-+ — value-level Int arithmetic here, annotated to
    the driver's existing arithmetic recipes (re_plus_comm2 etc.).

  ACCEPTANCE RULE (T6): every step is annotated `-- [driver: <primitive>]`.
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.Count

namespace ACL2.Spike.Interleave

open ACL2 ACL2.Replay ACL2.Replay.Driver

/-! ## The real artifact -/

private def ivLog : String :=
  include_str "../../acl2_samples/recon-tests/13-multi-measured-var.proof-log"

def ivDevelopment : Development :=
  (((ProofLog.parse ivLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world ivWorld from ivDevelopment

#guard (ivDevelopment.toWorld.defs.get? { name := "INTERLEAVE" }).isSome

/-! ## Term literals (LEN and BINARY-+ are BUILTINS — world-absent) -/

def vX : SExpr := .atom (.symbol { name := "X" })
def vY : SExpr := .atom (.symbol { name := "Y" })
def cdrX : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons vX .nil)

def ivT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "INTERLEAVE" })) (.cons a (.cons b .nil))
def lenT (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "LEN" })) (.cons a .nil)
def plusT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons b .nil))
def equalT (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil))

/-- The pushed `*1` clause (singleton pool, single literal):
    `(EQUAL (LEN (INTERLEAVE X Y)) (BINARY-+ (LEN X) (LEN Y)))`. -/
def goalT : SExpr := equalT (lenT (ivT vX vY)) (plusT (lenT vX) (lenT vY))

/-- INTERLEAVE's body as emitted:
    `(IF (CONSP X) (CONS (CAR X) (INTERLEAVE Y (CDR X))) Y)`. -/
def ivBody : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
    (.cons (.cons (.atom (.symbol { name := "CONS" }))
      (.cons (.cons (.atom (.symbol { name := "CAR" })) (.cons vX .nil))
      (.cons (ivT vY cdrX) .nil)))
    (.cons vY .nil)))

#guard ivDevelopment.toWorld.defs.get? { name := "INTERLEAVE" }
  == some ([{ name := "X" }, { name := "Y" }], ivBody)

/-! ## The μ-registry SUM instance (design I1)

Measure `(BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y))`, measured subset
{Y, X} = free vars of the measure term ⊆ :CONTROLLERS (Y X) — T3 holds. -/

def μ (env : Env) : Nat :=
  ((env.get? { name := "X" }).getD .nil).acl2Count
    + ((env.get? { name := "Y" }).getD .nil).acl2Count

/-- `Logic.len` always returns an int atom (both arms of its match do).
    [driver: named-new J2 lemma (`len_int`) — the value decode the
    arithmetic recipes need] -/
private theorem len_int (v : SExpr) :
    ∃ k : Int, Logic.len v = .atom (.number (.int k)) := by
  cases v <;> exact ⟨_, rfl⟩

/-- `Logic.equal` is two-valued; a non-nil equal IS t (existing kit). -/
private theorem equal_t_of_ne_nil {a b : SExpr}
    (h : Logic.equal a b ≠ SExpr.nil) : Logic.equal a b = SExpr.t := by
  by_cases hab : a == b
  · simp [Logic.equal, hab]
  · exact absurd (by simp [Logic.equal, hab]) h

/-- Integer addition at the value layer: `Logic.plus` on int atoms.
    [driver: the arithmetic recipes' value decode (re_plus_* territory)] -/
private theorem plus_int (j k : Int) :
    Logic.plus (.atom (.number (.int j))) (.atom (.number (.int k)))
      = .atom (.number (.int (j + k))) := by
  simp [Logic.plus, Logic.toRat, Logic.mkNumber]

/-- BASE (Subgoal *1/1): a non-cons X — INTERLEAVE takes the else branch
    (value = Y's value), and the goal equality closes by
    `(+ 0 k) = k` arithmetic + equal-self.
    [driver: replayDefinition unfold (conv_defn_2 + re_if_false) +
     arithmetic value decode + evtrue_of_eq_t] -/
private theorem base_case (env : Env) (xv : SExpr)
    (hget : (env.get? { name := "X" }).getD .nil = xv)
    (hconsp : Logic.consp xv = SExpr.nil)
    (hlen0 : Logic.len xv = .atom (.number (.int 0))) :
    EvTrue ivWorld env goalT := by
  have hvarX : ∃ N, ∀ f ≥ N, evalOpt f ivWorld env vX = some xv := by
    have h := re_val_var ivWorld env { name := "X" } (by decide)
    rw [hget] at h; exact h
  have hvarY : ∃ N, ∀ f ≥ N, evalOpt f ivWorld env vY
      = some ((env.get? { name := "Y" }).getD .nil) :=
    re_val_var ivWorld env { name := "Y" } (by decide)
  -- the body at bindArgs [X,Y] [xv, yv]: consp → nil, else-branch → yv
  have hconspB : ∃ N, ∀ f ≥ N,
      evalOpt f ivWorld
        (bindArgs [{ name := "X" }, { name := "Y" }]
          [xv, (env.get? { name := "Y" }).getD .nil])
        (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
      = some SExpr.nil := by
    have h := conv_builtin1 ivWorld
      (bindArgs [{ name := "X" }, { name := "Y" }]
        [xv, (env.get? { name := "Y" }).getD .nil])
      { name := "CONSP" } vX xv (Logic.consp xv) (by decide) (by decide)
      (re_val_var_bind2_fst ivWorld { name := "X" } { name := "Y" } xv _)
      (callBuiltin_consp xv)
    rw [hconsp] at h; exact h
  have hYB := re_val_var_bind2_snd ivWorld { name := "X" } { name := "Y" }
    xv ((env.get? { name := "Y" }).getD .nil) (by decide)
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f ivWorld
        (bindArgs [{ name := "X" }, { name := "Y" }]
          [xv, (env.get? { name := "Y" }).getD .nil]) ivBody
      = some ((env.get? { name := "Y" }).getD .nil) := by
    obtain ⟨N1, h1⟩ := re_if_false ivWorld
      (bindArgs [{ name := "X" }, { name := "Y" }]
        [xv, (env.get? { name := "Y" }).getD .nil])
      (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
      (.cons (.atom (.symbol { name := "CONS" }))
        (.cons (.cons (.atom (.symbol { name := "CAR" })) (.cons vX .nil))
        (.cons (ivT vY cdrX) .nil)))
      vY ((env.get? { name := "Y" }).getD .nil) hconspB hYB
    obtain ⟨N2, h2⟩ := hYB
    exact ⟨max N1 N2, fun f hf =>
      (h1 f (le_trans (le_max_left _ _) hf)).trans
        (h2 f (le_trans (le_max_right _ _) hf))⟩
  -- (INTERLEAVE X Y) → yv  [driver: conv_defn_2]
  have hIV : ∃ N, ∀ f ≥ N,
      evalOpt f ivWorld env (ivT vX vY)
      = some ((env.get? { name := "Y" }).getD .nil) :=
    conv_defn_2 ivWorld env { name := "INTERLEAVE" } vX vY xv
      ((env.get? { name := "Y" }).getD .nil) { name := "X" } { name := "Y" }
      ivBody ((env.get? { name := "Y" }).getD .nil)
      (by decide) (by decide) hvarX hvarY hbody
  -- goal value: equal (len yv) (plus (len xv) (len yv)) = t by 0+k arithmetic
  have hlenIV := conv_builtin1 ivWorld env { name := "LEN" } (ivT vX vY)
    ((env.get? { name := "Y" }).getD .nil)
    (Logic.len ((env.get? { name := "Y" }).getD .nil))
    (by decide) (by decide) hIV
    (callBuiltin_len ((env.get? { name := "Y" }).getD .nil))
  have hlenX := conv_builtin1 ivWorld env { name := "LEN" } vX xv
    (Logic.len xv) (by decide) (by decide) hvarX (callBuiltin_len xv)
  have hlenY := conv_builtin1 ivWorld env { name := "LEN" } vY
    ((env.get? { name := "Y" }).getD .nil)
    (Logic.len ((env.get? { name := "Y" }).getD .nil))
    (by decide) (by decide) hvarY
    (callBuiltin_len ((env.get? { name := "Y" }).getD .nil))
  have hplusXY := conv_builtin2 ivWorld env { name := "BINARY-+" }
    (lenT vX) (lenT vY) (Logic.len xv)
    (Logic.len ((env.get? { name := "Y" }).getD .nil))
    (Logic.plus (Logic.len xv)
      (Logic.len ((env.get? { name := "Y" }).getD .nil)))
    (by decide) (by decide) hlenX hlenY rfl
  have hgoalVal := conv_builtin2 ivWorld env { name := "EQUAL" }
    (lenT (ivT vX vY)) (plusT (lenT vX) (lenT vY))
    (Logic.len ((env.get? { name := "Y" }).getD .nil))
    (Logic.plus (Logic.len xv)
      (Logic.len ((env.get? { name := "Y" }).getD .nil)))
    (Logic.equal (Logic.len ((env.get? { name := "Y" }).getD .nil))
      (Logic.plus (Logic.len xv)
        (Logic.len ((env.get? { name := "Y" }).getD .nil))))
    (by decide) (by decide) hlenIV hplusXY rfl
  have harith : Logic.equal (Logic.len ((env.get? { name := "Y" }).getD .nil))
      (Logic.plus (Logic.len xv)
        (Logic.len ((env.get? { name := "Y" }).getD .nil))) = SExpr.t := by
    obtain ⟨ky, hky⟩ := len_int ((env.get? { name := "Y" }).getD .nil)
    rw [hky, hlen0, plus_int]
    simp [Logic.equal]
  rw [harith] at hgoalVal
  exact evtrue_of_eq_t hgoalVal

/-! ## The mirror (CONDITIONAL — the driver's telescope shapes) -/

theorem len_interleave_mirror
    -- [driver: mkTotalityHypType INTERLEAVE 2]
    (htotal_iv : ∀ (env : Env) (a b : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f ivWorld env a = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f ivWorld env b = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f ivWorld env (ivT a b) = some v) :
    ∀ env : Env, EvTrue ivWorld env goalT := by
  intro env
  -- ── The scaffold spine (design I2, the SUM MeasureImage instance) ──
  -- [driver: measure_strong_induction (MeasureImage Nat) — J2's lemma]
  generalize hμ : μ env = n
  induction n using Nat.strong_induction_on generalizing env with
  | _ n IH =>
    -- ── Ruling-test case split (emitted tests: [(ATOM X)] / negation) ──
    -- [driver: the case-tree branch on the test's VALUE (I5)]
    match hshape : (env.get? { name := "X" }).getD .nil with
    | .cons a b =>
      -- ═ Subgoal *1/2 (STEP case, tests [(NOT (ATOM X))]) ═
      have hn : (SExpr.cons a b).acl2Count
          + ((env.get? { name := "Y" }).getD .nil).acl2Count = n := by
        rw [← hμ]; simp only [μ, hshape]
      -- THE SWAP IH: X := Y, Y := (CDR X) — env' updates BOTH, decrease of
      -- the SUM covered by INTERLEAVE's EMITTED clause
      --   ((ATOM X) (O< (+ (acl2-count Y) (acl2-count (CDR X)))
      --                 (+ (acl2-count X) (acl2-count Y))))
      -- [driver: named-new J4 Count lemma (swap-sum decrease) + I4 join]
      have hdec : μ (bindArgsOver env [{ name := "X" }, { name := "Y" }]
          [(env.get? { name := "Y" }).getD .nil, b]) < n := by
        have hupd : μ (bindArgsOver env [{ name := "X" }, { name := "Y" }]
            [(env.get? { name := "Y" }).getD .nil, b])
            = ((env.get? { name := "Y" }).getD .nil).acl2Count
              + b.acl2Count := by
          simp [μ, bindArgsOver]
        rw [hupd, ← hn]
        simp only [SExpr.acl2Count]
        omega
      have hIH : EvTrue ivWorld
          (bindArgsOver env [{ name := "X" }, { name := "Y" }]
            [(env.get? { name := "Y" }).getD .nil, b]) goalT :=
        -- [driver: strong-IH application at the SWAPPED env (I3)]
        IH _ hdec _ rfl
      -- the swap's argument values IN THE ORIGINAL env (simultaneity)
      -- [driver: re_val_var + conv_builtin1]
      have hvarX : ∃ N, ∀ f ≥ N,
          evalOpt f ivWorld env vX = some (SExpr.cons a b) := by
        have h := re_val_var ivWorld env { name := "X" } (by decide)
        rw [hshape] at h; exact h
      have hvarY : ∃ N, ∀ f ≥ N, evalOpt f ivWorld env vY
          = some ((env.get? { name := "Y" }).getD .nil) :=
        re_val_var ivWorld env { name := "Y" } (by decide)
      have hcdrV : ∃ N, ∀ f ≥ N,
          evalOpt f ivWorld env cdrX = some b :=
        conv_builtin1 ivWorld env { name := "CDR" } vX (SExpr.cons a b) b
          (by decide) (by decide) hvarX (callBuiltin_cdr (SExpr.cons a b))
      -- the 2-formal SIMULTANEOUS substN bridge: the IH at the swapped env
      -- IS the tree's IH literal
      --   (EQUAL (LEN (INTERLEAVE Y (CDR X))) (BINARY-+ (LEN Y) (LEN (CDR X))))
      -- [driver: evalOpt_substTerm_substN (2 pairs) + evtrue_of_fuel_eq]
      have hIHf : EvTrue ivWorld env
          (equalT (lenT (ivT vY cdrX)) (plusT (lenT vY) (lenT cdrX))) := by
        have hb := evalOpt_substTerm_substN ivWorld env
          [{ name := "X" }, { name := "Y" }] [vY, cdrX]
          [(env.get? { name := "Y" }).getD .nil, b] goalT (by decide) rfl
          (by intro p hp
              simp only [List.zip, List.zipWith, List.mem_cons,
                List.not_mem_nil, or_false] at hp
              rcases hp with h | h
              · rw [h]; exact hvarY
              · rw [h]; exact hcdrV)
        rw [show substTerm [{ name := "X" }, { name := "Y" }] [vY, cdrX] goalT
              = equalT (lenT (ivT vY cdrX)) (plusT (lenT vY) (lenT cdrX))
            from rfl] at hb
        exact evtrue_of_fuel_eq hb hIH
      -- ═ the step-case BODY (Subgoal *1/2''s recorded chain:
      --   definition:INTERLEAVE, definition:LEN (D4/gz_def_len territory),
      --   CDR-CONS, COMMUTATIVITY(-2)-OF-+ — value-level Int arithmetic,
      --   annotated to the driver's arithmetic recipes) ═
      -- pinned value of the recursive call  [driver: totality pinning]
      have hvarYex : ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f ivWorld env vY = some v := by
        obtain ⟨N, h⟩ := hvarY; exact ⟨N, _, h⟩
      have hcdrVex : ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f ivWorld env cdrX = some v := by
        obtain ⟨N, h⟩ := hcdrV; exact ⟨N, b, h⟩
      obtain ⟨NI, vI, hI⟩ := htotal_iv env vY cdrX hvarYex hcdrVex
      -- IH decode to the VALUE equation: len vI = plus (len yv) (len b)
      -- [driver: conv_builtin1/2 composition + ne_nil_of_evtrue_conv +
      --  Logic.eq_of_equal_ne_nil]
      have hlenI := conv_builtin1 ivWorld env { name := "LEN" } (ivT vY cdrX)
        vI (Logic.len vI) (by decide) (by decide) ⟨NI, hI⟩ (callBuiltin_len vI)
      have hlenY := conv_builtin1 ivWorld env { name := "LEN" } vY
        ((env.get? { name := "Y" }).getD .nil)
        (Logic.len ((env.get? { name := "Y" }).getD .nil))
        (by decide) (by decide) hvarY
        (callBuiltin_len ((env.get? { name := "Y" }).getD .nil))
      have hlenC := conv_builtin1 ivWorld env { name := "LEN" } cdrX b
        (Logic.len b) (by decide) (by decide) hcdrV (callBuiltin_len b)
      have hplusYC := conv_builtin2 ivWorld env { name := "BINARY-+" }
        (lenT vY) (lenT cdrX)
        (Logic.len ((env.get? { name := "Y" }).getD .nil)) (Logic.len b)
        (Logic.plus (Logic.len ((env.get? { name := "Y" }).getD .nil))
          (Logic.len b))
        (by decide) (by decide) hlenY hlenC rfl
      have hIHval := conv_builtin2 ivWorld env { name := "EQUAL" }
        (lenT (ivT vY cdrX)) (plusT (lenT vY) (lenT cdrX))
        (Logic.len vI)
        (Logic.plus (Logic.len ((env.get? { name := "Y" }).getD .nil))
          (Logic.len b))
        (Logic.equal (Logic.len vI)
          (Logic.plus (Logic.len ((env.get? { name := "Y" }).getD .nil))
            (Logic.len b)))
        (by decide) (by decide) hlenI hplusYC rfl
      have hlenEq : Logic.len vI
          = Logic.plus (Logic.len ((env.get? { name := "Y" }).getD .nil))
              (Logic.len b) :=
        Logic.eq_of_equal_ne_nil (ne_nil_of_evtrue_conv hIHf hIHval)
      -- the 2-ary PINNING TRANSFER  [driver: re_body_conv2 + conv_defn_2]
      have hbodyIV := re_body_conv2 ivWorld env { name := "INTERLEAVE" }
        { name := "X" } { name := "Y" } ivBody vY cdrX
        ((env.get? { name := "Y" }).getD .nil) b vI
        (by decide) (by decide) hvarY hcdrV ⟨NI, hI⟩
      have hXB := re_val_var_bind2_fst ivWorld { name := "X" } { name := "Y" }
        (SExpr.cons a b) ((env.get? { name := "Y" }).getD .nil)
      have hYB := re_val_var_bind2_snd ivWorld { name := "X" } { name := "Y" }
        (SExpr.cons a b) ((env.get? { name := "Y" }).getD .nil) (by decide)
      have hcarB := conv_builtin1 ivWorld
        (bindArgs [{ name := "X" }, { name := "Y" }]
          [SExpr.cons a b, (env.get? { name := "Y" }).getD .nil])
        { name := "CAR" } vX (SExpr.cons a b) a
        (by decide) (by decide) hXB (callBuiltin_car (SExpr.cons a b))
      have hcdrB := conv_builtin1 ivWorld
        (bindArgs [{ name := "X" }, { name := "Y" }]
          [SExpr.cons a b, (env.get? { name := "Y" }).getD .nil])
        { name := "CDR" } vX (SExpr.cons a b) b
        (by decide) (by decide) hXB (callBuiltin_cdr (SExpr.cons a b))
      have hIVB : ∃ N, ∀ f ≥ N,
          evalOpt f ivWorld
            (bindArgs [{ name := "X" }, { name := "Y" }]
              [SExpr.cons a b, (env.get? { name := "Y" }).getD .nil])
            (ivT vY cdrX) = some vI :=
        conv_defn_2 ivWorld _ { name := "INTERLEAVE" } vY cdrX
          ((env.get? { name := "Y" }).getD .nil) b { name := "X" }
          { name := "Y" } ivBody vI (by decide) (by decide) hYB hcdrB hbodyIV
      have hconsB : ∃ N, ∀ f ≥ N,
          evalOpt f ivWorld
            (bindArgs [{ name := "X" }, { name := "Y" }]
              [SExpr.cons a b, (env.get? { name := "Y" }).getD .nil])
            (.cons (.atom (.symbol { name := "CONS" }))
              (.cons (.cons (.atom (.symbol { name := "CAR" })) (.cons vX .nil))
              (.cons (ivT vY cdrX) .nil)))
          = some (SExpr.cons a vI) :=
        conv_builtin2 ivWorld _ { name := "CONS" }
          (.cons (.atom (.symbol { name := "CAR" })) (.cons vX .nil))
          (ivT vY cdrX) a vI (SExpr.cons a vI)
          (by decide) (by decide) hcarB hIVB rfl
      have hconspB : ∃ N, ∀ f ≥ N,
          evalOpt f ivWorld
            (bindArgs [{ name := "X" }, { name := "Y" }]
              [SExpr.cons a b, (env.get? { name := "Y" }).getD .nil])
            (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
          = some SExpr.t :=
        conv_builtin1 ivWorld _ { name := "CONSP" } vX (SExpr.cons a b)
          SExpr.t (by decide) (by decide) hXB
          (callBuiltin_consp (SExpr.cons a b))
      have hbodyStep : ∃ N, ∀ f ≥ N,
          evalOpt f ivWorld
            (bindArgs [{ name := "X" }, { name := "Y" }]
              [SExpr.cons a b, (env.get? { name := "Y" }).getD .nil]) ivBody
          = some (SExpr.cons a vI) := by
        obtain ⟨N1, h1⟩ := re_if_true ivWorld
          (bindArgs [{ name := "X" }, { name := "Y" }]
            [SExpr.cons a b, (env.get? { name := "Y" }).getD .nil])
          (.cons (.atom (.symbol { name := "CONSP" })) (.cons vX .nil))
          (.cons (.atom (.symbol { name := "CONS" }))
            (.cons (.cons (.atom (.symbol { name := "CAR" })) (.cons vX .nil))
            (.cons (ivT vY cdrX) .nil)))
          vY SExpr.t (SExpr.cons a vI) hconspB rfl hconsB
        obtain ⟨N2, h2⟩ := hconsB
        exact ⟨max N1 N2, fun f hf =>
          (h1 f (le_trans (le_max_left _ _) hf)).trans
            (h2 f (le_trans (le_max_right _ _) hf))⟩
      have hIVconv : ∃ N, ∀ f ≥ N,
          evalOpt f ivWorld env (ivT vX vY) = some (SExpr.cons a vI) :=
        conv_defn_2 ivWorld env { name := "INTERLEAVE" } vX vY
          (SExpr.cons a b) ((env.get? { name := "Y" }).getD .nil)
          { name := "X" } { name := "Y" } ivBody (SExpr.cons a vI)
          (by decide) (by decide) hvarX hvarY hbodyStep
      -- goal value + arithmetic close (the recorded COMMUTATIVITY rewrites,
      -- value-level)  [driver: gz_def_len/callBuiltin_len + re_plus recipes]
      have hlenIV := conv_builtin1 ivWorld env { name := "LEN" } (ivT vX vY)
        (SExpr.cons a vI) (Logic.len (SExpr.cons a vI))
        (by decide) (by decide) hIVconv (callBuiltin_len (SExpr.cons a vI))
      have hlenX := conv_builtin1 ivWorld env { name := "LEN" } vX
        (SExpr.cons a b) (Logic.len (SExpr.cons a b))
        (by decide) (by decide) hvarX (callBuiltin_len (SExpr.cons a b))
      have hplusXY := conv_builtin2 ivWorld env { name := "BINARY-+" }
        (lenT vX) (lenT vY) (Logic.len (SExpr.cons a b))
        (Logic.len ((env.get? { name := "Y" }).getD .nil))
        (Logic.plus (Logic.len (SExpr.cons a b))
          (Logic.len ((env.get? { name := "Y" }).getD .nil)))
        (by decide) (by decide) hlenX hlenY rfl
      have hgoalVal := conv_builtin2 ivWorld env { name := "EQUAL" }
        (lenT (ivT vX vY)) (plusT (lenT vX) (lenT vY))
        (Logic.len (SExpr.cons a vI))
        (Logic.plus (Logic.len (SExpr.cons a b))
          (Logic.len ((env.get? { name := "Y" }).getD .nil)))
        (Logic.equal (Logic.len (SExpr.cons a vI))
          (Logic.plus (Logic.len (SExpr.cons a b))
            (Logic.len ((env.get? { name := "Y" }).getD .nil))))
        (by decide) (by decide) hlenIV hplusXY rfl
      have harith : Logic.equal (Logic.len (SExpr.cons a vI))
          (Logic.plus (Logic.len (SExpr.cons a b))
            (Logic.len ((env.get? { name := "Y" }).getD .nil))) = SExpr.t := by
        obtain ⟨ky, hky⟩ := len_int ((env.get? { name := "Y" }).getD .nil)
        obtain ⟨kb, hkb⟩ := len_int b
        have hvi : Logic.len vI = .atom (.number (.int (ky + kb))) := by
          rw [hlenEq, hky, hkb, plus_int]
        have h1 : Logic.len (SExpr.cons a vI)
            = .atom (.number (.int (ky + kb + 1))) := by
          simp [Logic.len, hvi, Logic.toInt]
        have h2 : Logic.len (SExpr.cons a b)
            = .atom (.number (.int (kb + 1))) := by
          simp [Logic.len, hkb, Logic.toInt]
        rw [h1, h2, hky, plus_int]
        have hcomm : kb + 1 + ky = ky + kb + 1 := by omega
        rw [hcomm]
        simp [Logic.equal]
      rw [harith] at hgoalVal
      exact evtrue_of_eq_t hgoalVal
    | .atom av =>
      -- ═ Subgoal *1/1 (BASE case, tests [(ATOM X)]) ═
      exact base_case env (.atom av) hshape rfl rfl
    | .nil =>
      exact base_case env .nil hshape rfl rfl

-- the standing verification (must print exactly the classical trio)
#print axioms len_interleave_mirror

end ACL2.Spike.Interleave
