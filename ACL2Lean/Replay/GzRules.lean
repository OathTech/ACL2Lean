/-
  D5 — ground-zero rules as PRELUDE CONSTANTS (external-knowledge design
  §D5, WP3; policy MDD-ratified 2026-07-10).

  ACL2 admits the lexorder rules at boot with proofs SKIPPED
  (`ld-skip-proofsp`, interface-raw.lisp:9638) — no replayable ACL2
  evidence exists in any capturable image. The prelude constants below
  prove, ONCE, the ∀-env replayed statement of each such rule about the
  trusted-core primitive itself (`ACL2.lexorder`), resting on the
  `LexorderOrder` order theorems rather than on trust. This adds zero
  trust assumptions beyond the wiring assumption already policed
  differentially: the replayed statement's meaning is DEFINED by `Logic`/`evalOpt`.

  Statement discipline: each constant's type is EXACTLY the
  `mkRuleHypType` instance of the rule's EMITTED ground-zero snapshot
  entry (the `(:GROUND-ZERO-RULES …)` event: hyps, `:EQUIV EQUAL`,
  lhs, rhs `'T`), world-parametric (L3) with a LEXORDER no-shadow
  hypothesis (world-first dispatch would otherwise change the formula's
  meaning). The driver's discharge (`dischargeGzRuleHyp`) re-BUILDS the
  target type from the emitted spec and type-hints the instantiated
  constant against it — a drifted emission or a mis-stated constant
  fails there (fail-closed recompute-check, kernel-backed).
-/
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.LexorderOrder

namespace ACL2.Replay

open ACL2

/-- The term `(LEXORDER a b)`. -/
private def lexApp (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "LEXORDER" })) (.cons a (.cons b .nil))

private def vX : SExpr := .atom (.symbol { name := "X" })
private def vY : SExpr := .atom (.symbol { name := "Y" })
private def vZ : SExpr := .atom (.symbol { name := "Z" })

/-- The term `'T`. -/
private def qT : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)

/-- LEXORDER's head-symbol side conditions for `conv_builtin2`. -/
private theorem lex_ns :
    (Symbol.isNamed { name := "LEXORDER" } "QUOTE" = false) ∧
    (Symbol.isNamed { name := "LEXORDER" } "IF" = false) ∧
    (Symbol.isNamed { name := "LEXORDER" } "LET" = false) ∧
    (Symbol.isNamed { name := "LEXORDER" } "LET*" = false) := by decide

/-- `(LEXORDER a b)` on VARIABLE arguments converges to the primitive's
    value on the env lookups (the builtin dispatch under no-shadow). -/
private theorem lex_var_conv (w : World) (env : Env) (sa sb : Symbol)
    (hna : sa.isNamed "T" = false) (hnb : sb.isNamed "T" = false)
    (hno : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (lexApp (.atom (.symbol sa)) (.atom (.symbol sb)))
        = some (lexorder ((env.get? sa).getD .nil) ((env.get? sb).getD .nil)) :=
  conv_builtin2 w env { name := "LEXORDER" } (.atom (.symbol sa))
    (.atom (.symbol sb)) ((env.get? sa).getD .nil) ((env.get? sb).getD .nil)
    (lexorder ((env.get? sa).getD .nil) ((env.get? sb).getD .nil))
    lex_ns hno (re_val_var w env sa hna) (re_val_var w env sb hnb)
    (callBuiltin_lexorder _ _)

/-- A truthy lexorder value IS `t` (two-valuedness). -/
private theorem lexorder_t_of_ne_nil {a b : SExpr}
    (h : lexorder a b ≠ SExpr.nil) : lexorder a b = SExpr.t :=
  (lexorder_boolean a b).elim id (fun hn => absurd hn h)

/-- PRELUDE CONSTANT for ground-zero rule `LEXORDER-REFLEXIVE`
    (emitted entry: no hyps, `:EQUIV EQUAL`, `(LEXORDER X X)` ⇒ `'T`). -/
theorem gz_rule_lexorder_reflexive (w : World)
    (hno : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ env : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env (lexApp vX vX) = evalOpt f w env qT := by
  intro env
  refine fuel_eq_of_conv (lex_var_conv w env _ _ (by decide) (by decide) hno)
    (re_val_quote w env SExpr.t) ?_
  exact lexorder_refl _

/-- PRELUDE CONSTANT for ground-zero rule `LEXORDER-TRANSITIVE`
    (emitted entry: hyps `(LEXORDER X Y)`, `(LEXORDER Y Z)` — `Y` free —
    `:EQUIV EQUAL`, `(LEXORDER X Z)` ⇒ `'T`, `:match-free :all`). -/
theorem gz_rule_lexorder_transitive (w : World)
    (hno : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ env : Env,
      EvTrue w env (lexApp vX vY) →
      EvTrue w env (lexApp vY vZ) →
      ∃ N, ∀ f ≥ N,
        evalOpt f w env (lexApp vX vZ) = evalOpt f w env qT := by
  intro env h1 h2
  have cxy := lex_var_conv w env { name := "X" } { name := "Y" }
    (by decide) (by decide) hno
  have cyz := lex_var_conv w env { name := "Y" } { name := "Z" }
    (by decide) (by decide) hno
  have t1 := lexorder_t_of_ne_nil (ne_nil_of_evtrue_conv h1 cxy)
  have t2 := lexorder_t_of_ne_nil (ne_nil_of_evtrue_conv h2 cyz)
  refine fuel_eq_of_conv (lex_var_conv w env _ _ (by decide) (by decide) hno)
    (re_val_quote w env SExpr.t) ?_
  exact lexorder_trans t1 t2

/-! ### The list/arith boot rules (close-out D1: the constraint-theorem
    trees' remaining gz citations — same admission class as the lexorder
    pair: boot-strap `ld-skip-proofsp` rules with no replayable evidence,
    proved once about the trusted-core primitives). -/

private def sym (n : String) : SExpr := .atom (.symbol { name := n })
private def app1 (n : String) (a : SExpr) : SExpr :=
  .cons (sym n) (.cons a .nil)
private def app2 (n : String) (a b : SExpr) : SExpr :=
  .cons (sym n) (.cons a (.cons b .nil))
private def quo (v : SExpr) : SExpr :=
  .cons (sym "QUOTE") (.cons v .nil)
/-- The term `'NIL`. -/
private def qNil : SExpr := quo SExpr.nil
/-- `(env.get? s).getD nil` — the variable's env value. -/
private def envV (env : Env) (n : String) : SExpr :=
  (env.get? ({ name := n } : Symbol)).getD .nil

/-- `Logic.not (Logic.consp v) ≠ nil` forces a non-cons, whose `car` is
    `nil` (the primitive's default). -/
private theorem car_eq_nil_of_not_consp_ne_nil {v : SExpr}
    (h : Logic.not (Logic.consp v) ≠ SExpr.nil) :
    Logic.car v = SExpr.nil := by
  cases v with
  | cons a b => exact absurd rfl h
  | nil => rfl
  | atom a => rfl

/-- PRELUDE CONSTANT for ground-zero rule `DEFAULT-CAR`
    (emitted entry: hyps `((NOT (CONSP X)))`, `:EQUIV EQUAL`,
    `(CAR X)` ⇒ `'NIL`). -/
theorem gz_rule_default_car (w : World)
    (hnoCar : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (hnoConsp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (hnoNot : w.defs.get? ({ name := "NOT" } : Symbol) = none) :
    ∀ env : Env,
      EvTrue w env (app1 "NOT" (app1 "CONSP" vX)) →
      ∃ N, ∀ f ≥ N,
        evalOpt f w env (app1 "CAR" vX) = evalOpt f w env qNil := by
  intro env h
  have cx := re_val_var w env { name := "X" } (by decide)
  have cconsp := conv_builtin1 w env { name := "CONSP" } vX
    (envV env "X") (Logic.consp (envV env "X"))
    (by decide) hnoConsp cx rfl
  have cnot := conv_builtin1 w env { name := "NOT" } (app1 "CONSP" vX)
    (Logic.consp (envV env "X")) (Logic.not (Logic.consp (envV env "X")))
    (by decide) hnoNot cconsp rfl
  refine fuel_eq_of_conv
    (conv_builtin1 w env { name := "CAR" } vX
      (envV env "X") (Logic.car (envV env "X")) (by decide) hnoCar cx rfl)
    (re_val_quote w env SExpr.nil) ?_
  exact car_eq_nil_of_not_consp_ne_nil (ne_nil_of_evtrue_conv h cnot)

/-- `Logic.not (Logic.consp v) ≠ nil` forces a non-cons, whose `cdr` is
    `nil` (the primitive's default). -/
private theorem cdr_eq_nil_of_not_consp_ne_nil {v : SExpr}
    (h : Logic.not (Logic.consp v) ≠ SExpr.nil) :
    Logic.cdr v = SExpr.nil := by
  cases v with
  | cons a b => exact absurd rfl h
  | nil => rfl
  | atom a => rfl

/-- PRELUDE CONSTANT for ground-zero rule `DEFAULT-CDR`
    (emitted entry: hyps `((NOT (CONSP X)))`, `:EQUIV EQUAL`,
    `(CDR X)` ⇒ `'NIL`). -/
theorem gz_rule_default_cdr (w : World)
    (hnoCdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (hnoConsp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (hnoNot : w.defs.get? ({ name := "NOT" } : Symbol) = none) :
    ∀ env : Env,
      EvTrue w env (app1 "NOT" (app1 "CONSP" vX)) →
      ∃ N, ∀ f ≥ N,
        evalOpt f w env (app1 "CDR" vX) = evalOpt f w env qNil := by
  intro env h
  have cx := re_val_var w env { name := "X" } (by decide)
  have cconsp := conv_builtin1 w env { name := "CONSP" } vX
    (envV env "X") (Logic.consp (envV env "X"))
    (by decide) hnoConsp cx rfl
  have cnot := conv_builtin1 w env { name := "NOT" } (app1 "CONSP" vX)
    (Logic.consp (envV env "X")) (Logic.not (Logic.consp (envV env "X")))
    (by decide) hnoNot cconsp rfl
  refine fuel_eq_of_conv
    (conv_builtin1 w env { name := "CDR" } vX
      (envV env "X") (Logic.cdr (envV env "X")) (by decide) hnoCdr cx rfl)
    (re_val_quote w env SExpr.nil) ?_
  exact cdr_eq_nil_of_not_consp_ne_nil (ne_nil_of_evtrue_conv h cnot)

/-- IF with a converging nil test converges to the else-branch's value
    (the Replay-layer twin of `conv_if_true`). -/
private theorem gz_conv_if_false (w : World) (env : Env)
    (c t el ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some SExpr.nil)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w env el = some ev) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons t (.cons el .nil)))) = some ev := by
  obtain ⟨Nc, hcv⟩ := hc; obtain ⟨Ne, hev⟩ := he
  refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_if_false g w env c t el (hcv g (by omega))]
  exact hev g (by omega)

/-- `(IF a b c)`. -/
private def ifApp (a b c : SExpr) : SExpr :=
  .cons (sym "IF") (.cons a (.cons b (.cons c .nil)))

/-- `'(NIL)` — the CONS-CAR-CDR rule's else-value, `(cons nil nil)`
    quoted. -/
private def qNilList : SExpr := quo (.cons SExpr.nil SExpr.nil)

/-- PRELUDE CONSTANT for ground-zero rule `CONS-CAR-CDR`
    (emitted entry: no hyps, `:EQUIV EQUAL`,
    `(CONS (CAR X) (CDR X))` ⇒ `(IF (CONSP X) X '(NIL))`). -/
theorem gz_rule_cons_car_cdr (w : World)
    (hnoConsp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (hnoCar : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (hnoCdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (hnoCons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ env : Env,
      ∃ N, ∀ f ≥ N,
        evalOpt f w env (app2 "CONS" (app1 "CAR" vX) (app1 "CDR" vX))
          = evalOpt f w env (ifApp (app1 "CONSP" vX) vX qNilList) := by
  intro env
  obtain ⟨vx, hx⟩ : ∃ vx, ∃ N, ∀ f ≥ N, evalOpt f w env vX = some vx :=
    ⟨_, re_val_var w env { name := "X" } (by decide)⟩
  have hconsp := conv_builtin1 w env { name := "CONSP" } vX vx
    (Logic.consp vx) (by decide) hnoConsp hx rfl
  have hL := conv_builtin2 w env { name := "CONS" }
    (app1 "CAR" vX) (app1 "CDR" vX) (Logic.car vx) (Logic.cdr vx)
    (Logic.cons (Logic.car vx) (Logic.cdr vx)) (by decide) hnoCons
    (conv_builtin1 w env { name := "CAR" } vX vx (Logic.car vx)
      (by decide) hnoCar hx rfl)
    (conv_builtin1 w env { name := "CDR" } vX vx (Logic.cdr vx)
      (by decide) hnoCdr hx rfl)
    rfl
  match vx with
  | .cons a d =>
    exact fuel_eq_of_conv hL
      (conv_if_true w env (app1 "CONSP" vX) vX qNilList
        (Logic.consp (.cons a d)) (.cons a d) hconsp rfl hx)
      (by simp [Logic.cons, Logic.car, Logic.cdr])
  | .nil =>
    exact fuel_eq_of_conv hL
      (gz_conv_if_false w env (app1 "CONSP" vX) vX qNilList
        (.cons SExpr.nil SExpr.nil) hconsp
        (re_val_quote w env (.cons SExpr.nil SExpr.nil)))
      (by simp [Logic.cons, Logic.car, Logic.cdr])
  | .atom a =>
    exact fuel_eq_of_conv hL
      (gz_conv_if_false w env (app1 "CONSP" vX) vX qNilList
        (.cons SExpr.nil SExpr.nil) hconsp
        (re_val_quote w env (.cons SExpr.nil SExpr.nil)))
      (by simp [Logic.cons, Logic.car, Logic.cdr])

/-- The emitted `SYNP` hypothesis `(SYNP 'NIL '(SYNTAXP (QUOTEP v))
    '(IF (QUOTEP v) 'T 'NIL))` — logically `T` in ACL2; the constant
    receives it as an (unused) premise, exactly as emitted. -/
private def synpQuotep (v : String) : SExpr :=
  .cons (sym "SYNP")
    (.cons qNil
      (.cons (quo (app1 "SYNTAXP" (app1 "QUOTEP" (sym v))))
        (.cons (quo (.cons (sym "IF")
            (.cons (app1 "QUOTEP" (sym v))
              (.cons (quo SExpr.t) (.cons qNil .nil)))))
          .nil)))

/-- PRELUDE CONSTANT for ground-zero rule `FOLD-CONSTS-IN-+`
    (emitted entry: hyps `(SYNP …(QUOTEP X)…)`, `(SYNP …(QUOTEP Y)…)`,
    `:EQUIV EQUAL`, `(BINARY-+ X (BINARY-+ Y Z))` ⇒
    `(BINARY-+ (BINARY-+ X Y) Z)`). -/
theorem gz_rule_fold_consts_in_plus (w : World)
    (hno : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env : Env,
      EvTrue w env (synpQuotep "X") →
      EvTrue w env (synpQuotep "Y") →
      ∃ N, ∀ f ≥ N,
        evalOpt f w env (app2 "BINARY-+" vX (app2 "BINARY-+" vY vZ))
          = evalOpt f w env (app2 "BINARY-+" (app2 "BINARY-+" vX vY) vZ) := by
  intro env _ _
  have cx := re_val_var w env { name := "X" } (by decide)
  have cy := re_val_var w env { name := "Y" } (by decide)
  have cz := re_val_var w env { name := "Z" } (by decide)
  refine fuel_eq_of_conv
    (conv_builtin2 w env { name := "BINARY-+" } vX (app2 "BINARY-+" vY vZ)
      (envV env "X") (Logic.plus (envV env "Y") (envV env "Z"))
      (Logic.plus (envV env "X") (Logic.plus (envV env "Y") (envV env "Z")))
      (by decide) hno cx
      (conv_builtin2 w env { name := "BINARY-+" } vY vZ
        (envV env "Y") (envV env "Z")
        (Logic.plus (envV env "Y") (envV env "Z"))
        (by decide) hno cy cz rfl)
      rfl)
    (conv_builtin2 w env { name := "BINARY-+" } (app2 "BINARY-+" vX vY) vZ
      (Logic.plus (envV env "X") (envV env "Y")) (envV env "Z")
      (Logic.plus (Logic.plus (envV env "X") (envV env "Y")) (envV env "Z"))
      (by decide) hno
      (conv_builtin2 w env { name := "BINARY-+" } vX vY
        (envV env "X") (envV env "Y")
        (Logic.plus (envV env "X") (envV env "Y"))
        (by decide) hno cx cy rfl)
      cz rfl)
    (logic_plus_assoc (envV env "X") (envV env "Y") (envV env "Z")).symm

end ACL2.Replay
