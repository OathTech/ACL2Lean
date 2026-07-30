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

end ACL2.Replay
