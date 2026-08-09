/-
  Replay/Lemmas/Derived — section-aligned positional slice of the former
  EvalLemmas monolith (perf arc, 2026-08-07): MOVE-ONLY; the cut points
  are the file's own section-header layer boundaries, which sit in def-before-use
  order, so the import chain IS the dependency order.
-/
import ACL2Lean.Replay.Lemmas.Core

namespace ACL2.Replay

open ACL2

/-! ## Layer 2: Derived rules (compose Layer 1) -/

/-- Logic.equal returns T iff arguments are BEq-equal. -/
theorem Logic.equal_t_iff (a b : SExpr) :
    Logic.equal a b = SExpr.t ↔ a = b := by
  constructor
  · intro h
    simp [Logic.equal] at h
    exact h
  · intro h; subst h; exact Logic.equal_self a

/-- A truthy `Logic.equal` pins genuine equality — the two-valued decode
    every `EvTrue` consumer of an `equal`-headed fact uses (G2: no exact-t
    pin needed; `Logic.equal` returns `t` or `nil` by definition). -/
theorem Logic.eq_of_equal_ne_nil {a b : SExpr}
    (h : Logic.equal a b ≠ SExpr.nil) : a = b := by
  by_cases hab : a == b
  · exact eq_of_beq hab
  · simp [Logic.equal, hab] at h

/-- Logic.not returns NIL iff the argument is truthy (non-nil). -/
theorem Logic.not_nil_iff (a : SExpr) :
    Logic.not a = SExpr.nil ↔ Logic.toBool a = true := by
  simp [Logic.not]

/-- normalizedName for lowercase symbols is identity (needed because
    String.map Char.toLower is @[irreducible]). -/
theorem Symbol.normalizedName_lowercase (s : Symbol)
    (h : s.name = s.name) : s.name = s.name := h.symm

-- callBuiltin for specific builtins — avoids unfolding the whole match.
-- These use the string directly, not normalizedName.
@[simp] theorem callBuiltin_equal (a b : SExpr) :
    callBuiltin "EQUAL" [a, b] = some (Logic.equal a b) := by rfl
@[simp] theorem callBuiltin_not (a : SExpr) :
    callBuiltin "NOT" [a] = some (Logic.not a) := by rfl
@[simp] theorem callBuiltin_consp (a : SExpr) :
    callBuiltin "CONSP" [a] = some (Logic.consp a) := by rfl
@[simp] theorem callBuiltin_car (a : SExpr) :
    callBuiltin "CAR" [a] = some (Logic.car a) := by rfl
@[simp] theorem callBuiltin_cdr (a : SExpr) :
    callBuiltin "CDR" [a] = some (Logic.cdr a) := by rfl
@[simp] theorem callBuiltin_plus (a b : SExpr) :
    callBuiltin "BINARY-+" [a, b] = some (Logic.plus a b) := by rfl
@[simp] theorem callBuiltin_times (a b : SExpr) :
    callBuiltin "BINARY-*" [a, b] = some (Logic.times a b) := by rfl
@[simp] theorem callBuiltin_true_listp (a : SExpr) :
    callBuiltin "TRUE-LISTP" [a] = some (Logic.trueListp a) := by
  rfl

@[simp] theorem callBuiltin_acl2_numberp (a : SExpr) :
    callBuiltin "ACL2-NUMBERP" [a] = some (Logic.acl2Numberp a) := by
  cases a with
  | atom x => cases x <;> rfl
  | nil => rfl
  | cons _ _ => rfl
@[simp] theorem callBuiltin_numerator (a : SExpr) :
    callBuiltin "NUMERATOR" [a] = some (Logic.numerator a) := by rfl
@[simp] theorem callBuiltin_denominator (a : SExpr) :
    callBuiltin "DENOMINATOR" [a] = some (Logic.denominator a) := by rfl
@[simp] theorem callBuiltin_unary_minus (a : SExpr) :
    callBuiltin "UNARY--" [a] = some (Logic.neg a) := by rfl
@[simp] theorem callBuiltin_coerce (a b : SExpr) :
    callBuiltin "COERCE" [a, b] = some (Logic.coerce a b) := by rfl
@[simp] theorem callBuiltin_realpart (a : SExpr) :
    callBuiltin "REALPART" [a] = some (Logic.realpart a) := by rfl
@[simp] theorem callBuiltin_imagpart (a : SExpr) :
    callBuiltin "IMAGPART" [a] = some (Logic.imagpart a) := by rfl
@[simp] theorem callBuiltin_complex_rationalp (a : SExpr) :
    callBuiltin "COMPLEX-RATIONALP" [a] = some (Logic.complexRationalp a) := by rfl
@[simp] theorem callBuiltin_atom (a : SExpr) :
    callBuiltin "ATOM" [a] = some (Logic.atom a) := by rfl
@[simp] theorem callBuiltin_endp (a : SExpr) :
    callBuiltin "ENDP" [a] = some (Logic.endp a) := by rfl
@[simp] theorem callBuiltin_natp (a : SExpr) :
    callBuiltin "NATP" [a] = some (Logic.natp a) := by rfl
@[simp] theorem callBuiltin_posp (a : SExpr) :
    callBuiltin "POSP" [a] = some (Logic.posp a) := by rfl
@[simp] theorem callBuiltin_booleanp (a : SExpr) :
    callBuiltin "BOOLEANP" [a] = some (Logic.booleanp a) := by rfl
@[simp] theorem callBuiltin_symbolp (a : SExpr) :
    callBuiltin "SYMBOLP" [a] = some (Logic.symbolp a) := by rfl
@[simp] theorem callBuiltin_stringp (a : SExpr) :
    callBuiltin "STRINGP" [a] = some (Logic.stringp a) := by rfl
@[simp] theorem callBuiltin_rationalp (a : SExpr) :
    callBuiltin "RATIONALP" [a] = some (Logic.rationalp a) := by
  cases a with
  | atom x => cases x <;> rfl
  | nil => rfl
  | cons _ _ => rfl
@[simp] theorem callBuiltin_nfix (a : SExpr) :
    callBuiltin "NFIX" [a] = some (Logic.nfix a) := by rfl
@[simp] theorem callBuiltin_len (a : SExpr) :
    callBuiltin "LEN" [a] = some (Logic.len a) := by rfl
@[simp] theorem callBuiltin_fix (a : SExpr) :
    callBuiltin "FIX" [a] = some (Logic.fix a) := by rfl

/-! ## D4 — builtin DEFINITION FACTS (external-knowledge design §D4, WP2)

Each `gz_def_<fn>` lemma states that a `callBuiltin` builtin's value function
agrees, pointwise, with the VALUE COMPOSITION of ACL2's own ground-zero defun
body for that function — the `(:DEFUN <fn> … :SOURCE :GROUND-ZERO)` snapshot
emitted at capture start. The rhs is EXACTLY the shape the driver's value
walker (`dpValExpr`/`re_val_if`: `cond (toBool ·) · ·` for `if`, the `Logic`
function for a builtin application, the literal for a quote) builds from the
emitted body, so the D4 route in `replayDefinition` can apply the lemma ONLY
when the emitted snapshot instance unifies — a drifted emission fails proof
construction (the fail-closed recompute-check; the statement is never trusted
free-floating).

Bonus, not incidental (design §D4): each lemma is a kernel-checked proof that
the trusted-core primitive agrees with ACL2's own definition of the function —
a fidelity validation the differential harness can only sample. -/

/-- `(DEFUN TRUE-LISTP (X) (IF (CONSP X) (TRUE-LISTP (CDR X)) (EQ X NIL)))`
    (the snapshot body carries the translated `(EQUAL X 'NIL)`). -/
theorem gz_def_true_listp (a : SExpr) :
    Logic.trueListp a
      = cond (Logic.toBool (Logic.consp a))
          (Logic.trueListp (Logic.cdr a))
          (Logic.equal a SExpr.nil) := by
  cases a <;> rfl

/-- `(DEFUN LEN (X) (IF (CONSP X) (+ 1 (LEN (CDR X))) 0))` (the snapshot
    body carries the translated `(BINARY-+ '1 (LEN (CDR X)))`). -/
theorem gz_def_len (a : SExpr) :
    Logic.len a
      = cond (Logic.toBool (Logic.consp a))
          (Logic.plus (.atom (.number (.int 1))) (Logic.len (Logic.cdr a)))
          (.atom (.number (.int 0))) := by
  cases a with
  | cons h t =>
    -- `len` returns an int atom for every constructor of `t`, so the
    -- rational `plus` collapses to integer successor.
    obtain ⟨k, hk⟩ : ∃ k, Logic.len t = .atom (.number (.int k)) := by
      cases t <;> exact ⟨_, rfl⟩
    simp [Logic.len, Logic.plus, Logic.mkNumber, Logic.toRat, hk, Int.add_comm]
  | nil => rfl
  | atom x => rfl

/-- `(DEFUN NOT (P) (IF P NIL T))`. -/
theorem gz_def_not (a : SExpr) :
    Logic.not a = cond (Logic.toBool a) SExpr.nil SExpr.t := by
  cases a <;> rfl

/-- `(DEFUN NFIX (X) (IF (INTEGERP X) (IF (< X 0) 0 X) 0))`. -/
theorem gz_def_nfix (a : SExpr) :
    Logic.nfix a
      = cond (Logic.toBool (Logic.integerp a))
          (cond (Logic.toBool (Logic.lt a (.atom (.number (.int 0)))))
            (.atom (.number (.int 0))) a)
          (.atom (.number (.int 0))) := by
  cases a with
  | atom x =>
    cases x with
    | number n =>
      cases n with
      | int k =>
        rcases lt_or_ge k 0 with hk | hk <;>
          simp [Logic.toRat, hk, Int.not_lt.mpr, Int.not_le.mpr]
      | rational n d hc => rfl
    | _ => rfl
  | _ => rfl

/-- `(DEFUN FIX (X) (IF (ACL2-NUMBERP X) X 0))`. -/
theorem gz_def_fix (a : SExpr) :
    Logic.fix a
      = cond (Logic.toBool (Logic.acl2Numberp a)) a
          (.atom (.number (.int 0))) := by
  cases a with
  | atom x => cases x <;> rfl
  | _ => rfl

/-- `(DEFUN BOOLEANP (X) (IF (EQUAL X T) T (EQUAL X NIL)))`. -/
theorem gz_def_booleanp (a : SExpr) :
    Logic.booleanp a
      = cond (Logic.toBool (Logic.equal a SExpr.t)) SExpr.t
          (Logic.equal a SExpr.nil) := by
  by_cases ht : a == SExpr.t <;> by_cases hn : a == SExpr.nil <;>
    simp_all [Logic.booleanp, Logic.equal]

/-- `(DEFUN ENDP (X) (IF (CONSP X) NIL T))` (a `defun` in axioms.lisp;
    guard-trivial body). -/
theorem gz_def_endp (a : SExpr) :
    Logic.endp a
      = cond (Logic.toBool (Logic.consp a)) SExpr.nil SExpr.t := by
  cases a <;> rfl

/-- `(DEFUN ATOM (X) (IF (CONSP X) NIL T))` — same body shape as `ENDP`. -/
theorem gz_def_atom (a : SExpr) :
    Logic.atom a
      = cond (Logic.toBool (Logic.consp a)) SExpr.nil SExpr.t := by
  cases a <;> rfl

/-! ### D4 close-out completion (Phase 3 close-out item 2): agreement
lemmas for the REMAINING builtin-named ground-zero snapshot defuns
(audit 2026-08-08 outside F13). `LEXORDER` and `EXPT` are FLAGGED
instead (see `scripts/check-gz-agreement.sh`): their emitted bodies
cite non-builtin fns (`ALPHORDER`, `ZIP`), so the pure-`Logic` value
composition this family states does not exist for them; `LEXORDER`'s
fidelity rests on the `LexorderOrder` theorems + the differential
corpus. -/

/-- `(DEFUN IMPLIES (P Q) (IF P (IF Q 'T 'NIL) 'T))`. -/
theorem gz_def_implies (a b : SExpr) :
    Logic.implies a b
      = cond (Logic.toBool a)
          (cond (Logic.toBool b) SExpr.t SExpr.nil) SExpr.t := by
  cases ha : Logic.toBool a <;> cases hb : Logic.toBool b <;>
    simp only [Logic.implies, ha, hb] <;> rfl

/-- `(DEFUN IFF (P Q) (IF P (IF Q 'T 'NIL) (IF Q 'NIL 'T)))`. -/
theorem gz_def_iff (a b : SExpr) :
    Logic.iff a b
      = cond (Logic.toBool a)
          (cond (Logic.toBool b) SExpr.t SExpr.nil)
          (cond (Logic.toBool b) SExpr.nil SExpr.t) := by
  cases ha : Logic.toBool a <;> cases hb : Logic.toBool b <;>
    simp only [Logic.iff, ha, hb] <;> rfl

/-- `(DEFUN EQL (X Y) (EQUAL X Y))` — the `EQL` builtin dispatches to
    `Logic.equal`, so the agreement is stated at the `callBuiltin`
    level (there is no distinct `Logic` value fn to relate). -/
theorem gz_def_eql (a b : SExpr) :
    callBuiltin "EQL" [a, b] = some (Logic.equal a b) := rfl

/-- `(DEFUN FORCE (X) X)` — identity. -/
theorem gz_def_force (a : SExpr) :
    callBuiltin "FORCE" [a] = some a := rfl

/-- `(DEFUN HIDE (X) X)` — identity. -/
theorem gz_def_hide (a : SExpr) :
    callBuiltin "HIDE" [a] = some a := rfl

/-- `(DEFUN IFIX (X) (IF (INTEGERP X) X '0))` — the `IFIX` builtin arm
    is an inline match, so the agreement is stated at the `callBuiltin`
    level. -/
theorem gz_def_ifix (a : SExpr) :
    callBuiltin "IFIX" [a]
      = some (cond (Logic.toBool (Logic.integerp a)) a
          (.atom (.number (.int 0)))) := by
  cases a with
  | atom x =>
    cases x with
    | number n => cases n <;> rfl
    | _ => rfl
  | _ => rfl

/-- `(DEFUN NATP (X) (IF (INTEGERP X) (IF (< X '0) 'NIL 'T) 'NIL))`. -/
theorem gz_def_natp (a : SExpr) :
    Logic.natp a
      = cond (Logic.toBool (Logic.integerp a))
          (cond (Logic.toBool (Logic.lt a (.atom (.number (.int 0)))))
            SExpr.nil SExpr.t)
          SExpr.nil := by
  cases a with
  | atom x =>
    cases x with
    | number n =>
      cases n with
      | int k =>
        rcases lt_or_ge k 0 with hk | hk <;>
          simp [Logic.toRat, hk, Int.not_lt.mpr, Int.not_le.mpr]
      | rational n d hc => rfl
    | _ => rfl
  | _ => rfl

/-- `(DEFUN POSP (X) (IF (INTEGERP X) (< '0 X) 'NIL))`. -/
theorem gz_def_posp (a : SExpr) :
    Logic.posp a
      = cond (Logic.toBool (Logic.integerp a))
          (Logic.lt (.atom (.number (.int 0))) a) SExpr.nil := by
  cases a with
  | atom x =>
    cases x with
    | number n =>
      cases n with
      | int k =>
        rcases lt_or_ge 0 k with hk | hk <;>
          simp [Logic.toRat, hk, Int.not_lt.mpr]
      | rational n d hc => rfl
    | _ => rfl
  | _ => rfl

/-- `(DEFUN ZP (X) (IF (INTEGERP X) (IF (< '0 X) 'NIL 'T) 'T))` — a
    non-integer coerces to `0` under `toInt`, agreeing with the body's
    `'T` else-branch. -/
theorem gz_def_zp (a : SExpr) :
    Logic.zp a
      = cond (Logic.toBool (Logic.integerp a))
          (cond (Logic.toBool
              (Logic.lt (.atom (.number (.int 0))) a))
            SExpr.nil SExpr.t)
          SExpr.t := by
  cases a with
  | atom x =>
    cases x with
    | number n =>
      cases n with
      | int k =>
        rcases lt_or_ge 0 k with hk | hk <;>
          simp [Logic.toRat, hk, Int.not_lt.mpr, Int.not_le.mpr]
      | rational n d hc => rfl
    | _ => rfl
  | _ => rfl

/-! ### IF-collapse reconciliation value pack (final-closeout arc —
the PCE-class chain-end bridge): boolean-RANGE facts for the emitted
case-split shapes and the `(IF x 'T 'NIL) ⇒ x` collapse, plus
converged-value uniqueness. -/

/-- `Logic.equal` is two-valued. -/
theorem logic_equal_range (a b : SExpr) :
    Logic.equal a b = SExpr.t ∨ Logic.equal a b = SExpr.nil := by
  by_cases h : a == b <;> simp [Logic.equal, h]

/-- `Logic.not` is two-valued. -/
theorem logic_not_range (a : SExpr) :
    Logic.not a = SExpr.t ∨ Logic.not a = SExpr.nil := by
  unfold Logic.not
  by_cases h : Logic.toBool a = true
  · rw [if_pos h]; right; rfl
  · rw [if_neg h]; left; rfl

/-- A `cond` of two-valued branches is two-valued. -/
theorem cond_range {x y : SExpr} (b : Bool)
    (hx : x = SExpr.t ∨ x = SExpr.nil)
    (hy : y = SExpr.t ∨ y = SExpr.nil) :
    cond b x y = SExpr.t ∨ cond b x y = SExpr.nil := by
  cases b <;> simpa

/-- The `(IF x 'T 'NIL)` collapse for a two-valued `x`: the value
    composition `cond (toBool v) t nil` IS `v`. -/
theorem cond_tnil_of_range {v : SExpr}
    (h : v = SExpr.t ∨ v = SExpr.nil) :
    cond (Logic.toBool v) SExpr.t SExpr.nil = v := by
  rcases h with h | h <;> subst h <;> rfl

/-- A `cond` on a test KNOWN `'t` takes its first branch. -/
theorem cond_of_val_t {v x y : SExpr} (h : v = SExpr.t) :
    cond (Logic.toBool v) x y = x := by subst h; rfl

/-- Converged values are unique (fuel monotonicity's working form). -/
theorem conv_val_eq {w : World} {env : Env} {t u v : SExpr}
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env t = some u)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env t = some v) : u = v := by
  obtain ⟨n1, h1⟩ := h1; obtain ⟨n2, h2⟩ := h2
  have e1 := h1 (n1 + n2) (by omega)
  have e2 := h2 (n1 + n2) (by omega)
  exact Option.some.inj (e1.symm.trans e2)

/-- The L-orientation call-stack fold's value identity (RESURRECTED at
    the final close-out — killed at 910785a; the PCE tower is its now-
    reachable consumer): `(equal 't (equal a b)) = (equal a b)`. -/
theorem logic_equal_t_equal_l (a b : SExpr) :
    Logic.equal SExpr.t (Logic.equal a b) = Logic.equal a b := by
  by_cases h : (a == b) = true <;> simp [Logic.equal, h, SExpr.t]

/-- The BOOLEAN-TP fold's value identity (RESURRECTED, same round): a
    two-valued `v` (the emitted boolean TP corollary's lifted content)
    satisfies `(equal v 't) = v`. -/
theorem logic_equal_t_self_of_boolean_tp {v : SExpr}
    (h : (bif Logic.toBool (Logic.equal v SExpr.t) then SExpr.t
          else Logic.equal v SExpr.nil) = SExpr.t) :
    Logic.equal v SExpr.t = v := by
  by_cases hv : (v == SExpr.t) = true
  · have hveq : v = SExpr.t := eq_of_beq hv
    subst hveq
    simp [Logic.equal]
  · have h1 : Logic.equal v SExpr.t = SExpr.nil := by
      simp [Logic.equal, hv]
    rw [h1]
    rw [h1] at h
    simp only [Logic.toBool, cond_false] at h
    have hnil : v = SExpr.nil := by
      by_cases h2 : (v == SExpr.nil) = true
      · exact eq_of_beq h2
      · simp [Logic.equal, h2, SExpr.t] at h
    rw [hnil]

/-- T3: EQUAL-self — (EQUAL t t) evaluates to T when t converges. -/
theorem evalOpt_equal_self (f : Nat) (w : World) (env : Env)
    (t : SExpr) (v : SExpr)
    (hv : evalOpt f w env t = some v)
    (h_not_def : w.defs.get? ({ name := "EQUAL" } : Symbol) = none) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "EQUAL" })) (.cons t (.cons t .nil)))
    = some SExpr.t := by
  have h_ns : ({ name := "EQUAL" } : Symbol).isNamed "QUOTE" = false ∧
              ({ name := "EQUAL" } : Symbol).isNamed "IF" = false ∧
              ({ name := "EQUAL" } : Symbol).isNamed "LET" = false ∧
              ({ name := "EQUAL" } : Symbol).isNamed "LET*" = false := by decide
  rw [evalOpt_builtin_2 f w env { name := "EQUAL" } t t v v h_ns h_not_def hv hv]
  simp [callBuiltin_equal]

/-- T2: EQUAL-T implies evaluation equality. -/
theorem eval_equal_t_implies_eq (f : Nat) (w : World) (env : Env)
    (a b : SExpr) (va vb : SExpr)
    (ha : evalOpt f w env a = some va)
    (hb : evalOpt f w env b = some vb)
    (h_not_def : w.defs.get? (({ name := "EQUAL" } : Symbol)) = none)
    (h_eq : evalOpt (f + 1) w env
      (.cons (.atom (.symbol (({ name := "EQUAL" } : Symbol)))) (.cons a (.cons b .nil)))
      = some SExpr.t) :
    va = vb := by
  have h_ns : (({ name := "EQUAL" } : Symbol)).isNamed "QUOTE" = false ∧
              (({ name := "EQUAL" } : Symbol)).isNamed "IF" = false ∧
              (({ name := "EQUAL" } : Symbol)).isNamed "LET" = false ∧
              (({ name := "EQUAL" } : Symbol)).isNamed "LET*" = false := by decide
  rw [evalOpt_builtin_2 f w env (({ name := "EQUAL" } : Symbol)) a b va vb h_ns h_not_def ha hb] at h_eq
  -- h_eq : some (callBuiltin "EQUAL" [va, vb]) = some SExpr.t
  simp only [callBuiltin_equal, Option.some.injEq] at h_eq
  exact (Logic.equal_t_iff va vb).mp h_eq

/-- T11a: NOT(e) = NIL implies e evaluates to something truthy. -/
theorem not_nil_means_truthy (f : Nat) (w : World) (env : Env)
    (t : SExpr) (tv : SExpr)
    (h_not_def : w.defs.get? (({ name := "NOT" } : Symbol)) = none)
    (ht : evalOpt f w env t = some tv)
    (h_not : evalOpt (f + 1) w env
      (.cons (.atom (.symbol (({ name := "NOT" } : Symbol)))) (.cons t .nil))
      = some SExpr.nil) :
    Logic.toBool tv = true := by
  have h_ns : (({ name := "NOT" } : Symbol)).isNamed "QUOTE" = false ∧
              (({ name := "NOT" } : Symbol)).isNamed "IF" = false ∧
              (({ name := "NOT" } : Symbol)).isNamed "LET" = false ∧
              (({ name := "NOT" } : Symbol)).isNamed "LET*" = false := by decide
  rw [evalOpt_builtin_1 f w env (({ name := "NOT" } : Symbol)) t tv h_ns h_not_def ht] at h_not
  -- h_not : some (callBuiltin "NOT" [tv]) = some SExpr.nil
  simp only [callBuiltin_not, Option.some.injEq] at h_not
  exact (Logic.not_nil_iff tv).mp h_not

/-! ## Layer 0 continued: Value-level Logic axioms (T8) -/

/-- CDR of CONS is the second argument. -/
theorem logic_cdr_cons (a b : SExpr) : Logic.cdr (.cons a b) = b := by
  simp [Logic.cdr]

/-- CAR of CONS is the first argument. -/
theorem logic_car_cons (a b : SExpr) : Logic.car (.cons a b) = a := by
  simp [Logic.car]

/-- EQUAL is reflexive. -/
theorem logic_equal_self (a : SExpr) : Logic.equal a a = SExpr.t :=
  Logic.equal_self a

/-- T8: Commutativity of plus. -/
theorem logic_plus_comm (a b : SExpr) : Logic.plus a b = Logic.plus b a := by
  simp only [Logic.plus]
  congr 1
  · omega
  · exact Nat.mul_comm _ _

/-- Plus of two integers is the integer sum (my-len/+ values are integers,
    so the proof can work at the integer level). -/
theorem logic_plus_int (a b : Int) :
    Logic.plus (.atom (.number (.int a))) (.atom (.number (.int b)))
    = .atom (.number (.int (a + b))) := by
  simp [Logic.plus, Logic.toRat, Logic.mkNumber]

/-- `(+ 0 k) = k` for an integer `k` (the unicity-of-0 fact specialized to the
    integer value `my-len` returns, via `type-prescription:my-len`). -/
theorem logic_plus_zero_int (k : Int) :
    Logic.plus (.atom (.number (.int 0))) (.atom (.number (.int k)))
    = .atom (.number (.int k)) := by
  rw [logic_plus_int, Int.zero_add]

/-! ### Unconditional rational arithmetic for `Logic.plus`

ACL2's `commutativity-of-+` and `commutativity-2-of-+` are UNCONDITIONAL rewrite
rules (`binary-+` coerces non-numbers via `fix`), so a faithful replay must hold
for all values — not just integers. We prove `Logic.plus` is associative
(hence comm-2) over arbitrary `SExpr`. Strategy: `mkNumber` is invariant under
scaling numerator+denominator (`mkNumber_scale`); composing with the reduced
form of `toRat (mkNumber ..)` (`toRat_mkNumber`) gives the *unreduced*
`plus (mkNumber n d) c` (`plus_mkNumber_left`), after which associativity is a
ring identity on numerators and a `Nat`-comm identity on denominators. -/

/-- `toRat` always yields a positive denominator (canonical `Number`: a
    ratio's denominator is ≥ 2 by the carried invariant). -/
theorem toRat_den_pos (s : SExpr) : 0 < (Logic.toRat s).2 := by
  unfold Logic.toRat
  split
  · exact Nat.one_pos
  · rename_i n d hc
    simp only [canonRat, Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  · exact Nat.one_pos

/-- `Logic.plus` in terms of the rational components (definitional). -/
theorem plus_eq (a c : SExpr) :
    Logic.plus a c = Logic.mkNumber
      ((Logic.toRat a).1 * ((Logic.toRat c).2 : Int) + (Logic.toRat c).1 * ((Logic.toRat a).2 : Int))
      ((Logic.toRat a).2 * (Logic.toRat c).2) := rfl

/-- The reduced form produced by `mkNumber` (positive denominator). -/
theorem toRat_mkNumber (n : Int) (d : Nat) (hd : 0 < d) :
    Logic.toRat (Logic.mkNumber n d)
      = (n / (Nat.gcd n.natAbs d : Int), d / Nat.gcd n.natAbs d) := by
  have hdg : 0 < d / Nat.gcd n.natAbs d :=
    Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ hd)
  simp only [Logic.mkNumber, Int.ofNat_eq_natCast, dif_neg (show ¬ d = 0 by omega)]
  by_cases h1 : d / Nat.gcd n.natAbs d = 1
  · simp [Logic.toRat, h1]
  · simp [Logic.toRat, h1]

/-- `mkNumber` is invariant under scaling numerator and denominator by `k > 0`. -/
theorem mkNumber_scale (n : Int) (d k : Nat) (hk : 0 < k) :
    Logic.mkNumber (n * (k : Int)) (d * k) = Logic.mkNumber n d := by
  by_cases hd : d = 0
  · subst hd; simp [Logic.mkNumber]
  · have hdk : ¬ (d * k = 0) := Nat.mul_ne_zero hd (by omega)
    have hnat : (n * (k : Int)).natAbs = n.natAbs * k := by rw [Int.natAbs_mul]; simp
    have hd2 : d * k / (Nat.gcd n.natAbs d * k) = d / Nat.gcd n.natAbs d :=
      Nat.mul_div_mul_right d (Nat.gcd n.natAbs d) hk
    have hn2 : n * (k : Int) / ((Nat.gcd n.natAbs d * k : Nat) : Int)
             = n / (Nat.gcd n.natAbs d : Int) := by
      push_cast
      exact Int.mul_ediv_mul_of_pos_left n _ (by exact_mod_cast hk)
    simp only [Logic.mkNumber, Int.ofNat_eq_natCast, dif_neg hd, dif_neg hdk, hnat,
               Nat.gcd_mul_right, hd2, hn2]

private theorem mkNumber_one (n : Int) :
    Logic.mkNumber n 1 = .atom (.number (.int n)) := by
  simp [Logic.mkNumber, Nat.gcd_one_right]

private theorem integerp_mkNumber_two_even (n : Int) (h : n % 2 = 0) :
    Logic.integerp (Logic.mkNumber n 2) = SExpr.t := by
  have h2 : (2 : Nat) ∣ n.natAbs :=
    Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero h)
  have hg : Nat.gcd n.natAbs 2 = 2 := Nat.gcd_eq_right h2
  simp [Logic.mkNumber, hg]

private theorem integerp_mkNumber_two_odd (n : Int) (h : n % 2 = 1) :
    Logic.integerp (Logic.mkNumber n 2) = SExpr.nil := by
  have hg : Nat.gcd n.natAbs 2 = 1 :=
    Nat.coprime_two_right.mpr
      (Int.natAbs_odd.mpr (Int.odd_iff.mpr h))
  simp [Logic.mkNumber, hg]

/-- `(DEFUN EVENP (X) (INTEGERP (BINARY-* X '1/2)))` — a non-number
    coerces to `0` under `toRat` (so `(* x 1/2)` is the integer `0`),
    agreeing with `Logic.evenp`'s `'T` on non-numbers; a canonical
    non-integer rational `n/d` scales to `n/2d`, whose reduced
    denominator still exceeds `1` (else `d ∣ gcd(|n|, d) = 1`). -/
theorem gz_def_evenp (a : SExpr) :
    Logic.evenp a
      = Logic.integerp (Logic.times a
          (.atom (.number (.rational 1 2 (by decide))))) := by
  cases a with
  | atom x =>
    cases x with
    | number n =>
      cases n with
      | int k =>
        show (if k % 2 == 0 then SExpr.t else SExpr.nil)
          = Logic.integerp (Logic.mkNumber (k * 1) (1 * 2))
        rw [Int.mul_one k, show ((1 : Nat) * 2) = 2 from rfl]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · rw [integerp_mkNumber_two_even k h]; simp [h]
        · rw [integerp_mkNumber_two_odd k h]; simp [h]
      | rational n d hc =>
        show SExpr.nil
          = Logic.integerp (Logic.mkNumber (n * 1) (d * 2))
        rw [Int.mul_one n]
        have hcanon := hc
        simp only [canonRat, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at hcanon
        obtain ⟨hd2, hg1⟩ := hcanon
        have hne : ¬ (d * 2 / Nat.gcd n.natAbs (d * 2) = 1) := by
          intro h1
          set g := Nat.gcd n.natAbs (d * 2) with hgdef
          have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
          obtain ⟨c, hcq⟩ : g ∣ d * 2 := Nat.gcd_dvd_right _ _
          rw [hcq, Nat.mul_div_cancel_left c hgpos] at h1
          subst h1
          have hgeq : g = d * 2 := by simpa using hcq.symm
          have hdd : d ∣ n.natAbs :=
            dvd_trans ⟨2, rfl⟩ (hgeq ▸ Nat.gcd_dvd_left n.natAbs (d * 2))
          have hdg : d ∣ Nat.gcd n.natAbs d := Nat.dvd_gcd hdd dvd_rfl
          rw [hg1] at hdg
          have := Nat.le_of_dvd (by omega) hdg
          omega
        simp [Logic.mkNumber, hne, show ¬ (d * 2 = 0) by omega]
    | _ => rfl
  | _ => rfl

/-- The UNREDUCED form of `plus (mkNumber n d) c`: scaling collapses `mkNumber`'s
    internal gcd reduction, so the result is `mkNumber (n·cd + cn·d) (d·cd)` with
    `(cn, cd) = toRat c`. The key lemma for proving associativity. -/
theorem plus_mkNumber_left (n : Int) (d : Nat) (hd : 0 < d) (c : SExpr) :
    Logic.plus (Logic.mkNumber n d) c
      = Logic.mkNumber (n * ((Logic.toRat c).2 : Int) + (Logic.toRat c).1 * (d : Int))
                       (d * (Logic.toRat c).2) := by
  have hg : 0 < Nat.gcd n.natAbs d := Nat.gcd_pos_of_pos_right _ hd
  have hgn : (Nat.gcd n.natAbs d : Int) ∣ n := Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _)
  have hgd : Nat.gcd n.natAbs d ∣ d := Nat.gcd_dvd_right _ _
  have hn : n / (Nat.gcd n.natAbs d : Int) * (Nat.gcd n.natAbs d : Int) = n :=
    Int.ediv_mul_cancel hgn
  have hdd : ((d / Nat.gcd n.natAbs d : Nat) : Int) * (Nat.gcd n.natAbs d : Int) = (d : Int) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hgd]
  rw [plus_eq, toRat_mkNumber n d hd]
  dsimp only
  rw [← mkNumber_scale
        (n / (Nat.gcd n.natAbs d : Int) * ((Logic.toRat c).2 : Int)
          + (Logic.toRat c).1 * ((d / Nat.gcd n.natAbs d : Nat) : Int))
        (d / Nat.gcd n.natAbs d * (Logic.toRat c).2) (Nat.gcd n.natAbs d) hg]
  congr 1
  · have hrw : (n / (Nat.gcd n.natAbs d : Int) * ((Logic.toRat c).2 : Int)
          + (Logic.toRat c).1 * ((d / Nat.gcd n.natAbs d : Nat) : Int)) * (Nat.gcd n.natAbs d : Int)
        = (n / (Nat.gcd n.natAbs d : Int) * (Nat.gcd n.natAbs d : Int)) * ((Logic.toRat c).2 : Int)
          + (Logic.toRat c).1 * (((d / Nat.gcd n.natAbs d : Nat) : Int) * (Nat.gcd n.natAbs d : Int)) := by
      ring
    rw [hrw, hn, hdd]
  · rw [Nat.mul_right_comm, Nat.div_mul_cancel hgd]

/-- Associativity of `Logic.plus` (unconditional). -/
theorem logic_plus_assoc (a b c : SExpr) :
    Logic.plus (Logic.plus a b) c = Logic.plus a (Logic.plus b c) := by
  have hab : 0 < (Logic.toRat a).2 * (Logic.toRat b).2 :=
    Nat.mul_pos (toRat_den_pos a) (toRat_den_pos b)
  have hbc : 0 < (Logic.toRat b).2 * (Logic.toRat c).2 :=
    Nat.mul_pos (toRat_den_pos b) (toRat_den_pos c)
  rw [plus_eq a b, plus_mkNumber_left _ _ hab, logic_plus_comm a (Logic.plus b c),
      plus_eq b c, plus_mkNumber_left _ _ hbc]
  congr 1
  · push_cast; ring
  · ring

/-- `commutativity-2-of-+` (unconditional): `(+ a (+ b c)) = (+ b (+ a c))`. -/
theorem logic_plus_comm2 (a b c : SExpr) :
    Logic.plus a (Logic.plus b c) = Logic.plus b (Logic.plus a c) := by
  rw [← logic_plus_assoc, ← logic_plus_assoc, logic_plus_comm a b]

/-! ## With-lemma replay combinators (driver dispatch entries)

  One schematic combinator per imported rewrite rule (rune). Each takes the
  rewrite-site terms and EXISTENTIAL convergence facts about their operands
  (totality / type-prescription — never a function's specific value), and
  returns the node's eval-equality, discharged by the rune's proven value-
  equality. The driver applies these to the terms; values stay opaque. There is
  deliberately NO computational inhabitant of these eval-equalities for symbolic
  terms — the rune's lemma is the only route. -/

/-- RUNE `cdr-cons`: `(cdr (cons a b)) ⇒ b`. -/
theorem re_cdr_cons (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CDR" }))
        (.cons (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env b :=
  fuel_eq_of_conv
    (conv_builtin1 w env { name := "CDR" }
      (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil)))
      (.cons av bv) bv (by decide) h_no_cdr
      (conv_builtin2 w env { name := "CONS" } a b av bv (.cons av bv) (by decide) h_no_cons ha hb rfl)
      (by rw [callBuiltin_cdr, logic_cdr_cons]))
    hb rfl

/-- RUNE `car-cons`: `(car (cons a b)) ⇒ a`. Operands existential. -/
theorem re_car_cons (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CAR" }))
        (.cons (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env a :=
  fuel_eq_of_conv
    (conv_builtin1 w env { name := "CAR" }
      (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil)))
      (.cons av bv) av (by decide) h_no_car
      (conv_builtin2 w env { name := "CONS" } a b av bv (.cons av bv) (by decide) h_no_cons ha hb rfl)
      (by rw [callBuiltin_car, logic_car_cons]))
    ha rfl

/-- RUNE `commutativity-of-+`: `(+ a b) ⇒ (+ b a)`. -/
theorem re_plus_comm (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons b (.cons a .nil))) :=
  fuel_eq_of_conv
    (conv_builtin2 w env { name := "BINARY-+" } a b av bv (Logic.plus av bv)
      (by decide) h_no_plus ha hb (callBuiltin_plus _ _))
    (conv_builtin2 w env { name := "BINARY-+" } b a bv av (Logic.plus bv av)
      (by decide) h_no_plus hb ha (callBuiltin_plus _ _))
    (logic_plus_comm av bv)

/-- RUNE `commutativity-2-of-+`: `(+ a (+ b c)) ⇒ (+ b (+ a c))`. Unconditional —
    faithful to ACL2's `(defthm commutativity-2-of-+ …)`, which has no type
    hypothesis (`binary-+` coerces via `fix`). Operands converge to SOME value;
    the value-equality is `logic_plus_comm2`. -/
theorem re_plus_comm2 (w : World) (env : Env) (a b c : SExpr) (av bv cv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" }))
        (.cons a (.cons (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons b (.cons c .nil))) .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" }))
        (.cons b (.cons (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons c .nil))) .nil))) := by
  have hbc : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons b (.cons c .nil)))
      = some (Logic.plus bv cv) :=
    conv_builtin2 w env { name := "BINARY-+" } b c _ _ _ (by decide) h_no_plus hb hc (callBuiltin_plus _ _)
  have hac : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons c .nil)))
      = some (Logic.plus av cv) :=
    conv_builtin2 w env { name := "BINARY-+" } a c _ _ _ (by decide) h_no_plus ha hc (callBuiltin_plus _ _)
  exact fuel_eq_of_conv
    (conv_builtin2 w env { name := "BINARY-+" } a _ _ _ _ (by decide) h_no_plus ha hbc (callBuiltin_plus _ _))
    (conv_builtin2 w env { name := "BINARY-+" } b _ _ _ _ (by decide) h_no_plus hb hac (callBuiltin_plus _ _))
    (logic_plus_comm2 av bv cv)

/-- RUNE `if-simplification` (true test): `(if c t e) ⇒ t` when the test converges
    to a truthy value. Term-to-term; the then-branch's value stays existential. -/
theorem re_if_true (w : World) (env : Env) (c t e cv tv : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv) (hcv : Logic.toBool cv = true)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w env t = some tv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env t :=
  fuel_eq_of_conv (conv_if_true w env c t e cv tv hc hcv ht) ht rfl

/-- RUNE `if-simplification` (false test): `(if c t e) ⇒ e` when the test
    converges to `nil`. Term-to-term; the else-branch's value stays existential. -/
theorem re_if_false (w : World) (env : Env) (c t e ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some .nil)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w env e = some ev) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env e := by
  have hconv : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))) = some ev := by
    obtain ⟨Nc, hc'⟩ := hc; obtain ⟨Ne, he'⟩ := he
    refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_false g w env c t e (hc' g (by omega))]
    exact he' g (by omega)
  exact fuel_eq_of_conv hconv he rfl

/-- `(bindArgs [s] [v]).get? s = some v`. -/
theorem bindArgs_single_get_self (s : Symbol) (v : SExpr) :
    (bindArgs [s] [v]).get? s = some v := by
  show (({} : Env).insert s v).get? s = some v
  simp

/-- `(bindArgs [f1,f2] [v1,v2]).get? f1 = some v1`. -/
theorem bindArgs_pair_get_fst (f1 f2 : Symbol) (v1 v2 : SExpr) :
    (bindArgs [f1, f2] [v1, v2]).get? f1 = some v1 := by
  show ((({} : Env).insert f2 v2).insert f1 v1).get? f1 = some v1
  simp

/-- `(bindArgs [f1,f2] [v1,v2]).get? f2 = some v2` (distinct formals). -/
theorem bindArgs_pair_get_snd (f1 f2 : Symbol) (v1 v2 : SExpr) (hne : f1 ≠ f2) :
    (bindArgs [f1, f2] [v1, v2]).get? f2 = some v2 := by
  show ((({} : Env).insert f2 v2).insert f1 v1).get? f2 = some v2
  simp only [Env.get?_insert, beq_iff_eq]
  rw [if_neg (Ne.symm hne)]
  simp

/-- RUNE `:DEFINITION fn` on a VARIABLE argument: `(fn x) ⇒ body` (the formal is
    the call's variable, so the substitution is the identity). Term-to-term; the
    body's value `v` stays existential (totality). -/
theorem re_unfold1_var (w : World) (env : Env) (fn formal : Symbol) (av body v : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([formal], body))
    (hclosed : ∀ s ∈ freeVars body, s = formal) (hws : WellScoped body = true)
    (hbind : ∀ f, evalOpt (f + 1) w env (.atom (.symbol formal)) = some av)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons (.atom (.symbol formal)) .nil))
      = evalOpt f w env body := by
  refine fuel_eq_of_conv
    (conv_defn_1 w env fn (.atom (.symbol formal)) av formal body v hns hdef
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact hbind g⟩ hbody)
    ?_ rfl
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨Nb, fun f hf => ?_⟩
  rw [evalOpt_freevar_congr w f env (bindArgs [formal] [av]) body hws (fun s hs => ?_)]
  · exact hb f hf
  · rw [hclosed s hs]
    exact (hbind 0).trans (evalOpt_var 0 w _ formal av (bindArgs_single_get_self formal av)).symm

/-- RUNE `:DEFINITION fn` on two VARIABLE arguments: `(fn x y) ⇒ body`. -/
theorem re_unfold2_var (w : World) (env : Env) (fn f1 f2 : Symbol) (av1 av2 body v : SExpr)
    (hne : f1 ≠ f2)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([f1, f2], body))
    (hclosed : ∀ s ∈ freeVars body, s = f1 ∨ s = f2) (hws : WellScoped body = true)
    (hbind1 : ∀ f, evalOpt (f + 1) w env (.atom (.symbol f1)) = some av1)
    (hbind2 : ∀ f, evalOpt (f + 1) w env (.atom (.symbol f2)) = some av2)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [f1, f2] [av1, av2]) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn))
        (.cons (.atom (.symbol f1)) (.cons (.atom (.symbol f2)) .nil)))
      = evalOpt f w env body := by
  refine fuel_eq_of_conv
    (conv_defn_2 w env fn (.atom (.symbol f1)) (.atom (.symbol f2)) av1 av2 f1 f2 body v hns hdef
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact hbind1 g⟩
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact hbind2 g⟩ hbody)
    ?_ rfl
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨Nb, fun f hf => ?_⟩
  rw [evalOpt_freevar_congr w f env (bindArgs [f1, f2] [av1, av2]) body hws (fun s hs => ?_)]
  · exact hb f hf
  · rcases hclosed s hs with h | h
    · rw [h]; exact (hbind1 0).trans
        (evalOpt_var 0 w _ f1 av1 (bindArgs_pair_get_fst f1 f2 av1 av2)).symm
    · rw [h]; exact (hbind2 0).trans
        (evalOpt_var 0 w _ f2 av2 (bindArgs_pair_get_snd f1 f2 av1 av2 hne)).symm

/-! ## Induction principles (T10) -/

/-- T10: Induction on consp/cdr structure (matching my-app's recursion).
    If P holds when consp(v) is nil, and P(cdr(v)) implies P(v) when consp(v) is non-nil,
    then P holds for all v. Proved by well-founded induction on consCount. -/
theorem acl2_induction_consp (P : SExpr → Prop)
    (base : ∀ v, Logic.consp v = .nil → P v)
    (step : ∀ v, Logic.consp v ≠ .nil → P (Logic.cdr v) → P v) :
    ∀ v, P v := by
  intro v
  -- Strong induction on consCount v
  have : ∀ n, ∀ v, v.consCount ≤ n → P v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      -- consCount v ≤ 0 means v is nil or atom (not cons)
      apply base
      match v with
      | .nil => rfl
      | .atom _ => rfl
      | .cons a d => simp [SExpr.consCount] at hv
    | succ n ih =>
      intro v hv
      by_cases hc : Logic.consp v = .nil
      · exact base v hc
      · apply step v hc
        apply ih
        -- Need: consCount (Logic.cdr v) ≤ n
        match v, hc with
        | .cons a d, _ =>
          simp [Logic.cdr, SExpr.consCount] at hv ⊢
          omega
  exact this v.consCount v (Nat.le_refl _)

/-- G5/v2: STRONG induction on `consCount` — the general principle for
    multi-case schemes. The case dispatch (the emitted decision tree) and the
    per-IH measure decrease (Count lemmas under the in-scope ruling tests)
    happen inside `step`, mirroring ACL2's induction machine, instead of
    being baked into a fixed-shape lemma like `acl2_induction_consp`. -/
theorem acl2_strong_induction_count (P : SExpr → Prop)
    (step : ∀ v, (∀ u, u.consCount < v.consCount → P u) → P v) : ∀ v, P v := by
  intro v
  have : ∀ n, ∀ v, v.consCount ≤ n → P v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      exact step v (fun u hu => absurd (Nat.lt_of_lt_of_le hu hv) (Nat.not_lt_zero _))
    | succ n ih =>
      intro v hv
      exact step v (fun u hu => ih u (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hu hv)))
  exact this v.consCount v (Nat.le_refl _)

/-- G5/v2: case-split on a CONVERGENT test term's value — nil or truthy. The
    env-level dispatch step of the emitted decision tree: each ruling test
    must converge (primitive walk or totality-from-admission), then the goal
    splits classically on its value. -/
theorem conv_value_split {w : World} {env : Env} {t : SExpr} {motive : Prop}
    (hconv : ∃ N v, ∀ f ≥ N, evalOpt f w env t = some v)
    (hnil : (∃ N, ∀ f ≥ N, evalOpt f w env t = some SExpr.nil) → motive)
    (htruthy : ∀ v, v ≠ SExpr.nil → (∃ N, ∀ f ≥ N, evalOpt f w env t = some v) →
      motive) : motive := by
  obtain ⟨N, v, hv⟩ := hconv
  by_cases h : v = SExpr.nil
  · exact hnil ⟨N, fun f hf => h ▸ hv f hf⟩
  · exact htruthy v h ⟨N, hv⟩

/-! ## Driver combinators for terminal nodes (fuel-existential form)

These package a terminal rune as the `∃N∀f≥N` fact the driver emits, so `replayNode`
just applies the combinator (no inline fuel plumbing). Kernel-checked once here. -/

end ACL2.Replay
