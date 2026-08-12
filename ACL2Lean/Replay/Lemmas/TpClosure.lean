/-
  Replay/Lemmas/TpClosure — the TP prover's RETURN-PATH composition lemma
  and the per-corollary-CLASS value-closure facts it consumes (TP-replay
  arc increment 1, 2026-08-12).

  The split is deliberate. `convP_builtin2` is the SHAPE move: a return-path
  application of a registered primitive carries the corollary predicate from
  its arguments to the application, for an ARBITRARY predicate `P`, given
  that the primitive's value function preserves `P`. That preservation is
  the only class-specific content, and it lives here as one lemma per
  (corollary class, primitive) pair — a statement about the LIFTED emitted
  corollary itself, never about any particular function.
-/
import ACL2Lean.Replay.Lemmas.Discharge

namespace ACL2.Replay

open ACL2

/-! ## The return-path composition move -/

/-- A 2-ary registered BUILTIN on the TP return path: the value predicate
    carries from the arguments to the application. `g`/`hg` are the
    primitive's total value function and its `callBuiltin` characterization
    (the `dpBinary` rfl lemma); `hcl` is the corollary class's CLOSURE fact
    for that primitive. The TP analogue of `conv_builtin2_ex`. -/
theorem convP_builtin2 (w : World) (env : Env) (s : Symbol) (a b : SExpr)
    (g : SExpr → SExpr → SExpr) (P : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_no : w.defs.get? s = none)
    (hg : ∀ u v, callBuiltin s.name [u, v] = some (g u v))
    (hcl : ∀ u v, P u → P v → P (g u v))
    (ha : ConvToP w env a P) (hb : ConvToP w env b P) :
    ConvToP w env
      (.cons (.atom (.symbol s)) (.cons a (.cons b .nil))) P := by
  obtain ⟨av, hPa, ha'⟩ := ha
  obtain ⟨bv, hPb, hb'⟩ := hb
  exact ⟨g av bv, hcl av bv hPa hPb,
    conv_builtin2 w env s a b av bv (g av bv) h_ns h_no ha' hb' (hg av bv)⟩

/-! ## Corollary-class closure facts

A class is named for the EMITTED corollary shape it lifts (the recognizer
lives with the prover, `tpCorClass?`). `NON-NEGATIVE-INTEGER` is ACL2's
`(IF (INTEGERP (f …)) (NOT (< (f …) '0)) 'NIL)` — `:BASICTS 7`,
`*ts-non-negative-integer*` — value-lifted by `dpValExpr`, i.e. EXACTLY the
`P` the prover builds for that corollary (`bif`/`cond`-shaped `IF`, `Logic`
primitives, the quoted `'0` reflected). `dp_nonneg_int_of_tp` is the
forward decode of that same predicate; `nonNegIntCor_of_nat` is its
converse. -/

/-- The lifted `NON-NEGATIVE-INTEGER` corollary holds of every Nat-image
    integer atom — the converse of `dp_nonneg_int_of_tp`. -/
theorem nonNegIntCor_of_nat (n : Nat) :
    (bif Logic.toBool (Logic.integerp (.atom (.number (.int (n : Int)))))
     then Logic.not
       (Logic.lt (.atom (.number (.int (n : Int)))) (.atom (.number (.int 0))))
     else SExpr.nil) = SExpr.t := by
  simp [Logic.integerp, Logic.toBool, Logic.not, Logic.lt, Logic.toRat,
    if_neg (show ¬((n : Int) < 0) by omega)]

/-- CLOSURE, `NON-NEGATIVE-INTEGER` × `BINARY-+`: the emitted corollary's
    lifted predicate is preserved by ACL2 addition. This is the whole
    Lean-side content of the TP prover's `BINARY-+` return-path arm —
    ACL2's emitted leaf verdict says the leaf's type-set is covered by the
    corollary, and this says our value model agrees. -/
theorem nonNegIntCor_closed_plus (u v : SExpr)
    (hu : (bif Logic.toBool (Logic.integerp u)
           then Logic.not (Logic.lt u (.atom (.number (.int 0))))
           else SExpr.nil) = SExpr.t)
    (hv : (bif Logic.toBool (Logic.integerp v)
           then Logic.not (Logic.lt v (.atom (.number (.int 0))))
           else SExpr.nil) = SExpr.t) :
    (bif Logic.toBool (Logic.integerp (Logic.plus u v))
     then Logic.not (Logic.lt (Logic.plus u v) (.atom (.number (.int 0))))
     else SExpr.nil) = SExpr.t := by
  obtain ⟨m, rfl⟩ := dp_nonneg_int_of_tp hu
  obtain ⟨n, rfl⟩ := dp_nonneg_int_of_tp hv
  rw [logic_plus_int, show (m : Int) + (n : Int) = ((m + n : Nat) : Int) by omega]
  exact nonNegIntCor_of_nat (m + n)

end ACL2.Replay
