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

/-- The UNCONSTRAINED argument obligation (TP-replay arc increment 2,
    2026-08-13). A constructor closure need not constrain every argument:
    `CONSP` of a `CONS` holds whatever the arguments are, and `TRUE-LISTP`
    of a `CONS` constrains only the TAIL. The unconstrained positions carry
    this trivial predicate, so a `ConvToP … TpArgAny` is exactly plain
    evaluability (`convP_any`) — the walk's existing convergence machinery,
    with no type content added Lean-side. -/
def TpArgAny : SExpr → Prop := fun _ => True

/-- An unconstrained argument position: plain convergence IS the
    obligation. -/
theorem convP_any {w : World} {env : Env} {t : SExpr}
    (h : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v) :
    ConvToP w env t TpArgAny := by
  obtain ⟨N, v, hv⟩ := h
  exact ⟨v, trivial, N, hv⟩

/-- A 2-ary registered BUILTIN on the TP return path: the value predicate
    carries from the arguments to the application. `g`/`hg` are the
    primitive's total value function and its `callBuiltin` characterization
    (the `dpBinary` rfl lemma); `hcl` is the corollary class's CLOSURE fact
    for that primitive. The TP analogue of `conv_builtin2_ex`.

    `Pa`/`Pb` are the PER-ARGUMENT obligations, which are NOT in general
    `P`: the driver reads them off the closure's registered ARG-OBLIGATION
    PROFILE (`TpArgProfile`) and passes `TpArgAny` at every unconstrained
    position. -/
theorem convP_builtin2 (w : World) (env : Env) (s : Symbol) (a b : SExpr)
    (g : SExpr → SExpr → SExpr) (P Pa Pb : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_no : w.defs.get? s = none)
    (hg : ∀ u v, callBuiltin s.name [u, v] = some (g u v))
    (hcl : ∀ u v, Pa u → Pb v → P (g u v))
    (ha : ConvToP w env a Pa) (hb : ConvToP w env b Pb) :
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

/-! ### The CONSTRUCTOR classes (TP-replay arc increment 2, 2026-08-13)

`CONSP` is ACL2's `*ts-cons*` (`:BASICTS 3072` = proper ∪ improper cons)
and `TRUE-LISTP` is `*ts-true-list*` (`1152` = proper-cons ∪ nil); both are
emitted as BARE corollaries — `(CONSP (f …))` / `(TRUE-LISTP (f …))` — so
the lifted `P` is just the `Logic` recognizer at the value. Their `CONS`
closures differ exactly in their ARG-OBLIGATION PROFILE: every cons is a
cons (no obligation on either argument), while a cons is a true-list iff
its TAIL is (the head arbitrary). -/

/-- CLOSURE, `CONSP` × `CONS`, profile `neither`: a `CONS` is a `CONSP`
    whatever its arguments are. The arguments carry only `TpArgAny` —
    the walk still has to CONVERGE them, but nothing about their type is
    used or claimed. -/
theorem conspCor_closed_cons (u v : SExpr)
    (_hu : TpArgAny u) (_hv : TpArgAny v) :
    Logic.consp (SExpr.cons u v) = SExpr.t := rfl

/-- CLOSURE, `TRUE-LISTP` × `CONS`, profile `sndOnly`: consing onto a
    true-list gives a true-list; the HEAD is unconstrained (`TpArgAny`).
    `Logic.trueListp` recurses straight into the tail, so the emitted
    corollary's own lifted predicate is what carries. -/
theorem trueListpCor_closed_cons (u v : SExpr) (_hu : TpArgAny u)
    (hv : Logic.trueListp v = SExpr.t) :
    Logic.trueListp (SExpr.cons u v) = SExpr.t := hv

/-! ## The CALLEE-TP return path (TP-replay arc increment 3, 2026-08-13)

A return path may END in a call to ANOTHER function — `SORTFN1`'s
`(SORTFN1-INSERT (CAR X) (SORTFN1 (CDR X)))`, or the `BINARY-+` summand
`(HOW-MANY-SMALLER (CAR X) (CDR X))` inside `BNEXT-SIZE`'s leaf. The
value fact at such a position is the CALLEE's OWN emitted type
prescription, proved by the same prover recursively; nothing about the
callee is assumed or derived here. -/

/-- The CALLEE-TP position move: the call CONVERGES (the plain totality
    walk, which is what the callee's admission licenses), and the
    callee's own type-prescription fact — a statement about ANY value
    the call converges to (`mkTpHypType`'s shape) — supplies `P` there.
    `P` is the OUTER corollary's predicate; the driver composes the
    callee's predicate into it via the registered class implication (or
    the identity, when the classes coincide). -/
theorem convP_of_conv_ex {w : World} {env : Env} {t : SExpr}
    {P : SExpr → Prop}
    (h : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v)
    (hP : ∀ v, (∃ N, ∀ f ≥ N, evalOpt f w env t = some v) → P v) :
    ConvToP w env t P := by
  obtain ⟨N, v, hv⟩ := h
  exact ⟨v, hP v ⟨N, hv⟩, N, hv⟩

/-- CLASS IMPLICATION, `CONSP` ⇒ `CONSP`-or-`NIL`: a callee whose emitted
    corollary is the BARE `(CONSP (g …))` (`*ts-cons*`, 3072) satisfies
    the weaker consp-or-nil `IF` corollary (`*ts-cons*` ∪ `*ts-nil*`,
    3200) the caller's own type prescription states. This is the whole
    Lean-side content of a cross-class callee step: both corollaries are
    EMITTED, and this says our value model agrees that one implies the
    other. The driver additionally recompute-checks the mask containment
    3072 ⊆ 3200 against the same `TpCorClass.tsMask` data. -/
theorem conspOrNilCor_of_conspCor (v : SExpr) (h : Logic.consp v = SExpr.t) :
    (bif Logic.toBool (Logic.consp v) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t := by
  rw [h]; rfl

end ACL2.Replay
