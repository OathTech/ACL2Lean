import ACL2Lean.Imported.Sorting

/-! # Imported: the bsort book — the BNEXT FIXED-POINT row

The bsort cluster's decode layer, split out of `Imported/Sorting.lean`
(which is at its module-weight baseline). The BNEXT simulation itself
(`bnextExec` / `bnext_exec_corr` / the generated `bnextExec_enc`) and the
native pass `bnextL` live there; this module carries the row assemblies
that consume them.

ORDEREDP-WHEN-BNEXT-CONSTANT is the bubble-sort termination argument's
other half: a list the bubble pass leaves ALONE is already sorted. Its
native reading needs no new simulation — `bnextL` (the pass) and
`orderedpRec` (the chain2 reading of ORDEREDP) both exist, so the decode
is the standard implies-eliminator over the two sims.

The BNEXT-LEVEL COUNT ROWS (HOW-MANY-SMALLER-BNEXT,
HOW-MANY-BAD-PAIRS-BNEXT) need two more simulations, built here: the
`how-many-smaller` count (elements strictly below a given one) and the
`bnext-size` bubble measure (the sum of those counts down the list).
Both are `derive_exec%`/`derive_sim%` pairs; their emitted
non-negative-integer type-prescriptions are carried as MINTED
FORBIDDEN-DEBT dischargers (`dis_how_many_smaller_tp`,
`dis_bnext_size_tp` — reuse-vs-mint ruling 2026-08-11, capped to the
existing TP-replay unlock class). -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm ACL2.ExecGen

namespace ACL2.Worlds.Sorting

/-- The ORDEREDP-WHEN-BNEXT-CONSTANT replayed-statement formula — the root
    Goal clause, exactly as the log emits it:
    `(IMPLIES (EQUAL (BNEXT X) X) (ORDEREDP X))`. -/
def orderedp_when_bnext_constantFormula : SExpr :=
  impliesT (equalT (app1 "BNEXT" xT) xT) (orderedpT xT)

/-- ORDEREDP-WHEN-BNEXT-CONSTANT, natively: A FIXED POINT OF THE BUBBLE
    PASS IS SORTED — if one pass of `bnextL` leaves the list unchanged,
    every adjacent pair is lexorder-related.
    SCOPE: the native quantifies over `List SExpr` — the `enc` IMAGE —
    while the ACL2 theorem is over ALL objects, so this is strictly
    WEAKER than the replayed statement (the standing type-absorbed
    doctrine). -/
theorem orderedp_when_bnext_constant_native_of_replayed (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_ord : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_when_bnext_constantFormula = some v
        ∧ v ≠ SExpr.nil)
    (xs : List SExpr) (h : bnextL xs = xs) :
    orderedpRec xs = true := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  -- the antecedent: (bnext x) computes the native pass, which the
  -- hypothesis says IS x — so (equal (bnext x) x) is truthy
  have hbn : ConvTo w e (app1 "BNEXT" xT) (bnextExec (enc xs)) :=
    bnext_exec_corr w h_bnext h_no_consp h_no_car h_no_cdr h_no_cons
      h_no_lexorder e xT (enc xs) hx
  rw [bnextExec_enc] at hbn
  have hEq := conv_equalT w e (app1 "BNEXT" xT) xT (enc (bnextL xs))
    (enc xs) h_no_equal hbn hx
  -- the consequent: (orderedp x) computes the chain2 reading
  have hOrd := corr_orderedp_enc w h_ord h_no_consp h_no_cdr h_no_car
    h_no_lexorder xs e xT hx
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hEq hOrd (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hp : Logic.toBool (Logic.equal (enc (bnextL xs)) (enc xs)) = true :=
    equal_truthy_of_eq (by rw [h])
  exact bool_true_of_cond_truthy (truthy_of_implies_t hIt hp)

/-! ## The HOW-MANY-SMALLER kit (the bubble measure's summand) -/

abbrev howManySmallerT (e x : SExpr) : SExpr := app2 "HOW-MANY-SMALLER" e x

/-- `(defun how-many-smaller (e x) …)`, macroexpanded — count the
    elements of `x` that are lexorder-below `e` and not `e` itself. -/
def howManySmallerBody : SExpr :=
  appIf (conspT xT)
    (appIf (equalT eT (carT xT))
      (howManySmallerT eT (cdrT xT))
      (appIf (app2 "LEXORDER" (carT xT) eT)
        (plusT (qInt 1) (howManySmallerT eT (cdrT xT)))
        (howManySmallerT eT (cdrT xT))))
    (qInt 0)

def how_many_smaller_sym : Symbol :=
  { package := "ACL2", name := "HOW-MANY-SMALLER" }

/-- `how-many-smaller`'s body as a total Lean function — GENERATED. -/
derive_exec% howManySmallerExec corr how_many_smaller_exec_corr
  for how_many_smaller_sym
  formals [eS, xS] body howManySmallerBody measured 1

/-- The NATIVE count of the elements strictly below `e` — self-contained
    (waypoint criterion: `lexorderB` and `List` vocabulary only). -/
def howManySmallerL (e : SExpr) : List SExpr → Nat
  | [] => 0
  | a :: t =>
    bif e == a then howManySmallerL e t
    else bif lexorderB a e then 1 + howManySmallerL e t
      else howManySmallerL e t

/-- Stage 2: `howManySmallerExec` on an encoded list computes
    `howManySmallerL` — GENERATED; the result reading is `intRep`. -/
derive_sim% howManySmallerExec_enc for "HOW-MANY-SMALLER"
  vars (e : raw) (xs : list)
  exec [e, xs]
  native (SExpr.atom (.number (.int (howManySmallerL e xs))))
  simp [howManySmallerL, Logic.plus, Logic.toRat, Logic.mkNumber,
    lexorder_eq_boolEnc]
  induct structural xs

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11; minted under the
    reuse-vs-mint ruling — existing-class cap): this establishes
    `tp:HOW-MANY-SMALLER` — the emitted non-negative-integer corollary
    `(IF (INTEGERP (HOW-MANY-SMALLER E X))
         (NOT (< (HOW-MANY-SMALLER E X) '0)) 'NIL)` — Lean-side; content
    ACL2 derives. Statement kept as the named premise; proof retired to
    `sorry`. UNLOCK: TP-replay discharge. -/
theorem dis_how_many_smaller_tp (w : World)
    (h_how_many_smaller : w.defs.get? how_many_smaller_sym
      = some ([eS, xS], howManySmallerBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_binary__ : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol how_many_smaller_sym))
        (SExpr.cons a0 (SExpr.cons a1 SExpr.nil))) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
        Logic.not (Logic.lt v (.atom (.number (.int 0))))
      else SExpr.nil) = SExpr.t := by
  sorry

/-! ## The BNEXT-SIZE kit (the bubble measure) -/

abbrev bnextSizeT (x : SExpr) : SExpr := app1 "BNEXT-SIZE" x

/-- `(defun bnext-size (x) …)`, macroexpanded — the number of
    out-of-order pairs, summed down the list. -/
def bnextSizeBody : SExpr :=
  appIf (conspT xT)
    (plusT (howManySmallerT (carT xT) (cdrT xT)) (bnextSizeT (cdrT xT)))
    (qInt 0)

def bnext_size_sym : Symbol := { package := "ACL2", name := "BNEXT-SIZE" }

/-- `bnext-size`'s body as a total Lean function — GENERATED (the
    HOW-MANY-SMALLER call resolves through the kit registry). -/
derive_exec% bnextSizeExec corr bnext_size_exec_corr for bnext_size_sym
  formals [xS] body bnextSizeBody measured 0

/-- The NATIVE bubble measure: for each element, how many of the
    elements AFTER it are strictly below it. -/
def bnextSizeL : List SExpr → Nat
  | [] => 0
  | a :: t => howManySmallerL a t + bnextSizeL t

/-- Stage 2: `bnextSizeExec` on an encoded list computes `bnextSizeL` —
    GENERATED; the HOW-MANY-SMALLER callee iso resolves through the kit
    registry. -/
derive_sim% bnextSizeExec_enc for "BNEXT-SIZE"
  vars (xs : list)
  exec [xs]
  native (SExpr.atom (.number (.int (bnextSizeL xs))))
  simp [bnextSizeL, Logic.plus, Logic.toRat, Logic.mkNumber]
  induct structural xs

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11; minted under the
    reuse-vs-mint ruling — existing-class cap): this establishes
    `tp:BNEXT-SIZE` — the emitted non-negative-integer corollary
    `(IF (INTEGERP (BNEXT-SIZE X)) (NOT (< (BNEXT-SIZE X) '0)) 'NIL)` —
    Lean-side; content ACL2 derives. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: TP-replay discharge. -/
theorem dis_bnext_size_tp (w : World)
    (h_how_many_smaller : w.defs.get? how_many_smaller_sym
      = some ([eS, xS], howManySmallerBody))
    (h_bnext_size : w.defs.get? bnext_size_sym
      = some ([xS], bnextSizeBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_binary__ : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol bnext_size_sym))
        (SExpr.cons a0 SExpr.nil)) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
        Logic.not (Logic.lt v (.atom (.number (.int 0))))
      else SExpr.nil) = SExpr.t := by
  sorry

/-! ## HOW-MANY-SMALLER-BNEXT -/

/-- The HOW-MANY-SMALLER-BNEXT replayed-statement formula — the root Goal
    clause, exactly as the log emits it:
    `(EQUAL (HOW-MANY-SMALLER E (BNEXT X)) (HOW-MANY-SMALLER E X))`. -/
def how_many_smaller_bnextFormula : SExpr :=
  equalT (howManySmallerT eT (app1 "BNEXT" xT)) (howManySmallerT eT xT)

/-- HOW-MANY-SMALLER-BNEXT, natively: ONE BUBBLE PASS PRESERVES EVERY
    COUNTS-BELOW — for every element, the number of list entries strictly
    below it is the same before and after the pass.
    SCOPE: the native quantifies over `List SExpr` — the `enc` IMAGE —
    while the ACL2 theorem is over ALL objects, so this is strictly
    WEAKER than the replayed statement (the standing type-absorbed
    doctrine). -/
theorem how_many_smaller_bnext_native_of_replayed (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_hms : w.defs.get? how_many_smaller_sym
      = some ([eS, xS], howManySmallerBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_smaller_bnextFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    howManySmallerL ev (bnextL xs) = howManySmallerL ev xs := by
  let e : Env := (({} : Env).insert xS (enc xs)).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hbn : ConvTo w e (app1 "BNEXT" xT) (bnextExec (enc xs)) :=
    bnext_exec_corr w h_bnext h_no_consp h_no_car h_no_cdr h_no_cons
      h_no_lexorder e xT (enc xs) hx
  rw [bnextExec_enc] at hbn
  have hL := how_many_smaller_exec_corr w h_hms h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder h_no_plus e eT (app1 "BNEXT" xT) ev
    (enc (bnextL xs)) he hbn
  rw [howManySmallerExec_enc] at hL
  have hR := how_many_smaller_exec_corr w h_hms h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder h_no_plus e eT xT ev (enc xs) he hx
  rw [howManySmallerExec_enc] at hR
  have hnat := native_of_replayed_equal w e intRep _ _
    (howManySmallerL ev (bnextL xs)) (howManySmallerL ev xs) h_no_equal
    hL hR (hreplayed e)
  omega

/-! ## HOW-MANY-BAD-PAIRS-BNEXT -/

/-- The HOW-MANY-BAD-PAIRS-BNEXT replayed-statement formula — the root
    Goal clause, exactly as the log emits it:
    `(IMPLIES (NOT (EQUAL X (BNEXT X)))
              (< (BNEXT-SIZE (BNEXT X)) (BNEXT-SIZE X)))`. -/
def how_many_bad_pairs_bnextFormula : SExpr :=
  impliesT (app1 "NOT" (equalT xT (app1 "BNEXT" xT)))
    (app2 "<" (bnextSizeT (app1 "BNEXT" xT)) (bnextSizeT xT))

/-- HOW-MANY-BAD-PAIRS-BNEXT, natively: A BUBBLE PASS THAT CHANGES THE
    LIST STRICTLY DECREASES THE BUBBLE MEASURE — the well-foundedness of
    bubble sort, stated over the native pass and measure.
    SCOPE: the native quantifies over `List SExpr` — the `enc` IMAGE —
    while the ACL2 theorem is over ALL objects, so this is strictly
    WEAKER than the replayed statement (the standing type-absorbed
    doctrine). -/
theorem how_many_bad_pairs_bnext_native_of_replayed (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_hms : w.defs.get? how_many_smaller_sym
      = some ([eS, xS], howManySmallerBody))
    (h_bs : w.defs.get? bnext_size_sym = some ([xS], bnextSizeBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_bad_pairs_bnextFormula = some v
        ∧ v ≠ SExpr.nil)
    (xs : List SExpr) (h : xs ≠ bnextL xs) :
    bnextSizeL (bnextL xs) < bnextSizeL xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hbn : ConvTo w e (app1 "BNEXT" xT) (bnextExec (enc xs)) :=
    bnext_exec_corr w h_bnext h_no_consp h_no_car h_no_cdr h_no_cons
      h_no_lexorder e xT (enc xs) hx
  rw [bnextExec_enc] at hbn
  -- the antecedent: `(not (equal x (bnext x)))` is truthy exactly when
  -- the pass moved something (`enc` is injective)
  have hEqX := conv_equalT w e xT (app1 "BNEXT" xT) (enc xs)
    (enc (bnextL xs)) h_no_equal hx hbn
  have hNot := conv_builtin1 w e { name := "NOT" }
    (equalT xT (app1 "BNEXT" xT)) (Logic.equal (enc xs) (enc (bnextL xs)))
    (Logic.not (Logic.equal (enc xs) (enc (bnextL xs)))) (by decide)
    h_no_not hEqX (callBuiltin_not _)
  -- the two measures
  have hSL := bnext_size_exec_corr w h_hms h_bs h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder h_no_plus e (app1 "BNEXT" xT)
    (enc (bnextL xs)) hbn
  rw [bnextSizeExec_enc] at hSL
  have hSR := bnext_size_exec_corr w h_hms h_bs h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder h_no_plus e xT (enc xs) hx
  rw [bnextSizeExec_enc] at hSR
  have hLt := conv_builtin2 w e { name := "<" }
    (bnextSizeT (app1 "BNEXT" xT)) (bnextSizeT xT) _ _ _ (by decide)
    h_no_lt hSL hSR (callBuiltin_lt _ _)
  have hImp := conv_impliesT w e (app1 "NOT" (equalT xT (app1 "BNEXT" xT)))
    (app2 "<" (bnextSizeT (app1 "BNEXT" xT)) (bnextSizeT xT)) _ _
    h_no_implies hNot hLt
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hp : Logic.toBool
      (Logic.not (Logic.equal (enc xs) (enc (bnextL xs)))) = true := by
    have hne : ¬ (enc xs = enc (bnextL xs)) := fun hE => h (enc_inj hE)
    simp [Logic.equal, Logic.not, Logic.toBool, hne]
  have hq := truthy_of_implies_t hIt hp
  by_cases hcmp : bnextSizeL (bnextL xs) < bnextSizeL xs
  · exact hcmp
  · exfalso
    simp [Logic.lt, Logic.toRat, hcmp, Logic.toBool] at hq

end ACL2.Worlds.Sorting
