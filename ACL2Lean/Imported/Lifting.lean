/-
  THE NATIVE LIFTING LIBRARY (task #62; design doc §6 — "the accumulated
  patterns are the seed of a standard lifting library").

  Built BY EXAMPLE from the catalog (`Imported/WaypointCatalog.lean`): every
  lemma here was first proved inline for a concrete catalog entry and then
  generalized when a second entry needed the same shape.

  THE SPINE (MDD-ratified 2026-06-10) is `Conv` / `Rep` / `Implements`:
  `Rep α` represents a Lean type in ACL2's value space (injective encoding
  onto an ACL2 RECOGNIZER — `idRep`, `intRep`/`integerp`,
  `listRep`/`true-listp`), `Implements` says an ACL2 function symbol computes
  a Lean operation along representations, and `native_of_replayed_equal` is the
  generic equational ender (replayed `equal ⇒ t` replayed statement + a representation of
  each side ⇒ the NATIVE equality). Around the spine:

  1. THE LIST MORPHISM — `enc : List SExpr → SExpr`, injective and surjective
     onto `true-listp` (`enc_inj`, `trueListp_enc`,
     `exists_enc_of_trueListp`): the genuine isomorphism
     `List SExpr ≃ {s // trueListp s = t}` underlying `listRep`.
  2. THE DECODE KIT — term builders (`qInt`, `app1`/`app2` + abbreviations),
     variable/ground/builtin convergence lemmas (`conv_var_of_get`,
     `conv_qInt`, `conv_plus_int`, …), and decode ENDERS (`int_atom_inj`,
     `truthy_of_implies_t`, `eq_of_equal_truthy`, `conv_unique`).
  3. NAME-GENERIC STRUCTURAL CORRESPONDENCES — simulation lemmas proved once
     over the function NAME: `corr_append_enc` (any 2-formal append-shaped
     defun: `app`, `my-app`, …) and `corr_len_enc` (any 1-formal
     length-shaped defun: `my-len`, `len2`, …), surfaced as `Implements`
     instances (`implements_append`, `implements_len`) alongside the builtin
     ones (`implements_plus`, `implements_times`). The body shapes
     (`appendBody fn` / `lenBody fn`) mirror ACL2's macroexpanded DEFUN
     emission exactly; a world fact `w.defs.get? { package := "ACL2", name := fn } = some (…)`
     instantiates them at any hand or log-derived world by `decide`.

  The TARGET theorems stay user-supplied — this algebra only structures their
  decodes. Polymorphic `Rep` transformers (`Rep α → Rep (List α)`) remain
  deliberately deferred (TODO.md); `Rep` composes, so they drop in later.
-/
import ACL2Lean.EvalOpt
import ACL2Lean.Replay.EvalLemmas

open ACL2 ACL2.Replay

namespace ACL2.Lifting

/-! ## The list morphism -/

/-- The TYPE morphism: a Lean `List SExpr` ↦ the ACL2 proper cons-list. -/
def enc (xs : List SExpr) : SExpr := xs.foldr SExpr.cons SExpr.nil

theorem enc_inj : ∀ {l1 l2 : List SExpr}, enc l1 = enc l2 → l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h; cases l2 with
    | nil => rfl
    | cons b t => simp [enc] at h
  | cons a s ih => intro l2 h; cases l2 with
    | nil => simp [enc] at h
    | cons b t =>
      simp only [enc, List.foldr_cons, SExpr.cons.injEq] at h
      obtain ⟨rfl, htl⟩ := h
      rw [ih htl]

/-! ## Term builders -/

/-- `(quote <n>)` for an integer literal. -/
def qInt (n : Int) : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons (.atom (.number (.int n))) .nil)

/-- 1-ary application `(fn a)`. -/
def app1 (fn : String) (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := fn })) (.cons a .nil)

/-- 2-ary application `(fn a b)`. -/
def app2 (fn : String) (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := fn })) (.cons a (.cons b .nil))

abbrev plusT (a b : SExpr) : SExpr := app2 "BINARY-+" a b
abbrev timesT (a b : SExpr) : SExpr := app2 "BINARY-*" a b
abbrev equalT (a b : SExpr) : SExpr := app2 "EQUAL" a b
abbrev impliesT (a b : SExpr) : SExpr := app2 "IMPLIES" a b
abbrev consT (a b : SExpr) : SExpr := app2 "CONS" a b
abbrev carT (a : SExpr) : SExpr := app1 "CAR" a
abbrev cdrT (a : SExpr) : SExpr := app1 "CDR" a
abbrev conspT (a : SExpr) : SExpr := app1 "CONSP" a

/-- Peel the `atom/number/int` constructors off a value equation. -/
theorem int_atom_inj {m n : Int}
    (h : (.atom (.number (.int m)) : SExpr) = .atom (.number (.int n))) :
    m = n := by
  injection h with h; injection h with h; injection h with h

/-! ## The spine: `Conv` / `Rep` / `Implements`

`Conv` names the catalog's ubiquitous eventual-convergence form. `Rep α` is a
Lean type REPRESENTED in ACL2's value space: an injective encoding landing in
the ACL2 RECOGNIZER that carves out its image — NOT an isomorphism with all
of `SExpr` (the value space is untyped), but an isomorphism ONTO the
recognizer, which is exactly how ACL2 itself speaks types (and what the
type-prescription machinery talks about). `Implements` says an ACL2 function
symbol computes a Lean operation along representations — "lifting an
operation between the worlds". `Implements` facts compose up a formula
spine, and `native_of_replayed_equal` is the generic equational ender: a
replayed `equal ⇒ t` replayed statement plus a representation of each side yields the
NATIVE equality. The target theorems stay user-supplied; this algebra only
structures their decodes. -/

/-- Eventual convergence of a term to a VALUE. -/
def Conv (w : World) (e : Env) (t v : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, evalOpt f w e t = some v

/-- Converged values are unique. -/
theorem conv_unique {w : World} {e : Env} {t u v : SExpr}
    (hu : Conv w e t u) (hv : Conv w e t v) : u = v :=
  val_unique hu hv

/-- A Lean type represented in ACL2's value space. -/
structure Rep (α : Type) where
  /-- The encoding. -/
  enc : α → SExpr
  /-- Distinct Lean values encode distinctly (the decode direction). -/
  inj : ∀ {a b : α}, enc a = enc b → a = b
  /-- The ACL2 recognizer carving out the image. -/
  recog : SExpr → Prop
  /-- Encodings satisfy the recognizer. -/
  mem : ∀ a, recog (enc a)

/-- The identity representation: raw ACL2 values, no recognizer constraint —
    for native facts stated directly at the `SExpr`/`Logic` layer. -/
def idRep : Rep SExpr where
  enc := id
  inj := id
  recog _ := True
  mem _ := trivial

/-- Integers, recognized by `integerp`. -/
def intRep : Rep Int where
  enc n := .atom (.number (.int n))
  inj := int_atom_inj
  recog s := Logic.integerp s = SExpr.t
  mem _ := rfl

/-- `enc` lands in `true-listp`. -/
theorem trueListp_enc (xs : List SExpr) : Logic.trueListp (enc xs) = SExpr.t := by
  induction xs with
  | nil => rfl
  | cons h t ih => simpa [enc, Logic.trueListp] using ih

/-- `enc` is SURJECTIVE onto `true-listp` — together with injectivity, the
    genuine isomorphism `List SExpr ≃ {s // trueListp s = t}`. -/
theorem exists_enc_of_trueListp : ∀ {s : SExpr},
    Logic.trueListp s = SExpr.t → ∃ xs : List SExpr, enc xs = s := by
  intro s
  induction s with
  | nil => exact fun _ => ⟨[], rfl⟩
  | atom a => intro h; simp [Logic.trueListp, SExpr.t] at h
  | cons a b _ ihb =>
    intro h
    obtain ⟨xs, rfl⟩ := ihb (by simpa [Logic.trueListp] using h)
    exact ⟨a :: xs, rfl⟩

/-- Lists of ACL2 values, recognized by `true-listp`. -/
def listRep : Rep (List SExpr) where
  enc := enc
  inj := enc_inj
  recog s := Logic.trueListp s = SExpr.t
  mem := trueListp_enc

/-- `fn` IMPLEMENTS the unary operation `g` along the representations. -/
def Implements₁ (w : World) (fn : String) (ra : Rep α) (rb : Rep β)
    (g : α → β) : Prop :=
  ∀ (e : Env) (a : SExpr) (x : α),
    Conv w e a (ra.enc x) → Conv w e (app1 fn a) (rb.enc (g x))

/-- `fn` IMPLEMENTS the binary operation `g` along the representations. -/
def Implements₂ (w : World) (fn : String) (ra : Rep α) (rb : Rep β) (rc : Rep γ)
    (g : α → β → γ) : Prop :=
  ∀ (e : Env) (a b : SExpr) (x : α) (y : β),
    Conv w e a (ra.enc x) → Conv w e b (rb.enc y) →
    Conv w e (app2 fn a b) (rc.enc (g x y))

/-! ## Variable / ground convergence kit -/

/-- Variable convergence from a concrete env binding. -/
theorem conv_var_of_get (w : World) (e : Env) (s : Symbol) (v : SExpr)
    (h : e.get? s = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (.atom (.symbol s)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w e s v h⟩

/-- Ground quote convergence. -/
theorem conv_qInt (w : World) (e : Env) (n : Int) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (qInt n) = some (.atom (.number (.int n))) :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w e _⟩

/-- Ground `binary-+` convergence to the SYMBOLIC sum. -/
theorem conv_plus_int (w : World) (e : Env) (a b : SExpr) (m n : Int)
    (h_no : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some (.atom (.number (.int m))))
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some (.atom (.number (.int n)))) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (plusT a b)
      = some (.atom (.number (.int (m + n)))) := by
  have h := conv_builtin2 w e { name := "BINARY-+" } a b
    (.atom (.number (.int m))) (.atom (.number (.int n)))
    (Logic.plus (.atom (.number (.int m))) (.atom (.number (.int n))))
    (by decide) h_no ha hb (callBuiltin_plus _ _)
  rwa [logic_plus_int] at h

/-- Ground `binary-*` convergence to the SYMBOLIC product. -/
theorem conv_times_int (w : World) (e : Env) (a b : SExpr) (m n : Int)
    (h_no : w.defs.get? ({ name := "BINARY-*" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some (.atom (.number (.int m))))
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some (.atom (.number (.int n)))) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (timesT a b)
      = some (.atom (.number (.int (m * n)))) := by
  have h := conv_builtin2 w e { name := "BINARY-*" } a b
    (.atom (.number (.int m))) (.atom (.number (.int n)))
    (Logic.times (.atom (.number (.int m))) (.atom (.number (.int n))))
    (by decide) h_no ha hb (callBuiltin_times _ _)
  rwa [Logic.times_int] at h

/-- `(equal a b)` converges to the SYMBOLIC `Logic.equal` of the values. -/
theorem conv_equalT (w : World) (e : Env) (a b av bv : SExpr)
    (h_no : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (equalT a b) = some (Logic.equal av bv) :=
  conv_builtin2 w e { name := "EQUAL" } a b av bv _ (by decide) h_no ha hb
    (callBuiltin_equal _ _)

/-- `(implies a b)` converges to the SYMBOLIC `Logic.implies` of the values. -/
theorem conv_impliesT (w : World) (e : Env) (a b av bv : SExpr)
    (h_no : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (impliesT a b) = some (Logic.implies av bv) :=
  conv_builtin2 w e { name := "IMPLIES" } a b av bv _ (by decide) h_no ha hb
    (callBuiltin_implies _ _)

/-! ## Decode enders -/

/-- THE GENERIC EQUATIONAL ENDER: a replayed TRUE `equal` statement (truthiness,
    G2) plus a representation of each side's value yields the NATIVE equality
    — via `equal`'s two-valuedness, no exact-t pin. Every equational catalog
    entry finishes here. -/
theorem native_of_replayed_equal {γ : Type} (w : World) (e : Env) (r : Rep γ)
    (lhs rhs : SExpr) (x y : γ)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hL : Conv w e lhs (r.enc x)) (hR : Conv w e rhs (r.enc y))
    (hreplayed : EvTrue w e (equalT lhs rhs)) : x = y :=
  r.inj (Logic.eq_of_equal_ne_nil
    (ne_nil_of_evtrue_conv hreplayed
      (conv_equalT w e lhs rhs _ _ h_no_equal hL hR)))

/-- The HYPOTHESIS-decode ender: a truthy antecedent forces the consequent
    of a replayed `implies ⇒ t` fact to be truthy. -/
theorem truthy_of_implies_t {p q : SExpr}
    (h : Logic.implies p q = SExpr.t) (hp : Logic.toBool p = true) :
    Logic.toBool q = true := by
  rw [logic_implies_cond, hp, cond_true] at h
  cases hq : Logic.toBool q
  · rw [hq, cond_false] at h; exact absurd h (by decide)
  · rfl

/-- A non-nil `Logic.implies` IS `t` (two-valued) — the G2 decode of an
    `implies`-headed replayed fact: truthiness recovers the exact value. -/
theorem implies_t_of_ne_nil {p q : SExpr}
    (h : Logic.implies p q ≠ SExpr.nil) : Logic.implies p q = SExpr.t := by
  rcases logic_implies_boolean p q with ht | hnil
  · exact ht
  · exact absurd hnil h

/-- A truthy `Logic.equal` is a real equality. -/
theorem eq_of_equal_truthy {a b : SExpr}
    (h : Logic.toBool (Logic.equal a b) = true) : a = b := by
  by_cases hab : a = b
  · exact hab
  · rw [show Logic.equal a b = SExpr.nil from by
      simp [Logic.equal, beq_iff_eq, hab]] at h
    exact absurd h (by decide)

/-- Convenience: truthify a native equality for the antecedent side. -/
theorem equal_truthy_of_eq {a b : SExpr} (h : a = b) :
    Logic.toBool (Logic.equal a b) = true := by
  rw [(Logic.equal_t_iff a b).mpr h]; rfl

/-! ## The replayed-statement-decode kit (extracted from entry 9's repeated glue —
lifter sprint 2026-07-06). Every native entry: compute the formula's value
FORWARD via the `corr_*` layer, PIN it by the replayed statement's truthiness, then
project through implies/and/equal down to Bool facts. -/

/-- The replayed statement's truthiness PINS a computed value: the formula evaluates to
    a non-nil value, and we computed WHICH value — so that value ≠ nil. -/
theorem replayed_pins_ne_nil {w : World} {e : Env} {t v : SExpr}
    (hm : ∃ N, ∀ f, f ≥ N → ∃ u, evalOpt f w e t = some u ∧ u ≠ SExpr.nil)
    (hv : ∃ N, ∀ f ≥ N, evalOpt f w e t = some v) : v ≠ SExpr.nil := by
  obtain ⟨Nm, hm'⟩ := hm
  obtain ⟨Nv, hv'⟩ := hv
  obtain ⟨u, hu, hune⟩ := hm' (max Nm Nv) (by omega)
  exact (Option.some.inj ((hv' (max Nm Nv) (by omega)).symm.trans hu)) ▸ hune

/-- Bool-cond DISCRIMINATION: equal `bif _ then t else nil` values have
    equal Bools (t/nil discriminate). -/
theorem bool_of_cond_eq {b1 b2 : Bool}
    (h : (bif b1 then SExpr.t else SExpr.nil)
       = (bif b2 then SExpr.t else SExpr.nil)) : b1 = b2 := by
  cases b1 <;> cases b2 <;> simp_all [SExpr.t]

/-- A truthy bool-cond's Bool is `true`. -/
theorem bool_true_of_cond_truthy {b : Bool}
    (h : Logic.toBool (bif b then SExpr.t else SExpr.nil) = true) : b = true := by
  cases b <;> simp_all [Logic.toBool]

/-- A `true` Bool's cond is `t` (antecedent side). -/
theorem cond_t_of_true {b : Bool} (h : b = true) :
    (bif b then SExpr.t else SExpr.nil) = SExpr.t := by subst h; rfl

/-- `booleanp` of a bool-cond is `t` — the type-absorbed conjunct of a
    `defequiv` obligation. -/
theorem booleanp_cond (b : Bool) :
    Logic.booleanp (bif b then SExpr.t else SExpr.nil) = SExpr.t := by
  cases b <;> rfl

/-- PEEL one guard off a truthy conjunction tower `(if G rest 'nil)`: the
    guard's Bool is `true` (a native fact) AND the rest stays truthy — the
    stepwise decode of a `defequiv`-style macroexpanded `and`-nest. -/
theorem replayed_peel_guard {w : World} {e : Env} {G rest : SExpr} {bg : Bool}
    (hm : ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w e (.cons (.atom (.symbol { name := "IF" }))
        (.cons G (.cons rest (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          .nil)))) = some v ∧ v ≠ SExpr.nil)
    (hG : ∃ N, ∀ f ≥ N, evalOpt f w e G
      = some (bif bg then SExpr.t else SExpr.nil)) :
    bg = true ∧ (∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w e rest = some v ∧ v ≠ SExpr.nil) := by
  cases hb : bg with
  | false =>
    -- guard nil ⟹ the tower IS nil — contradicts the pinned truthiness
    have hGn : ∃ N, ∀ f ≥ N, evalOpt f w e G = some SExpr.nil := by
      simpa [hb] using hG
    have hq := re_val_quote w e SExpr.nil
    have hnil := fuel_conv_of_eq
      (re_if_false w e G rest
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
        SExpr.nil hGn hq) hq
    exact absurd hnil (fun h => replayed_pins_ne_nil hm h rfl)
  | true =>
    have hGt : ∃ N, ∀ f ≥ N, evalOpt f w e G = some SExpr.t := by
      simpa [hb] using hG
    refine ⟨rfl, ?_⟩
    obtain ⟨Nm, hm'⟩ := hm
    obtain ⟨Ng, hg'⟩ := hGt
    refine ⟨max Nm Ng, fun f hf => ?_⟩
    -- at fuel f+1 the `if` IS the rest (raw step equation, no branch
    -- convergence needed) — rest inherits the pinned truthy value
    obtain ⟨v, hv, hvne⟩ := hm' (f + 1) (by omega)
    have hstep := evalOpt_if_true f w e G rest
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
      SExpr.t (hg' f (by omega)) rfl
    exact ⟨v, hstep ▸ hv, hvne⟩

/-- Value of the macroexpanded `and` — `(if A B 'nil)` — of two computed
    bool-conds: the `&&`-cond. -/
theorem conv_and_conds (w : World) (e : Env) (A B : SExpr) (b1 b2 : Bool)
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w e A
      = some (bif b1 then SExpr.t else SExpr.nil))
    (hB : ∃ N, ∀ f ≥ N, evalOpt f w e B
      = some (bif b2 then SExpr.t else SExpr.nil)) :
    ∃ N, ∀ f ≥ N, evalOpt f w e
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons A (.cons B (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          .nil)))) =
      some (bif (b1 && b2) then SExpr.t else SExpr.nil) := by
  cases hb1 : b1 with
  | true =>
    have hAt : ∃ N, ∀ f ≥ N, evalOpt f w e A = some SExpr.t := by
      simpa [hb1] using hA
    have h := re_if_true w e A B
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
      SExpr.t (bif b2 then SExpr.t else SExpr.nil) hAt rfl hB
    simpa using fuel_conv_of_eq h hB
  | false =>
    have hAn : ∃ N, ∀ f ≥ N, evalOpt f w e A = some SExpr.nil := by
      simpa [hb1] using hA
    have hq := re_val_quote w e SExpr.nil
    have h := re_if_false w e A B
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
      SExpr.nil hAn hq
    simpa using fuel_conv_of_eq h hq

/-! ## Name-generic structural correspondences

The standard ACL2 list-recursion body shapes, parameterized by the function
NAME. `appendBody fn` / `lenBody fn` are EXACTLY the macroexpanded bodies
ACL2 emits for the two-formal append and one-formal length defuns, so a
single `decide` on any world (hand or log-derived) instantiates the
correspondence lemmas at that world's function. -/

private def xS : Symbol := { package := "ACL2", name := "X" }
private def yS : Symbol := { package := "ACL2", name := "Y" }
private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def q0 : SExpr := qInt 0
private def q1 : SExpr := qInt 1

/-- `(if (consp x) (cons (car x) (fn (cdr x) y)) y)` — the standard append
    body, the shape of `app`, `my-app`, …. -/
def appendBody (fn : String) : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (conspT xT)
      (.cons (consT (carT xT) (app2 fn (cdrT xT) yT))
        (.cons yT .nil)))

/-- `(if (consp x) (binary-+ '1 (fn (cdr x))) '0)` — the standard length
    body, the shape of `my-len`, `len2`, …. -/
def lenBody (fn : String) : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (conspT xT)
      (.cons (plusT q1 (app1 fn (cdrT xT)))
        (.cons q0 .nil)))

private theorem bindArgs_xy_x (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? xS = some vx := by
  show ((({} : Env).insert yS vy).insert xS vx).get? xS = some vx
  simp
private theorem bindArgs_xy_y (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? yS = some vy := by
  show ((({} : Env).insert yS vy).insert xS vx).get? yS = some vy
  simp only [Env.get?_insert]
  rw [if_neg (by decide)]; simp
private theorem bindArgs_x_x (vx : SExpr) :
    (bindArgs [xS] [vx]).get? xS = some vx := by
  show (({} : Env).insert xS vx).get? xS = some vx
  simp

/-- SIMULATION, name-generic: any append-shaped defun over encoded lists
    computes `++` under `enc`. Induction on the Lean list. -/
theorem corr_append_enc (w : World) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "QUOTE" = false ∧
            ({ name := fn } : Symbol).isNamed "IF" = false ∧
            ({ name := fn } : Symbol).isNamed "LET" = false ∧
            ({ name := fn } : Symbol).isNamed "LET*" = false)
    (h_fn : w.defs.get? { package := "ACL2", name := fn }
      = some ([{ package := "ACL2", name := "X" }, { package := "ACL2", name := "Y" }], appendBody fn))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a b : SExpr) (ys : List SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    (∃ N, ∀ f ≥ N, evalOpt f w e' b = some (enc ys)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (app2 fn a b) = some (enc (xs ++ ys)) := by
  intro xs
  induction xs with
  | nil =>
    intro e' a b ys ha hb
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc [], enc ys]) xT = some (enc []) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_xy_x _ _)⟩
    have hy_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc [], enc ys]) yT = some (enc ys) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ yS _ (bindArgs_xy_y _ _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc [], enc ys]) (conspT xT) = some .nil :=
      conv_builtin1 w _ { name := "CONSP" } xT (enc []) (Logic.consp (enc []))
        (by decide) h_no_consp hx_ba (callBuiltin_consp _)
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc [], enc ys]) (appendBody fn)
        = some (enc ys) := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [xS, yS] [enc [], enc ys]) (conspT xT)
        (consT (carT xT) (app2 fn (cdrT xT) yT)) yT (enc ys) hconspx_ba hy_ba
      obtain ⟨Ny, hy⟩ := hy_ba
      exact ⟨max Ni Ny, fun f hf => (hi f (by omega)).trans (hy f (by omega))⟩
    exact conv_defn_2 w e' { package := "ACL2", name := fn } a b (enc []) (enc ys) xS yS (appendBody fn)
      (enc ys) h_ns h_fn ha hb hbody
  | cons hd tl ih =>
    intro e' a b ys ha hb
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) xT
        = some (.cons hd (enc tl)) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_xy_x _ _)⟩
    have hy_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) yT = some (enc ys) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ yS _ (bindArgs_xy_y _ _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (conspT xT)
        = some (Logic.consp (.cons hd (enc tl))) :=
      conv_builtin1 w _ { name := "CONSP" } xT (.cons hd (enc tl))
        (Logic.consp (.cons hd (enc tl))) (by decide) h_no_consp hx_ba
        (callBuiltin_consp _)
    have hcarx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (carT xT)
        = some hd := by
      have h := conv_builtin1 w _ { name := "CAR" } xT (.cons hd (enc tl))
        (Logic.car (.cons hd (enc tl))) (by decide) h_no_car hx_ba (callBuiltin_car _)
      -- v4.33 (4.31 #13636): `simpa using h` now closes at REDUCIBLE
      -- transparency, which no longer unfolds the plain-`def` `app1`/`app2`
      -- under the `carT`/`cdrT`/`consT` abbrevs — so the failing `simpa`s in
      -- this file name the def explicitly (same closes, spelled out).
      simpa [Logic.car, app1] using h
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (cdrT xT)
        = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "CDR" } xT (.cons hd (enc tl))
        (Logic.cdr (.cons hd (enc tl))) (by decide) h_no_cdr hx_ba (callBuiltin_cdr _)
      simpa [Logic.cdr, app1] using h
    have hrec : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
          (app2 fn (cdrT xT) yT) = some (enc (tl ++ ys)) :=
      ih (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (cdrT xT) yT ys hcdrx_ba hy_ba
    have hthen : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
          (consT (carT xT) (app2 fn (cdrT xT) yT))
        = some (.cons hd (enc (tl ++ ys))) :=
      conv_builtin2 w _ { name := "CONS" } (carT xT) (app2 fn (cdrT xT) yT)
        hd (enc (tl ++ ys)) (.cons hd (enc (tl ++ ys))) (by decide) h_no_cons
        hcarx_ba hrec rfl
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (appendBody fn)
        = some (.cons hd (enc (tl ++ ys))) := by
      obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
        (conspT xT) (consT (carT xT) (app2 fn (cdrT xT) yT)) yT
        (Logic.consp (.cons hd (enc tl)))
        (.cons hd (enc (tl ++ ys))) hconspx_ba rfl hthen
      obtain ⟨Nt, ht⟩ := hthen
      exact ⟨max Ni Nt, fun f hf => (hi f (by omega)).trans (ht f (by omega))⟩
    exact conv_defn_2 w e' { package := "ACL2", name := fn } a b (.cons hd (enc tl)) (enc ys) xS yS
      (appendBody fn) (.cons hd (enc (tl ++ ys))) h_ns h_fn ha hb hbody

/-- SIMULATION, name-generic: any length-shaped defun over encoded lists
    computes `List.length` under `enc`. Induction on the Lean list. -/
theorem corr_len_enc (w : World) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "QUOTE" = false ∧
            ({ name := fn } : Symbol).isNamed "IF" = false ∧
            ({ name := fn } : Symbol).isNamed "LET" = false ∧
            ({ name := fn } : Symbol).isNamed "LET*" = false)
    (h_fn : w.defs.get? { package := "ACL2", name := fn } = some ([{ package := "ACL2", name := "X" }], lenBody fn))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (app1 fn a)
      = some (.atom (.number (.int xs.length))) := by
  intro xs
  induction xs with
  | nil =>
    intro e' a ha
    have hx_ba : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [xS] [enc []]) xT
        = some (enc []) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_x_x _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []]) (conspT xT) = some .nil :=
      conv_builtin1 w _ { name := "CONSP" } xT (enc []) (Logic.consp (enc []))
        (by decide) h_no_consp hx_ba (callBuiltin_consp _)
    have hq0_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []]) q0 = some (.atom (.number (.int 0))) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []]) (lenBody fn)
        = some (.atom (.number (.int 0))) := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [xS] [enc []]) (conspT xT)
        (plusT q1 (app1 fn (cdrT xT))) q0 (.atom (.number (.int 0)))
        hconspx_ba hq0_ba
      obtain ⟨Nq, hq⟩ := hq0_ba
      exact ⟨max Ni Nq, fun f hf => (hi f (by omega)).trans (hq f (by omega))⟩
    exact conv_defn_1 w e' { package := "ACL2", name := fn } a (enc []) xS (lenBody fn)
      (.atom (.number (.int 0))) h_ns h_fn ha hbody
  | cons hd tl ih =>
    intro e' a ha
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) xT
        = some (.cons hd (enc tl)) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_x_x _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (conspT xT)
        = some (Logic.consp (.cons hd (enc tl))) :=
      conv_builtin1 w _ { name := "CONSP" } xT (.cons hd (enc tl))
        (Logic.consp (.cons hd (enc tl))) (by decide) h_no_consp hx_ba
        (callBuiltin_consp _)
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (cdrT xT) = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "CDR" } xT (.cons hd (enc tl))
        (Logic.cdr (.cons hd (enc tl))) (by decide) h_no_cdr hx_ba (callBuiltin_cdr _)
      simpa [Logic.cdr, app1] using h
    have hq1_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) q1
        = some (.atom (.number (.int 1))) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    obtain ⟨Nk, hk⟩ := ih (bindArgs [xS] [enc (hd :: tl)]) (cdrT xT) hcdrx_ba
    have hsum : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (plusT q1 (app1 fn (cdrT xT)))
        = some (.atom (.number (.int (1 + (tl.length : Int))))) := by
      have h := conv_builtin2 w _ { name := "BINARY-+" } q1 (app1 fn (cdrT xT))
        (.atom (.number (.int 1))) (.atom (.number (.int (tl.length : Int))))
        (Logic.plus (.atom (.number (.int 1)))
          (.atom (.number (.int (tl.length : Int)))))
        (by decide) h_no_plus hq1_ba ⟨Nk, hk⟩ (callBuiltin_plus _ _)
      rwa [logic_plus_int] at h
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (lenBody fn)
        = some (.atom (.number (.int (1 + (tl.length : Int))))) := by
      obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [xS] [enc (hd :: tl)]) (conspT xT)
        (plusT q1 (app1 fn (cdrT xT))) q0 (Logic.consp (.cons hd (enc tl)))
        (.atom (.number (.int (1 + (tl.length : Int))))) hconspx_ba rfl hsum
      obtain ⟨Ns, hs⟩ := hsum
      exact ⟨max Ni Ns, fun f hf => (hi f (by omega)).trans (hs f (by omega))⟩
    have hlen : (1 + (tl.length : Int)) = ((hd :: tl).length : Int) := by
      rw [List.length_cons]; push_cast; ring
    rw [hlen] at hbody
    exact conv_defn_1 w e' { package := "ACL2", name := fn } a (.cons hd (enc tl)) xS (lenBody fn)
      (.atom (.number (.int ((hd :: tl).length : Int)))) h_ns h_fn ha hbody

/-- `(if (consp x) (cons 'c (fn (cdr x))) 'nil)` — the standard MAP-CONST
    body (p7's `dub`, …): rebuild the list with every element the quoted
    constant `c` (validator/lifter arc inc-0). -/
def mapConstBody (c : SExpr) (fn : String) : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (conspT xT)
      (.cons (consT (.cons (.atom (.symbol { name := "QUOTE" })) (.cons c .nil))
        (app1 fn (cdrT xT)))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          .nil)))

/-- SIMULATION, name-generic: any map-const-shaped defun over encoded lists
    computes `List.map (fun _ => c)` under `enc`. Induction on the Lean
    list (the `corr_len_enc` template with the CONS composition of
    `corr_append_enc`'s step). -/
theorem corr_mapconst_enc (w : World) (c : SExpr) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "QUOTE" = false ∧
            ({ name := fn } : Symbol).isNamed "IF" = false ∧
            ({ name := fn } : Symbol).isNamed "LET" = false ∧
            ({ name := fn } : Symbol).isNamed "LET*" = false)
    (h_fn : w.defs.get? { package := "ACL2", name := fn }
      = some ([{ package := "ACL2", name := "X" }], mapConstBody c fn))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (app1 fn a)
      = some (enc (xs.map (fun _ => c))) := by
  intro xs
  induction xs with
  | nil =>
    intro e' a ha
    have hx_ba : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [xS] [enc []]) xT
        = some (enc []) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_x_x _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []]) (conspT xT) = some .nil :=
      conv_builtin1 w _ { name := "CONSP" } xT (enc []) (Logic.consp (enc []))
        (by decide) h_no_consp hx_ba (callBuiltin_consp _)
    have hqnil_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []])
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
        = some .nil :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []]) (mapConstBody c fn)
        = some .nil := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [xS] [enc []]) (conspT xT)
        (consT (.cons (.atom (.symbol { name := "QUOTE" })) (.cons c .nil))
          (app1 fn (cdrT xT)))
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
        .nil hconspx_ba hqnil_ba
      obtain ⟨Nq, hq⟩ := hqnil_ba
      exact ⟨max Ni Nq, fun f hf => (hi f (by omega)).trans (hq f (by omega))⟩
    exact conv_defn_1 w e' { package := "ACL2", name := fn } a (enc []) xS
      (mapConstBody c fn) .nil h_ns h_fn ha hbody
  | cons hd tl ih =>
    intro e' a ha
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) xT
        = some (.cons hd (enc tl)) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_x_x _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (conspT xT)
        = some (Logic.consp (.cons hd (enc tl))) :=
      conv_builtin1 w _ { name := "CONSP" } xT (.cons hd (enc tl))
        (Logic.consp (.cons hd (enc tl))) (by decide) h_no_consp hx_ba
        (callBuiltin_consp _)
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (cdrT xT)
        = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "CDR" } xT (.cons hd (enc tl))
        (Logic.cdr (.cons hd (enc tl))) (by decide) h_no_cdr hx_ba
        (callBuiltin_cdr _)
      simpa [Logic.cdr, app1] using h
    have hqc_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)])
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons c .nil))
        = some c :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    obtain ⟨Nk, hk⟩ := ih (bindArgs [xS] [enc (hd :: tl)]) (cdrT xT) hcdrx_ba
    have hcons : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)])
          (consT (.cons (.atom (.symbol { name := "QUOTE" })) (.cons c .nil))
            (app1 fn (cdrT xT)))
        = some (.cons c (enc (tl.map (fun _ => c)))) := by
      have h := conv_builtin2 w _ { name := "CONS" }
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons c .nil))
        (app1 fn (cdrT xT)) c (enc (tl.map (fun _ => c)))
        (Logic.cons c (enc (tl.map (fun _ => c))))
        (by decide) h_no_cons hqc_ba ⟨Nk, hk⟩ (callBuiltin_cons _ _)
      simpa [Logic.cons, app2] using h
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (mapConstBody c fn)
        = some (.cons c (enc (tl.map (fun _ => c)))) := by
      obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [xS] [enc (hd :: tl)])
        (conspT xT)
        (consT (.cons (.atom (.symbol { name := "QUOTE" })) (.cons c .nil))
          (app1 fn (cdrT xT)))
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
        (Logic.consp (.cons hd (enc tl)))
        (.cons c (enc (tl.map (fun _ => c)))) hconspx_ba rfl hcons
      obtain ⟨Ns, hs⟩ := hcons
      exact ⟨max Ni Ns, fun f hf => (hi f (by omega)).trans (hs f (by omega))⟩
    exact conv_defn_1 w e' { package := "ACL2", name := fn } a
      (.cons hd (enc tl)) xS (mapConstBody c fn)
      (.cons c (enc (tl.map (fun _ => c)))) h_ns h_fn ha hbody

/-! ## Booleans + the ADJACENT-PAIRS (chain2) recognizer schematic
(validator/lifter arc inc-1: p5's `dupp` — and p3's `ordd` / p6's `ordn`
are the SAME body shape with a different comparison, which is exactly why
this is name- AND comparison-generic). -/

/-- ACL2's boolean encoding: `t` / `nil`. -/
def boolEnc (b : Bool) : SExpr := bif b then SExpr.t else SExpr.nil

-- (a `Rep Bool` instance was drafted here and DELETED unwired — audit F2,
-- the banned build-now-wire-later anti-pattern; reintroduce it WITH its
-- first consumer when a decode needs it. `boolEnc` below is used.)

/-- `(if (consp x) (if (consp (cdr x)) (if (cmp (car x) (car (cdr x)))
    (fn (cdr x)) 'nil) 't) 't)` — the ADJACENT-PAIRS recognizer body
    (`dupp` with `cmp = EQUAL`; `ordd` with `LEXORDER`). -/
def chain2Body (cmp fn : String) : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (conspT xT)
      (.cons
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (conspT (cdrT xT))
            (.cons
              (.cons (.atom (.symbol { name := "IF" }))
                (.cons (app2 cmp (carT xT) (carT (cdrT xT)))
                  (.cons (app1 fn (cdrT xT))
                    (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                      (.cons .nil .nil)) .nil))))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil)) .nil))))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons SExpr.t .nil)) .nil)))

/-- The native adjacent-pairs fold: every adjacent pair satisfies `p`. -/
def chain2Rec (p : SExpr → SExpr → Bool) : List SExpr → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => p a b && chain2Rec p (b :: t)

/-- SIMULATION, name- and comparison-generic: any chain2-shaped defun over
    encoded lists computes `chain2Rec cmpB` under `enc`/`boolEnc`, given the
    comparison is an UNSHADOWED BOOLEAN-VALUED builtin (`h_cmp_call`). -/
theorem corr_chain2_enc (w : World) (cmp fn : String)
    (cmpB : SExpr → SExpr → Bool)
    (h_ns : ({ name := fn } : Symbol).isNamed "QUOTE" = false ∧
            ({ name := fn } : Symbol).isNamed "IF" = false ∧
            ({ name := fn } : Symbol).isNamed "LET" = false ∧
            ({ name := fn } : Symbol).isNamed "LET*" = false)
    (h_cmp_ns : ({ name := cmp } : Symbol).isNamed "QUOTE" = false ∧
            ({ name := cmp } : Symbol).isNamed "IF" = false ∧
            ({ name := cmp } : Symbol).isNamed "LET" = false ∧
            ({ name := cmp } : Symbol).isNamed "LET*" = false)
    (h_fn : w.defs.get? { package := "ACL2", name := fn }
      = some ([{ package := "ACL2", name := "X" }], chain2Body cmp fn))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cmp : w.defs.get? ({ name := cmp } : Symbol) = none)
    (h_cmp_call : ∀ a b, callBuiltin cmp [a, b]
      = some (boolEnc (cmpB a b))) :
    ∀ (xs : List SExpr) (e' : Env) (a : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (app1 fn a)
      = some (boolEnc (chain2Rec cmpB xs)) := by
  intro xs
  induction xs with
  | nil =>
    intro e' a ha
    have hx_ba : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [xS] [enc []]) xT
        = some (enc []) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_x_x _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []]) (conspT xT) = some .nil :=
      conv_builtin1 w _ { name := "CONSP" } xT (enc []) (Logic.consp (enc []))
        (by decide) h_no_consp hx_ba (callBuiltin_consp _)
    have hqt_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []])
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
        = some SExpr.t :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc []]) (chain2Body cmp fn)
        = some SExpr.t := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [xS] [enc []]) (conspT xT)
        _ _ SExpr.t hconspx_ba hqt_ba
      obtain ⟨Nq, hq⟩ := hqt_ba
      exact ⟨max Ni Nq, fun f hf => (hi f (by omega)).trans (hq f (by omega))⟩
    exact conv_defn_1 w e' { package := "ACL2", name := fn } a (enc []) xS
      (chain2Body cmp fn) SExpr.t h_ns h_fn ha hbody
  | cons hd tl ih =>
    intro e' a ha
    have hx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) xT
        = some (.cons hd (enc tl)) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_var g w _ xS _ (bindArgs_x_x _)⟩
    have hconspx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (conspT xT)
        = some (Logic.consp (.cons hd (enc tl))) :=
      conv_builtin1 w _ { name := "CONSP" } xT (.cons hd (enc tl))
        (Logic.consp (.cons hd (enc tl))) (by decide) h_no_consp hx_ba
        (callBuiltin_consp _)
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (cdrT xT)
        = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "CDR" } xT (.cons hd (enc tl))
        (Logic.cdr (.cons hd (enc tl))) (by decide) h_no_cdr hx_ba
        (callBuiltin_cdr _)
      simpa [Logic.cdr, app1] using h
    have hconspcdr_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (conspT (cdrT xT))
        = some (Logic.consp (enc tl)) :=
      conv_builtin1 w _ { name := "CONSP" } (cdrT xT) (enc tl)
        (Logic.consp (enc tl)) (by decide) h_no_consp hcdrx_ba
        (callBuiltin_consp _)
    match tl with
    | [] =>
      have hqt_ba : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc [hd]])
            (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          = some SExpr.t :=
        ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                           exact evalOpt_quote g w _ _⟩
      have hinner : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc [hd]])
            (.cons (.atom (.symbol { name := "IF" }))
              (.cons (conspT (cdrT xT))
                (.cons
                  (.cons (.atom (.symbol { name := "IF" }))
                    (.cons (app2 cmp (carT xT) (carT (cdrT xT)))
                      (.cons (app1 fn (cdrT xT))
                        (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                          (.cons .nil .nil)) .nil))))
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                    (.cons SExpr.t .nil)) .nil))))
          = some SExpr.t := by
        obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [xS] [enc [hd]])
          (conspT (cdrT xT)) _ _ SExpr.t hconspcdr_ba hqt_ba
        obtain ⟨Nq, hq⟩ := hqt_ba
        exact ⟨max Ni Nq, fun f hf => (hi f (by omega)).trans (hq f (by omega))⟩
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc [hd]]) (chain2Body cmp fn)
          = some SExpr.t := by
        obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [xS] [enc [hd]]) (conspT xT)
          _ _ (Logic.consp (.cons hd (enc []))) SExpr.t hconspx_ba rfl hinner
        obtain ⟨Ns, hs⟩ := hinner
        exact ⟨max Ni Ns, fun f hf => (hi f (by omega)).trans (hs f (by omega))⟩
      exact conv_defn_1 w e' { package := "ACL2", name := fn } a
        (.cons hd (enc [])) xS (chain2Body cmp fn) SExpr.t h_ns h_fn ha hbody
    | b :: t2 =>
      have hcarx_ba : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc (hd :: b :: t2)]) (carT xT)
          = some hd := by
        have h := conv_builtin1 w _ { name := "CAR" } xT
          (.cons hd (enc (b :: t2))) (Logic.car (.cons hd (enc (b :: t2))))
          (by decide) h_no_car hx_ba (callBuiltin_car _)
        simpa [Logic.car, app1] using h
      have hcarcdr_ba : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc (hd :: b :: t2)]) (carT (cdrT xT))
          = some b := by
        have h := conv_builtin1 w _ { name := "CAR" } (cdrT xT)
          (.cons b (enc t2)) (Logic.car (.cons b (enc t2)))
          (by decide) h_no_car hcdrx_ba (callBuiltin_car _)
        simpa [Logic.car, app1] using h
      have hcmp_ba : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc (hd :: b :: t2)])
            (app2 cmp (carT xT) (carT (cdrT xT)))
          = some (boolEnc (cmpB hd b)) :=
        conv_builtin2 w _ ({ name := cmp } : Symbol) (carT xT) (carT (cdrT xT)) hd b
          (boolEnc (cmpB hd b)) h_cmp_ns h_no_cmp hcarx_ba hcarcdr_ba
          (h_cmp_call hd b)
      obtain ⟨Nk, hk⟩ := ih (bindArgs [xS] [enc (hd :: b :: t2)]) (cdrT xT)
        hcdrx_ba
      have hqnil_ba : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc (hd :: b :: t2)])
            (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          = some .nil :=
        ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                           exact evalOpt_quote g w _ _⟩
      have hinnermost : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc (hd :: b :: t2)])
            (.cons (.atom (.symbol { name := "IF" }))
              (.cons (app2 cmp (carT xT) (carT (cdrT xT)))
                (.cons (app1 fn (cdrT xT))
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                    (.cons .nil .nil)) .nil))))
          = some (boolEnc (chain2Rec cmpB (hd :: b :: t2))) := by
        cases hcb : cmpB hd b with
        | true =>
          obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [xS] [enc (hd :: b :: t2)])
            (app2 cmp (carT xT) (carT (cdrT xT))) _ _ (boolEnc (cmpB hd b))
            (boolEnc (chain2Rec cmpB (b :: t2))) hcmp_ba
            (by rw [hcb]; rfl) ⟨Nk, hk⟩
          refine ⟨max Ni Nk, fun f hf => (hi f (by omega)).trans ?_⟩
          rw [hk f (by omega)]
          simp [chain2Rec, hcb]
        | false =>
          obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [xS] [enc (hd :: b :: t2)])
            (app2 cmp (carT xT) (carT (cdrT xT))) _ _ .nil
            (by simpa [boolEnc, hcb] using hcmp_ba) hqnil_ba
          obtain ⟨Nq, hq⟩ := hqnil_ba
          refine ⟨max Ni Nq, fun f hf => (hi f (by omega)).trans ?_⟩
          rw [hq f (by omega)]
          simp [chain2Rec, hcb, boolEnc]
      have hinner : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc (hd :: b :: t2)])
            (.cons (.atom (.symbol { name := "IF" }))
              (.cons (conspT (cdrT xT))
                (.cons
                  (.cons (.atom (.symbol { name := "IF" }))
                    (.cons (app2 cmp (carT xT) (carT (cdrT xT)))
                      (.cons (app1 fn (cdrT xT))
                        (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                          (.cons .nil .nil)) .nil))))
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                    (.cons SExpr.t .nil)) .nil))))
          = some (boolEnc (chain2Rec cmpB (hd :: b :: t2))) := by
        obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [xS] [enc (hd :: b :: t2)])
          (conspT (cdrT xT)) _ _ (Logic.consp (enc (b :: t2)))
          (boolEnc (chain2Rec cmpB (hd :: b :: t2))) hconspcdr_ba rfl hinnermost
        obtain ⟨Ns, hs⟩ := hinnermost
        exact ⟨max Ni Ns, fun f hf => (hi f (by omega)).trans (hs f (by omega))⟩
      have hbody : ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [xS] [enc (hd :: b :: t2)]) (chain2Body cmp fn)
          = some (boolEnc (chain2Rec cmpB (hd :: b :: t2))) := by
        obtain ⟨Ni, hi⟩ := re_if_true w (bindArgs [xS] [enc (hd :: b :: t2)])
          (conspT xT) _ _ (Logic.consp (.cons hd (enc (b :: t2))))
          (boolEnc (chain2Rec cmpB (hd :: b :: t2))) hconspx_ba rfl hinner
        obtain ⟨Ns, hs⟩ := hinner
        exact ⟨max Ni Ns, fun f hf => (hi f (by omega)).trans (hs f (by omega))⟩
      exact conv_defn_1 w e' { package := "ACL2", name := fn } a
        (.cons hd (enc (b :: t2))) xS (chain2Body cmp fn)
        (boolEnc (chain2Rec cmpB (hd :: b :: t2))) h_ns h_fn ha hbody

/-! ## Fuel bookkeeping

The name-generic TP discharger that used to live here (`drv_tp_len`,
validator/lifter arc inc-0) is RETIRED: the driver's TP prover discharges
the `tp:<fn>` hypothesis of a len-shaped defun from ACL2's own emitted
`:TYPE-PRESCRIPTION` corollary + `:LEAVES` (TP-replay arc increment 1,
2026-08-12), so no Lean-side statement of that fact remains. -/

/-- Fix a value out of a per-fuel existential (fuel monotonicity). -/
theorem conv_fix {w : World} {e : Env} {t : SExpr}
    (h : ∃ M, ∀ f ≥ M, ∃ av, evalOpt f w e t = some av) :
    ∃ av, ∃ M, ∀ f ≥ M, evalOpt f w e t = some av := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨av, hav⟩ := hM M (Nat.le_refl M)
  exact ⟨av, M, fun f hf => evalOpt_ge_fuel M f w e t av hav hf⟩

/-! ## `Implements` instances — the operations lifted so far -/

/-- `binary-+` (unshadowed) implements integer addition. -/
theorem implements_plus (w : World)
    (h_no : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    Implements₂ w "BINARY-+" intRep intRep intRep (· + ·) :=
  fun e a b x y ha hb => conv_plus_int w e a b x y h_no ha hb

/-- `binary-*` (unshadowed) implements integer multiplication. -/
theorem implements_times (w : World)
    (h_no : w.defs.get? ({ name := "BINARY-*" } : Symbol) = none) :
    Implements₂ w "BINARY-*" intRep intRep intRep (· * ·) :=
  fun e a b x y ha hb => conv_times_int w e a b x y h_no ha hb

/-- Any append-shaped defun implements `List.append`. -/
theorem implements_append (w : World) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "QUOTE" = false ∧
            ({ name := fn } : Symbol).isNamed "IF" = false ∧
            ({ name := fn } : Symbol).isNamed "LET" = false ∧
            ({ name := fn } : Symbol).isNamed "LET*" = false)
    (h_fn : w.defs.get? { package := "ACL2", name := fn }
      = some ([{ package := "ACL2", name := "X" }, { package := "ACL2", name := "Y" }], appendBody fn))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    Implements₂ w fn listRep listRep listRep (· ++ ·) :=
  fun e a b xs ys ha hb =>
    corr_append_enc w fn h_ns h_fn h_no_consp h_no_cdr h_no_car h_no_cons
      xs e a b ys ha hb

/-- Any length-shaped defun implements (integer-valued) `List.length`. -/
theorem implements_len (w : World) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "QUOTE" = false ∧
            ({ name := fn } : Symbol).isNamed "IF" = false ∧
            ({ name := fn } : Symbol).isNamed "LET" = false ∧
            ({ name := fn } : Symbol).isNamed "LET*" = false)
    (h_fn : w.defs.get? { package := "ACL2", name := fn } = some ([{ package := "ACL2", name := "X" }], lenBody fn))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none) :
    Implements₁ w fn listRep intRep (fun xs => (xs.length : Int)) :=
  fun e a xs ha =>
    corr_len_enc w fn h_ns h_fn h_no_consp h_no_plus h_no_cdr xs e a ha


/-! ## Decode-kit v2 (sorting-absolute 1d — promoted from Sorting.lean's
privates): the boolEnc conjunction ladder (`conv_if3`), the false-branch
collapse (`conv_if_false'`), the EQUAL/IFF Bool readings
(`toBool_equal`, `bool_of_iff_truthy`, `eq_of_iff_truthy_two_valued`).

CONSUMER COUNTS — CORRECTED (R0 item 11, 2026-08-13). This header used to
claim "3+ consumers each", which was FALSE. Measured outside this module:

| lemma                         | consumers |
| ----------------------------- | --------- |
| `toBool_equal`                | 10 (Sorting ×7, SimGen, SortingConvertPerm, Logic) |
| `conv_if3`                    | 1 (Sorting) |
| `bool_of_iff_truthy`          | 1 (Sorting) |
| `eq_of_iff_truthy_two_valued` | 1 (Sorting) |
| `conv_if_false'`              | 0 |

Only `toBool_equal` met the extraction bar. The lemmas are KEPT — they are
correct, used, and this is the right home for the kit; the defect was the
CLAIM, not the code. Treat the n=1 entries as the decode kit's declared
surface, not as evidence of duplication removed. -/

/-- `(IF c t e)` term builder (the decode kit's own copy — `ifT` lives in
    the Replay namespace and aliasing it here would make every
    open-both consumer ambiguous). -/
abbrev appIf (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

/-- `(QUOTE NIL)`. -/
abbrev qNilT : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)


/-- Value-level if-false composition (the `re_if_false` + else-value glue
    used throughout the waypoints). -/
theorem conv_if_false' (w : World) (e : Env) (c t el ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w e c = some SExpr.nil)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w e el = some ev) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (appIf c t el) = some ev := by
  obtain ⟨Ni, hi⟩ := re_if_false w e c t el ev hc he
  obtain ⟨Ne, he'⟩ := he
  exact ⟨max Ni Ne, fun f hf => (hi f (by omega)).trans (he' f (by omega))⟩

theorem toBool_equal (a b : SExpr) :
    Logic.toBool (Logic.equal a b) = (a == b) := by
  cases h : a == b <;> simp [Logic.equal, h]

/-- The three-guard if-nest of boolEncs computes the conjunction. -/
theorem conv_if3 (w : World) (e : Env) (c1 c2 c3 : SExpr)
    (b1 b2 b3 : Bool)
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w e c1 = some (boolEnc b1))
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w e c2 = some (boolEnc b2))
    (h3 : ∃ N, ∀ f ≥ N, evalOpt f w e c3 = some (boolEnc b3)) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (appIf c1 (appIf c2 c3 qNilT) qNilT)
      = some (boolEnc (b1 && (b2 && b3))) := by
  cases hb1 : b1 with
  | false =>
    have h1n : ∃ N, ∀ f ≥ N, evalOpt f w e c1 = some SExpr.nil := by
      simpa [hb1, boolEnc] using h1
    simpa [Bool.false_and, boolEnc] using
      conv_if_false' w e c1 (appIf c2 c3 qNilT) qNilT SExpr.nil h1n
        (re_val_quote w e SExpr.nil)
  | true =>
    have hInner : ∃ N, ∀ f ≥ N, evalOpt f w e (appIf c2 c3 qNilT)
        = some (boolEnc (b2 && b3)) := by
      cases hb2 : b2 with
      | false =>
        have h2n : ∃ N, ∀ f ≥ N, evalOpt f w e c2 = some SExpr.nil := by
          simpa [hb2, boolEnc] using h2
        simpa [Bool.false_and, boolEnc] using
          conv_if_false' w e c2 c3 qNilT SExpr.nil h2n
            (re_val_quote w e SExpr.nil)
      | true =>
        have := conv_if_true w e c2 c3 qNilT (boolEnc b2) (boolEnc b3) h2
          (by rw [hb2]; rfl) h3
        simpa [hb2, Bool.true_and] using this
    have := conv_if_true w e c1 (appIf c2 c3 qNilT) qNilT (boolEnc b1)
      (boolEnc (b2 && b3)) h1 (by rw [hb1]; rfl) hInner
    simpa [hb1, Bool.true_and] using this

/-- Truthy `iff` of two boolEncs is Bool equality. -/
theorem bool_of_iff_truthy {x y : Bool}
    (h : Logic.toBool (Logic.iff (boolEnc x) (boolEnc y)) = true) :
    x = y := by
  cases x <;> cases y <;> simp_all [Logic.iff, boolEnc, Logic.toBool]

theorem eq_of_iff_truthy_two_valued {p q : SExpr}
    (hp : p = SExpr.t ∨ p = SExpr.nil) (hq : q = SExpr.t ∨ q = SExpr.nil)
    (h : Logic.toBool (Logic.iff p q) = true) : p = q := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    simp_all [Logic.iff, Logic.toBool, SExpr.t]

end ACL2.Lifting
