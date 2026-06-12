/-
  THE NATIVE LIFTING LIBRARY (task #62; design doc §6 — "the accumulated
  patterns are the seed of a standard lifting library").

  Built BY EXAMPLE from the catalog (`Imported/NativeMirrors.lean`): every
  lemma here was first proved inline for a concrete catalog entry and then
  generalized when a second entry needed the same shape.

  THE SPINE (MDD-ratified 2026-06-10) is `Conv` / `Rep` / `Implements`:
  `Rep α` represents a Lean type in ACL2's value space (injective encoding
  onto an ACL2 RECOGNIZER — `idRep`, `intRep`/`integerp`,
  `listRep`/`true-listp`), `Implements` says an ACL2 function symbol computes
  a Lean operation along representations, and `native_of_mirror_equal` is the
  generic equational ender (replayed `equal ⇒ t` mirror + a representation of
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
     emission exactly; a world fact `w.defs.get? ⟨"ACL2", fn⟩ = some (…)`
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
  .cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int n))) .nil)

/-- 1-ary application `(fn a)`. -/
def app1 (fn : String) (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := fn })) (.cons a .nil)

/-- 2-ary application `(fn a b)`. -/
def app2 (fn : String) (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := fn })) (.cons a (.cons b .nil))

abbrev plusT (a b : SExpr) : SExpr := app2 "binary-+" a b
abbrev timesT (a b : SExpr) : SExpr := app2 "binary-*" a b
abbrev equalT (a b : SExpr) : SExpr := app2 "equal" a b
abbrev impliesT (a b : SExpr) : SExpr := app2 "implies" a b
abbrev consT (a b : SExpr) : SExpr := app2 "cons" a b
abbrev carT (a : SExpr) : SExpr := app1 "car" a
abbrev cdrT (a : SExpr) : SExpr := app1 "cdr" a
abbrev conspT (a : SExpr) : SExpr := app1 "consp" a

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
spine, and `native_of_mirror_equal` is the generic equational ender: a
replayed `equal ⇒ t` mirror plus a representation of each side yields the
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
    (h_no : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some (.atom (.number (.int m))))
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some (.atom (.number (.int n)))) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (plusT a b)
      = some (.atom (.number (.int (m + n)))) := by
  have h := conv_builtin2 w e { name := "binary-+" } a b
    (.atom (.number (.int m))) (.atom (.number (.int n)))
    (Logic.plus (.atom (.number (.int m))) (.atom (.number (.int n))))
    (by decide) h_no ha hb (callBuiltin_plus _ _)
  rwa [logic_plus_int] at h

/-- Ground `binary-*` convergence to the SYMBOLIC product. -/
theorem conv_times_int (w : World) (e : Env) (a b : SExpr) (m n : Int)
    (h_no : w.defs.get? ({ name := "binary-*" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some (.atom (.number (.int m))))
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some (.atom (.number (.int n)))) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (timesT a b)
      = some (.atom (.number (.int (m * n)))) := by
  have h := conv_builtin2 w e { name := "binary-*" } a b
    (.atom (.number (.int m))) (.atom (.number (.int n)))
    (Logic.times (.atom (.number (.int m))) (.atom (.number (.int n))))
    (by decide) h_no ha hb (callBuiltin_times _ _)
  rwa [Logic.times_int] at h

/-- `(equal a b)` converges to the SYMBOLIC `Logic.equal` of the values. -/
theorem conv_equalT (w : World) (e : Env) (a b av bv : SExpr)
    (h_no : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (equalT a b) = some (Logic.equal av bv) :=
  conv_builtin2 w e { name := "equal" } a b av bv _ (by decide) h_no ha hb
    (callBuiltin_equal _ _)

/-- `(implies a b)` converges to the SYMBOLIC `Logic.implies` of the values. -/
theorem conv_impliesT (w : World) (e : Env) (a b av bv : SExpr)
    (h_no : w.defs.get? ({ name := "implies" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w e b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (impliesT a b) = some (Logic.implies av bv) :=
  conv_builtin2 w e { name := "implies" } a b av bv _ (by decide) h_no ha hb
    (callBuiltin_implies _ _)

/-! ## Decode enders -/

/-- THE GENERIC EQUATIONAL ENDER: a replayed TRUE `equal` mirror (truthiness,
    G2) plus a representation of each side's value yields the NATIVE equality
    — via `equal`'s two-valuedness, no exact-t pin. Every equational catalog
    entry finishes here. -/
theorem native_of_mirror_equal {γ : Type} (w : World) (e : Env) (r : Rep γ)
    (lhs rhs : SExpr) (x y : γ)
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (hL : Conv w e lhs (r.enc x)) (hR : Conv w e rhs (r.enc y))
    (hmirror : EvTrue w e (equalT lhs rhs)) : x = y :=
  r.inj (Logic.eq_of_equal_ne_nil
    (ne_nil_of_evtrue_conv hmirror
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
    `implies`-headed mirror fact: truthiness recovers the exact value. -/
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

/-! ## Name-generic structural correspondences

The standard ACL2 list-recursion body shapes, parameterized by the function
NAME. `appendBody fn` / `lenBody fn` are EXACTLY the macroexpanded bodies
ACL2 emits for the two-formal append and one-formal length defuns, so a
single `decide` on any world (hand or log-derived) instantiates the
correspondence lemmas at that world's function. -/

private def xS : Symbol := ⟨"ACL2", "x"⟩
private def yS : Symbol := ⟨"ACL2", "y"⟩
private def xT : SExpr := .atom (.symbol { name := "x" })
private def yT : SExpr := .atom (.symbol { name := "y" })
private def q0 : SExpr := qInt 0
private def q1 : SExpr := qInt 1

/-- `(if (consp x) (cons (car x) (fn (cdr x) y)) y)` — the standard append
    body, the shape of `app`, `my-app`, …. -/
def appendBody (fn : String) : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
    (.cons (conspT xT)
      (.cons (consT (carT xT) (app2 fn (cdrT xT) yT))
        (.cons yT .nil)))

/-- `(if (consp x) (binary-+ '1 (fn (cdr x))) '0)` — the standard length
    body, the shape of `my-len`, `len2`, …. -/
def lenBody (fn : String) : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
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
    (h_ns : ({ name := fn } : Symbol).isNamed "quote" = false ∧
            ({ name := fn } : Symbol).isNamed "if" = false ∧
            ({ name := fn } : Symbol).isNamed "let" = false ∧
            ({ name := fn } : Symbol).isNamed "let*" = false)
    (h_fn : w.defs.get? ⟨"ACL2", fn⟩
      = some ([⟨"ACL2", "x"⟩, ⟨"ACL2", "y"⟩], appendBody fn))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
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
      conv_builtin1 w _ { name := "consp" } xT (enc []) (Logic.consp (enc []))
        (by decide) h_no_consp hx_ba (callBuiltin_consp _)
    have hbody : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc [], enc ys]) (appendBody fn)
        = some (enc ys) := by
      obtain ⟨Ni, hi⟩ := re_if_false w (bindArgs [xS, yS] [enc [], enc ys]) (conspT xT)
        (consT (carT xT) (app2 fn (cdrT xT) yT)) yT (enc ys) hconspx_ba hy_ba
      obtain ⟨Ny, hy⟩ := hy_ba
      exact ⟨max Ni Ny, fun f hf => (hi f (by omega)).trans (hy f (by omega))⟩
    exact conv_defn_2 w e' ⟨"ACL2", fn⟩ a b (enc []) (enc ys) xS yS (appendBody fn)
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
      conv_builtin1 w _ { name := "consp" } xT (.cons hd (enc tl))
        (Logic.consp (.cons hd (enc tl))) (by decide) h_no_consp hx_ba
        (callBuiltin_consp _)
    have hcarx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (carT xT)
        = some hd := by
      have h := conv_builtin1 w _ { name := "car" } xT (.cons hd (enc tl))
        (Logic.car (.cons hd (enc tl))) (by decide) h_no_car hx_ba (callBuiltin_car _)
      simpa [Logic.car] using h
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (cdrT xT)
        = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "cdr" } xT (.cons hd (enc tl))
        (Logic.cdr (.cons hd (enc tl))) (by decide) h_no_cdr hx_ba (callBuiltin_cdr _)
      simpa [Logic.cdr] using h
    have hrec : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
          (app2 fn (cdrT xT) yT) = some (enc (tl ++ ys)) :=
      ih (bindArgs [xS, yS] [enc (hd :: tl), enc ys]) (cdrT xT) yT ys hcdrx_ba hy_ba
    have hthen : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS, yS] [enc (hd :: tl), enc ys])
          (consT (carT xT) (app2 fn (cdrT xT) yT))
        = some (.cons hd (enc (tl ++ ys))) :=
      conv_builtin2 w _ { name := "cons" } (carT xT) (app2 fn (cdrT xT) yT)
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
    exact conv_defn_2 w e' ⟨"ACL2", fn⟩ a b (.cons hd (enc tl)) (enc ys) xS yS
      (appendBody fn) (.cons hd (enc (tl ++ ys))) h_ns h_fn ha hb hbody

/-- SIMULATION, name-generic: any length-shaped defun over encoded lists
    computes `List.length` under `enc`. Induction on the Lean list. -/
theorem corr_len_enc (w : World) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "quote" = false ∧
            ({ name := fn } : Symbol).isNamed "if" = false ∧
            ({ name := fn } : Symbol).isNamed "let" = false ∧
            ({ name := fn } : Symbol).isNamed "let*" = false)
    (h_fn : w.defs.get? ⟨"ACL2", fn⟩ = some ([⟨"ACL2", "x"⟩], lenBody fn))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none) :
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
      conv_builtin1 w _ { name := "consp" } xT (enc []) (Logic.consp (enc []))
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
    exact conv_defn_1 w e' ⟨"ACL2", fn⟩ a (enc []) xS (lenBody fn)
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
      conv_builtin1 w _ { name := "consp" } xT (.cons hd (enc tl))
        (Logic.consp (.cons hd (enc tl))) (by decide) h_no_consp hx_ba
        (callBuiltin_consp _)
    have hcdrx_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (cdrT xT) = some (enc tl) := by
      have h := conv_builtin1 w _ { name := "cdr" } xT (.cons hd (enc tl))
        (Logic.cdr (.cons hd (enc tl))) (by decide) h_no_cdr hx_ba (callBuiltin_cdr _)
      simpa [Logic.cdr] using h
    have hq1_ba : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) q1
        = some (.atom (.number (.int 1))) :=
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                         exact evalOpt_quote g w _ _⟩
    obtain ⟨Nk, hk⟩ := ih (bindArgs [xS] [enc (hd :: tl)]) (cdrT xT) hcdrx_ba
    have hsum : ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [xS] [enc (hd :: tl)]) (plusT q1 (app1 fn (cdrT xT)))
        = some (.atom (.number (.int (1 + (tl.length : Int))))) := by
      have h := conv_builtin2 w _ { name := "binary-+" } q1 (app1 fn (cdrT xT))
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
    exact conv_defn_1 w e' ⟨"ACL2", fn⟩ a (.cons hd (enc tl)) xS (lenBody fn)
      (.atom (.number (.int ((hd :: tl).length : Int)))) h_ns h_fn ha hbody

/-! ## `Implements` instances — the operations lifted so far -/

/-- `binary-+` (unshadowed) implements integer addition. -/
theorem implements_plus (w : World)
    (h_no : w.defs.get? ({ name := "binary-+" } : Symbol) = none) :
    Implements₂ w "binary-+" intRep intRep intRep (· + ·) :=
  fun e a b x y ha hb => conv_plus_int w e a b x y h_no ha hb

/-- `binary-*` (unshadowed) implements integer multiplication. -/
theorem implements_times (w : World)
    (h_no : w.defs.get? ({ name := "binary-*" } : Symbol) = none) :
    Implements₂ w "binary-*" intRep intRep intRep (· * ·) :=
  fun e a b x y ha hb => conv_times_int w e a b x y h_no ha hb

/-- Any append-shaped defun implements `List.append`. -/
theorem implements_append (w : World) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "quote" = false ∧
            ({ name := fn } : Symbol).isNamed "if" = false ∧
            ({ name := fn } : Symbol).isNamed "let" = false ∧
            ({ name := fn } : Symbol).isNamed "let*" = false)
    (h_fn : w.defs.get? ⟨"ACL2", fn⟩
      = some ([⟨"ACL2", "x"⟩, ⟨"ACL2", "y"⟩], appendBody fn))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none) :
    Implements₂ w fn listRep listRep listRep (· ++ ·) :=
  fun e a b xs ys ha hb =>
    corr_append_enc w fn h_ns h_fn h_no_consp h_no_cdr h_no_car h_no_cons
      xs e a b ys ha hb

/-- Any length-shaped defun implements (integer-valued) `List.length`. -/
theorem implements_len (w : World) (fn : String)
    (h_ns : ({ name := fn } : Symbol).isNamed "quote" = false ∧
            ({ name := fn } : Symbol).isNamed "if" = false ∧
            ({ name := fn } : Symbol).isNamed "let" = false ∧
            ({ name := fn } : Symbol).isNamed "let*" = false)
    (h_fn : w.defs.get? ⟨"ACL2", fn⟩ = some ([⟨"ACL2", "x"⟩], lenBody fn))
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none) :
    Implements₁ w fn listRep intRep (fun xs => (xs.length : Int)) :=
  fun e a xs ha =>
    corr_len_enc w fn h_ns h_fn h_no_consp h_no_plus h_no_cdr xs e a ha

end ACL2.Lifting
