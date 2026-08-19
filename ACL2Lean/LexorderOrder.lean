import ACL2Lean.Lexorder

/-!
# The `lexorder` order properties (ACL2's ground-zero lexorder rules)

ACL2 admits four rules about `lexorder` at ground zero (axioms.lisp:27154ff)
whose proofs the boot-strap SKIPS (`ld-skip-proofsp`): LEXORDER-REFLEXIVE,
LEXORDER-ANTI-SYMMETRIC, LEXORDER-TRANSITIVE, LEXORDER-TOTAL. Per the
external-knowledge design (docs/plans/2026-07-10_external-knowledge-design.md,
D5) we are in a strictly better position than ACL2 itself: we PROVE these
facts about our own implementation of the primitive, and the WP3 prelude
constants rest on these theorems rather than on trust.

Proof architecture, bottom-up:
  1. within-class facts — numbers by exact rational value (the cross-
     multiplication order; injectivity is exactly where the canonical
     `Number` invariant (BUG-012) earns its keep), chars by code, strings
     and symbol (name, package) pairs by the core `String` order;
  2. `alphLe` is a total order (reflexive/antisymmetric/transitive/total)
     on views;
  3. `lexView?` is INJECTIVE, via the explicit retraction `unview` — this
     rests on the symbol-space canonicity invariants (`canonSym`,
     BUG-013/BUG-014): `nil`/`t`/keywords each have exactly one
     representation;
  4. the four `lexorder` theorems, by structural induction with the
     lexicographic cons layer on top (transitivity's cons case uses
     antisymmetry, proved first).

This file deliberately imports NO Mathlib: Mathlib's `String.LT'` instance
OVERRIDES the core `String` order that `symbolLe` is compiled against, so
any `<`/`≤` written here would denote a different (if equivalent) relation.
Core provides everything needed (`String.lt_trans`/`le_antisymm`/…,
`UInt8.le_antisymm`/…, `Int`/`Nat` order and gcd lemmas), and staying
core-only also keeps the axiom footprint of these theorems minimal.
-/

namespace ACL2

open Logic

/-! ## Within-class facts: numbers -/

/-- Unpack the canonicity invariant. -/
private theorem canonRat_facts {n : Int} {d : Nat} (h : canonRat n d = true) :
    2 ≤ d ∧ Nat.gcd n.natAbs d = 1 := by
  simpa [canonRat] using h

/-- The denominator `toRat` extracts from a (canonical) number is positive. -/
private theorem den_pos (v : Number) :
    0 < (Logic.toRat (.atom (.number v))).2 := by
  cases v with
  | int n => simp [Logic.toRat]
  | rational n d hc =>
    have := (canonRat_facts hc).1
    simp only [Logic.toRat]
    omega

private theorem mul_right_comm' (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_comm b c, ← Int.mul_assoc]

/-- Transitivity of the cross-multiplication order on exact rationals:
    `n1/d1 ≤ n2/d2 ≤ n3/d3` (as `nᵢ*dⱼ ≤ nⱼ*dᵢ`) chains, cancelling the
    positive middle denominator. -/
private theorem cross_le_trans {n1 n2 n3 : Int} {d1 d2 d3 : Nat}
    (hd2 : 0 < d2)
    (h12 : n1 * (d2 : Int) ≤ n2 * (d1 : Int))
    (h23 : n2 * (d3 : Int) ≤ n3 * (d2 : Int)) :
    n1 * (d3 : Int) ≤ n3 * (d1 : Int) := by
  have h1 : n1 * d2 * d3 ≤ n2 * d1 * d3 :=
    Int.mul_le_mul_of_nonneg_right h12 (Int.natCast_nonneg d3)
  have h2 : n2 * d3 * d1 ≤ n3 * d2 * d1 :=
    Int.mul_le_mul_of_nonneg_right h23 (Int.natCast_nonneg d1)
  have h3 : n1 * d2 * d3 ≤ n3 * d2 * d1 := by
    refine Int.le_trans h1 ?_
    rw [mul_right_comm' n2 d1 d3]
    exact h2
  have h4 : n1 * d3 * d2 ≤ n3 * d1 * d2 := by
    rw [mul_right_comm' n1 d3 d2, mul_right_comm' n3 d1 d2]
    exact h3
  exact Int.le_of_mul_le_mul_right h4 (by omega)

/-- A canonical rational is never integral: `m * d = n` is impossible when
    `(n, d)` is canonical (`d ≥ 2` would divide `n`, contradicting
    reducedness). -/
private theorem cross_ne_int {m n : Int} {d : Nat} (hc : canonRat n d = true) :
    m * (d : Int) ≠ n := by
  intro h
  rcases canonRat_facts hc with ⟨hd2, hcop⟩
  have hdvd : (d : Int) ∣ n := ⟨m, by rw [← h]; exact Int.mul_comm m d⟩
  have hdvd' : d ∣ n.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hg : d ∣ Nat.gcd n.natAbs d := Nat.dvd_gcd hdvd' (Nat.dvd_refl d)
  rw [hcop] at hg
  have := Nat.le_of_dvd Nat.one_pos hg
  omega

/-- INJECTIVITY of the exact rational value on canonical numbers: equal
    cross-products mean equal `Number`s. This is where the BUG-012
    canonical-`Number` invariant pays off — without it (e.g. with `2/4` and
    `1/2` both representable) this, and hence lexorder antisymmetry, is
    FALSE. -/
private theorem number_eq_of_cross_eq {v1 v2 : Number}
    (h : (Logic.toRat (.atom (.number v1))).1
           * ((Logic.toRat (.atom (.number v2))).2 : Int)
       = (Logic.toRat (.atom (.number v2))).1
           * ((Logic.toRat (.atom (.number v1))).2 : Int)) :
    v1 = v2 := by
  cases v1 with
  | int m =>
    cases v2 with
    | int n =>
      simp [Logic.toRat] at h
      exact congrArg Number.int h
    | rational n d hc =>
      simp [Logic.toRat] at h
      exact absurd h (cross_ne_int hc)
  | rational n d hc =>
    cases v2 with
    | int m =>
      simp [Logic.toRat] at h
      exact absurd h.symm (cross_ne_int hc)
    | rational n2 d2 hc2 =>
      simp only [Logic.toRat] at h
      rcases canonRat_facts hc with ⟨hd2, hcop⟩
      rcases canonRat_facts hc2 with ⟨hd2', hcop2⟩
      -- |n|·d2 = |n2|·d, then coprimality forces d = d2, then n = n2
      have habs : n.natAbs * d2 = n2.natAbs * d := by
        have := congrArg Int.natAbs h
        simpa [Int.natAbs_mul] using this
      have hdd2 : d ∣ d2 := by
        have hdvd : d ∣ n.natAbs * d2 :=
          ⟨n2.natAbs, by rw [habs]; exact Nat.mul_comm _ _⟩
        exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left hdvd
      have hd2d : d2 ∣ d := by
        have hdvd : d2 ∣ n2.natAbs * d :=
          ⟨n.natAbs, by rw [← habs]; exact Nat.mul_comm _ _⟩
        exact (Nat.Coprime.symm hcop2).dvd_of_dvd_mul_left hdvd
      have hdeq : d = d2 := Nat.dvd_antisymm hdd2 hd2d
      subst hdeq
      have hneq : n = n2 :=
        Int.eq_of_mul_eq_mul_right (by omega : (d : Int) ≠ 0) h
      subst hneq
      rfl

/-! ## Within-class facts: symbols

    All stated as Bool equations over `symbolLe`, manipulating the CORE
    `String` order relations its compiled `if`s carry. -/

private theorem symbolLe_refl (n p : String) : symbolLe n p n p = true := by
  simp [symbolLe]

private theorem symbolLe_antisymm {n1 p1 n2 p2 : String}
    (h12 : symbolLe n1 p1 n2 p2 = true) (h21 : symbolLe n2 p2 n1 p1 = true) :
    n1 = n2 ∧ p1 = p2 := by
  simp only [symbolLe] at h12 h21
  split at h12
  · next hlt =>
    split at h21
    · next hlt' => exact absurd hlt' (String.lt_asymm hlt)
    · split at h21
      · next heq =>
        subst heq
        exact absurd hlt (String.lt_irrefl _)
      · exact absurd h21 Bool.false_ne_true
  · next hnlt =>
    split at h12
    · next heq =>
      subst heq
      split at h21
      · next hlt' => exact absurd hlt' (String.lt_irrefl _)
      · split at h21
        · exact ⟨rfl, String.le_antisymm (of_decide_eq_true h12)
            (of_decide_eq_true h21)⟩
        · exact absurd h21 Bool.false_ne_true
    · exact absurd h12 Bool.false_ne_true

private theorem symbolLe_trans {n1 p1 n2 p2 n3 p3 : String}
    (h12 : symbolLe n1 p1 n2 p2 = true) (h23 : symbolLe n2 p2 n3 p3 = true) :
    symbolLe n1 p1 n3 p3 = true := by
  simp only [symbolLe] at h12 h23 ⊢
  split at h12
  · next hlt12 =>
    split at h23
    · next hlt23 => rw [if_pos (String.lt_trans hlt12 hlt23)]
    · split at h23
      · next heq23 =>
        subst heq23
        rw [if_pos hlt12]
      · exact absurd h23 Bool.false_ne_true
  · next hnlt12 =>
    split at h12
    · next heq12 =>
      subst heq12
      split at h23
      · next hlt23 => rw [if_pos hlt23]
      · split at h23
        · next heq23 =>
          subst heq23
          rw [if_neg (String.lt_irrefl _), if_pos rfl]
          exact decide_eq_true
            (String.le_trans (of_decide_eq_true h12) (of_decide_eq_true h23))
        · exact absurd h23 Bool.false_ne_true
    · exact absurd h12 Bool.false_ne_true

private theorem symbolLe_total (n1 p1 n2 p2 : String) :
    symbolLe n1 p1 n2 p2 = true ∨ symbolLe n2 p2 n1 p1 = true := by
  simp only [symbolLe]
  split
  · exact Or.inl rfl
  · next hnlt12 =>
    -- ¬ n1 < n2, i.e. n2 ≤ n1 (core `String.le` IS `¬ · < ·`)
    by_cases hlt21 : n2 < n1
    · right
      rw [if_pos hlt21]
    · have heq : n1 = n2 := String.le_antisymm hlt21 hnlt12
      subst heq
      rw [if_neg hnlt12, if_pos rfl, if_pos rfl]
      rcases String.le_total p1 p2 with hp | hp
      · exact Or.inl (decide_eq_true hp)
      · exact Or.inr (decide_eq_true hp)

/-! ## The view comparator `alphLe` is a total order -/

theorem alphLe_refl (a : LexView) : alphLe a a = true := by
  cases a with
  | number v => simp [alphLe, viewKind]
  | char c => simp [alphLe, viewKind]
  | string s => simp [alphLe, viewKind]
  | sym n p => simp [alphLe, viewKind, symbolLe_refl]

theorem alphLe_antisymm : ∀ {a b : LexView},
    alphLe a b = true → alphLe b a = true → a = b := by
  intro a b h12 h21
  cases a <;> cases b <;> simp_all [alphLe, viewKind]
  case number.number v1 v2 =>
    exact number_eq_of_cross_eq (Int.le_antisymm h12 h21)
  case char.char c1 c2 => exact UInt8.le_antisymm h12 h21
  case string.string s1 s2 => exact String.le_antisymm h12 h21
  case sym.sym n1 p1 n2 p2 => exact symbolLe_antisymm h12 h21

theorem alphLe_trans : ∀ {a b c : LexView},
    alphLe a b = true → alphLe b c = true → alphLe a c = true := by
  intro a b c h12 h23
  cases a <;> cases b <;> cases c <;> simp_all [alphLe, viewKind]
  case number.number.number v1 v2 v3 =>
    exact cross_le_trans (den_pos v2) h12 h23
  case char.char.char c1 c2 c3 => exact UInt8.le_trans h12 h23
  case string.string.string s1 s2 s3 => exact String.le_trans h12 h23
  case sym.sym.sym n1 p1 n2 p2 n3 p3 => exact symbolLe_trans h12 h23

theorem alphLe_total (a b : LexView) :
    alphLe a b = true ∨ alphLe b a = true := by
  cases a <;> cases b <;> simp [alphLe, viewKind]
  case number.number v1 v2 => exact Int.le_total _ _
  case char.char c1 c2 => exact UInt8.le_total c1 c2
  case string.string s1 s2 => exact String.le_total s1 s2
  case sym.sym n1 p1 n2 p2 => exact symbolLe_total n1 p1 n2 p2

/-! ## `lexView?` is injective -/

/-- The canonical SExpr carrying a given view — the retraction that
    witnesses `lexView?`'s injectivity. The `.sym` arm is where the
    symbol-space canonicity invariants (`canonSym`, BUG-013/BUG-014) are
    load-bearing: the COMMON-LISP `NIL`/`T` views and KEYWORD-package views
    map back to their UNIQUE representations (`SExpr.nil`/`SExpr.t`/
    `.keyword`). -/
private def unview : LexView → SExpr
  | .number v => .atom (.number v)
  | .char c => .atom (.char c)
  | .string s => .atom (.string s)
  | .sym n p =>
    if p = "KEYWORD" then .atom (.keyword n)
    else if p = "COMMON-LISP" ∧ n = "NIL" then .nil
    else if p = "COMMON-LISP" ∧ n = "T" then .t
    else if h : canonSym p n then .atom (.symbol ⟨p, n, h⟩)
    else .nil -- unreachable: canonSym only fails on the arms above

/-- Every viewable SExpr is recovered from its view: `unview` is a
    retraction of `lexView?`. -/
private theorem eq_unview : ∀ {x : SExpr} {v : LexView},
    lexView? x = some v → x = unview v := by
  intro x v h
  cases x with
  | nil =>
    cases h
    rfl
  | cons a b => simp [lexView?] at h
  | atom a =>
    cases a with
    | keyword k =>
      cases h
      rfl
    | number n =>
      cases h
      rfl
    | char c =>
      cases h
      rfl
    | string s =>
      cases h
      rfl
    | symbol s =>
      -- `lexView? (.atom (.symbol s))` is stuck on the `.t`-pattern overlap;
      -- split the compiled match (one case per source pattern — the
      -- structurally impossible ones are refuted by their pattern
      -- equations). Both symbol branches produce a `.sym` view whose
      -- `unview` lands back on the same value (the `.t` branch because
      -- `unview` maps the COMMON-LISP `T` view to `SExpr.t` itself).
      unfold lexView? at h
      split at h <;> cases h
      · -- `.nil` pattern: impossible
        rename_i heq
        simp at heq
      · -- the `.t` pattern
        rename_i heq
        rw [heq]
        simp [unview, SExpr.t]
      · -- generic symbol
        rename_i hcon heq
        injection heq with h1
        injection h1 with h2
        subst h2
        rcases s with ⟨p, n, hc⟩
        have hc' := hc
        simp only [canonSym, Bool.and_eq_true, Bool.not_eq_true',
          Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
          Bool.or_eq_false_iff, bne_iff_ne] at hc'
        have hnk : ¬(p = "KEYWORD") := hc'.2
        have hn1 : ¬(p = "COMMON-LISP" ∧ n = "NIL") := by
          intro hpn
          rcases hc'.1 with hne | ⟨hn1', _⟩
          · exact hne hpn.1
          · exact hn1' hpn.2
        have hn2 : ¬(p = "COMMON-LISP" ∧ n = "T") := by
          intro hpn
          rcases hc'.1 with hne | ⟨_, hn2'⟩
          · exact hne hpn.1
          · exact hn2' hpn.2
        simp only [unview]
        rw [if_neg hnk, if_neg hn1, if_neg hn2, dif_pos hc]
      · -- keyword pattern: impossible
        rename_i heq
        simp at heq
      · -- number pattern: impossible
        rename_i heq
        simp at heq
      · -- char pattern: impossible
        rename_i heq
        simp at heq
      · -- string pattern: impossible
        rename_i heq
        simp at heq

/-- INJECTIVITY of the lexorder view. This is the keystone the value-space
    canonicity invariants (BUG-012/013/014) were installed for: two SExpr
    values that `lexorder` cannot distinguish are EQUAL. -/
theorem lexView?_inj {x y : SExpr} {v : LexView}
    (hx : lexView? x = some v) (hy : lexView? y = some v) : x = y :=
  (eq_unview hx).trans (eq_unview hy).symm

/-! ## Bridge lemmas: `lexorder` through views -/

private theorem lexorder_some_some {x y : SExpr} {a b : LexView}
    (hx : lexView? x = some a) (hy : lexView? y = some b) :
    lexorder x y = if alphLe a b then SExpr.t else SExpr.nil := by
  unfold lexorder
  rw [hx, hy]

private theorem lexorder_some_none {x y : SExpr} {a : LexView}
    (hx : lexView? x = some a) (hy : lexView? y = none) :
    lexorder x y = SExpr.t := by
  unfold lexorder
  rw [hx, hy]

private theorem lexorder_none_some {x y : SExpr} {b : LexView}
    (hx : lexView? x = none) (hy : lexView? y = some b) :
    lexorder x y = SExpr.nil := by
  unfold lexorder
  rw [hx, hy]

private theorem lexorder_cons_cons (a1 b1 a2 b2 : SExpr) :
    lexorder (.cons a1 b1) (.cons a2 b2)
      = if a1 == a2 then lexorder b1 b2 else lexorder a1 a2 := rfl

/-- Every atom has a view (the symbol case needs the split on the compiled
    `.t`-pattern overlap; both branches are `some`). -/
private theorem atom_has_view (a : Atom) : ∃ v, lexView? (.atom a) = some v := by
  cases a with
  | symbol s =>
    unfold lexView?
    split
    all_goals first
      | exact ⟨_, rfl⟩
      | (rename_i heq; simp at heq)
  | keyword k => exact ⟨_, rfl⟩
  | number n => exact ⟨_, rfl⟩
  | char c => exact ⟨_, rfl⟩
  | string s => exact ⟨_, rfl⟩

/-- A viewless SExpr is a cons. -/
private theorem eq_cons_of_lexView?_none : ∀ {x : SExpr},
    lexView? x = none → ∃ u w, x = .cons u w := by
  intro x h
  cases x with
  | nil => simp [lexView?] at h
  | cons u w => exact ⟨u, w, rfl⟩
  | atom a =>
    exfalso
    rcases atom_has_view a with ⟨v, hv⟩
    rw [hv] at h
    cases h

/-- Every SExpr either has a view or is a cons — the case split the main
    inductions run on. -/
private theorem view_or_cons (x : SExpr) :
    (∃ v, lexView? x = some v) ∨ ∃ u w, x = .cons u w := by
  cases hx : lexView? x with
  | some v => exact Or.inl ⟨v, rfl⟩
  | none => exact Or.inr (eq_cons_of_lexView?_none hx)

/-- Extract the Bool from a `.t`-valued if-then-else. -/
private theorem cond_eq_t {c : Bool}
    (h : (if c then SExpr.t else SExpr.nil) = SExpr.t) : c = true := by
  cases c
  · exact absurd h (by simp [SExpr.t])
  · rfl

/-- Transitivity when the left argument has a view (no induction needed:
    only the view layer is involved). -/
private theorem trans_of_viewed {x y z : SExpr} {a : LexView}
    (hx : lexView? x = some a)
    (h1 : lexorder x y = SExpr.t) (h2 : lexorder y z = SExpr.t) :
    lexorder x z = SExpr.t := by
  rcases hy : lexView? y with _ | b
  · -- y is a cons: z must be a cons too (else h2 is nil), and then x < z
    rcases hz : lexView? z with _ | c
    · exact lexorder_some_none hx hz
    · rw [lexorder_none_some hy hz] at h2
      exact absurd h2 (by simp [SExpr.t])
  · rcases hz : lexView? z with _ | c
    · exact lexorder_some_none hx hz
    · have hab : alphLe a b = true := by
        rw [lexorder_some_some hx hy] at h1
        exact cond_eq_t h1
      have hbc : alphLe b c = true := by
        rw [lexorder_some_some hy hz] at h2
        exact cond_eq_t h2
      rw [lexorder_some_some hx hz, if_pos (alphLe_trans hab hbc)]

/-- Totality when the left argument has a view. -/
private theorem total_of_viewed {x : SExpr} {a : LexView}
    (hx : lexView? x = some a) (y : SExpr) :
    lexorder x y = SExpr.t ∨ lexorder y x = SExpr.t := by
  rcases hy : lexView? y with _ | b
  · exact Or.inl (lexorder_some_none hx hy)
  · rcases alphLe_total a b with h | h
    · exact Or.inl (by rw [lexorder_some_some hx hy, if_pos h])
    · exact Or.inr (by rw [lexorder_some_some hy hx, if_pos h])

/-! ## The four ground-zero order theorems

    These are the Lean-proved counterparts of ACL2's boot-strap-admitted
    rules (axioms.lisp:27154ff). ACL2 states them with its truthy `lexorder`;
    `lexorder_boolean` (EvalLemmas.lean) makes `= SExpr.t` the faithful
    rendering of "lexorder holds". -/

/-- LEXORDER-REFLEXIVE: `(lexorder x x)`. -/
theorem lexorder_refl (x : SExpr) : lexorder x x = SExpr.t := by
  induction x with
  | nil =>
    rw [lexorder_some_some rfl rfl, if_pos (alphLe_refl _)]
  | atom a =>
    rcases atom_has_view a with ⟨v, hv⟩
    rw [lexorder_some_some hv hv, if_pos (alphLe_refl v)]
  | cons a b _ ihb =>
    rw [lexorder_cons_cons, if_pos (beq_self_eq_true a)]
    exact ihb

/-- LEXORDER-ANTI-SYMMETRIC: `(implies (and (lexorder x y) (lexorder y x))
    (equal x y))`. -/
theorem lexorder_antisymm : ∀ {x y : SExpr},
    lexorder x y = SExpr.t → lexorder y x = SExpr.t → x = y := by
  intro x
  induction x with
  | nil =>
    intro y h1 h2
    rcases view_or_cons y with ⟨b, hy⟩ | ⟨u, w, rfl⟩
    · have ha : alphLe (.sym "NIL" "COMMON-LISP") b = true := by
        rw [lexorder_some_some rfl hy] at h1
        exact cond_eq_t h1
      have hb : alphLe b (.sym "NIL" "COMMON-LISP") = true := by
        rw [lexorder_some_some hy rfl] at h2
        exact cond_eq_t h2
      exact lexView?_inj rfl (hy.trans (congrArg some (alphLe_antisymm hb ha)))
    · rw [lexorder_none_some rfl rfl] at h2
      exact absurd h2 (by simp [SExpr.t])
  | atom a =>
    intro y h1 h2
    rcases atom_has_view a with ⟨v, hv⟩
    rcases view_or_cons y with ⟨b, hy⟩ | ⟨u, w, rfl⟩
    · have ha : alphLe v b = true := by
        rw [lexorder_some_some hv hy] at h1
        exact cond_eq_t h1
      have hb : alphLe b v = true := by
        rw [lexorder_some_some hy hv] at h2
        exact cond_eq_t h2
      exact lexView?_inj hv (hy.trans (congrArg some (alphLe_antisymm hb ha)))
    · rw [lexorder_none_some rfl hv] at h2
      exact absurd h2 (by simp [SExpr.t])
  | cons a1 b1 iha ihb =>
    intro y h1 h2
    rcases view_or_cons y with ⟨b, hy⟩ | ⟨u, w, rfl⟩
    · rw [lexorder_none_some rfl hy] at h1
      exact absurd h1 (by simp [SExpr.t])
    · rw [lexorder_cons_cons] at h1 h2
      by_cases hb : (a1 == u) = true
      · have heq : a1 = u := eq_of_beq hb
        subst heq
        rw [if_pos (beq_self_eq_true a1)] at h1 h2
        rw [ihb h1 h2]
      · have hb' : (u == a1) = false := by
          have hne : a1 ≠ u := fun he => hb (beq_iff_eq.mpr he)
          exact beq_eq_false_iff_ne.mpr (fun he => hne he.symm)
        rw [if_neg hb] at h1
        rw [if_neg (by simp [hb'])] at h2
        exact absurd (beq_iff_eq.mpr (iha h1 h2)) hb

/-- LEXORDER-TRANSITIVE: `(implies (and (lexorder x y) (lexorder y z))
    (lexorder x z))`. -/
theorem lexorder_trans : ∀ {x y z : SExpr},
    lexorder x y = SExpr.t → lexorder y z = SExpr.t → lexorder x z = SExpr.t := by
  intro x
  induction x with
  | nil =>
    intro y z h1 h2
    exact trans_of_viewed rfl h1 h2
  | atom a =>
    intro y z h1 h2
    rcases atom_has_view a with ⟨v, hv⟩
    exact trans_of_viewed hv h1 h2
  | cons a1 b1 iha ihb =>
    intro y z h1 h2
    -- x is a cons, so y (then z) must be conses too
    rcases view_or_cons y with ⟨b, hy⟩ | ⟨a2, b2, rfl⟩
    · rw [lexorder_none_some rfl hy] at h1
      exact absurd h1 (by simp [SExpr.t])
    rcases view_or_cons z with ⟨c, hz⟩ | ⟨a3, b3, rfl⟩
    · rw [lexorder_none_some rfl hz] at h2
      exact absurd h2 (by simp [SExpr.t])
    rw [lexorder_cons_cons] at h1 h2 ⊢
    by_cases h12 : (a1 == a2) = true
    · have he12 : a1 = a2 := eq_of_beq h12
      subst he12
      rw [if_pos (beq_self_eq_true a1)] at h1
      by_cases h23 : (a1 == a3) = true
      · have he23 : a1 = a3 := eq_of_beq h23
        subst he23
        rw [if_pos (beq_self_eq_true a1)] at h2 ⊢
        exact ihb h1 h2
      · rw [if_neg h23] at h2 ⊢
        exact h2
    · rw [if_neg h12] at h1
      by_cases h23 : (a2 == a3) = true
      · have he23 : a2 = a3 := eq_of_beq h23
        subst he23
        rw [if_neg h12]
        exact h1
      · rw [if_neg h23] at h2
        by_cases h13 : (a1 == a3) = true
        · -- a1 = a3 would make the strict car chain a cycle: antisymmetry
          -- collapses it to a1 = a2, contradicting h12
          have he13 : a1 = a3 := eq_of_beq h13
          subst he13
          exact absurd (beq_iff_eq.mpr (lexorder_antisymm h1 h2)) h12
        · rw [if_neg h13]
          exact iha h1 h2

/-- LEXORDER-TOTAL: `(or (lexorder x y) (lexorder y x))`. -/
theorem lexorder_total : ∀ (x y : SExpr),
    lexorder x y = SExpr.t ∨ lexorder y x = SExpr.t := by
  intro x
  induction x with
  | nil => exact fun y => total_of_viewed rfl y
  | atom a =>
    intro y
    rcases atom_has_view a with ⟨v, hv⟩
    exact total_of_viewed hv y
  | cons a1 b1 iha ihb =>
    intro y
    rcases view_or_cons y with ⟨b, hy⟩ | ⟨a2, b2, rfl⟩
    · exact Or.symm (total_of_viewed hy (.cons a1 b1))
    · rw [lexorder_cons_cons, lexorder_cons_cons]
      by_cases h12 : (a1 == a2) = true
      · have he : a1 = a2 := eq_of_beq h12
        subst he
        rw [if_pos (beq_self_eq_true a1), if_pos (beq_self_eq_true a1)]
        exact ihb b2
      · have h21 : (a2 == a1) = false := by
          have hne : a1 ≠ a2 := fun he => h12 (beq_iff_eq.mpr he)
          exact beq_eq_false_iff_ne.mpr (fun he => hne he.symm)
        rw [if_neg h12, if_neg (by simp [h21])]
        exact iha a2

end ACL2
