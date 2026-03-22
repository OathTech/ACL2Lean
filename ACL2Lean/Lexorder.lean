import ACL2Lean.Logic

namespace ACL2

open Logic

/-- Ordering among Atom kinds: number < keyword < string < symbol.
    Follows ACL2's ordering convention. -/
def atomKind : Atom → Nat
  | .number _ => 0
  | .keyword _ => 1
  | .string _ => 2
  | .symbol _ => 3

/-- `lexorder x y` — total ordering on SExpr values.
    nil is smallest, atoms ordered by kind then value, conses are largest
    and compared lexicographically (car then cdr). -/
def lexorder (x y : SExpr) : SExpr :=
  match x, y with
  | .nil, _ => .t          -- nil ≤ everything
  | _, .nil => .nil                         -- nothing > nil except nil
  | .atom a, .atom b =>
    if atomKind a < atomKind b then .t
    else if atomKind a > atomKind b then .nil
    else -- same kind
      match a, b with
      | .number (.int m), .number (.int n) => if m ≤ n then .t else .nil
      | .keyword k1, .keyword k2 => if k1 ≤ k2 then .t else .nil
      | .string s1, .string s2 => if s1 ≤ s2 then .t else .nil
      | .symbol s1, .symbol s2 =>
        if s1.name < s2.name then .t
        else if s1.name = s2.name then
          if s1.package ≤ s2.package then .t else .nil
        else .nil
      -- Mixed number subtypes (int vs rational vs decimal)
      | .number (.int _), .number _ => .t
      | .number _, .number (.int _) => .nil
      | .number (.rational n1 d1), .number (.rational n2 d2) =>
        if n1 < n2 ∨ (n1 = n2 ∧ d1 ≤ d2) then .t else .nil
      | .number (.rational _ _), .number (.decimal _ _) => .t
      | .number (.decimal _ _), .number (.rational _ _) => .nil
      | .number (.decimal m1 e1), .number (.decimal m2 e2) =>
        if e1 < e2 then .t
        else if e1 = e2 then if m1 ≤ m2 then .t else .nil
        else .nil
      | _, _ => .nil -- unreachable (same kind guarantees same constructor)
  | .atom _, .cons _ _ => .t  -- atoms before conses
  | .cons _ _, .atom _ => .nil
  | .cons a1 b1, .cons a2 b2 =>
    if a1 == a2 then lexorder b1 b2
    else lexorder a1 a2

@[simp] theorem lexorder_nil (y : SExpr) : lexorder .nil y = .t := by
  cases y <;> rfl

/-- `lexorder x x = t` for all x (reflexivity). -/
theorem lexorder_refl (x : SExpr) : lexorder x x = .t := by
  induction x with
  | nil => rfl
  | atom a =>
    simp only [lexorder, show ¬(atomKind a < atomKind a) from Nat.lt_irrefl _, ite_false]
    cases a with
    | number n =>
      cases n with
      | int k => simp
      | rational n d => simp
      | decimal m e => simp
    | keyword k => simp
    | string s => simp
    | symbol s => simp [show ¬(s.name < s.name) from String.lt_irrefl _]
  | cons a b _ ihb => simp only [lexorder, beq_self_eq_true, ite_true]; exact ihb

set_option maxHeartbeats 400000 in
/-- `lexorder x y = t ∨ lexorder y x = t` for all x, y (totality). -/
theorem lexorder_total (x y : SExpr) :
    Logic.toBool (lexorder x y) = true ∨ Logic.toBool (lexorder y x) = true := by
  induction x, y using lexorder.induct with
  -- nil ≤ everything
  | case1 y => left; simp [lexorder, Logic.toBool]
  -- x ≠ nil, nil → right (nil ≤ x)
  | case2 t _ => right; simp [lexorder, Logic.toBool]
  -- atom a, atom b with kind a < kind b → left
  | case3 a b hlt => left; simp [lexorder, hlt, Logic.toBool]
  -- atom a, atom b with kind a > kind b → right (kind b < kind a)
  | case4 a b _ hgt => right; simp [lexorder, Logic.toBool, show atomKind b < atomKind a from hgt]
  -- int m ≤ n → left
  | case5 m n hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- int ¬(m ≤ n) → right (n ≤ m)
  | case6 m n hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool, show n ≤ m from Int.le_of_lt (Int.not_le.mp hnle)]
  -- keyword k1 ≤ k2 → left
  | case7 k1 k2 hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- keyword ¬(k1 ≤ k2) → right (k2 ≤ k1)
  | case8 k1 k2 hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool,
      show k2 ≤ k1 from fun h => String.lt_asymm (String.not_le.mp hnle) h]
  -- string s1 ≤ s2 → left
  | case9 s1 s2 hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- string ¬(s1 ≤ s2) → right (s2 ≤ s1)
  | case10 s1 s2 hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool,
      show s2 ≤ s1 from fun h => String.lt_asymm (String.not_le.mp hnle) h]
  -- symbol s1.name < s2.name → left
  | case11 s1 s2 hlt _ _ => left; simp [lexorder, atomKind, Logic.toBool, hlt]
  -- symbol name equal, package ≤ → left
  | case12 s1 s2 _ heq hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, heq, hle]
  -- symbol name equal, ¬(package ≤) → right (reverse package ≤)
  | case13 s1 s2 _ heq hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool, heq.symm,
      show s2.package ≤ s1.package from fun h => String.lt_asymm (String.not_le.mp hnle) h]
  -- symbol ¬(name <), ¬(name =) → right (reverse name <)
  | case14 s1 s2 hnlt hneq _ _ =>
    have hlt2 : s2.name < s1.name := by
      rw [show (s2.name < s1.name) ↔ ¬(s1.name ≤ s2.name) from String.not_le.symm]
      intro hle; exact hneq (String.le_antisymm hle (fun h => hnlt h))
    right; simp [lexorder, atomKind, Logic.toBool, hlt2]
  -- int _, number _ (not int) → left
  | case15 _ _ _ _ _ => left; simp [lexorder, atomKind, Logic.toBool]
  -- number _ (not int), int _ → right
  | case16 _ _ _ _ _ => right; simp [lexorder, atomKind, Logic.toBool]
  -- rational, n1*d2 ≤ n2*d1 → left
  | case17 n1 d1 n2 d2 hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- rational, ¬(n1 < n2 ∨ n1 = n2 ∧ d1 ≤ d2) → right
  | case18 n1 d1 n2 d2 hnle _ _ =>
    right; simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool]
    have h := not_or.mp hnle
    have hge : ¬(n1 < n2) := h.1
    have hneqd : ¬(n1 = n2 ∧ d1 ≤ d2) := h.2
    simp [show n2 < n1 ∨ (n2 = n1 ∧ d2 ≤ d1) from by omega]
  -- rational, decimal → left
  | case19 _ _ _ _ _ _ => left; simp [lexorder, atomKind, Logic.toBool]
  -- decimal, rational → right
  | case20 _ _ _ _ _ _ => right; simp [lexorder, atomKind, Logic.toBool]
  -- decimal e1 < e2 → left
  | case21 _ _ _ _ hlt _ _ => left; simp [lexorder, atomKind, Logic.toBool, hlt]
  -- decimal e1 = e2, m1 ≤ m2 → left
  | case22 _ _ _ hle _ _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- decimal e1 = e2, ¬(m1 ≤ m2) → right (m2 ≤ m1)
  | case23 m1 m2 _ hnle _ _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool,
      show m2 ≤ m1 from Int.le_of_lt (Int.not_le.mp hnle)]
  -- decimal ¬(e1 < e2), ¬(e1 = e2) → right (e2 < e1)
  | case24 _ e1 _ e2 hnlt hneq _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool, show e2 < e1 from by omega]
  -- catch-all: same kind but no specific pair matches → contradiction
  | case25 a b hka1 hka2 _ h_kw h_str h_sym h_int_num h_num_int h_rat_rat h_rat_dec h_dec_rat h_dec_dec =>
    exfalso
    have hkeq : atomKind a = atomKind b := Nat.le_antisymm (Nat.not_lt.mp hka2) (Nat.not_lt.mp hka1)
    cases a with
    | number n1 =>
      cases b with
      | number n2 =>
        cases n1 with
        | int v1 => exact h_int_num v1 n2 rfl rfl
        | rational num1 den1 =>
          cases n2 with
          | int v2 => exact h_num_int (.rational num1 den1) v2 rfl rfl
          | rational num2 den2 => exact h_rat_rat num1 den1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_rat_dec num1 den1 m2 e2 rfl rfl
        | decimal m1 e1 =>
          cases n2 with
          | int v2 => exact h_num_int (.decimal m1 e1) v2 rfl rfl
          | rational num2 den2 => exact h_dec_rat m1 e1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_dec_dec m1 e1 m2 e2 rfl rfl
      | keyword _ => simp [atomKind] at hkeq
      | string _ => simp [atomKind] at hkeq
      | symbol _ => simp [atomKind] at hkeq
    | keyword k1 =>
      cases b with
      | keyword k2 => exact h_kw k1 k2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | string s1 =>
      cases b with
      | string s2 => exact h_str s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | symbol s1 =>
      cases b with
      | symbol s2 => exact h_sym s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
  -- atom vs cons → left
  | case26 _ _ _ => left; simp [lexorder, Logic.toBool]
  -- cons vs atom → right
  | case27 _ _ _ => right; simp [lexorder, Logic.toBool]
  -- cons a1 b1, cons a2 b2 with a1 == a2 → IH on b1, b2
  | case28 a1 b1 a2 b2 heq ih =>
    simp only [lexorder, heq]
    have : (a2 == a1) = true := by simp [beq_iff_eq] at heq ⊢; exact heq.symm
    simp only [this, ite_true]
    exact ih
  -- cons a1 b1, cons a2 b2 with ¬(a1 == a2) → IH on a1, a2
  | case29 a1 b1 a2 b2 hne ih =>
    simp only [lexorder, hne]
    have : ¬(a2 == a1) = true := by simp only [beq_iff_eq] at hne ⊢; exact fun h => hne h.symm
    simp only [this]
    exact ih

/-- Antisymmetry restricted to integers. Fully proved. -/
theorem lexorder_antisym_int (m n : Int)
    (hxy : Logic.toBool (lexorder (.atom (.number (.int m))) (.atom (.number (.int n)))) = true)
    (hyx : Logic.toBool (lexorder (.atom (.number (.int n))) (.atom (.number (.int m)))) = true) :
    SExpr.atom (.number (.int m)) = SExpr.atom (.number (.int n)) := by
  simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hxy hyx
  split at hxy <;> split at hyx <;> simp_all
  congr; omega

set_option maxHeartbeats 400000 in
/-- Antisymmetry: `lexorder x y ∧ lexorder y x → x = y`. -/
theorem lexorder_antisym (x y : SExpr)
    (hxy : Logic.toBool (lexorder x y) = true)
    (hyx : Logic.toBool (lexorder y x) = true) :
    x = y := by
  induction x, y using lexorder.induct with
  -- nil ≤ y, y ≤ nil → y = nil
  | case1 y =>
    cases y with | nil => rfl | _ => simp [lexorder, Logic.toBool] at hyx
  -- t ≤ nil (t ≠ nil) → contradiction
  | case2 t ht =>
    cases t with | nil => exact absurd rfl ht | _ => simp [lexorder, Logic.toBool] at hxy
  -- kind a < kind b → lexorder b a = nil → contradiction
  | case3 a b hlt =>
    simp [lexorder, hlt, show ¬(atomKind b < atomKind a) from Nat.not_lt.mpr (Nat.le_of_lt hlt),
      Logic.toBool] at hyx
  -- kind a > kind b → lexorder a b = nil → contradiction
  | case4 a b hnlt hgt =>
    simp [lexorder, show ¬(atomKind a < atomKind b) from hnlt, hgt, Logic.toBool] at hxy
  -- int m ≤ n, int n ≤ m → m = n
  | case5 m n hle hnlt hngt =>
    simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hyx
    split at hyx <;> simp_all
    congr; omega
  -- int ¬(m ≤ n) → contradiction
  | case6 m n hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  -- keyword k1 ≤ k2, k2 ≤ k1 → k1 = k2
  | case7 k1 k2 hle hnlt hngt =>
    simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hyx
    split at hyx <;> simp_all
    congr; exact String.le_antisymm hle (by assumption)
  -- keyword ¬(k1 ≤ k2) → contradiction
  | case8 k1 k2 hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  -- string s1 ≤ s2, s2 ≤ s1 → s1 = s2
  | case9 s1 s2 hle hnlt hngt =>
    simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hyx
    split at hyx <;> simp_all
    congr; exact String.le_antisymm hle (by assumption)
  -- string ¬(s1 ≤ s2) → contradiction
  | case10 s1 s2 hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  -- symbol s1.name < s2.name → lexorder s2 s1 = nil → contradiction
  | case11 s1 s2 hlt hnlt hngt =>
    simp [lexorder, atomKind, Logic.toBool,
      show ¬(s2.name < s1.name) from String.lt_asymm hlt,
      show ¬(s2.name = s1.name) from fun h => String.lt_irrefl _ (h ▸ hlt)] at hyx
  -- symbol name equal, package ≤ both ways → equal
  | case12 s1 s2 hnlt heq hle hnlt2 hngt =>
    simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, heq.symm, ite_true, Logic.toBool] at hyx
    have hpkg : s2.package ≤ s1.package := by
      simp only [String.lt_irrefl, ite_false] at hyx
      exact Decidable.byContradiction fun h => by simp [h] at hyx
    have heqpkg : s1.package = s2.package := String.le_antisymm hle hpkg
    have : s1 = s2 := by cases s1; cases s2; simp_all
    subst this; rfl
  -- symbol name equal, ¬(package ≤) → contradiction
  | case13 s1 s2 hnlt heq hnle hnlt2 hngt =>
    simp [lexorder, atomKind, heq, hnle, Logic.toBool] at hxy
  -- symbol ¬(name <), ¬(name =) → contradiction
  | case14 s1 s2 hnlt hneq hnlt2 hngt =>
    simp [lexorder, atomKind, hnlt, hneq, Logic.toBool] at hxy
  -- int _, number _ (not int) → lexorder (number _) (int _) = nil → contradiction
  | case15 n1 n2 hnlt hngt hneq =>
    cases n2 with
    | int k => exact absurd rfl (hnlt k)
    | rational n d => simp [lexorder, atomKind, Logic.toBool] at hyx
    | decimal m e => simp [lexorder, atomKind, Logic.toBool] at hyx
  -- number _ (not int), int _ → contradiction
  | case16 n1 n2 hnlt hngt hneq =>
    cases n1 with
    | int k => exact absurd rfl (hnlt k)
    | rational n d => simp [lexorder, atomKind, Logic.toBool] at hxy
    | decimal m e => simp [lexorder, atomKind, Logic.toBool] at hxy
  -- rational (n1,d1) ≤ (n2,d2) and reverse → equal
  | case17 n1 d1 n2 d2 hle hnlt hngt =>
    simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hyx
    split at hyx <;> simp_all
    congr 1; congr 1 <;> omega
  -- rational ¬(n1,d1) ≤ (n2,d2) → contradiction
  | case18 n1 d1 n2 d2 hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  -- rational vs decimal → contradiction (decimal < rational)
  | case19 n1 d1 m2 e2 hnlt hngt =>
    simp [lexorder, atomKind, Logic.toBool] at hyx
  -- decimal vs rational → contradiction
  | case20 m1 e1 n2 d2 hnlt hngt =>
    simp [lexorder, atomKind, Logic.toBool] at hxy
  -- decimal e1 < e2 → contradiction (e2 < e1 is false)
  | case21 m1 e1 m2 e2 hlt hnlt hngt =>
    simp [lexorder, atomKind, Logic.toBool, show ¬(e2 < e1) from Int.not_lt.mpr (Int.le_of_lt hlt),
      show ¬(e2 = e1) from fun h => Int.lt_irrefl _ (h ▸ hlt)] at hyx
  -- decimal e1 = e2, m1 ≤ m2, m2 ≤ m1 → equal
  | case22 m1 m2 e hle hnlt hngt =>
    simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hyx
    simp only [show ¬(e < e) from Int.lt_irrefl _, ite_false, ite_true] at hyx
    split at hyx <;> simp_all
    congr; omega
  -- decimal e1 = e2, ¬(m1 ≤ m2) → contradiction
  | case23 m1 m2 e hnle hnlt hngt =>
    simp [lexorder, atomKind, show ¬(e < e) from Int.lt_irrefl _, hnle, Logic.toBool] at hxy
  -- decimal ¬(e1 < e2), ¬(e1 = e2) → contradiction
  | case24 m1 e1 m2 e2 hnlt hneq hnlt2 hngt =>
    simp [lexorder, atomKind, hnlt, hneq, Logic.toBool] at hxy
  -- catch-all unreachable
  | case25 a b hka1 hka2 _ h_kw h_str h_sym h_int_num h_num_int h_rat_rat h_rat_dec h_dec_rat h_dec_dec =>
    exfalso
    have hkeq : atomKind a = atomKind b := Nat.le_antisymm (Nat.not_lt.mp hka2) (Nat.not_lt.mp hka1)
    cases a with
    | number n1 =>
      cases b with
      | number n2 =>
        cases n1 with
        | int v1 => exact h_int_num v1 n2 rfl rfl
        | rational num1 den1 =>
          cases n2 with
          | int v2 => exact h_num_int (.rational num1 den1) v2 rfl rfl
          | rational num2 den2 => exact h_rat_rat num1 den1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_rat_dec num1 den1 m2 e2 rfl rfl
        | decimal m1 e1 =>
          cases n2 with
          | int v2 => exact h_num_int (.decimal m1 e1) v2 rfl rfl
          | rational num2 den2 => exact h_dec_rat m1 e1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_dec_dec m1 e1 m2 e2 rfl rfl
      | keyword _ => simp [atomKind] at hkeq
      | string _ => simp [atomKind] at hkeq
      | symbol _ => simp [atomKind] at hkeq
    | keyword k1 =>
      cases b with
      | keyword k2 => exact h_kw k1 k2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | string s1 =>
      cases b with
      | string s2 => exact h_str s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | symbol s1 =>
      cases b with
      | symbol s2 => exact h_sym s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
  -- atom vs cons → contradiction
  | case26 a b1 b2 => simp [lexorder, Logic.toBool] at hyx
  -- cons vs atom → contradiction
  | case27 a1 a2 b => simp [lexorder, Logic.toBool] at hxy
  -- cons with equal heads → IH on tails
  | case28 a1 b1 a2 b2 heq ih =>
    have ha : a1 = a2 := by rw [beq_iff_eq] at heq; exact heq
    subst ha
    simp only [lexorder, beq_self_eq_true, ite_true, Logic.toBool] at hxy hyx
    congr 1; exact ih hxy hyx
  -- cons with different heads → contradiction (IH gives a1 = a2)
  | case29 a1 b1 a2 b2 hne ih =>
    simp only [lexorder, hne] at hxy hyx
    have hne' : ¬(a2 == a1) = true := by simp [beq_iff_eq] at hne ⊢; exact fun h => hne h.symm
    simp only [hne', Logic.toBool] at hxy hyx
    exact absurd (ih hxy hyx) (by simp [beq_iff_eq] at hne; exact hne)

/-- Transitivity restricted to integers. Fully proved. -/
theorem lexorder_trans_int (a b c : Int)
    (hab : Logic.toBool (lexorder (.atom (.number (.int a))) (.atom (.number (.int b)))) = true)
    (hbc : Logic.toBool (lexorder (.atom (.number (.int b))) (.atom (.number (.int c)))) = true) :
    Logic.toBool (lexorder (.atom (.number (.int a))) (.atom (.number (.int c)))) = true := by
  simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at *
  split at hab <;> split at hbc <;> simp_all
  simp [show a ≤ c by omega]

private theorem lexorder_atom_kind_le (a b : Atom)
    (h : Logic.toBool (lexorder (.atom a) (.atom b)) = true) :
    atomKind a ≤ atomKind b := by
  simp only [lexorder, Logic.toBool] at h
  by_cases hab : atomKind a < atomKind b
  · exact Nat.le_of_lt hab
  · by_cases hab2 : atomKind a > atomKind b
    · simp [hab, hab2] at h
    · exact Nat.le_of_not_lt hab2

private theorem lexorder_atom_of_kind_lt (a c : Atom)
    (h : atomKind a < atomKind c) :
    Logic.toBool (lexorder (.atom a) (.atom c)) = true := by
  simp [lexorder, h, Logic.toBool]

set_option maxHeartbeats 12800000 in
private theorem lexorder_atom_trans (a b c : Atom)
    (hab : Logic.toBool (lexorder (.atom a) (.atom b)) = true)
    (hbc : Logic.toBool (lexorder (.atom b) (.atom c)) = true) :
    Logic.toBool (lexorder (.atom a) (.atom c)) = true := by
  have hk_ab := lexorder_atom_kind_le a b hab
  have hk_bc := lexorder_atom_kind_le b c hbc
  by_cases hk : atomKind a < atomKind c
  · exact lexorder_atom_of_kind_lt a c hk
  · have hk_ac : atomKind a = atomKind c := Nat.le_antisymm (Nat.le_trans hk_ab hk_bc) (Nat.not_lt.mp hk)
    have hk_ab_eq : atomKind a = atomKind b := Nat.le_antisymm hk_ab (by omega)
    have hk_bc_eq : atomKind b = atomKind c := Nat.le_antisymm hk_bc (by omega)
    cases a with
    | number na =>
      cases b with
      | number nb =>
        cases c with
        | number nc =>
          cases na with
          | int va =>
            cases nb with
            | int vb =>
              cases nc with
              | int vc =>
                simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hab hbc ⊢
                split at hab <;> split at hbc <;> simp_all; split <;> simp_all; omega
              | _ => simp [lexorder, atomKind, Logic.toBool]
            | _ =>
              cases nc with
              | int _ => simp [lexorder, atomKind, Logic.toBool] at hbc
              | _ => simp [lexorder, atomKind, Logic.toBool]
          | rational na1 nd1 =>
            cases nb with
            | int _ => simp [lexorder, atomKind, Logic.toBool] at hab
            | rational nb1 nd2 =>
              cases nc with
              | int _ => simp [lexorder, atomKind, Logic.toBool] at hbc
              | rational nc1 nd3 =>
                simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hab hbc ⊢
                split at hab <;> split at hbc <;> simp_all <;> split <;> simp_all
                all_goals (first | omega | (obtain ⟨_, _⟩ := ‹_ ∧ _›; omega) |
                  (obtain ⟨h1, h2⟩ := ‹_ ∧ _›; obtain ⟨h3, h4⟩ := ‹_ ∧ _›;
                   exact Or.inr ⟨h1.trans h3, Nat.le_trans h2 h4⟩))
              | decimal _ _ => simp [lexorder, atomKind, Logic.toBool]
            | decimal _ _ =>
              cases nc with
              | int _ => simp [lexorder, atomKind, Logic.toBool] at hbc
              | rational _ _ => simp [lexorder, atomKind, Logic.toBool] at hbc
              | decimal _ _ => simp [lexorder, atomKind, Logic.toBool]
          | decimal ma ea =>
            cases nb with
            | int _ => simp [lexorder, atomKind, Logic.toBool] at hab
            | rational _ _ => simp [lexorder, atomKind, Logic.toBool] at hab
            | decimal mb eb =>
              cases nc with
              | int _ => simp [lexorder, atomKind, Logic.toBool] at hbc
              | rational _ _ => simp [lexorder, atomKind, Logic.toBool] at hbc
              | decimal mc ec =>
                simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false] at hab hbc ⊢
                -- decimal/decimal/decimal: lex on (exponent, mantissa)
                by_cases h1 : ea < eb
                · simp [h1, Logic.toBool] at hab
                  by_cases h2 : eb < ec
                  · simp [show ea < ec from Int.lt_trans h1 h2, Logic.toBool]
                  · by_cases h3 : eb = ec
                    · simp [show ea < ec by omega, Logic.toBool]
                    · simp [h2, h3, Logic.toBool] at hbc
                · by_cases h2 : ea = eb
                  · simp [h1, h2, Logic.toBool] at hab ⊢
                    by_cases h3 : eb < ec
                    · simp [h3, Logic.toBool]
                    · by_cases h4 : eb = ec
                      · simp [h3, h4, Logic.toBool] at hbc ⊢
                        by_cases h5 : ma ≤ mb
                        · by_cases h6 : mb ≤ mc
                          · simp [show ma ≤ mc by omega]
                          · simp [h6] at hbc
                        · simp [h5] at hab
                      · simp [h3, h4, Logic.toBool] at hbc
                  · simp [h1, h2, Logic.toBool] at hab
        | _ => simp [atomKind] at hk_bc_eq
      | _ => simp [atomKind] at hk_ab_eq
    | keyword ka =>
      cases b with
      | keyword kb =>
        cases c with
        | keyword kc =>
          simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hab hbc ⊢
          split at hab <;> split at hbc <;> simp_all
          simp [String.le_trans ‹ka ≤ kb› ‹kb ≤ kc›]
        | _ => simp [atomKind] at hk_bc_eq
      | _ => simp [atomKind] at hk_ab_eq
    | string sa =>
      cases b with
      | string sb =>
        cases c with
        | string sc =>
          simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hab hbc ⊢
          split at hab <;> split at hbc <;> simp_all
          simp [String.le_trans ‹sa ≤ sb› ‹sb ≤ sc›]
        | _ => simp [atomKind] at hk_bc_eq
      | _ => simp [atomKind] at hk_ab_eq
    | symbol sa =>
      cases b with
      | symbol sb =>
        cases c with
        | symbol sc =>
          -- Use original hypotheses directly with full simp to reduce everything
          simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false] at hab hbc ⊢
          -- hab : Logic.toBool (if sa.name < sb.name then .t else ...) = true
          -- Key: Logic.toBool .t = true, Logic.toBool .nil = false
          -- So we can case-split on the conditions
          by_cases h1 : sa.name < sb.name
          · simp [h1, Logic.toBool] at hab
            by_cases h2 : sb.name < sc.name
            · simp [String.lt_trans h1 h2, Logic.toBool]
            · by_cases h3 : sb.name = sc.name
              · simp [show sa.name < sc.name by rwa [← h3], Logic.toBool]
              · simp [h2, h3, Logic.toBool] at hbc
          · by_cases h2 : sa.name = sb.name
            · simp [h1, h2, Logic.toBool] at hab ⊢
              by_cases h3 : sb.name < sc.name
              · simp [h3, Logic.toBool]
              · by_cases h4 : sb.name = sc.name
                · simp [h3, h4, Logic.toBool] at hbc ⊢
                  by_cases h5 : sa.package ≤ sb.package
                  · by_cases h6 : sb.package ≤ sc.package
                    · simp [String.le_trans h5 h6]
                    · simp [h6] at hbc
                  · simp [h5] at hab
                · simp [h3, h4, Logic.toBool] at hbc
            · simp [h1, h2, Logic.toBool] at hab
        | _ => simp [atomKind] at hk_bc_eq
      | _ => simp [atomKind] at hk_ab_eq

set_option maxHeartbeats 3200000 in
/-- Transitivity: `lexorder x y ∧ lexorder y z → lexorder x z`. -/
theorem lexorder_trans (x y z : SExpr)
    (hxy : Logic.toBool (lexorder x y) = true)
    (hyz : Logic.toBool (lexorder y z) = true) :
    Logic.toBool (lexorder x z) = true := by
  induction x, y using lexorder.induct generalizing z with
  -- nil ≤ y: lexorder nil z = .t always
  | case1 y => simp [lexorder, Logic.toBool]
  -- y = nil, x ≠ nil: hxy false
  | case2 t ht =>
    cases t with | nil => exact absurd rfl ht | _ => simp [lexorder, Logic.toBool] at hxy
  -- All atom/atom cases (3-25): need to show atom transitivity
  -- atom a < atom b (by kind): case split z
  | case3 a b hlt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case4 a b hnlt hgt =>
    simp [lexorder, show ¬(atomKind a < atomKind b) from hnlt, hgt, Logic.toBool] at hxy
  | case5 m n hle hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case6 m n hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  | case7 k1 k2 hle hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case8 k1 k2 hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  | case9 s1 s2 hle hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case10 s1 s2 hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  | case11 s1 s2 hlt hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case12 s1 s2 hnlt heq hle hnlt2 hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case13 s1 s2 hnlt heq hnle hnlt2 hngt =>
    simp [lexorder, atomKind, heq, hnle, Logic.toBool] at hxy
  | case14 s1 s2 hnlt hneq hnlt2 hngt =>
    simp [lexorder, atomKind, hnlt, hneq, Logic.toBool] at hxy
  | case15 n1 n2 hnlt hngt hneq =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case16 n1 n2 hnlt hngt hneq =>
    -- n1 (not int), int n2: lexorder gives .nil
    cases n1 with
    | int k => exact absurd rfl (hnlt k)
    | rational n d => simp [lexorder, atomKind, Logic.toBool] at hxy
    | decimal m e => simp [lexorder, atomKind, Logic.toBool] at hxy
  | case17 n1 d1 n2 d2 hle hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case18 n1 d1 n2 d2 hnle hnlt hngt =>
    simp [lexorder, atomKind, hnle, Logic.toBool] at hxy
  | case19 n1 d1 m2 e2 hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case20 m1 e1 n2 d2 hnlt hngt =>
    simp [lexorder, atomKind, Logic.toBool] at hxy
  | case21 m1 e1 m2 e2 hlt hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case22 m1 m2 e hle hnlt hngt =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => exact lexorder_atom_trans _ _ c hxy hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  | case23 m1 m2 e hnle hnlt hngt =>
    simp [lexorder, atomKind, show ¬(e < e) from Int.lt_irrefl _, hnle, Logic.toBool] at hxy
  | case24 m1 e1 m2 e2 hnlt hneq hnlt2 hngt =>
    simp [lexorder, atomKind, hnlt, hneq, Logic.toBool] at hxy
  | case25 a b hka1 hka2 _ h_kw h_str h_sym h_int_num h_num_int h_rat_rat h_rat_dec h_dec_rat h_dec_dec =>
    -- Unreachable: same as in antisymmetry
    exfalso
    have hkeq : atomKind a = atomKind b := Nat.le_antisymm (Nat.not_lt.mp hka2) (Nat.not_lt.mp hka1)
    cases a with
    | number n1 =>
      cases b with
      | number n2 =>
        cases n1 with
        | int v1 => exact h_int_num v1 n2 rfl rfl
        | rational num1 den1 =>
          cases n2 with
          | int v2 => exact h_num_int (.rational num1 den1) v2 rfl rfl
          | rational num2 den2 => exact h_rat_rat num1 den1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_rat_dec num1 den1 m2 e2 rfl rfl
        | decimal m1 e1 =>
          cases n2 with
          | int v2 => exact h_num_int (.decimal m1 e1) v2 rfl rfl
          | rational num2 den2 => exact h_dec_rat m1 e1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_dec_dec m1 e1 m2 e2 rfl rfl
      | keyword _ => simp [atomKind] at hkeq
      | string _ => simp [atomKind] at hkeq
      | symbol _ => simp [atomKind] at hkeq
    | keyword k1 =>
      cases b with
      | keyword k2 => exact h_kw k1 k2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | string s1 =>
      cases b with
      | string s2 => exact h_str s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | symbol s1 =>
      cases b with
      | symbol s2 => exact h_sym s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
  -- atom vs cons
  | case26 a b1 b2 =>
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => simp [lexorder, Logic.toBool] at hyz
    | cons _ _ => simp [lexorder, Logic.toBool]
  -- cons vs atom
  | case27 a1 a2 b => simp [lexorder, Logic.toBool] at hxy
  -- cons(a1,b1) vs cons(a2,b2), a1 == a2
  | case28 a1 b1 a2 b2 heq ih =>
    have ha12 : a1 = a2 := by rw [beq_iff_eq] at heq; exact heq
    subst ha12
    simp only [lexorder, beq_self_eq_true, ite_true, Logic.toBool] at hxy
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => simp [lexorder, Logic.toBool] at hyz
    | cons a3 b3 =>
      simp only [lexorder, Logic.toBool] at hyz ⊢
      by_cases ha13 : (a1 == a3) = true
      · -- a1 == a3 (and a1 = a2, so a2 == a3 too)
        simp only [ha13, ite_true] at hyz ⊢
        exact ih b3 hxy hyz
      · -- a1 ≠ a3
        simp only [show ¬(a1 == a3) = true from ha13] at hyz ⊢
        exact hyz
  -- cons(a1,b1) vs cons(a2,b2), a1 ≠ a2
  | case29 a1 b1 a2 b2 hne ih =>
    simp only [lexorder, hne, Logic.toBool] at hxy
    cases z with
    | nil => simp [lexorder, Logic.toBool] at hyz
    | atom c => simp [lexorder, Logic.toBool] at hyz
    | cons a3 b3 =>
      simp only [lexorder, Logic.toBool] at hyz ⊢
      by_cases ha23 : (a2 == a3) = true
      · -- a2 == a3: hyz is about b2, b3. Need lexorder a1 a3.
        have ha23' : a2 = a3 := by rw [beq_iff_eq] at ha23; exact ha23
        subst ha23'
        -- a1 ≠ a2 = a3, so a1 ≠ a3
        by_cases ha13 : (a1 == a2) = true
        · exact absurd ha13 hne
        · simp only [ha13]
          exact hxy
      · -- a2 ≠ a3: hyz gives lexorder a2 a3.
        simp only [show ¬(a2 == a3) = true from ha23] at hyz
        -- By IH: lexorder a1 a3
        have h13 := ih a3 hxy hyz
        by_cases ha13 : (a1 == a3) = true
        · -- a1 == a3: need lexorder b1 b3, but by antisymmetry a1 = a2
          have ha13' : a1 = a3 := by rw [beq_iff_eq] at ha13; exact ha13
          subst ha13'
          -- We have lexorder a1 a2 = true (hxy) and lexorder a2 a1 = true (h13 with a3=a1)
          -- Wait, h13 is lexorder a1 a1 = true. And lexorder a1 a2 = true.
          -- Also lexorder a2 a1: from hyz and totality?
          -- Actually h13 = lexorder a1 a1 = lexorder_refl, which is always true.
          -- We need lexorder b1 b3. We don't have it directly.
          -- But since a1 = a3 and a1 ≠ a2, from hxy: lexorder a1 a2 = true
          -- from hyz: lexorder a2 a1 = true (since a2 ≠ a1 = a3, hyz = lexorder a2 a3 = lexorder a2 a1)
          -- By antisymmetry: a1 = a2, contradiction with hne.
          have hyz' : Logic.toBool (lexorder a2 a1) = true := hyz
          have := lexorder_antisym a1 a2 hxy hyz'
          rw [beq_iff_eq] at hne; exact absurd this hne
        · simp only [ha13]
          exact h13

end ACL2
