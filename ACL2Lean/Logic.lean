import ACL2Lean.Syntax

namespace ACL2
namespace Logic

open ACL2

/-- ACL2 truthiness: everything except `nil` is truthy (only `nil` is false). -/
@[inline, simp] def toBool (s : SExpr) : Bool :=
  match s with
  | .nil => false
  | _ => true

/-- ACL2 `if` lazy evaluation. -/
@[inline, simp] def if_ (c t e : SExpr) : SExpr :=
  if toBool c then t else e

/-- Coerce an S-expression to an integer if possible, else 0. -/
@[inline, simp] def toInt (s : SExpr) : Int :=
  match s with
  | .atom (.number (.int n)) => n
  | _ => 0

/-- Coerce an S-expression to a natural number for termination measures. -/
@[inline, simp] def toNat (s : SExpr) : Nat :=
  (toInt s).toNat

/-- Extract (numerator, denominator) from any SExpr. Non-numbers → (0, 1).
    On the canonical `Number` type (BUG-012 Option A) the denominator is ≥ 2
    and the pair is reduced, so `toRat` is INJECTIVE on numbers. -/
@[inline] def toRat (s : SExpr) : Int × Nat :=
  match s with
  | .atom (.number (.int n)) => (n, 1)
  | .atom (.number (.rational n d _)) => (n, d)
  | _ => (0, 1)

/-- `natAbs` of an EXACT integer division by a positive `Nat` divisor.
    (Stated standalone with a clean variable so `subst` applies; proved from
    core lemmas only — the Mathlib `Int.natAbs_ediv_of_dvd` pulls in
    `Classical.choice`, which would leak into every proof that computes
    through `mkNumber`.) -/
theorem natAbs_ediv_exact (g : Nat) (n : Int) (hg : 0 < g)
    (h : (Int.ofNat g) ∣ n) : (n / Int.ofNat g).natAbs = n.natAbs / g := by
  rcases h with ⟨k, hk⟩
  subst hk
  rw [Int.mul_ediv_cancel_left _ (by simp only [Int.ofNat_eq_natCast]; omega), Int.natAbs_mul]
  show k.natAbs = g * k.natAbs / g   -- (Int.ofNat g).natAbs ≡ g definitionally
  exact (Nat.mul_div_cancel_left _ hg).symm

/-- The gcd-reduction in `mkNumber` yields a CANONICAL ratio: if the reduced
    denominator is not 1, it is ≥ 2 and coprime to the reduced numerator. -/
theorem canonRat_mkNumber {n : Int} {d : Nat} (hd : d ≠ 0)
    (hd' : d / Nat.gcd n.natAbs d ≠ 1) :
    canonRat (n / Int.ofNat (Nat.gcd n.natAbs d)) (d / Nat.gcd n.natAbs d)
      = true := by
  have hg : 0 < Nat.gcd n.natAbs d :=
    Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hd)
  have hdvd_d : Nat.gcd n.natAbs d ∣ d := Nat.gcd_dvd_right _ _
  have hdvd_n : (Int.ofNat (Nat.gcd n.natAbs d)) ∣ n := by
    rcases Nat.gcd_dvd_left n.natAbs d with ⟨c, hc⟩
    refine Int.dvd_natAbs.mp ⟨Int.ofNat c, ?_⟩
    conv => lhs; rw [hc]
    rfl
  -- denominator ≥ 2: the exact quotient is nonzero (g ∣ d, d ≠ 0) and ≠ 1
  have hd'pos : 0 < d / Nat.gcd n.natAbs d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd_d) hg
  have h2 : 2 ≤ d / Nat.gcd n.natAbs d := by omega
  -- coprimality: |n/g| = |n|/g, and (|n|/g, d/g) is the coprime pair
  have habs : (n / Int.ofNat (Nat.gcd n.natAbs d)).natAbs
      = n.natAbs / Nat.gcd n.natAbs d := natAbs_ediv_exact _ _ hg hdvd_n
  have hcop : Nat.Coprime (n.natAbs / Nat.gcd n.natAbs d)
      (d / Nat.gcd n.natAbs d) := Nat.coprime_div_gcd_div_gcd hg
  simp only [canonRat, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, habs]
  exact ⟨h2, hcop⟩

/-- Construct a normalized number SExpr from numerator/denominator — THE
    smart constructor for every ACL2 number (BUG-012 Option A: the canonicity
    invariant is proved here, so junk representations are unrepresentable).
    Reduces by GCD; returns an integer when denominator divides out. -/
@[inline] def mkNumber (n : Int) (d : Nat) : SExpr :=
  if hd : d = 0 then .atom (.number (.int 0))
  else
    let g := Nat.gcd n.natAbs d
    let n' := n / Int.ofNat g
    let d' := d / g
    if hd' : d' = 1 then .atom (.number (.int n'))
    else .atom (.number (.rational n' d' (canonRat_mkNumber hd hd')))

/-- ACL2 `zp`: true if `n` is not a positive integer. -/
@[inline, simp] def zp (n : SExpr) : SExpr :=
  if toInt n <= 0 then .t else .nil

/-- ACL2 `plus`. Full rational arithmetic. -/
@[inline] def plus (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  mkNumber (an * bd + bn * ad) (ad * bd)

/-- ACL2 `minus`. Full rational arithmetic. -/
@[inline] def minus (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  mkNumber (an * bd - bn * ad) (ad * bd)

/-- ACL2 `times`. Full rational arithmetic. -/
@[inline] def times (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  mkNumber (an * bn) (ad * bd)

/-- ACL2 `div`. Full rational arithmetic. -/
@[inline] def div (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  if bn == 0 then .atom (.number (.int 0))
  else
    -- (an/ad) / (bn/bd) = (an*bd) / (ad*bn)
    let rn := an * bd
    let rd := ad * bn.natAbs
    let rn := if bn < 0 then -rn else rn
    mkNumber rn rd

/-- ACL2 `lt`. Full rational comparison. -/
@[inline, simp] def lt (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  if an * bd < bn * ad then .t else .nil

/-- ACL2 `eq`. -/
@[inline, simp] def eq (a b : SExpr) : SExpr :=
  if a == b then .t else .nil

/-- ACL2 `equal`. -/
@[inline, simp] def equal (a b : SExpr) : SExpr :=
  if a == b then .t else .nil

/-- ACL2 `consp`. -/
@[inline, simp] def consp (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .t
  | _ => .nil

/-- ACL2 `acl2-numberp`: true exactly on numbers. (The Logic-level twin of
    `callBuiltin`'s inline match, for the driver's uniform value layer.) -/
@[inline, simp] def acl2Numberp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number _) => .t
  | _ => .nil

/-- ACL2 `atom`. -/
@[inline, simp] def atom (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .nil
  | _ => .t

/-- ACL2 `car`. -/
@[inline, simp] def car (s : SExpr) : SExpr :=
  match s with
  | .cons a _ => a
  | _ => .nil

/-- ACL2 `cdr`. -/
@[inline, simp] def cdr (s : SExpr) : SExpr :=
  match s with
  | .cons _ d => d
  | _ => .nil

/-- ACL2 `cons`. -/
@[inline, simp] def cons (a d : SExpr) : SExpr :=
  .cons a d

/-- ACL2 `list`. -/
@[inline, simp] def list (args : List SExpr) : SExpr :=
  SExpr.ofList args

/-- ACL2 `implies`. -/
@[inline, simp] def implies (p q : SExpr) : SExpr :=
  if toBool p then
    if toBool q then .t else .nil
  else .t

/-- ACL2 `and`. -/
@[inline, simp] def and (a b : SExpr) : SExpr :=
  if toBool a then b else .nil

/-- ACL2 `or`. -/
@[inline, simp] def or (a b : SExpr) : SExpr :=
  if toBool a then a else b

/-- ACL2 `not`. -/
@[inline, simp] def not (a : SExpr) : SExpr :=
  if toBool a then .nil else .t

/-- ACL2 `integerp`. -/
@[inline, simp] def integerp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int _)) => .t
  | _ => .nil

/-- ACL2 `posp`. -/
@[inline, simp] def posp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n > 0 then .t else .nil
  | _ => .nil

/-- ACL2 `natp`. -/
@[inline, simp] def natp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n >= 0 then .t else .nil
  | _ => .nil

/-- ACL2 `evenp`. -/
@[inline, simp] def evenp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n % 2 == 0 then .t else .nil
  | _ => .nil

/-- ACL2 `oddp`. -/
@[inline, simp] def oddp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n % 2 != 0 then .t else .nil
  | _ => .nil

/-- ACL2 `quote`. -/
@[inline, simp] def quote_ (s : SExpr) : SExpr := s

/-- ACL2 `expt`. For negative exponents, returns the rational `1/(x^|y|)`. -/
@[inline, simp] def expt (a b : SExpr) : SExpr :=
  let x := toInt a
  let y := toInt b
  if y < 0 then
    -- 1/(x^-y) as an EXACT canonical rational: sign to the numerator
    -- (1/p = sign(p)/|p|). Fixes the former junk producer (`expt 1 -1` built
    -- `.rational 1 1`) and its sign bug (`expt -1 -1` lost the sign) — both
    -- latent, EXPT is not yet wired into callBuiltin.
    let p := x ^ (-y).toNat
    if p == 0 then .atom (.number (.int 0))
    else mkNumber p.sign p.natAbs
  else .atom (.number (.int (x ^ y.toNat)))

/-- ACL2 `le` (<=). Full rational comparison. -/
@[inline, simp] def le (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  if an * bd ≤ bn * ad then .t else .nil

/-- ACL2 `ge` (>=). Full rational comparison. -/
@[inline, simp] def ge (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  if an * bd ≥ bn * ad then .t else .nil

/-- ACL2 `gt` (>). Full rational comparison. -/
@[inline, simp] def gt (a b : SExpr) : SExpr :=
  let (an, ad) := toRat a
  let (bn, bd) := toRat b
  if an * bd > bn * ad then .t else .nil

/-- ACL2 `first`. -/
@[inline, simp] def first (s : SExpr) : SExpr := car s

/-- ACL2 `second`. -/
@[inline, simp] def second (s : SExpr) : SExpr := car (cdr s)

/-- ACL2 `endp`. -/
@[inline, simp] def endp (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .nil
  | _ => .t

/-- ACL2 `stringp`. -/
@[inline, simp] def stringp (s : SExpr) : SExpr :=
  match s with
  | .atom (.string _) => .t
  | _ => .nil

/-- ACL2 `characterp`. -/
@[inline, simp] def characterp (s : SExpr) : SExpr :=
  match s with
  | .atom (.char _) => .t
  | _ => .nil

/-- ACL2 `char-code`: a character's code (0–255). Completion axiom
    (axioms.lisp `completion-of-char-code`): a NON-character is 0. -/
@[inline, simp] def charCode (s : SExpr) : SExpr :=
  match s with
  | .atom (.char c) => .atom (.number (.int c.toNat))
  | _ => .atom (.number (.int 0))

/-- ACL2 `code-char`: the character with the given code, for an integer in
    [0, 256). Completion axiom (`completion-of-code-char`): a non-integer, or
    an integer outside [0, 256), maps to `*null-char*` = code 0. -/
@[inline, simp] def codeChar (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) =>
    if 0 ≤ n ∧ n < 256 then .atom (.char (UInt8.ofNat n.toNat))
    else .atom (.char 0)
  | _ => .atom (.char 0)

/-- ACL2 `booleanp` — `t` iff the value is exactly `t` or `nil`
    (`(or (equal x t) (equal x nil))`). -/
@[inline, simp] def booleanp (s : SExpr) : SExpr :=
  if s == SExpr.t || s == SExpr.nil then .t else .nil

/-- ACL2 `symbolp` (`nil` is a symbol). -/
@[inline, simp] def symbolp (s : SExpr) : SExpr :=
  match s with
  -- Keywords ARE symbols in ACL2 (they live in the KEYWORD package;
  -- `keywordp-forward-to-symbolp` in axioms.lisp), so `.keyword` is truthy
  -- here too. `nil` is the symbol NIL. (A keyword stays DISTINCT from the
  -- like-named symbol under `equal` — only `symbolp` unifies them.)
  | .atom (.symbol _) | .atom (.keyword _) | .nil => .t
  | _ => .nil

/-- ACL2 `nfix` — coerce to a natural: a non-negative integer is itself,
    anything else (negative int, non-int) becomes `0`. -/
@[inline, simp] def nfix (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n >= 0 then s else .atom (.number (.int 0))
  | _ => .atom (.number (.int 0))

/-- ACL2 `fix` — coerce to a number: a number is itself, anything else
    becomes `0` (`(if (acl2-numberp x) x 0)`). The Logic-level twin of
    `callBuiltin`'s former inline match, named so the D4 definition-fact
    route can state lemmas about it. -/
@[inline, simp] def fix (s : SExpr) : SExpr :=
  match s with
  | .atom (.number _) => s
  | _ => .atom (.number (.int 0))

/-- ACL2 `string-append`. Returns empty string on non-string inputs. -/
@[inline, simp] def string_append (a b : SExpr) : SExpr :=
  match a, b with
  | .atom (.string s1), .atom (.string s2) => .atom (.string (s1 ++ s2))
  | _, _ => .atom (.string "")

/-- Two's complement bitwise AND on integers.
    Uses De Morgan: `NOT a AND NOT b = NOT (a OR b)`,
    and `a AND NOT b = a XOR (a AND b)`. -/
private def intLogand (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => Int.ofNat (Nat.land m n)
  | .negSucc m, .ofNat n => Int.ofNat (Nat.xor n (Nat.land n m))
  | .ofNat m, .negSucc n => Int.ofNat (Nat.xor m (Nat.land m n))
  | .negSucc m, .negSucc n => Int.negSucc (Nat.lor m n)

/-- Two's complement bitwise OR on integers. -/
private def intLogor (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => Int.ofNat (Nat.lor m n)
  | .negSucc m, .ofNat n => Int.negSucc (Nat.xor m (Nat.land m n))
  | .ofNat m, .negSucc n => Int.negSucc (Nat.xor n (Nat.land n m))
  | .negSucc m, .negSucc n => Int.negSucc (Nat.land m n)

/-- Two's complement bitwise XOR on integers. -/
private def intLogxor (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => Int.ofNat (Nat.xor m n)
  | .negSucc m, .ofNat n => Int.negSucc (Nat.xor m n)
  | .ofNat m, .negSucc n => Int.negSucc (Nat.xor m n)
  | .negSucc m, .negSucc n => Int.ofNat (Nat.xor m n)

/-- ACL2 `logand`. Two's complement semantics. -/
@[inline, simp] def logand (a b : SExpr) : SExpr :=
  .atom (.number (.int (intLogand (toInt a) (toInt b))))

/-- ACL2 `logor`. Two's complement semantics. -/
@[inline, simp] def logor (a b : SExpr) : SExpr :=
  .atom (.number (.int (intLogor (toInt a) (toInt b))))

/-- ACL2 `logxor`. Two's complement semantics. -/
@[inline, simp] def logxor (a b : SExpr) : SExpr :=
  .atom (.number (.int (intLogxor (toInt a) (toInt b))))

/-- ACL2 `lognot`. -/
@[inline, simp] def lognot (a : SExpr) : SExpr :=
  .atom (.number (.int (-(toInt a) - 1)))

/-- ACL2 `ash` (arithmetic shift). -/
@[inline, simp] def ash (n i : SExpr) : SExpr :=
  let val := toInt n
  let count := toInt i
  if count >= 0 then
    .atom (.number (.int (val <<< count.toNat)))
  else
    .atom (.number (.int (val >>> (-count).toNat)))

instance : OfNat SExpr n where
  ofNat := .atom (.number (.int n))

-- Basic Axioms / Lemmas for proofs

@[simp] theorem toNat_minus_one (n : SExpr) (h : toBool (zp n) = false) :
  toNat (minus n (SExpr.atom (Atom.number (Number.int 1)))) < toNat n := by
  cases n with
  | nil => simp [zp, toBool] at h
  | cons _ _ => simp [zp, toInt, toBool] at h
  | atom a =>
    cases a with
    | symbol _ | keyword _ | string _ | char _ => simp [zp, toInt, toBool] at h
    | number num =>
      cases num with
      | rational _ _ _ => simp [zp, toInt, toBool] at h
      | int k =>
        simp only [zp, toInt] at h
        split at h
        · simp [toBool] at h
        · simp [minus, toRat, mkNumber, toNat, toInt]
          omega

@[simp, grind =] theorem car_cons (a d : SExpr) : car (cons a d) = a := rfl

@[simp, grind =] theorem cdr_cons (a d : SExpr) : cdr (cons a d) = d := rfl

@[simp, grind =] theorem toBool_true : toBool (.t) = true := rfl

@[simp, grind =] theorem toBool_nil : toBool .nil = false := rfl

@[simp, grind =] theorem if_true (t e : SExpr) : if_ (.t) t e = t := rfl

@[simp, grind =] theorem if_nil (t e : SExpr) : if_ .nil t e = e := rfl

@[grind =] theorem equal_self (x : SExpr) : equal x x = .t := by
  simp [equal]

@[simp, grind =] theorem toInt_plus_int (m n : Int) :
    toInt (plus (.atom (.number (.int m))) (.atom (.number (.int n)))) = m + n := by
  simp [plus, toRat, mkNumber, toInt]

@[simp, grind =] theorem toInt_int (n : Int) : toInt (.atom (.number (.int n))) = n := rfl

@[simp, grind =] theorem toInt_nil : toInt .nil = 0 := rfl

@[simp, grind =] theorem toInt_cons (a d : SExpr) : toInt (.cons a d) = 0 := rfl

@[simp, grind =] theorem plus_int (m n : Int) :
    plus (.atom (.number (.int m))) (.atom (.number (.int n))) =
    .atom (.number (.int (m + n))) := by
  simp [plus, toRat, mkNumber]

@[simp, grind =] theorem minus_int (m n : Int) :
    minus (.atom (.number (.int m))) (.atom (.number (.int n))) =
    .atom (.number (.int (m - n))) := by
  simp [minus, toRat, mkNumber]

@[simp, grind =] theorem times_int (m n : Int) :
    times (.atom (.number (.int m))) (.atom (.number (.int n))) =
    .atom (.number (.int (m * n))) := by
  simp [times, toRat, mkNumber]

@[simp, grind =] theorem lt_int (m n : Int) :
    lt (.atom (.number (.int m))) (.atom (.number (.int n))) =
    if m < n then .t else .nil := by
  simp [lt, toRat]

@[simp, grind =] theorem equal_atom_int (n m : Int) : equal (.atom (.number (.int n))) (.atom (.number (.int m))) = (if n = m then .t else .nil) := by
  simp [equal]

@[grind =] theorem toBool_equal (a b : SExpr) : toBool (equal a b) = true ↔ a = b := by
  unfold equal; split
  · simp_all [toBool]
  · simp_all [toBool]

@[grind =] theorem toBool_eq (a b : SExpr) : toBool (eq a b) = true ↔ a = b := by
  unfold eq; split
  · simp_all [toBool]
  · simp_all [toBool]

@[grind =] theorem equal_toInt (x : SExpr) : toBool (integerp x) = true → equal x (.atom (.number (.int (toInt x)))) = .t := by
  intro h
  cases x with
  | nil => simp [integerp, toBool] at h
  | cons _ _ => simp [integerp, toBool] at h
  | atom a =>
    cases a with
    | symbol _ | keyword _ | string _ | char _ => simp [integerp, toBool] at h
    | number n =>
      cases n with
      | rational _ _ _ => simp [integerp, toBool] at h
      | int k => simp [equal, toInt]

@[grind →] theorem integerp_toInt (x : SExpr) : toBool (integerp x) = true → x = .atom (.number (.int (toInt x))) := by
  intro h
  cases x with
  | nil => simp [integerp, toBool] at h
  | cons _ _ => simp [integerp, toBool] at h
  | atom a =>
    cases a with
    | symbol _ | keyword _ | string _ | char _ => simp [integerp, toBool] at h
    | number n =>
      cases n with
      | rational _ _ _ => simp [integerp, toBool] at h
      | int k => simp [toInt]

@[simp] theorem toInt_minus_int (m n : Int) :
    toInt (minus (.atom (.number (.int m))) (.atom (.number (.int n)))) = m - n := by
  simp [minus, toRat, mkNumber, toInt]

@[simp] theorem toInt_times_int (m n : Int) :
    toInt (times (.atom (.number (.int m))) (.atom (.number (.int n)))) = m * n := by
  simp [times, toRat, mkNumber, toInt]

@[simp, grind =] theorem consp_cons (a d : SExpr) : consp (cons a d) = .t := rfl

@[simp, grind =] theorem consp_nil : consp .nil = .nil := rfl

@[simp, grind =] theorem car_nil : car .nil = .nil := rfl

@[simp, grind =] theorem cdr_nil : cdr .nil = .nil := rfl

@[simp, grind =] theorem toBool_consp (s : SExpr) : toBool (consp s) = true ↔ ∃ a d, s = cons a d := by
  constructor
  · intro h
    cases s with
    | nil => simp [consp, toBool] at h
    | atom _ => simp [consp, toBool] at h
    | cons a d => exact ⟨a, d, rfl⟩
  · intro ⟨a, d, h⟩; subst h; simp [consp, toBool]

@[simp, grind =] theorem toBool_integerp (s : SExpr) : toBool (integerp s) = true ↔ ∃ n, s = .atom (.number (.int n)) := by
  constructor
  · intro h
    cases s with
    | nil => simp [integerp, toBool] at h
    | cons _ _ => simp [integerp, toBool] at h
    | atom a =>
      cases a with
      | symbol _ | keyword _ | string _ | char _ => simp [integerp, toBool] at h
      | number n =>
        cases n with
        | rational _ _ _ => simp [integerp, toBool] at h
        | int k => exact ⟨k, rfl⟩
  · intro ⟨n, h⟩; subst h; simp [integerp, toBool]

/-- ACL2 `append` — concatenate two lists. Non-cons first arg returns second. -/
def append (x y : SExpr) : SExpr :=
  match x with
  | .cons a b => .cons a (append b y)
  | _ => y

/-- ACL2 `len` — length of a list as an ACL2 integer. -/
def len (x : SExpr) : SExpr :=
  match x with
  | .cons _ b => .atom (.number (.int (toInt (len b) + 1)))
  | _ => .atom (.number (.int 0))

/-- ACL2 `true-listp` — returns t if nil-terminated cons chain, nil otherwise. -/
def trueListp (x : SExpr) : SExpr :=
  match x with
  | .cons _ b => trueListp b
  | .nil => .t
  | _ => .nil

@[simp] theorem append_nil (y : SExpr) : append .nil y = y := rfl

@[simp] theorem append_cons (a b y : SExpr) :
    append (.cons a b) y = .cons a (append b y) := rfl

@[simp] theorem append_atom (at_ : Atom) (y : SExpr) :
    append (.atom at_) y = y := rfl

@[simp] theorem len_nil : len .nil = .atom (.number (.int 0)) := rfl

@[simp] theorem len_cons (a b : SExpr) :
    len (.cons a b) = .atom (.number (.int (toInt (len b) + 1))) := rfl

@[simp] theorem trueListp_nil : trueListp .nil = .t := rfl

@[simp] theorem trueListp_cons (a b : SExpr) :
    trueListp (.cons a b) = trueListp b := rfl

/-- ACL2 `iff` — biconditional. -/
@[inline, simp] def iff (p q : SExpr) : SExpr :=
  if toBool p then
    if toBool q then .t else .nil
  else
    if toBool q then .nil else .t

/-- ACL2 `force` — identity, used as a proof hint with no logical content. -/
@[inline, simp] def force (x : SExpr) : SExpr := x

/-- ACL2 `double-rewrite` — identity, used as a proof hint. -/
@[inline, simp] def double_rewrite (x : SExpr) : SExpr := x

/-- ACL2 `evens` — every other element starting from index 0. -/
def evens (l : SExpr) : SExpr :=
  match l with
  | .cons a (.cons _ d) => .cons a (evens d)
  | .cons a _ => .cons a .nil
  | _ => .nil

/-- ACL2 `odds` — every other element starting from index 1. -/
def odds (l : SExpr) : SExpr := evens (cdr l)

@[simp] theorem iff_def (p q : SExpr) :
    iff p q = if toBool p then (if toBool q then .t else .nil)
              else (if toBool q then .nil else .t) := rfl

@[simp] theorem force_def (x : SExpr) : force x = x := rfl

@[simp] theorem double_rewrite_def (x : SExpr) : double_rewrite x = x := rfl

@[simp] theorem evens_nil : evens .nil = .nil := rfl

@[simp] theorem evens_cons_cons (a b d : SExpr) :
    evens (.cons a (.cons b d)) = .cons a (evens d) := rfl

@[simp] theorem evens_cons_nil (a : SExpr) :
    evens (.cons a .nil) = .cons a .nil := rfl

@[simp] theorem evens_cons_atom (a : SExpr) (at_ : Atom) :
    evens (.cons a (.atom at_)) = .cons a .nil := rfl

@[simp] theorem odds_def (l : SExpr) : odds l = evens (cdr l) := rfl

end Logic
end ACL2
