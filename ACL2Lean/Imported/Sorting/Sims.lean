import ACL2Lean.Imported.Lifting
import ACL2Lean.Imported.Perm
import ACL2Lean.Lexorder

/-! # The sorting books — LAYER 1 of 4: THE DEFINITIONS

**Read this file to know what the imported theorems are ABOUT.**

Everything here is plain Lean over `SExpr` (ACL2's value universe):

* the NATIVE READINGS — `isortL`, `msortL`, `qsortL`, `merge2L`,
  `evensL`, `filterL`, `insertL`, `bnextL`, `relL`, `allRelL`,
  `lexorderB`, `orderedpRec` — ordinary recursive functions, no
  evaluator anywhere in sight;
* the P2 MEASURE lemmas those definitions terminate by;
* the ACL2 SYMBOL/BODY constants (`insertBody`, `msortBody`, …) — the
  verbatim `defun` bodies as `SExpr` terms, and the term builders that
  spell the books' formulas.

Nothing in this file mentions the replay: no proof logs, no clause
trees, no `driver_replayed%`. `scripts/check-trust-imports.sh` (in
`just ci`) keeps it that way — see that script's header for the exact,
honest statement of what it does and does not check (the encoders in
`Imported/Lifting.lean` do transitively pull the evaluation lemmas
today; that is a known limitation, not a claim made here).

Layer map: **Sims** → `Iso` (correspondence) → `Decode` (transports
from replayed statements) → `Debt` (the assumed facts). The layering is
the trust story; `Imported/Sorting.lean` is a facade re-exporting all
of it, so `import ACL2Lean.Imported.Sorting` keeps working unchanged.
-/

open ACL2 ACL2.Lifting ACL2.Worlds.Perm

namespace ACL2.Worlds.Sorting


/-! ## The LEXORDER Bool kit

`lexorder` (the trusted-core primitive, Lexorder.lean) is two-valued;
`lexorderB` is its Bool reading, and the bridge lets the chain2
schematic consume LEXORDER as its comparison. -/

theorem lexorder_t_or_nil (x y : SExpr) :
    lexorder x y = SExpr.t ∨ lexorder x y = SExpr.nil := by
  fun_induction lexorder x y <;> first | assumption | simp

/-- The Bool reading of the two-valued `lexorder`. -/
def lexorderB (x y : SExpr) : Bool := lexorder x y == SExpr.t

/-- The chain2 fold IS Mathlib's `List.IsChain` — the fully idiomatic
    reading of the ORDEREDP-shaped recognizers. -/
theorem chain2Rec_iff_isChain (p : SExpr → SExpr → Bool) :
    ∀ xs : List SExpr,
      chain2Rec p xs = true ↔ xs.IsChain (fun a b => p a b = true)
  | [] => by simp [chain2Rec]
  | [_] => by simp [chain2Rec]
  | a :: b :: t => by
    rw [show chain2Rec p (a :: b :: t)
          = (p a b && chain2Rec p (b :: t)) from rfl,
        Bool.and_eq_true, chain2Rec_iff_isChain p (b :: t),
        List.isChain_cons_cons]

/-! ## ORDEREDP: the chain2 instance -/

/-- `(orderedp x)`. -/
abbrev orderedpT (x : SExpr) : SExpr := app1 "ORDEREDP" x

/-- The native reading of ORDEREDP: every adjacent pair is
    lexorder-related. -/
abbrev orderedpRec (xs : List SExpr) : Bool := chain2Rec lexorderB xs

/-! ## The ordered-perms book: symbol/term constants -/

def aS : Symbol := { package := "ACL2", name := "A" }

def eS : Symbol := { package := "ACL2", name := "E" }

def aT : SExpr := .atom (.symbol { name := "A" })

def eT : SExpr := .atom (.symbol { name := "E" })

/-! ## Shared term builders: `if`, quoted `nil` -/

abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

def qNil : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.nil .nil)

/-! ## The isort book: `insert` / `isort`

The book's `defun` bodies as `SExpr` terms, and their NATIVE readings
`insertL` / `isortL` — ordinary Lean recursion, nothing else. The
correspondence between the two is `Iso.lean`'s two-stage lift
(docs/plans/2026-07-06_two-stage-lift.md); the book's one assumption
(`tp:INSERT`) is `Debt.lean`'s `dis_insert_tp`. -/

def xS : Symbol := { package := "ACL2", name := "X" }

def xT : SExpr := .atom (.symbol { name := "X" })

abbrev insertT (e x : SExpr) : SExpr := app2 "INSERT" e x

abbrev isortT (x : SExpr) : SExpr := app1 "ISORT" x

abbrev lexT (a b : SExpr) : SExpr := app2 "LEXORDER" a b

/-- `(defun insert (e x) …)`, macroexpanded — exactly as the sorting
    books' logs carry it. -/
def insertBody : SExpr :=
  ifT (conspT xT)
    (ifT (lexT eT (carT xT))
      (consT eT xT)
      (consT (carT xT) (insertT eT (cdrT xT))))
    (consT eT xT)

/-- `(defun isort (x) …)`, macroexpanded. -/
def isortBody : SExpr :=
  ifT (conspT xT) (insertT (carT xT) (isortT (cdrT xT))) qNil

def insert_sym : Symbol := { package := "ACL2", name := "INSERT" }

def isort_sym : Symbol := { package := "ACL2", name := "ISORT" }

/-- `insert`'s native reading: ordered insertion by `lexorderB`. -/
def insertL (e : SExpr) : List SExpr → List SExpr
  | [] => [e]
  | a :: t => bif lexorderB e a then e :: a :: t else a :: insertL e t

/-- `isort`'s native reading: insertion sort by `lexorderB`. -/
def isortL : List SExpr → List SExpr
  | [] => []
  | a :: t => insertL a (isortL t)

/-! ## Ground-zero rule vocabulary

The stored ground-zero rewrite rules (`(:GROUND-ZERO-RULES …)`) are
cited as `rule:` conditions by the sorting rows; their world-parametric
statements live in `Imported/GzPrelude.lean` (the ratified D5
carve-out). Only the term builder they need sits here. -/

abbrev notT (a : SExpr) : SExpr := app1 "NOT" a

/-! ## EQUAL-CONS -/

def bS : Symbol := { package := "ACL2", name := "B" }

def bT : SExpr := .atom (.symbol { name := "B" })

/-! ## ORDERED-PERMS — the book's capstone (for lexorder-sorted lists,
    equality IS permutation-equivalence): its formula's term builders.
    The theorem's decode is `Decode.lean`. -/

def permT' (x y : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "PERM" })) (.cons x (.cons y .nil))

def trueListpT (x : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons x .nil)

/-! ## Arithmetic rule vocabulary

The variable symbols the arithmetic-3 commutativity/associativity family
and the two if-lifting rules use (X/Y/Z, and A/B/C in the if-lifting
rules), per the stored specs. The rules themselves are world-parametric
value-level facts in `Imported/GzPrelude.lean`. -/

def yS : Symbol := { package := "ACL2", name := "Y" }

def yT : SExpr := .atom (.symbol { name := "Y" })

private def zS : Symbol := { package := "ACL2", name := "Z" }

private def zT : SExpr := .atom (.symbol { name := "Z" })

private def cS : Symbol := { package := "ACL2", name := "C" }

private def cT : SExpr := .atom (.symbol { name := "C" })

/-! ## `how-many`: the ACL2 body constants -/

abbrev howManyT (e x : SExpr) : SExpr := app2 "HOW-MANY" e x

def q1 : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.number (.int 1))) .nil)

def q0 : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.number (.int 0))) .nil)

def int1 : SExpr := .atom (.number (.int 1))

/-- `(defun how-many (e x) …)`, macroexpanded. -/
def howManyBody : SExpr :=
  ifT (conspT xT)
    (ifT (equalT eT (carT xT))
      (plusT q1 (howManyT eT (cdrT xT)))
      (howManyT eT (cdrT xT)))
    q0

def how_many_sym : Symbol := { package := "ACL2", name := "HOW-MANY" }

/-! ## The qsort book: HOW-MANY-APPEND / CAR-APPEND -/

abbrev appendT (a b : SExpr) : SExpr := app2 "BINARY-APPEND" a b

/-! ## The REL / ALL-REL kit (qsort's comparison dispatch) -/

def fnS : Symbol := { package := "ACL2", name := "FN" }

def fnT : SExpr := .atom (.symbol { name := "FN" })

def iS : Symbol := { package := "ACL2", name := "I" }

def iT : SExpr := .atom (.symbol { name := "I" })

def jS : Symbol := { package := "ACL2", name := "J" }

def jT : SExpr := .atom (.symbol { name := "J" })

def dS : Symbol := { package := "ACL2", name := "D" }

def dT : SExpr := .atom (.symbol { name := "D" })

def xEquivS : Symbol := { package := "ACL2", name := "X-EQUIV" }

def xEquivT : SExpr := .atom (.symbol { name := "X-EQUIV" })

def symV (s : String) : SExpr := .atom (.symbol { name := s })

def qSym (s : String) : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons (symV s) .nil)

def qT' : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)

abbrev relT (f i j : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "REL" }))
    (.cons f (.cons i (.cons j .nil)))

abbrev allRelT (f x e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "ALL-REL" }))
    (.cons f (.cons x (.cons e .nil)))

/-- `(defun rel (fn i j) …)` — the 4-way comparison dispatch,
    macroexpanded. -/
def relBody : SExpr :=
  ifT (equalT fnT (qSym "LT"))
    (ifT (lexT iT jT) (ifT (equalT iT jT) qNil qT') qNil)
    (ifT (equalT fnT (qSym "LTE"))
      (lexT iT jT)
      (ifT (equalT fnT (qSym "GT"))
        (ifT (lexT jT iT) (ifT (equalT iT jT) qNil qT') qNil)
        (lexT jT iT)))

/-- `(defun all-rel (fn x e) …)`, macroexpanded. -/
def allRelBody : SExpr :=
  ifT (conspT xT)
    (ifT (relT fnT (carT xT) eT) (allRelT fnT (cdrT xT) eT) qNil)
    qT'

def rel_sym : Symbol := { package := "ACL2", name := "REL" }

def all_rel_sym : Symbol := { package := "ACL2", name := "ALL-REL" }

/-- The NATIVE reading of one REL verdict — an ordinary Lean match on the
    four comparison modes, in `lexorderB`/`==` vocabulary only (the mirror
    criterion: no exec function in a mirror statement). -/
def relL (fv a e : SExpr) : Bool :=
  if fv == symV "LT" then lexorderB a e && !(a == e)
  else if fv == symV "LTE" then lexorderB a e
  else if fv == symV "GT" then lexorderB e a && !(a == e)
  else lexorderB e a

/-- The native reading of ALL-REL: every element is `relL`-related to
    `ev`. -/
def allRelL (fv ev : SExpr) (xs : List SExpr) : Bool :=
  xs.all (fun a => relL fv a ev)

/-! ## The FILTER kit -/

abbrev filterT (f x e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "FILTER" }))
    (.cons f (.cons x (.cons e .nil)))

/-- `(defun filter (fn x e) …)`, macroexpanded. -/
def filterBody : SExpr :=
  ifT (conspT xT)
    (ifT (relT fnT (carT xT) eT)
      (consT (carT xT) (filterT fnT (cdrT xT) eT))
      (filterT fnT (cdrT xT) eT))
    qNil

def filter_sym : Symbol := { package := "ACL2", name := "FILTER" }

/-- The native reading of FILTER: `List.filter` by the `relL` verdict. -/
def filterL (fv ev : SExpr) (xs : List SExpr) : List SExpr :=
  xs.filter (fun a => relL fv a ev)

/-! ## The concrete comparison modes (native vocabulary for the FILTER
rows: the quoted mode symbols specialize `relL` to plain `lexorderB`
combinations). -/

/-- Strict lexorder: `≤` and not equal. -/
def lexLtB (a e : SExpr) : Bool := lexorderB a e && !(a == e)

theorem relL_LT (a e : SExpr) : relL (symV "LT") a e = lexLtB a e := by
  rw [relL, if_pos (by decide)]; rfl

theorem relL_LTE (a e : SExpr) : relL (symV "LTE") a e = lexorderB a e := by
  rw [relL, if_neg (by decide), if_pos (by decide)]

theorem relL_GTE (a e : SExpr) : relL (symV "GTE") a e = lexorderB e a := by
  rw [relL, if_neg (by decide), if_neg (by decide), if_neg (by decide)]

/-! ## ORDEREDP-APPEND -/

def append_sym : Symbol := { package := "ACL2", name := "BINARY-APPEND" }

abbrev iffT (a b : SExpr) : SExpr := app2 "IFF" a b

/-! ## The msort book: `merge2` / `evens` / `odds` / `msort` -/

abbrev merge2T (x y : SExpr) : SExpr := app2 "MERGE2" x y

abbrev evensT (x : SExpr) : SExpr := app1 "EVENS" x

abbrev oddsT (x : SExpr) : SExpr := app1 "ODDS" x

abbrev msortT (x : SExpr) : SExpr := app1 "MSORT" x

def lS : Symbol := { package := "ACL2", name := "L" }

def lT : SExpr := .atom (.symbol { name := "L" })

/-- `(defun merge2 (x y) …)`, macroexpanded. -/
def merge2Body : SExpr :=
  ifT (conspT xT)
    (ifT (conspT yT)
      (ifT (lexT (carT xT) (carT yT))
        (consT (carT xT) (merge2T (cdrT xT) yT))
        (consT (carT yT) (merge2T xT (cdrT yT))))
      xT)
    yT

/-- `(defun evens (l) …)`, macroexpanded. -/
def evensBody : SExpr :=
  ifT (conspT lT) (consT (carT lT) (evensT (cdrT (cdrT lT)))) qNil

/-- `(defun odds (l) …)` — `(EVENS (CDR L))`. -/
def oddsBody : SExpr := evensT (cdrT lT)

/-- `(defun msort (x) …)`, macroexpanded. -/
def msortBody : SExpr :=
  ifT (conspT xT)
    (ifT (conspT (cdrT xT))
      (merge2T (msortT (evensT xT)) (msortT (oddsT xT)))
      (consT (carT xT) qNil))
    qNil

def merge2_sym : Symbol := { package := "ACL2", name := "MERGE2" }

def evens_sym : Symbol := { package := "ACL2", name := "EVENS" }

def odds_sym : Symbol := { package := "ACL2", name := "ODDS" }

def msort_sym : Symbol := { package := "ACL2", name := "MSORT" }

/-- The native merge: Lean's ordinary two-list merge by `lexorderB`. -/
def merge2L : List SExpr → List SExpr → List SExpr
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | a :: xs, b :: ys =>
    bif lexorderB a b then a :: merge2L xs (b :: ys)
    else b :: merge2L (a :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- The native evens: every other element, starting at the head. -/
def evensL : List SExpr → List SExpr
  | [] => []
  | a :: t => a :: evensL t.tail
termination_by l => l.length
decreasing_by
  cases t with
  | nil => simp
  | cons b t' => simp

/-- The evens split halves the length (rounding up). -/
theorem evensL_length : ∀ l : List SExpr,
    (evensL l).length = (l.length + 1) / 2
  | [] => by simp [evensL]
  | [_] => by simp [evensL]
  | _ :: _ :: t => by
    have := evensL_length t
    simp only [evensL, List.tail_cons, List.length_cons, this]
    omega
termination_by l => l.length

/-- The native merge sort. -/
def msortL (xs : List SExpr) : List SExpr :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    merge2L (msortL (evensL (a :: b :: t))) (msortL (evensL (b :: t)))
termination_by xs.length
decreasing_by
  · rw [evensL_length]; simp; omega
  · rw [evensL_length]; simp; omega

/-! ## The ordinal kit (`total:O<`): O-FINP / O-FIRST-EXPT /
O-FIRST-COEFF / O-RST / O< — the ground-zero ordinal fns the qsort
admissions cite. -/

abbrev oFinpT (x : SExpr) : SExpr := app1 "O-FINP" x

abbrev oFirstExptT (x : SExpr) : SExpr := app1 "O-FIRST-EXPT" x

abbrev oFirstCoeffT (x : SExpr) : SExpr := app1 "O-FIRST-COEFF" x

abbrev oRstT (x : SExpr) : SExpr := app1 "O-RST" x

abbrev oLtT (x y : SExpr) : SExpr := app2 "O<" x y

abbrev ltT (a b : SExpr) : SExpr := app2 "<" a b

def oFinpBody : SExpr := ifT (conspT xT) qNil qT'

def oFirstExptBody : SExpr := ifT (oFinpT xT) q0 (carT (carT xT))

def oFirstCoeffBody : SExpr := ifT (oFinpT xT) xT (cdrT (carT xT))

def oRstBody : SExpr := cdrT xT

def oLtBody : SExpr :=
  ifT (oFinpT xT)
    (ifT (oFinpT yT) (ltT xT yT) qT')
    (ifT (oFinpT yT) qNil
      (ifT (equalT (oFirstExptT xT) (oFirstExptT yT))
        (ifT (equalT (oFirstCoeffT xT) (oFirstCoeffT yT))
          (oLtT (oRstT xT) (oRstT yT))
          (ltT (oFirstCoeffT xT) (oFirstCoeffT yT)))
        (oLtT (oFirstExptT xT) (oFirstExptT yT))))

def o_finp_sym : Symbol := { package := "ACL2", name := "O-FINP" }

def o_fe_sym : Symbol := { package := "ACL2", name := "O-FIRST-EXPT" }

def o_fc_sym : Symbol :=
  { package := "ACL2", name := "O-FIRST-COEFF" }

def o_rst_sym : Symbol := { package := "ACL2", name := "O-RST" }

def o_lt_sym : Symbol := { package := "ACL2", name := "O<" }

/-! ## The `acl2-count` kit (`tp:ACL2-COUNT`): INTEGER-ABS / LENGTH /
ACL2-COUNT. The COMPLEX-RATIONALP branch is DEAD in the model (the
predicate is constantly nil — complexes are unrepresentable), so its
recursion is discharged by contradiction. -/

abbrev integerAbsT (x : SExpr) : SExpr := app1 "INTEGER-ABS" x

abbrev lengthT (x : SExpr) : SExpr := app1 "LENGTH" x

abbrev acl2CountT (x : SExpr) : SExpr := app1 "ACL2-COUNT" x

def integerAbsBody : SExpr :=
  ifT (app1 "INTEGERP" xT)
    (ifT (ltT xT q0) (app1 "UNARY--" xT) xT)
    q0

def lengthBody : SExpr :=
  ifT (app1 "STRINGP" xT)
    (app1 "LEN" (app2 "COERCE" xT (qSym "LIST")))
    (app1 "LEN" xT)

def acl2CountBody : SExpr :=
  ifT (conspT xT)
    (plusT q1 (plusT (acl2CountT (carT xT)) (acl2CountT (cdrT xT))))
    (ifT (app1 "RATIONALP" xT)
      (ifT (app1 "INTEGERP" xT)
        (integerAbsT xT)
        (plusT (integerAbsT (app1 "NUMERATOR" xT))
          (app1 "DENOMINATOR" xT)))
      (ifT (app1 "COMPLEX-RATIONALP" xT)
        (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
          (acl2CountT (app1 "IMAGPART" xT))))
        (ifT (app1 "STRINGP" xT) (lengthT xT) q0)))

def integer_abs_sym : Symbol :=
  { package := "ACL2", name := "INTEGER-ABS" }

def length_sym : Symbol := { package := "ACL2", name := "LENGTH" }

def acl2_count_sym : Symbol :=
  { package := "ACL2", name := "ACL2-COUNT" }

/-! ## The qsort book: `qsort` itself -/

abbrev qsortT (x : SExpr) : SExpr := app1 "QSORT" x

/-- `(defun qsort (x) …)`, macroexpanded. -/
def qsortBody : SExpr :=
  ifT (conspT xT)
    (ifT (conspT (cdrT xT))
      (appendT
        (qsortT (filterT (qSym "LT") (cdrT xT) (carT xT)))
        (consT (carT xT)
          (qsortT (filterT (qSym "GTE") (cdrT xT) (carT xT)))))
      (consT (carT xT) qNil))
    qNil

def qsort_sym : Symbol := { package := "ACL2", name := "QSORT" }

/-- The native quicksort. -/
def qsortL (xs : List SExpr) : List SExpr :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    qsortL ((b :: t).filter (fun c => relL (symV "LT") c a))
      ++ a :: qsortL ((b :: t).filter (fun c => relL (symV "GTE") c a))
termination_by xs.length
decreasing_by
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-! ## PERM-COUNTER-EXAMPLE — the perm-lane vocabulary of the qsort
flagship: ACL2's witness function, which returns the one element at
which two lists disagree. Its native reading `pceL` is in
`Imported/SortingConvertPerm.lean` (with the book's own decodes); the
`rule:CONVERT-PERM-TO-HOW-MANY` assumption is `Debt.lean`'s
`dis_convert_perm`. -/

abbrev pceT (x y : SExpr) : SExpr := app2 "PERM-COUNTER-EXAMPLE" x y

/-- `(defun perm-counter-example (x y) …)`, macroexpanded. -/
def pceBody : SExpr :=
  ifT (conspT xT)
    (ifT (membT (carT xT) yT)
      (pceT (cdrT xT) (rmT (carT xT) yT))
      (carT xT))
    (carT yT)

def pce_sym : Symbol :=
  { package := "ACL2", name := "PERM-COUNTER-EXAMPLE" }

def orderedp_sym : Symbol := { package := "ACL2", name := "ORDEREDP" }

/-! ## The bsort book: BNEXT — the bubble pass

The body constant and its native reading `bnextL`. (`bnext`'s recursion
carries a CONS-argument call site,
`(BNEXT (CONS (CAR X) (CDR (CDR X))))`, which is beyond `derive_exec%`'s
reach — so `Iso.lean` takes the hand route, on the `msortExec`
precedent.) -/

/-- `(defun bnext (x) …)`, macroexpanded — the bubble pass: adjacent
    in-order heads keep, out-of-order heads swap; recursion continues past
    the (possibly swapped) head. -/
def bnextBody : SExpr :=
  ifT (conspT xT)
    (ifT (conspT (cdrT xT))
      (ifT (lexT (carT xT) (carT (cdrT xT)))
        (consT (carT xT) (app1 "BNEXT" (cdrT xT)))
        (consT (carT (cdrT xT))
          (app1 "BNEXT" (consT (carT xT) (cdrT (cdrT xT))))))
      xT)
    xT

def bnext_sym : Symbol := { package := "ACL2", name := "BNEXT" }

/-- The NATIVE bubble pass over Lean lists — self-contained (mirror
    criterion: `lexorderB` only, no evaluator vocabulary). -/
def bnextL : List SExpr → List SExpr
  | [] => []
  | [x] => [x]
  | x1 :: x2 :: rest =>
    bif lexorderB x1 x2 then x1 :: bnextL (x2 :: rest)
    else x2 :: bnextL (x1 :: rest)
termination_by l => l.length

end ACL2.Worlds.Sorting
