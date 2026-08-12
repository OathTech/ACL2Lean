import ACL2Lean.Syntax

/-! # THE DEMO'S ACL2 SOURCE — the transcribed `defun` data

**Part 1 of the demo (`docs/demo/1-tcb.md`); the trust base is this
folder.**

PURE DATA. Every constant here is an `SExpr` term or a `Symbol`: the
macroexpanded `defun` bodies of the ACL2 sorting books exactly as the
proof logs carry them (`insertBody`, `msortBody`, `qsortBody`, …), the
function symbols that name them, and the term builders those
transcriptions are spelled in. Nothing here computes, proves, or
asserts anything — it is the ACL2 side of the correspondence, written
down.

You need this file only to check ONE thing, and only if you care about
the ATTRIBUTION (that the theorems really came from ACL2's proofs of
ACL2's functions): that these transcriptions match the `.lisp` books.
They are NOT premises of the theorems — a wrong transcription can only
make a replay fail to exist. See `Statements.lean`'s trust map.

IMPORTS: the syntax core alone (`ACL2Lean.Syntax` — `SExpr`, `Symbol`,
`Atom`), pinned by `scripts/check-trust-imports.sh`.
-/

open ACL2

namespace ACL2.Lifting

/-! ## Term builders

The application/quotation vocabulary every transcription below is
spelled in. -/

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

/-- `(IF c t e)` term builder (the decode kit's own copy — `ifT` lives in
    the Replay namespace and aliasing it here would make every
    open-both consumer ambiguous). -/
abbrev appIf (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

/-- `(QUOTE NIL)`. -/
abbrev qNilT : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)

/-! ## Name-generic body SHAPES

The standard ACL2 list-recursion body shapes, parameterized by the
function NAME. `appendBody fn` / `lenBody fn` are EXACTLY the
macroexpanded bodies ACL2 emits for the two-formal append and
one-formal length defuns, so a single `decide` on any world (hand or
log-derived) instantiates the correspondence lemmas at that world's
function. -/

def xS : Symbol := { package := "ACL2", name := "X" }
def yS : Symbol := { package := "ACL2", name := "Y" }
def xT : SExpr := .atom (.symbol { name := "X" })
def yT : SExpr := .atom (.symbol { name := "Y" })
def q0 : SExpr := qInt 0
def q1 : SExpr := qInt 1

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

end ACL2.Lifting

namespace ACL2.Worlds.Perm

open ACL2.Lifting

/-! ## The perm book's defuns, exactly as the log-derived world carries
them -/

def aS : Symbol := { package := "ACL2", name := "A" }
def eS : Symbol := { package := "ACL2", name := "E" }
def xS : Symbol := { package := "ACL2", name := "X" }
def yS : Symbol := { package := "ACL2", name := "Y" }

def aT : SExpr := .atom (.symbol { name := "A" })
def eT : SExpr := .atom (.symbol { name := "E" })
def xT : SExpr := .atom (.symbol { name := "X" })
def yT : SExpr := .atom (.symbol { name := "Y" })

def qT : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)
def qNil : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.nil .nil)

abbrev membT (a x : SExpr) : SExpr := app2 "MEMB" a x
abbrev rmT (e x : SExpr) : SExpr := app2 "RM" e x
abbrev permT (x y : SExpr) : SExpr := app2 "PERM" x y
abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

/-- `(defun rm (e x) …)`, macroexpanded. -/
def rmBody : SExpr :=
  ifT (conspT xT)
    (ifT (equalT eT (carT xT)) (cdrT xT) (consT (carT xT) (rmT eT (cdrT xT))))
    qNil

/-- `(defun memb (a x) …)`, macroexpanded. -/
def membBody : SExpr :=
  ifT (conspT xT)
    (ifT (equalT aT (carT xT)) qT (membT aT (cdrT xT)))
    qNil

/-- `(defun perm (x y) …)`, macroexpanded. -/
def permBody : SExpr :=
  ifT (conspT xT)
    (ifT (membT (carT xT) yT) (permT (cdrT xT) (rmT (carT xT) yT)) qNil)
    (ifT (conspT yT) qNil qT)

end ACL2.Worlds.Perm

namespace ACL2.Worlds.Sorting

open ACL2.Lifting ACL2.Worlds.Perm

/-! ## ORDEREDP: the chain2 instance -/

/-- `(orderedp x)`. -/
abbrev orderedpT (x : SExpr) : SExpr := app1 "ORDEREDP" x

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

The book's `defun` bodies as `SExpr` terms. Their NATIVE readings
(`insertL` / `isortL`) are in `TCB.lean`; the correspondence between
the two is `Imported/Sorting/Iso.lean`'s two-stage lift
(docs/plans/2026-07-06_two-stage-lift.md); the book's one assumption
(`tp:INSERT`) is `Assumptions.lean`'s `dis_insert_tp`. -/

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

def zS : Symbol := { package := "ACL2", name := "Z" }

def zT : SExpr := .atom (.symbol { name := "Z" })

def cS : Symbol := { package := "ACL2", name := "C" }

def cT : SExpr := .atom (.symbol { name := "C" })

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

def qSym (s : String) : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.symbol { name := s })) .nil)

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

/-! ## PERM-COUNTER-EXAMPLE — the perm-lane vocabulary of the qsort
flagship: ACL2's witness function, which returns the one element at
which two lists disagree. Its native reading `pceL` is in `TCB.lean`
(the book's own decodes are `Imported/SortingConvertPerm.lean`); the
`rule:CONVERT-PERM-TO-HOW-MANY` assumption is `Assumptions.lean`'s
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

The body constant; its native reading `bnextL` is in `TCB.lean`.
(`bnext`'s recursion carries a CONS-argument call site,
`(BNEXT (CONS (CAR X) (CDR (CDR X))))`, which is beyond
`derive_exec%`'s reach — so `Imported/Sorting/Iso.lean` takes the hand
route, on the `msortExec` precedent.) -/

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

/-! ## The bsort book: the HOW-MANY-SMALLER / BNEXT-SIZE measure kit -/

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

abbrev bnextSizeT (x : SExpr) : SExpr := app1 "BNEXT-SIZE" x

/-- `(defun bnext-size (x) …)`, macroexpanded — the number of
    out-of-order pairs, summed down the list. -/
def bnextSizeBody : SExpr :=
  appIf (conspT xT)
    (plusT (howManySmallerT (carT xT) (cdrT xT)) (bnextSizeT (cdrT xT)))
    (qInt 0)

def bnext_size_sym : Symbol := { package := "ACL2", name := "BNEXT-SIZE" }

/-! ## The equisort scopes' `:LOCAL-WITNESS` defuns

The `SORTFN1`/`SSORTFN1` insertion-sort clones (they differ from the
isort book's `INSERT`/`ISORT` only in their self-call names),
transcribed from the emitted `(:DEFUN …)` events (equisort.proof-log
lines 123/127/13674/13678). -/

private def app3 (n : String) (a b c : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := n }))
    (.cons a (.cons b (.cons c .nil)))

def sortfn1_insert_sym : Symbol :=
  { package := "ACL2", name := "SORTFN1-INSERT" }
def sortfn1_sym : Symbol :=
  { package := "ACL2", name := "SORTFN1" }
def ssortfn1_insert_sym : Symbol :=
  { package := "ACL2", name := "SSORTFN1-INSERT" }
def ssortfn1_sym : Symbol :=
  { package := "ACL2", name := "SSORTFN1" }

/-- `(defun sortfn1-insert (e x) …)` — the emitted witness body. -/
def sortfn1InsertBody : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app3 "IF" (app2 "LEXORDER" eT (app1 "CAR" xT))
      (app2 "CONS" eT xT)
      (app2 "CONS" (app1 "CAR" xT)
        (app2 "SORTFN1-INSERT" eT (app1 "CDR" xT))))
    (app2 "CONS" eT xT)

/-- `(defun sortfn1 (x) …)` — the emitted witness body. -/
def sortfn1Body : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app2 "SORTFN1-INSERT" (app1 "CAR" xT)
      (app1 "SORTFN1" (app1 "CDR" xT)))
    qNil

/-- `(defun ssortfn1-insert (e x) …)` — the emitted witness body. -/
def ssortfn1InsertBody : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app3 "IF" (app2 "LEXORDER" eT (app1 "CAR" xT))
      (app2 "CONS" eT xT)
      (app2 "CONS" (app1 "CAR" xT)
        (app2 "SSORTFN1-INSERT" eT (app1 "CDR" xT))))
    (app2 "CONS" eT xT)

/-- `(defun ssortfn1 (x) …)` — the emitted witness body. -/
def ssortfn1Body : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app2 "SSORTFN1-INSERT" (app1 "CAR" xT)
      (app1 "SSORTFN1" (app1 "CDR" xT)))
    qNil

end ACL2.Worlds.Sorting
