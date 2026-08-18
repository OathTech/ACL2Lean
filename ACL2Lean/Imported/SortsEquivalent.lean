import ACL2Lean.Imported.SortingBsortKit
import ACL2Lean.Imported.SortingQsortReading
import ACL2Lean.Imported.LiftingRel

/-! # Imported: the sorts-equivalent book — THE CAPSTONES

`MSORT-IS-ISORT`, `QSORT-IS-ISORT` and `BSORT-IS-ISORT`: the corpus's
top-level claim that the sorts agree. Each is a one-node proof in
ACL2 — a `:USE (:FUNCTIONAL-INSTANCE …)` of the equisort scope's
constrained-sorter capstone at the concrete pair — so the whole content
of the row is the functional instantiation, and until R4 wave 2g the
only thing in this repository that could discharge one was the coverage
sweep's own pre-pass. `driver_replayed%`'s `usefi` clause
(`Imported/Waypoints/Macro.lean`) is that route at the waypoint layer;
`Imported/Waypoints/SortsEquivalent.lean` carries the rows.

This module is the DECODE layer for them: each theorem's replayed
statement, read down to an equation between the two NATIVE readings.

TWO NOTES ON SHAPE, both deliberate.

* The world-fact hypotheses spell their symbols as LITERALS rather than
  naming `Imported/Sorting.lean`'s `*_sym` constants, which are
  `private` there. The literal is DEFEQ to the private constant, so the
  callee corrs accept it unchanged, and nothing is de-privatised (the
  J-2b-5 class: de-privatising renames a constant and moves every proof
  term that mentions it).
* `QSORT-IS-ISORT` decodes to `qsortOwnL`, the depth-1 dispatch-free
  reading (wave 2e), because that is the reading the mirror's `qsort`
  agree square is stated against.

SCOPE, for both: the native quantifies over `List SExpr` — the
`enc` IMAGE — while the ACL2 theorem is over ALL objects, so each is
strictly WEAKER than its replayed statement (the standing type-absorbed
doctrine). -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.Sorting

/-! ## The book's symbols, spelled locally (see the header) -/

def seInsertSym : Symbol := { package := "ACL2", name := "INSERT" }
def seIsortSym : Symbol := { package := "ACL2", name := "ISORT" }
def seMerge2Sym : Symbol := { package := "ACL2", name := "MERGE2" }
def seEvensSym : Symbol := { package := "ACL2", name := "EVENS" }
def seOddsSym : Symbol := { package := "ACL2", name := "ODDS" }
def seMsortSym : Symbol := { package := "ACL2", name := "MSORT" }
def seQsortSym : Symbol := { package := "ACL2", name := "QSORT" }
def seRelSym : Symbol := { package := "ACL2", name := "REL" }
def seFilterSym : Symbol := { package := "ACL2", name := "FILTER" }
def seAppendSym : Symbol := { package := "ACL2", name := "BINARY-APPEND" }
def seLSym : Symbol := { package := "ACL2", name := "L" }
def seFnSym : Symbol := { package := "ACL2", name := "FN" }
def seISym : Symbol := { package := "ACL2", name := "I" }
def seJSym : Symbol := { package := "ACL2", name := "J" }

abbrev seTrueListpT (x : SExpr) : SExpr := app1 "TRUE-LISTP" x

/-! ## MSORT-IS-ISORT -/

/-- The MSORT-IS-ISORT replayed-statement formula — the root Goal clause,
    exactly as the log emits it: `(EQUAL (MSORT X) (ISORT X))`. -/
def msort_is_isortFormula : SExpr := equalT (msortT xT) (isortT xT)

/-- MSORT-IS-ISORT, natively: MERGE SORT AND INSERTION SORT AGREE. -/
theorem msort_is_isort_native_of_replayed (w : World)
    (h_insert : w.defs.get? seInsertSym = some ([eS, xS], insertBody))
    (h_isort : w.defs.get? seIsortSym = some ([xS], isortBody))
    (h_m2 : w.defs.get? seMerge2Sym = some ([xS, yS], merge2Body))
    (h_evens : w.defs.get? seEvensSym = some ([seLSym], evensBody))
    (h_odds : w.defs.get? seOddsSym = some ([seLSym], oddsBody))
    (h_msort : w.defs.get? seMsortSym = some ([xS], msortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env msort_is_isortFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    msortL xs = isortL xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hms := msort_exec_corr w h_m2 h_evens h_odds h_msort h_no_consp
    h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [msortExec_enc] at hms
  have his := corr_isort_enc w h_insert h_isort h_no_consp h_no_car
    h_no_cdr h_no_cons h_no_lexorder xs e xT hx
  exact native_of_replayed_equal w e listRep (msortT xT) (isortT xT)
    (msortL xs) (isortL xs) h_no_equal hms his (hreplayed e)

/-! ## QSORT-IS-ISORT -/

/-- The QSORT-IS-ISORT replayed-statement formula — the root Goal clause,
    exactly as the log emits it: `(EQUAL (QSORT X) (ISORT X))`. -/
def qsort_is_isortFormula : SExpr := equalT (qsortT xT) (isortT xT)

/-- QSORT-IS-ISORT, natively: QUICKSORT AND INSERTION SORT AGREE (at the
    depth-1 reading `qsortOwnL`). -/
theorem qsort_is_isort_native_of_replayed (w : World)
    (h_insert : w.defs.get? seInsertSym = some ([eS, xS], insertBody))
    (h_isort : w.defs.get? seIsortSym = some ([xS], isortBody))
    (h_qs : w.defs.get? seQsortSym = some ([xS], qsortBody))
    (h_rel : w.defs.get? seRelSym
      = some ([seFnSym, seISym, seJSym], relBody))
    (h_filter : w.defs.get? seFilterSym = some ([seFnSym, xS, eS], filterBody))
    (h_app : w.defs.get? seAppendSym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env qsort_is_isortFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    qsortOwnL xs = isortL xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hqs := qsort_exec_corr w h_qs h_rel h_filter h_app h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [qsortExec_enc_own] at hqs
  have his := corr_isort_enc w h_insert h_isort h_no_consp h_no_car
    h_no_cdr h_no_cons h_no_lexorder xs e xT hx
  exact native_of_replayed_equal w e listRep (qsortT xT) (isortT xT)
    (qsortOwnL xs) (isortL xs) h_no_equal hqs his (hreplayed e)

/-! ## BSORT-IS-ISORT

The corpus's one CONDITIONAL capstone: the book states it under a
`TRUE-LISTP` hypothesis (`bsort` is admitted without a true-list guard,
so `weak-sortfn1-is-sortfn2` — not the strong twin — is what
`sorts-equivalent` functionally instantiates for it). The hypothesis is
type-absorbed here in the standing way: the native quantifies over
`List SExpr`, every `enc` image IS a true list, and the antecedent is
discharged by that fact rather than assumed.

So the decode is the UNCONDITIONAL equal-decode composed with the
generic IMPLIES PEEL (`Lifting.replayed_of_replayed_implies`) — no new
content, exactly as that transformer was extracted to allow. -/

/-- The BSORT-IS-ISORT replayed-statement formula — the root Goal clause,
    exactly as the log emits it:
    `(IMPLIES (TRUE-LISTP X) (EQUAL (BSORT X) (ISORT X)))`. -/
def bsort_is_isortFormula : SExpr :=
  impliesT (seTrueListpT xT) (equalT (bsortT xT) (isortT xT))

/-- The `(TRUE-LISTP X)` antecedent, at an ENCODED list, converges to
    `t` — the hypothesis-absorption step. The content is
    `Lifting.trueListp_enc`: every `enc` image is a true list. -/
private theorem conv_seTrueListp_enc (w : World) (e : Env)
    (h_no_tlp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (t : SExpr) (l : List SExpr)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (seTrueListpT t) = some SExpr.t := by
  have h := conv_builtin1 w e { name := "TRUE-LISTP" } t (enc l)
    (Logic.trueListp (enc l)) (by decide) h_no_tlp ht
    (callBuiltin_true_listp _)
  rwa [trueListp_enc] at h

/-- BSORT-IS-ISORT, natively: BUBBLE SORT AND INSERTION SORT AGREE. -/
theorem bsort_is_isort_native_of_replayed (w : World)
    (h_insert : w.defs.get? seInsertSym = some ([eS, xS], insertBody))
    (h_isort : w.defs.get? seIsortSym = some ([xS], isortBody))
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_bsort : w.defs.get? bsort_sym = some ([xS], bsortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (h_no_tlp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env bsort_is_isortFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    bsortL xs = isortL xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hbs := bsort_exec_corr w h_bnext h_bsort h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [bsortExec_enc] at hbs
  have his := corr_isort_enc w h_insert h_isort h_no_consp h_no_car
    h_no_cdr h_no_cons h_no_lexorder xs e xT hx
  -- the peel: the antecedent is `t` on the enc image, so the replayed
  -- implication IS the replayed equality
  have hpeel := replayed_of_replayed_implies w e (seTrueListpT xT)
    (equalT (bsortT xT) (isortT xT))
    (Logic.equal (enc (bsortL xs)) (enc (isortL xs))) h_no_implies
    (conv_seTrueListp_enc w e h_no_tlp xT xs hx)
    (conv_equalT w e (bsortT xT) (isortT xT) _ _ h_no_equal hbs his)
    (hreplayed e)
  exact native_of_replayed_equal w e listRep (bsortT xT) (isortT xT)
    (bsortL xs) (isortL xs) h_no_equal hbs his hpeel

end ACL2.Worlds.Sorting
