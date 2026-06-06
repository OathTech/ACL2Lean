import ACL2Lean.Logic
import ACL2Lean.Lexorder
import ACL2Lean.Count

namespace ACL2

open Logic

/-! # ACL2 Term Ordering

Port of ACL2's `term-order`, `merge-term-order`, and `merge-sort-term-order`
from `type-set-b.lisp`, `linear-a.lisp`, and `rewrite.lisp`.

`term-order` is a total ordering on pseudo-terms. When called with
`invisible-fns-table = nil` (our case), it:
1. Compares variable occurrence counts
2. Breaks ties with function symbol counts
3. Breaks ties with pseudo-function counts (size of quoted constants)
4. Falls back to `lexorder`
-/

private def fnCountEvgMaxVal : Nat := 200000
private def fnCountEvgMaxCalls : Nat := 1000

/-- Count the "size" of an integer for fn-count-evg. -/
private def fnCountEvgInt (n : Int) (acc : Nat) : Nat :=
  if n < 0 then
    let absN := (-n).toNat
    if absN >= fnCountEvgMaxVal then fnCountEvgMaxVal
    else Nat.min fnCountEvgMaxVal (acc + 2 + absN)
  else
    let natN := n.toNat
    if natN >= fnCountEvgMaxVal then fnCountEvgMaxVal
    else Nat.min fnCountEvgMaxVal (acc + 1 + natN)

/-- Count the "size" of an atom for fn-count-evg. -/
private def fnCountEvgAtom (a : Atom) (acc : Nat) : Nat :=
  match a with
  | .symbol s =>
    if s.name.isEmpty then Nat.min fnCountEvgMaxVal (acc + 8)
    else
      let len := s.name.length
      if len >= fnCountEvgMaxVal then fnCountEvgMaxVal
      else Nat.min fnCountEvgMaxVal (acc + 2 + 2 * len)
  | .number (.int n) => fnCountEvgInt n acc
  | .number (.rational n d) =>
    fnCountEvgInt n (fnCountEvgInt (Int.ofNat d) (acc + 1))
  | .number (.decimal _ _) => Nat.min fnCountEvgMaxVal (acc + 1)
  | .string s =>
    let len := s.length
    if len >= fnCountEvgMaxVal then fnCountEvgMaxVal
    else Nat.min fnCountEvgMaxVal (acc + 1 + 2 * len)
  | .keyword k =>
    let len := k.length
    if len >= fnCountEvgMaxVal then fnCountEvgMaxVal
    else Nat.min fnCountEvgMaxVal (acc + 2 + 2 * len)

/-- Port of ACL2's `fn-count-evg-rec`: count the "size" of a quoted constant
    for term ordering. -/
def fnCountEvgRec (evg : SExpr) (acc calls : Nat) : Nat :=
  if calls >= fnCountEvgMaxCalls || acc >= fnCountEvgMaxVal then fnCountEvgMaxVal
  else match evg with
  | .nil => Nat.min fnCountEvgMaxVal (acc + 8)
  | .atom a => fnCountEvgAtom a acc
  | .cons a d =>
    let acc' := fnCountEvgRec a (acc + 1) (calls + 1)
    fnCountEvgRec d acc' (calls + 2)
termination_by evg.acl2Count

/-- Port of ACL2's `fn-count-evg`: count size starting from 0. -/
def fnCountEvg (evg : SExpr) : Nat := fnCountEvgRec evg 0 0

/-- Port of ACL2's `var-fn-count-1` with `invisible-fns-table = nil`.
    When `flg = false`: processes a single pseudo-term.
    When `flg = true`: processes a list of pseudo-terms.

    In ACL2's pseudo-term representation:
    - An atom is a variable
    - `(QUOTE v)` is a quoted constant
    - `(f arg1 arg2 ...)` is a function application -/
private def varFnCount1 (flg : Bool) (x : SExpr) (vc fc pfc : Nat)
    : Nat × Nat × Nat :=
  if flg then
    -- List mode
    match x with
    | .cons hd tl =>
      let (vc', fc', pfc') := varFnCount1 false hd vc fc pfc
      varFnCount1 true tl vc' fc' pfc'
    | _ => (vc, fc, pfc)
  else
    -- Term mode
    match x with
    | .nil => (vc + 1, fc, pfc)
    | .atom _ => (vc + 1, fc, pfc)
    | .cons (.atom (.symbol s)) rest =>
      if s.isNamed "quote" then
        match rest with
        | .cons v .nil => (vc, fc, pfc + fnCountEvg v)
        | _ => (vc, fc, pfc)
      else
        varFnCount1 true rest vc (fc + 1) pfc
    | .cons _ rest =>
      varFnCount1 true rest vc (fc + 1) pfc
termination_by x.acl2Count
decreasing_by all_goals (simp_all [SExpr.acl2Count]; try omega)

/-- Port of ACL2's `term-order`: total ordering on S-expressions treated as
    pseudo-terms. -/
def term_order (term1 term2 : SExpr) : SExpr :=
  let (vc1, fc1, pfc1) := varFnCount1 false term1 0 0 0
  let (vc2, fc2, pfc2) := varFnCount1 false term2 0 0 0
  if vc1 < vc2 then .t
  else if vc1 > vc2 then .nil
  else if fc1 < fc2 then .t
  else if fc1 > fc2 then .nil
  else if pfc1 < pfc2 then .t
  else if pfc1 > pfc2 then .nil
  else lexorder term1 term2

/-- Port of ACL2's `merge-term-order`: merge two term-ordered lists.
    ACL2: `(cond ((endp l1) l2) ((endp l2) l1) ...)` -/
def merge_term_order (l1 l2 : SExpr) : SExpr :=
  match l1, l2 with
  | .cons a1 r1, .cons a2 r2 =>
    if toBool (term_order a1 a2) then
      .cons a1 (merge_term_order r1 (.cons a2 r2))
    else
      .cons a2 (merge_term_order (.cons a1 r1) r2)
  | .cons _ _, _ => l1 -- l1 is cons, l2 is endp → return l1
  | _, _ => l2 -- l1 is endp → return l2
termination_by l1.acl2Count + l2.acl2Count
decreasing_by all_goals simp [SExpr.acl2Count]; omega

/-- Port of ACL2's `merge-sort-term-order`: sort a list by term-order. -/
def merge_sort_term_order (l : SExpr) : SExpr :=
  match l with
  | .cons a (.cons b d) =>
    merge_term_order
      (merge_sort_term_order (evens (.cons a (.cons b d))))
      (merge_sort_term_order (odds (.cons a (.cons b d))))
  | _ => l
termination_by l.acl2Count
decreasing_by
  all_goals simp only [SExpr.acl2Count, evens, odds, cdr]
  · have := acl2Count_evens_le d; omega
  · have := acl2Count_evens_le (.cons b d); simp [SExpr.acl2Count] at this; omega

end ACL2
