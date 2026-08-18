/-
  NEGATIVE PROBES for the relational decode combinators
  (`ACL2Lean/Imported/LiftingRel.lean`).

  WHAT THEY PIN: each combinator names the SHAPE of the replayed
  statement it decodes in its own type, so handing it a replayed fact of
  a DIFFERENT shape is an elaboration error at the seam rather than a
  silently-succeeding decode. Below, a `<` decode is handed an
  EQUAL-shaped replayed statement, a `≤` decode is handed the un-negated
  `<` shape, and the conjunction decode is handed a bare equality; all
  three must fail.

  THREAT MODEL — a SPEEDBUMP against the honest mistake (citing the wrong
  replayed constant when wiring a new waypoint), never a barrier against
  circumvention. Since the check IS the type, it cannot rot into
  something subtler; DO NOT HARDEN IT — if it ever becomes fragile,
  delete it.

  These probes declare nothing and prove nothing, so they cost no
  `sorryAx`.
-/
import ACL2Lean.Imported.LiftingRel

open ACL2 ACL2.Replay ACL2.Lifting

namespace ACL2.Tests.LiftingRelProbes

/- PROBE 1 — the `<` decode refuses an EQUAL-shaped replayed statement. -/

/--
error: Application type mismatch: The argument
  hbad
has type
  EvTrue w e (equalT a b)
but is expected to have type
  EvTrue w e (ltT a b)
in the application
  native_of_replayed_lt w e a b x y h_no_lt hL hR hbad
-/
#guard_msgs (whitespace := lax) in
example (w : World) (e : Env) (a b : SExpr) (x y : Int)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (hL : Conv w e a (intRep.enc x)) (hR : Conv w e b (intRep.enc y))
    (hbad : EvTrue w e (equalT a b)) : x < y :=
  native_of_replayed_lt w e a b x y h_no_lt hL hR hbad

/- PROBE 2 — the `≤` decode refuses the UN-NEGATED `<` shape (ACL2's
   `<=` macroexpands to `(NOT (< …))`; dropping the `NOT` would decode a
   strict comparison as a non-strict one). -/

/--
error: Application type mismatch: The argument
  hbad
has type
  EvTrue w e (ltT a b)
but is expected to have type
  EvTrue w e (notT (ltT a b))
in the application
  native_of_replayed_le w e a b x y h_no_lt h_no_not hL hR hbad
-/
#guard_msgs (whitespace := lax) in
example (w : World) (e : Env) (a b : SExpr) (x y : Int)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (hL : Conv w e a (intRep.enc x)) (hR : Conv w e b (intRep.enc y))
    (hbad : EvTrue w e (ltT a b)) : y ≤ x :=
  native_of_replayed_le w e a b x y h_no_lt h_no_not hL hR hbad

/- PROBE 3 — the conjunction decode refuses a replayed statement that is
   not the macroexpanded `AND`: only ONE conjunct's worth of truth is
   available from a bare equality, so both must not come out. -/

/--
error: Application type mismatch: The argument
  hbad
has type
  EvTrue w e (equalT l1 r1)
but is expected to have type
  EvTrue w e (andT (equalT l1 r1) (equalT l2 r2))
in the application
  native_of_replayed_and w e intRep intRep l1 r1 l2 r2 x1 y1 x2 y2 h_no_equal hL1 hR1 hL2 hR2 hbad
-/
#guard_msgs (whitespace := lax) in
example (w : World) (e : Env) (l1 r1 l2 r2 : SExpr) (x1 y1 x2 y2 : Int)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hL1 : Conv w e l1 (intRep.enc x1)) (hR1 : Conv w e r1 (intRep.enc y1))
    (hL2 : Conv w e l2 (intRep.enc x2)) (hR2 : Conv w e r2 (intRep.enc y2))
    (hbad : EvTrue w e (equalT l1 r1)) : x1 = y1 ∧ x2 = y2 :=
  native_of_replayed_and w e intRep intRep l1 r1 l2 r2 x1 y1 x2 y2
    h_no_equal hL1 hR1 hL2 hR2 hbad

end ACL2.Tests.LiftingRelProbes
