import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## Entry — `p7-cong-collapse`: the first VALIDATION-BOOK waypoint
(validator/lifter arc inc-0, 2026-07-30)

Rung 2's ground truth: `P7-TARGET` — `(equal (ln (dub x)) (ln x))`, the
theorem whose replay validates the congruence collapse — lifted to the
native fact `(l.map (fun _ => '0)).length = l.length`. The chain: the real
p7 log → parse → reconstruct → derived world → the driver's conditional
replayed statement (`tp:LN` only) → discharged by the NAME-GENERIC
`drv_tp_len` (the industrialization dividend: LN's body is exactly
`lenBody "LN"`) → instantiated at an encoded list → `corr_mapconst_enc` ∘
`corr_len_enc` → `native_of_replayed_equal intRep`. WAYPOINTS establish that
a replayed theorem means what the user intends (CLAUDE.md terminology,
2026-07-30) — this is the first for a pattern-test book. -/

private def p7Log : String :=
  include_str "../../../acl2_samples/pattern-tests/p7-cong-collapse.proof-log"

def p7Dev : Development :=
  load_development% p7Log

derive_world p7WorldD from p7Dev

def p7TargetReplayedCond := driver_replayed% p7Dev p7WorldD "p7-target"

private def q0Atom : SExpr := .atom (.number (.int 0))
private def xVarT : SExpr := .atom (.symbol { name := "X" })
private def p7xSym : Symbol := { package := "ACL2", name := "X" }
private def lnDubT : SExpr := app1 "LN" (app1 "DUB" xVarT)
private def lnXT : SExpr := app1 "LN" xVarT

/-- The replayed statement, UNCONDITIONAL: the sole `tp:LN` hypothesis is
    discharged by the name-generic len-class discharger. -/
theorem p7TargetReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f p7WorldD env
      (equalT lnDubT lnXT) = some v ∧ v ≠ SExpr.nil :=
  p7TargetReplayedCond env
    (drv_tp_len p7WorldD "LN" (by decide) (by decide) (by decide)
      (by decide) (by decide))

/-- The WAYPOINT: `(l.map (fun _ => '0)).length = l.length` — proved FROM the
    replayed P7-TARGET (via `Int` lengths and `Nat.cast` injectivity).
    NARROWING vs the book theorem (audit F6): the ACL2 statement holds for
    ALL X (atoms, improper lists); the waypoint quantifies over `List SExpr`
    — the true-listp fragment, inherent to native Lean lists. The
    discriminating content is the proof ROUTE through the replayed
    statement (the native statement alone is a simp one-liner — audit
    F5); nothing pins the route mechanically, so a future edit replacing
    it with a direct proof would silently drop the ground-truth value. -/
theorem p7_dub_len_native_driver (l : List SExpr) :
    (l.map (fun _ => q0Atom)).length = l.length := by
  let e : Env := ({} : Env).insert p7xSym (enc l)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e xVarT = some (enc l) :=
    conv_var_of_get p7WorldD e p7xSym (enc l) (by simp [e])
  have hdub : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e (app1 "DUB" xVarT)
      = some (enc (l.map (fun _ => q0Atom))) :=
    corr_mapconst_enc p7WorldD q0Atom "DUB" (by decide) (by decide)
      (by decide) (by decide) (by decide) l e xVarT hx
  have hlhs : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e lnDubT
      = some (.atom (.number (.int (l.map (fun _ => q0Atom)).length))) :=
    corr_len_enc p7WorldD "LN" (by decide) (by decide) (by decide)
      (by decide) (by decide) (l.map (fun _ => q0Atom)) e
      (app1 "DUB" xVarT) hdub
  have hrhs : ∃ N, ∀ f ≥ N, evalOpt f p7WorldD e lnXT
      = some (.atom (.number (.int l.length))) :=
    corr_len_enc p7WorldD "LN" (by decide) (by decide) (by decide)
      (by decide) (by decide) l e xVarT hx
  have hnat : ((l.map (fun _ => q0Atom)).length : Int) = (l.length : Int) :=
    native_of_replayed_equal p7WorldD e intRep lnDubT lnXT _ _
      (by decide) hlhs hrhs (p7TargetReplayed_uncond e)
  exact_mod_cast hnat

/-! ## Entry — `p5-or-shape-flipped`: the SECOND validation-book waypoint
(validator/lifter arc inc-1)

`DUPP-REP-MID` — `(implies (and (consp x) (equal (car x) e) (dupp x))
(or (equal x 'junk) (dupp (cons e x))))`, replayed UNCONDITIONAL — lifted
to the native fact: prepending an element equal to the head of an
adjacent-equal chain keeps it a chain. Exercises the machinery p7 did not:
the `chain2` schematic (comparison-generic — `dupp` is EQUAL's instance),
`boolEnc`, the IMPLIES hypothesis decode, and the or-disjunct
elimination (`enc l` is never the symbol `JUNK`). -/

private def p5MirrorLog : String :=
  include_str "../../../acl2_samples/pattern-tests/p5-or-shape-flipped.proof-log"

def p5Dev : Development :=
  load_development% p5MirrorLog

derive_world p5WorldD from p5Dev

def duppRepReplayed := driver_replayed% p5Dev p5WorldD "dupp-rep-mid"

private def p5eSym : Symbol := { package := "ACL2", name := "E" }
private def p5xSym : Symbol := { package := "ACL2", name := "X" }
private def p5eT : SExpr := .atom (.symbol { name := "E" })
private def p5xT : SExpr := .atom (.symbol { name := "X" })
private def junkQ : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.symbol { name := "JUNK" })) .nil)
private def junkA : SExpr := .atom (.symbol { name := "JUNK" })
/-- `dupp`'s native content: the EQUAL instance of the chain2 fold. -/
def duppRec : List SExpr → Bool := chain2Rec (· == ·)

private theorem callBuiltin_equal_bool (a b : SExpr) :
    callBuiltin "EQUAL" [a, b] = some (boolEnc (a == b)) := by
  rw [callBuiltin_equal]
  cases h : a == b <;> simp [Logic.equal, h, boolEnc]

/-- The dupp correspondence — ONE instantiation of the schematic. -/
private theorem corr_dupp (xs : List SExpr) (e' : Env) (a : SExpr)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD e' a = some (enc xs)) :
    ∃ N, ∀ f ≥ N, evalOpt f p5WorldD e' (app1 "DUPP" a)
      = some (boolEnc (duppRec xs)) :=
  corr_chain2_enc p5WorldD "EQUAL" "DUPP" (· == ·) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    callBuiltin_equal_bool xs e' a ha

/-- ENTRY, PROVED — the p5 WAYPOINT: prepending an element equal to the head
    preserves the adjacent-equal chain, THROUGH the replayed DUPP-REP-MID
    (implies decode; the `junk` disjunct dies because an encoded list is
    never that symbol).
    NARROWING vs the book theorem (audit F6): the ACL2 statement holds for
    ANY cons X including improper lists; this waypoint quantifies over
    `List SExpr` (the true-listp fragment — inherent to native Lean lists)
    and instantiates the `(equal (car x) e)` hypothesis at hd := e (faithful
    — EQUAL is identity here). -/
theorem p5_dupp_prepend_native_driver (e : SExpr) (tl : List SExpr)
    (h : duppRec (e :: tl) = true) : duppRec (e :: e :: tl) = true := by
  let env : Env := (({} : Env).insert p5eSym e).insert p5xSym (enc (e :: tl))
  have hx : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env p5xT = some (enc (e :: tl)) :=
    conv_var_of_get _ _ _ _ (by
      simp only [env, Env.get?_insert]
      rw [if_pos (by decide)])
  have he : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env p5eT = some e :=
    conv_var_of_get _ _ _ _ (by
      simp only [env, Env.get?_insert]
      rw [if_neg (by decide), if_pos (by decide)])
  have hconsp : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env (conspT p5xT)
      = some (Logic.consp (.cons e (enc tl))) :=
    conv_builtin1 p5WorldD env { name := "CONSP" } p5xT _ _ (by decide)
      (by decide) hx (callBuiltin_consp _)
  have hcar : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env (carT p5xT) = some e := by
    have hcar0 := conv_builtin1 p5WorldD env { name := "CAR" } p5xT
      (.cons e (enc tl)) (Logic.car (.cons e (enc tl))) (by decide)
      (by decide) hx (callBuiltin_car _)
    simpa [Logic.car] using hcar0
  have heqcar : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (equalT (carT p5xT) p5eT)
      = some (Logic.equal e e) :=
    conv_equalT p5WorldD env (carT p5xT) p5eT e e (by decide) hcar he
  have hdupx : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env (app1 "DUPP" p5xT)
      = some (boolEnc (duppRec (e :: tl))) :=
    corr_dupp (e :: tl) env p5xT hx
  -- the antecedent: (IF (CONSP X) (IF (EQUAL (CAR X) E) (DUPP X) 'NIL) 'NIL)
  -- — both tests TRUE by construction, so it converges to dupp's value
  have hanteInner : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (equalT (carT p5xT) p5eT)
            (.cons (app1 "DUPP" p5xT)
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons .nil .nil)) .nil))))
      = some (boolEnc (duppRec (e :: tl))) := by
    obtain ⟨Ni, hi⟩ := re_if_true p5WorldD env (equalT (carT p5xT) p5eT)
      _ _ (Logic.equal e e) (boolEnc (duppRec (e :: tl))) heqcar
      (by simp [Logic.equal, SExpr.t, Logic.toBool]) hdupx
    obtain ⟨Nd, hd⟩ := hdupx
    exact ⟨max Ni Nd, fun f hf => (hi f (by omega)).trans (hd f (by omega))⟩
  have hante : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (conspT p5xT)
            (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons (equalT (carT p5xT) p5eT)
                (.cons (app1 "DUPP" p5xT)
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                    (.cons .nil .nil)) .nil))))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons .nil .nil)) .nil))))
      = some (boolEnc (duppRec (e :: tl))) := by
    obtain ⟨Ni, hi⟩ := re_if_true p5WorldD env (conspT p5xT) _ _
      (Logic.consp (.cons e (enc tl))) (boolEnc (duppRec (e :: tl)))
      hconsp rfl hanteInner
    obtain ⟨Na, ha⟩ := hanteInner
    exact ⟨max Ni Na, fun f hf => (hi f (by omega)).trans (ha f (by omega))⟩
  -- the consequent: (IF (EQUAL X 'JUNK) (EQUAL X 'JUNK) (DUPP (CONS E X)))
  -- — the test is FALSE (an encoded list is never the JUNK symbol)
  have hjunk : ∃ N, ∀ f ≥ N, evalOpt f p5WorldD env junkQ = some junkA :=
    ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
                       exact evalOpt_quote g p5WorldD env _⟩
  have heqjunk : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (equalT p5xT junkQ) = some SExpr.nil := by
    have h0 := conv_equalT p5WorldD env p5xT junkQ (enc (e :: tl)) junkA
      (by decide) hx hjunk
    simpa [Logic.equal, enc, junkA] using h0
  have hconsex : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (consT p5eT p5xT)
      = some (enc (e :: e :: tl)) := by
    have h0 := conv_builtin2 p5WorldD env { name := "CONS" } p5eT p5xT
      e (enc (e :: tl)) (Logic.cons e (enc (e :: tl))) (by decide)
      (by decide) he hx (callBuiltin_cons _ _)
    simpa [Logic.cons, enc] using h0
  have hdupcons : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env (app1 "DUPP" (consT p5eT p5xT))
      = some (boolEnc (duppRec (e :: e :: tl))) :=
    corr_dupp (e :: e :: tl) env (consT p5eT p5xT) hconsex
  have hcons' : ∃ N, ∀ f ≥ N,
      evalOpt f p5WorldD env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (equalT p5xT junkQ)
            (.cons (equalT p5xT junkQ)
              (.cons (app1 "DUPP" (consT p5eT p5xT)) .nil))))
      = some (boolEnc (duppRec (e :: e :: tl))) := by
    obtain ⟨Ni, hi⟩ := re_if_false p5WorldD env (equalT p5xT junkQ)
      (equalT p5xT junkQ) (app1 "DUPP" (consT p5eT p5xT))
      (boolEnc (duppRec (e :: e :: tl))) heqjunk hdupcons
    obtain ⟨Nd, hd⟩ := hdupcons
    exact ⟨max Ni Nd, fun f hf => (hi f (by omega)).trans (hd f (by omega))⟩
  -- the whole formula's value, pinned truthy by the replayed statement
  have himp := conv_impliesT p5WorldD env _ _
    (boolEnc (duppRec (e :: tl))) (boolEnc (duppRec (e :: e :: tl)))
    (by decide) hante hcons'
  have hval : Logic.implies (boolEnc (duppRec (e :: tl)))
      (boolEnc (duppRec (e :: e :: tl))) = SExpr.t :=
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (duppRepReplayed env) himp)
  have hconc := truthy_of_implies_t hval (by rw [h]; rfl)
  cases hc : duppRec (e :: e :: tl) with
  | true => rfl
  | false => rw [hc] at hconc; exact absurd hconc (by decide)

end ACL2.Imported.Waypoints
