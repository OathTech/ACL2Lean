import ACL2Lean.Imported.Sorting.Sims

/-! # The sorting books — LAYER 4 of 4: THE DEBT (quarantined)

**This file IS the complete list of facts the sorting imports ASSUME.**

Twelve statements, each `sorry`-ed, each carrying `FORBIDDEN-DEBT`
(thin-Lean ruling 2026-08-11). Every one is a fact ACL2 itself
discharged — a defun's admission (`total:`), a defun's emitted
type-prescription corollary (`tp:`), or a previously-proved theorem
used as a rewrite rule (`rule:`) — for which the REPLAY route does not
exist yet. They are held here as visible `sorryAx`, never as a
Lean-side re-proof: proving one in Lean would be doing ACL2's job in
Lean, and the PROVENANCE GATE (`Mirrors/Catalog.lean`) fails the build
if a registered entry stops carrying its `sorry`.

By class (the authoritative registry is `TODO.md`'s DEBT REGISTRY):

| class | entries | unlock |
| --- | --- | --- |
| `tp:` | `dis_insert_tp`, `dis_how_many_tp`, `dis_all_rel_tp`, `dis_append_tp`, `dis_evens_tp`, `dis_acl2_count_tp` | a TP-replay discharge route |
| `total:` | `dis_merge2_total`, `dis_msort_total`, `dis_o_lt_total`, `dis_pce_total`, `dis_bnext_total` | `with_termination` admission coverage (REQUIRED class — the machinery exists, the rows need wiring) |
| `rule:` | `dis_convert_perm` | the R-lane arc (PERM-TLFIX replay → CONVERT-PERM-TO-HOW-MANY) |

Eight further sorries live outside the sorting books:
`Imported/SortingBsort.lean` (2, `tp:`), `Imported/EquisortWitness.lean`
(4, `tp:`), `Imported/SimpleWorld.lean` (1, `tp:`),
`Imported/Lifting.lean` (1, `tp:`) — 20 in the whole library.

NOTE the import line above: these statements are stated over the
DEFINITIONS alone (`Sims`). Nothing assumed here depends on the
correspondence or decode layers.
-/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm

namespace ACL2.Worlds.Sorting

/-! ## The `tp:INSERT` discharger — `(CONSP (INSERT E X))` -/

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:INSERT` — the emitted `(CONSP (INSERT E X))` corollary —
    Lean-side; content ACL2 derives. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: TP-replay discharge. -/
theorem dis_insert_tp (w : World)
    (h_insert : w.defs.get? insert_sym = some ([eS, xS], insertBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol insert_sym))
        (SExpr.cons a0 (SExpr.cons a1 SExpr.nil))) = some v) :
    Logic.consp v = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:HOW-MANY` — the emitted non-negative-integer corollary —
    Lean-side; content ACL2 derives. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: TP-replay discharge. -/
theorem dis_how_many_tp (w : World)
    (h_how_many : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_binary__ : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol how_many_sym))
        (SExpr.cons a0 (SExpr.cons a1 SExpr.nil))) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
        Logic.not (Logic.lt v (.atom (.number (.int 0))))
      else SExpr.nil) = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:ALL-REL` — the emitted boolean corollary — Lean-side; content
    ACL2 derives. Statement kept as the named premise; proof retired to
    `sorry`. UNLOCK: TP-replay discharge. -/
theorem dis_all_rel_tp (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_all_rel : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 a1 a2 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol all_rel_sym))
        (SExpr.cons a0 (SExpr.cons a1 (SExpr.cons a2 SExpr.nil))))
      = some v) :
    (bif Logic.toBool (Logic.equal v SExpr.t) then SExpr.t
      else Logic.equal v SExpr.nil) = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:BINARY-APPEND` — the args-valued TP hypothesis
    (`(IF (CONSP (BINARY-APPEND X Y)) 'T (EQUAL (BINARY-APPEND X Y) Y))`)
    — Lean-side; content ACL2 derives. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: TP-replay discharge. -/
theorem dis_append_tp (w : World)
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (e' : Env) (a0 a1 u0 u1 v : SExpr)
    (h0 : ∃ N, ∀ f ≥ N, evalOpt f w e' a0 = some u0)
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w e' a1 = some u1)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (appendT a0 a1) = some v) :
    (bif Logic.toBool (Logic.consp v) then SExpr.t else Logic.equal v u1)
      = SExpr.t := by
  sorry

/-! ## The msort dischargers -/

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `total:MERGE2` — the driver-shape totality premise — Lean-side;
    content ACL2 derives at admission. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: `with_termination`
    admission-replay coverage (REQUIRED-class debt). -/
theorem dis_merge2_total (w : World)
    (h_merge2 : w.defs.get? merge2_sym = some ([xS, yS], merge2Body))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env'
        (SExpr.cons (SExpr.atom (Atom.symbol merge2_sym))
          (SExpr.cons a0 (SExpr.cons a1 SExpr.nil))) = some v := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `total:MSORT` — the driver-shape totality premise — Lean-side;
    content ACL2 derives at admission. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: `with_termination`
    admission-replay coverage (REQUIRED-class debt). -/
theorem dis_msort_total (w : World)
    (h_m2 : w.defs.get? merge2_sym = some ([xS, yS], merge2Body))
    (h_evens : w.defs.get? evens_sym = some ([lS], evensBody))
    (h_odds : w.defs.get? odds_sym = some ([lS], oddsBody))
    (h_msort : w.defs.get? msort_sym = some ([xS], msortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env' : Env) (a0 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (msortT a0) = some v := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:EVENS` — the emitted `(TRUE-LISTP (EVENS L))` corollary —
    Lean-side; content ACL2 derives. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: TP-replay discharge. -/
theorem dis_evens_tp (w : World)
    (h_evens : w.defs.get? evens_sym = some ([lS], evensBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol evens_sym))
        (SExpr.cons a0 SExpr.nil)) = some v) :
    Logic.trueListp v = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `total:O<` — the driver-shape totality premise — Lean-side; content
    ACL2 derives at admission. Statement kept as the named premise;
    proof retired to `sorry`. UNLOCK: `with_termination`
    admission-replay coverage (REQUIRED-class debt). -/
theorem dis_o_lt_total (w : World)
    (h_lt : w.defs.get? o_lt_sym = some ([xS, yS], oLtBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_fe : w.defs.get? o_fe_sym = some ([xS], oFirstExptBody))
    (h_fc : w.defs.get? o_fc_sym = some ([xS], oFirstCoeffBody))
    (h_rst : w.defs.get? o_rst_sym = some ([xS], oRstBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (oLtT a0 a1) = some v := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:ACL2-COUNT` — the emitted non-negative-integer TP corollary
    (unary) — Lean-side; content ACL2 derives. Statement kept as the
    named premise; proof retired to `sorry`. UNLOCK: TP-replay
    discharge. -/
theorem dis_acl2_count_tp (w : World)
    (h_ac : w.defs.get? acl2_count_sym = some ([xS], acl2CountBody))
    (h_ia : w.defs.get? integer_abs_sym = some ([xS], integerAbsBody))
    (h_len : w.defs.get? length_sym = some ([xS], lengthBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_rationalp : w.defs.get? ({ name := "RATIONALP" } : Symbol) = none)
    (h_no_integerp : w.defs.get? ({ name := "INTEGERP" } : Symbol) = none)
    (h_no_num : w.defs.get? ({ name := "NUMERATOR" } : Symbol) = none)
    (h_no_den : w.defs.get? ({ name := "DENOMINATOR" } : Symbol) = none)
    (h_no_crp : w.defs.get?
      ({ name := "COMPLEX-RATIONALP" } : Symbol) = none)
    (h_no_stringp : w.defs.get? ({ name := "STRINGP" } : Symbol) = none)
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_coerce : w.defs.get? ({ name := "COERCE" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_neg : w.defs.get? ({ name := "UNARY--" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (acl2CountT a0) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
      Logic.not (Logic.lt v (.atom (.number (.int 0))))
    else SExpr.nil) = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `total:PERM-COUNTER-EXAMPLE` — the driver-shape totality premise —
    Lean-side; content ACL2 derives at admission. Statement kept as the
    named premise; proof retired to `sorry`. UNLOCK: `with_termination`
    admission-replay coverage (REQUIRED-class debt). -/
theorem dis_pce_total (w : World)
    (h_pce : w.defs.get? pce_sym = some ([xS, yS], pceBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (pceT a0 a1) = some v := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `rule:CONVERT-PERM-TO-HOW-MANY` — the stored included-book rule's
    content — Lean-side; content ACL2 derives. Statement kept as the
    named premise; proof retired to `sorry`. UNLOCK: the R-lane arc
    (PERM-TLFIX replay → CONVERT-PERM-TO-HOW-MANY discharge via the
    replayed tree). -/
theorem dis_convert_perm (w : World)
    (h_perm : w.defs.get? { package := "ACL2", name := "PERM" }
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }], permBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_pce : w.defs.get? pce_sym = some ([xS, yS], pceBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (permT xT yT)
        = evalOpt f w env'
            (equalT (howManyT (pceT xT yT) xT)
              (howManyT (pceT xT yT) yT)) := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `total:BNEXT` — bnext's driver-shape totality premise — Lean-side;
    content ACL2 derives at admission. Statement kept as the named
    premise; proof retired to `sorry`. UNLOCK: `with_termination`
    admission-replay coverage (REQUIRED-class debt). -/
theorem dis_bnext_total (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env' : Env) (a0 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (app1 "BNEXT" a0) = some v := by
  sorry

end ACL2.Worlds.Sorting
