import ACL2Lean.Imported.Waypoints.Basics
import ACL2Lean.Mirrors.Basics

/-! # MIRROR PROOFS — the basics books

The proofs of `ACL2Lean/Mirrors/Basics.lean`'s target Props, VIA
REPLAY. Placement per Mike's ruling (2026-08-12): spec files stay
zero-import; this layer imports the machinery and proves the Props.

PROVED HERE (3 of the 6 Basics Props): `app_assoc_int` (02-rev's
APP-ASSOC), `len_app_int` (simple.lisp's MY-LEN-MY-APP) and
`len_revAcc_int` (the 14-accumulator book's LEN-REV-ACC — the
accumulator class, landed with the Basics-closeout arc). The remaining
three are HONEST DEFERRALS, not oversights: `app_nil` waits on the
01/02 books' `rule:CONS-CAR-CDR` discharger + the true-listp hypothesis
decode, and `rev_app`/`rev_rev` on the rev-family dischargers — all
three waypoint rows are `.pending`, so there is no replayed statement
to transport yet and a Lean-side proof would be exactly the banned
route.

EXPECTATIONS (deliberately not a gate — these are small demos, kept
straight by convention):
- Each theorem's STATEMENT mentions only `ACL2Lean.Basics` constants
  and core instance types — a reader of the spec file can read these
  statements with no further vocabulary.
- Mirror CONTENT enters via the waypoint theorems (replayed-backed)
  and nowhere else. The inductions in this file are SQUARES —
  definitional agreement and homomorphism — never the property
  itself. For `app_assoc`, core Lean's `List.append_assoc` could
  close the theorem in one line; using it would make this file
  worthless (the route IS the product).
- `#guard_msgs` receipts pin each theorem's axiom set on the page.

THE LIST (the pathfinder's second deliverable — everything
hand-written here that the transfer kit should generate or subsume):
1. `Acl2Embed` + the `Int` instance → extract to the transfer kit
   (Phase C1) when the second instance appears.
2. `app_map_hom` (the homomorphism square) → `mirror_iso%`-generated
   (Phase C2; same-skeleton walk).
3. `app_agree_append` (vocabulary alignment at `List SExpr`) →
   dissolves if/when waypoint statements are generated in mirror
   vocabulary (Phase B5/C3 design point).
4. `encList_inj`/`map_inj` (injectivity plumbing) → transfer-kit
   lemma (C1).
5. The transport assembly in `app_assoc_int` (rewrite-lift-pullback)
   → `mirror transport`-generated (C3).
6. `len_agree_length` + `len_map_invariant` (the len squares) →
   mirror_iso%-generated (C2); the Nat-result transport pattern in
   `len_app_int` (no injectivity needed — numeric conclusion) → C3.
7. `app_assoc_sexpr`/`len_app_sexpr` (the waypoint crossings: three
   vocabulary rewrites + the waypoint theorem) → C3-generated with
   the transport; dissolve entirely if waypoint statements are ever
   generated in mirror vocabulary (the item-3 design point).
8. THE ACCUMULATOR FAMILY (`len_revAcc`, the third mirror — the final
   hand round; this is what C's generator must reproduce):
   - `revAcc_map_hom` — the item-2 homomorphism square, but over TWO
     ACCUMULATING ARGUMENTS: the square GENERALIZES over the
     accumulator (its induction hypothesis is taken at `a :: acc`, not
     at `acc`). `mirror_iso%` (C2) must therefore quantify every
     non-measured argument inside the motive, not carry it fixed —
     the one structural demand the app/len squares could not reveal.
   - `revAcc_agree_revAccL` — item 3 again, and the sharper form of
     it: the alignment is against a WAYPOINT-LAYER native (`revAccL`,
     a `List SExpr` function) rather than a core operator (`++`), so
     it is pure re-spelling of the SAME recursion. Exactly what
     generating waypoint statements in mirror vocabulary dissolves.
   - `len_revAcc_sexpr` — the item-7 crossing (one alignment rewrite
     + three `len_agree_length` rewrites, then exactly the waypoint
     theorem). The length-SUM content enters here and nowhere else.
   - the `len_revAcc_int` transport — item 5/6's assembly VERBATIM
     (numeric conclusion, so no injectivity pullback): the third
     independent sample, and the two `len_map_invariant` +
     one homomorphism + one crossing shape is now measured, not
     guessed, for the D generator. -/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

/-! ## The minimal embedding (THE LIST item 1) -/

/-- An element embedding into the ACL2 value universe: an injection
    `α → SExpr`. The pathfinder needs nothing more (no order field —
    that dimension arrives with sorting). -/
structure Acl2Embed (α : Type u) where
  enc : α → SExpr
  inj : ∀ {a b : α}, enc a = enc b → a = b

/-- `Int` embeds as integer atoms. -/
def intEmbed : Acl2Embed Int where
  enc n := .atom (.number (.int n))
  inj h := by injection h with h1; injection h1 with h2; injection h2

/-- Injectivity lifts pointwise to lists (THE LIST item 4). -/
theorem map_inj (e : Acl2Embed α) :
    ∀ {xs ys : List α}, xs.map e.enc = ys.map e.enc → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, b :: ys, h => by
    simp only [List.map] at h
    injection h with h1 h2
    rw [e.inj h1, map_inj e h2]

/-! ## The squares -/

/-- SQUARE A (vocabulary alignment, THE LIST item 3): our spec-layer
    `app` agrees with core `++` — needed only because the waypoint
    theorem is stated with `++`. Definitional agreement, not
    content. -/
theorem app_agree_append :
    ∀ (xs ys : List SExpr), Basics.app xs ys = xs ++ ys
  | [], _ => rfl
  | _ :: t, ys => by
    simp only [Basics.app, List.cons_append, app_agree_append t ys]

/-- The homomorphism square (THE LIST item 2): mapping commutes with
    our `app` — about OUR function's skeleton, not about
    associativity. -/
theorem app_map_hom (e : Acl2Embed α) :
    ∀ (xs ys : List α),
      (Basics.app xs ys).map e.enc =
        Basics.app (xs.map e.enc) (ys.map e.enc)
  | [], _ => rfl
  | _ :: t, ys => by
    simp only [Basics.app, List.map, app_map_hom e t ys]

/-! ## The waypoint crossing — associativity's SOLE entry point -/

/-- `app`-associativity over `List SExpr`, FROM the replayed-backed
    waypoint: three Square-A rewrites, then exactly the waypoint
    theorem (`app_assoc_native_driver` → `appAssocReplayed_uncond` →
    the driver's replay of the 02-rev book's APP-ASSOC). -/
theorem app_assoc_sexpr (xs ys zs : List SExpr) :
    Basics.app (Basics.app xs ys) zs =
      Basics.app xs (Basics.app ys zs) := by
  rw [app_agree_append, app_agree_append, app_agree_append,
      app_agree_append]
  exact Imported.Waypoints.app_assoc_native_driver xs ys zs

/-! ## THE FIRST MIRROR -/

/-- **`app_assoc` at `Int`, via ACL2 replay** (THE LIST item 5 — the
    transport assembly): encode along the embedding, apply the
    SExpr-level fact (whose content is the replayed APP-ASSOC), pull
    back by injectivity. -/
theorem app_assoc_int : Basics.app_assoc Int := by
  intro xs ys zs
  apply map_inj intEmbed
  rw [app_map_hom, app_map_hom, app_map_hom, app_map_hom]
  exact app_assoc_sexpr _ _ _

/-- info: 'ACL2Lean.MirrorProofs.app_assoc_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms app_assoc_int

/-! ## The stretch: `len_app` — the first honest debt inheritance -/

/-- Square: our spec-layer `len` agrees with core `length`
    (vocabulary alignment — the waypoint speaks `length`). -/
theorem len_agree_length :
    ∀ (xs : List SExpr), Basics.len xs = xs.length
  | [] => rfl
  | _ :: t => by simp only [Basics.len, List.length, len_agree_length t]

/-- Square: mapping the embedding preserves our `len` (homomorphism
    over OUR function's skeleton). -/
theorem len_map_invariant (e : Acl2Embed α) :
    ∀ (xs : List α), Basics.len (xs.map e.enc) = Basics.len xs
  | [] => rfl
  | _ :: t => by simp only [List.map, Basics.len, len_map_invariant e t]

/-- `len`/`app` over `List SExpr`, FROM the replayed-backed waypoint
    (three vocabulary rewrites, then exactly the waypoint theorem). -/
theorem len_app_sexpr (xs ys : List SExpr) :
    Basics.len (Basics.app xs ys) = Basics.len xs + Basics.len ys := by
  rw [app_agree_append, len_agree_length, len_agree_length,
      len_agree_length]
  exact Imported.Waypoints.my_len_my_app_native_driver xs ys

/-- **`len_app` at `Int`, via ACL2 replay** — the first mirror whose
    inherited DEBT RETIRED: the MY-LEN-MY-APP waypoint carried
    `sorryAx` via `drv_tp_mylen` (a TP fact ACL2 discharged, replayed
    Lean-side as registered debt) until the TP prover's return-path arm
    landed (TP-replay arc increment 1, 2026-08-12) — `tp:MY-LEN` now
    arrives from ACL2's emitted `:TYPE-PRESCRIPTION` corollary +
    `:LEAVES`, the waypoint is `.native`, and this receipt is the clean
    trio. Content enters via the waypoint and nowhere else. -/
theorem len_app_int : Basics.len_app Int := by
  intro xs ys
  rw [show Basics.len (Basics.app xs ys)
        = Basics.len ((Basics.app xs ys).map intEmbed.enc) from
      (len_map_invariant intEmbed _).symm,
    app_map_hom, len_app_sexpr,
    len_map_invariant, len_map_invariant]

/-- info: 'ACL2Lean.MirrorProofs.len_app_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms len_app_int

/-! ## THE THIRD MIRROR: `len_revAcc` — the accumulator (THE LIST item 8)

The 14-accumulator book's `REV-ACC`. Two squares are new here, and only
one of them is new in KIND: the homomorphism square has to generalize
over the accumulator (the IH lands at `a :: acc`), while the alignment
square is item 3's vocabulary rewrite against a waypoint-layer native
instead of a core operator. `len_agree_length`/`len_map_invariant` are
REUSED verbatim from `len_app`. -/

/-- SQUARE (vocabulary alignment, THE LIST item 3/8): our spec-layer
    `revAcc` at `List SExpr` IS the waypoint's `revAccL` — the same
    recursion spelled in the two layers' vocabularies. Definitional
    agreement, not content. -/
theorem revAcc_agree_revAccL :
    ∀ (xs acc : List SExpr),
      Basics.revAcc xs acc = Worlds.RevAcc.revAccL xs acc
  | [], _ => rfl
  | a :: t, acc => by
    simp only [Basics.revAcc, Worlds.RevAcc.revAccL,
      revAcc_agree_revAccL t (a :: acc)]

/-- The homomorphism square for the ACCUMULATOR (THE LIST item 8):
    mapping commutes with our `revAcc`. Note the generalization — the
    recursive appeal is at the EXTENDED accumulator `a :: acc`, so the
    square is about our function's skeleton with BOTH arguments moving,
    and says nothing about reversal. -/
theorem revAcc_map_hom (e : Acl2Embed α) :
    ∀ (xs acc : List α),
      (Basics.revAcc xs acc).map e.enc =
        Basics.revAcc (xs.map e.enc) (acc.map e.enc)
  | [], _ => rfl
  | a :: t, acc => by
    simp only [Basics.revAcc, List.map, revAcc_map_hom e t (a :: acc)]

/-- `len`/`revAcc` over `List SExpr`, FROM the replayed-backed waypoint:
    one alignment rewrite, three vocabulary rewrites, then exactly the
    waypoint theorem (`len_rev_acc_native_driver` →
    `lenRevAccReplayed_uncond` → the driver's replay of the
    14-accumulator book's LEN-REV-ACC). This is the SOLE entry point of
    the length-sum content. -/
theorem len_revAcc_sexpr (xs acc : List SExpr) :
    Basics.len (Basics.revAcc xs acc) = Basics.len xs + Basics.len acc := by
  rw [revAcc_agree_revAccL, len_agree_length, len_agree_length,
      len_agree_length]
  exact Imported.Waypoints.len_rev_acc_native_driver xs acc

/-- **`len_revAcc` at `Int`, via ACL2 replay** — the third mirror, and
    the accumulator class's first. Same transport assembly as
    `len_app_int` (numeric conclusion, so no injectivity pullback);
    content enters via the waypoint and nowhere else. The waypoint's own
    simulation step is the ALIGNED reading of `REV-ACC` (the
    `derive_sim%` template gate's decisive case) — the reassociating
    reading, which would have smuggled ACL2's own `(equal (rev-acc x
    acc) (append (rev x) acc))` into the iso, is rejected by that gate
    when its induction is driven off the reading itself. -/
theorem len_revAcc_int : Basics.len_revAcc Int := by
  intro xs acc
  rw [show Basics.len (Basics.revAcc xs acc)
        = Basics.len ((Basics.revAcc xs acc).map intEmbed.enc) from
      (len_map_invariant intEmbed _).symm,
    revAcc_map_hom, len_revAcc_sexpr,
    len_map_invariant, len_map_invariant]

/-- info: 'ACL2Lean.MirrorProofs.len_revAcc_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms len_revAcc_int

end ACL2Lean.MirrorProofs
