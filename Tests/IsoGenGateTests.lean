/-
  Tests/IsoGenGateTests — the NEGATIVE test for `mirror_iso%`'s unfold-list
  gate (R-1a, ruled by Mike 2026-08-16 off audit finding A1-F1).

  THE ATTACK, reproduced verbatim from the auditor's probe
  (`docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md` F1; probe file
  `.tmp/a1/attack4.lean`): prove the accumulator CONTENT law
  `revAccL xs acc = revAccL xs [] ++ acc` normally — machinery-side, where
  any lemma is allowed — then dress the exact residual the square template
  cannot close as a Prop-valued `def` and hand it to `unfold [...]`. Before
  the fix this CLOSED the standing-example content square
  (`rev xs = revAccL xs []`, an ACL2 BOOK theorem) with axioms `[propext]`;
  only the registry's duplicate-square fail-close stopped it at the last
  hop, and only because `rev` already had a square.

  The test asserts the invocation now fails AT THE UNFOLD GATE — before the
  square is generated, so nothing is declared. `#guard_msgs` makes a
  silent regression of the check a BUILD FAILURE.

  THREAT MODEL (two-standard rule — the gate this pins is a SPEEDBUMP).
  It catches the honest mistake (a bridging lemma written as a `def` and
  passed to `unfold`). It is NOT a barrier: the same audit records another
  route on the same page (A1-F9, `embed S via [fields]`), and no syntactic
  check on the invocation can classify content. Do not harden it; the
  per-book provenance audit is the backstop. If this test ever becomes
  fragile, delete it rather than growing it.
-/
import ACL2Lean.MirrorProofs.Basics

namespace ACL2.Tests.IsoGenGate

open ACL2 ACL2Lean

/-- The general accumulator law, proved normally — this is legitimate
    machinery-side work (it is about the WAYPOINT reading, not a mirror
    statement), and the attack's premise is that it exists. -/
private theorem accLaw : ∀ (xs acc : List SExpr),
    Worlds.RevAcc.revAccL xs acc = Worlds.RevAcc.revAccL xs [] ++ acc := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons a t ih =>
    intro acc
    show Worlds.RevAcc.revAccL t (a :: acc) = Worlds.RevAcc.revAccL t [a] ++ acc
    rw [ih (a :: acc), ih [a], List.append_assoc]; rfl

/-- THE SMUGGLE: the terminating orientation of exactly the residual the
    square template leaves open, dressed as a `def` so it passes a check
    that asks only "is it a definition?". (Not `private`: the gate's error
    prints the resolved name, and the pin below is more readable — and a
    better regression witness — with the source-level one.) -/
def smuggled : ∀ (t : List SExpr) (h : SExpr),
    Worlds.RevAcc.revAccL t [h] = Worlds.RevAcc.revAccL t [] ++ [h] :=
  fun t h => accLaw t [h]

/-- error: mirror_iso%: `unfold [ACL2.Tests.IsoGenGate.smuggled]` is a PROP-VALUED definition — a Prop-valued def in the unfold list is the content-smuggling channel the 2026-08-16 audit demonstrated (A1-F1) — rejected; unfold accepts non-Prop DEFINITIONS only. Route a bridging fact through a replayed ACL2 book theorem instead.
-/
#guard_msgs in
mirror_iso% evil_rev_via_acc for ACL2Lean.Basics.rev
  vars [xs]
  square agree (Worlds.RevAcc.revAccL xs [])
  unfold [Worlds.RevAcc.revAccL, smuggled]

/-
  THE SECOND NEGATIVE TEST (R4 wave 2a): `vars` now takes a CONSTRUCTOR
  LITERAL, which is what lets ONE definition carry a per-constructor
  FAMILY of agreement squares (the keyed registry). A literal is admitted
  at a `.fixed` position ONLY — a closed type the embedding does not act
  on. Handed one at a `List α` position, the generator must refuse BEFORE
  producing any declaration, so this pin costs no `sorryAx`.

  Same threat model as above: a SPEEDBUMP against the honest mistake
  (writing `.lt` where a binder was meant, or at the wrong position), not
  a barrier. If it becomes fragile, delete it.
-/

/-- error: mirror_iso%: a `vars` CONSTRUCTOR LITERAL was given at an argument position whose reading is not `.fixed` — a literal specializes a CLOSED-TYPE (pass-through) position, the one kind of argument the embedding does not act on. At a `List α` or `α` position there is nothing for a literal to specialize (fail-closed).
-/
#guard_msgs in
mirror_iso% evil_app_at_literal for ACL2Lean.Basics.app
  vars [.nil, ys]
  square agree (ys)

/-
  THE THIRD NEGATIVE TEST (R4 wave 2d): `mirror_transport%` now admits a
  spec `Prop` that CARRIES HYPOTHESES (`ordered_perm_unique`). The shape
  it admits is DATA-THEN-HYPOTHESES — the data binders are the ones the
  transport encodes with `List.map` — and a DATA binder appearing AFTER a
  hypothesis is outside the table. Refused before any declaration is
  produced, so this pin costs no `sorryAx`.

  Same threat model: a SPEEDBUMP against the honest mistake (a spec whose
  binder order the generator would silently mis-associate), not a
  barrier. If it becomes fragile, delete it.
-/

/-- a probe-only spec shape: a `List` binder AFTER a hypothesis. -/
def probeDataAfterHyp (α : Type) : Prop :=
  ∀ (xs : List α), xs = xs → ∀ (ys : List α), ys = ys

/-- a probe-only `from` argument: the binder walk refuses before the
    cited theorem is ever used, so any resolvable constant serves. -/
theorem probeWp : True := trivial

/-- error: mirror_transport%: ACL2.Tests.IsoGenGate.probeDataAfterHyp binds the `List SExpr` argument `ys` AFTER 1 hypothesis binder(s) — the derived transport table is DATA-THEN-HYPOTHESES (the data binders are what get encoded), and anything else is a named frontier
-/
#guard_msgs in
mirror_transport% evil_data_after_hyp : ACL2.Tests.IsoGenGate.probeDataAfterHyp Int
  embed ACL2Lean.MirrorProofs.intEmbed
  crossing evil_data_after_hyp_sexpr from probeWp

/-
  THE FOURTH NEGATIVE TEST (R4 wave 2f): `mirror_transport%`'s binder
  table now has a SCALAR row — an `SExpr` (element) binder, encoded by
  `e.enc` where a list binder is encoded by `List.map e.enc`. Its
  consumers are the multiplicity mirrors (`∀ (a : α) (xs : List α),
  howMany a (isort xs) = howMany a xs`).

  The row is admitted on the HYPOTHESIS-FREE path ONLY: carrying an
  encoded ELEMENT through a hypothesis would need an element-position
  invariance square, a class this layer does not have, so a spec that
  binds a scalar AND carries hypotheses must be refused rather than
  assembled against squares that cannot fire. Refused before any
  declaration is produced, so this pin costs no `sorryAx`.

  Same threat model: a SPEEDBUMP against the honest mistake (adding a
  hypothesis to a multiplicity spec and assuming the element rides
  along), not a barrier. If it becomes fragile, delete it.
-/

/-- a probe-only spec shape: a SCALAR binder in a spec that ALSO
    carries a hypothesis. -/
def probeScalarWithHyp (α : Type) : Prop :=
  ∀ (a : α) (xs : List α), xs = xs → a = a

/-- error: mirror_transport%: ACL2.Tests.IsoGenGate.probeScalarWithHyp binds an `SExpr` (scalar) argument AND 1 hypothesis binder(s) — the scalar row of the derived transport table is admitted for HYPOTHESIS-FREE spec `Prop`s only (a named frontier: carrying an encoded ELEMENT through a hypothesis needs an element-position invariance square, which is a class this layer does not have)
-/
#guard_msgs (whitespace := lax) in
mirror_transport% evil_scalar_with_hyp : ACL2.Tests.IsoGenGate.probeScalarWithHyp Int
  embed ACL2Lean.MirrorProofs.intEmbed
  crossing evil_scalar_with_hyp_sexpr from probeWp

/-
  THE FIFTH NEGATIVE TEST (R4 wave 2e): `mirror_iso%` now takes an
  `instances [...]` clause (O-7, 2026-08-18) — per-square facts that make
  two spellings of ONE INSTANCE ARGUMENT meet. The clause admits an
  EQUATION whose type is proof-irrelevant by construction (head in
  `{Decidable, DecidableEq}`, or a synthesizable `Subsingleton`), and
  that shape check is the whole gate: an equation at any other type CAN
  carry subject content.

  THE ATTACK is the file's own first one, re-aimed: hand the closer the
  accumulator CONTENT law (`revAccL xs acc = revAccL xs [] ++ acc`, an
  ACL2 book theorem's shape) through the NEW clause instead of through
  `unfold`. It is refused before any declaration is produced, because its
  equation is at `List SExpr`.

  Same threat model as the other four: a SPEEDBUMP against the honest
  mistake, not a barrier — no syntactic check on the invocation can
  classify content, and the bound is provenance only (A1-F1). If it
  becomes fragile, delete it.
-/

/-- THE SMUGGLE, through the instance-facts clause. (Not `private`: the
    gate's error prints the resolved name.) -/
theorem smuggledInstanceFact : ∀ (t : List SExpr) (h : SExpr),
    Worlds.RevAcc.revAccL t [h] = Worlds.RevAcc.revAccL t [] ++ [h] :=
  fun t h => accLaw t [h]

/-- error: mirror_iso%: `instances [ACL2.Tests.IsoGenGate.smuggledInstanceFact]` is an equation at `List SExpr`, which is neither in the instance-facts allowlist (`Decidable`, `DecidableEq`) nor provably `Subsingleton`.
The clause exists for ONE thing: two spellings of one INSTANCE ARGUMENT that a `local` spec instance and the ambient one produce (O-7, 2026-08-18). Such an equality is content-free BY CONSTRUCTION — proof-irrelevant, relating no two operations. An equation at any OTHER type CAN carry subject content, so it is refused here (fail-closed): route a bridging fact through a replayed ACL2 book theorem.
-/
#guard_msgs (whitespace := lax) in
mirror_iso% evil_rev_via_instances for ACL2Lean.Basics.rev
  vars [xs]
  square agree (Worlds.RevAcc.revAccL xs [])
  unfold [Worlds.RevAcc.revAccL]
  instances [smuggledInstanceFact]

/-
  THE SIXTH AND SEVENTH NEGATIVE TESTS (close-out arc item 2): the
  square table gained a FOURTH class, `hom elem` — a mirror definition
  whose RESULT is the element type, carried by the embedding rather
  than invariant under it. Like the other three the declared class is
  CHECKED AGAINST THE DEFINITION'S OWN RESULT TYPE, in both directions:
  `hom elem` at a list result, and `hom scalar` at an element result
  (the drift a reader is most likely to make, since `hom scalar` was
  the only non-list class before). Both are refused before any
  declaration is produced, so these pins cost no `sorryAx`.

  Same threat model as the five above: a SPEEDBUMP against the honest
  mistake, not a barrier. If either becomes fragile, delete it.
-/

/-- a probe-only definition whose RESULT is the element type. -/
def probeElemResult {α : Type} : List α → α → α
  | [], a => a
  | b :: _, _ => b

/-- error: mirror_iso%: ACL2Lean.Basics.app's result is NOT the element type, but `hom elem` was declared — declare `hom list` for a list result and `hom scalar` for anything the embedding does not act on (the declared class is checked against the definition's type so a drift fails closed)
-/
#guard_msgs (whitespace := lax) in
mirror_iso% evil_app_as_elem for ACL2Lean.Basics.app
  vars [xs, ys]
  square hom elem

/-- error: mirror_iso%: ACL2.Tests.IsoGenGate.probeElemResult's result IS the element type, but `hom scalar` was declared — an element result is CARRIED by the embedding, not invariant under it, so declare `hom elem` (the declared class is checked against the definition's type so a drift fails closed)
-/
#guard_msgs (whitespace := lax) in
mirror_iso% evil_elem_as_scalar for ACL2.Tests.IsoGenGate.probeElemResult
  vars [xs, a]
  square hom scalar

/-
  THE OPTION ROW'S FAIL-CLOSED SHAPE CHECK, pinned as a REFUTATION
  rather than as an error message (close-out arc item 2).

  `IsoKit.lean`'s `optEmbed` renders ACL2's value-or-nil idiom as
  `Acl2Embed (Option α)` — `none ↦ nil`, `some a ↦ e.enc a` — under one
  side condition: the underlying encoding AVOIDS `nil`. The condition is
  a HYPOTHESIS of the row's constructor, so the row simply does not
  build without it; there is no unchecked variant to reach for and
  therefore no error message to pin. What CAN be pinned is that the
  condition is load-bearing, and the two theorems below do that: an
  embedding that hits `nil` fails it, and any value-or-nil map at a type
  where it fails CONFLATES two distinct `Option` values — which is
  exactly the injectivity the row would otherwise claim.

  The second theorem is also the record of the row's BOUND at the ACL2
  value type itself (`α := SExpr`, identity encoding), which is why a
  `mirror_transport%` CROSSING — always stated at `SExpr` — cannot carry
  an `Option`-VALUED spec definition.
-/

/-- A perfectly good embedding whose image HITS `nil`. -/
def boolEmbed : ACL2Lean.MirrorProofs.Acl2Embed Bool where
  enc b := if b then SExpr.t else SExpr.nil
  inj := by intro a b h; cases a <;> cases b <;> simp_all

/-- The row's side condition FAILS for it — so `optEmbed boolEmbed …`
    cannot be written, which is the fail-closed direction. -/
theorem boolEmbed_hits_nil : ¬ (∀ b : Bool, boolEmbed.enc b ≠ SExpr.nil) :=
  fun h => h false rfl

/-- …and that is not a technicality: WITHOUT the side condition the
    value-or-nil map is not injective at all. Stated over an ARBITRARY
    candidate map so it is about the IDIOM, not about one embedding. -/
theorem valueOrNil_conflates_when_nil_is_hit
    {α : Type} (f : Option α → SExpr) (a₀ : α)
    (hnone : f none = SExpr.nil) (hhit : f (some a₀) = SExpr.nil) :
    f none = f (some a₀) ∧ (none : Option α) ≠ some a₀ :=
  ⟨hnone.trans hhit.symm, fun h => by simp at h⟩

end ACL2.Tests.IsoGenGate
