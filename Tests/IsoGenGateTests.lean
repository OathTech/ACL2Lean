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

end ACL2.Tests.IsoGenGate
