/-! # MIRRORS — the basics books (the narrow slice)

The simplest mirror specs, matching the project's earliest ACL2
examples (`simple.lisp`, the 01/02 recon books, the 14-accumulator
book). THE METHOD (Mike, 2026-08-12): get the full mirror route —
spec → refinement relation → replay → theorem — working END-TO-END on
these before prying the aperture wider (sorting adds the order
dimension; this slice has none, so the transfer kit's core is built
on pure structure).

Same rules as `Mirrors/Sorting.lean`: pure idiomatic Lean, ZERO
imports (core prelude only), self-contained vocabulary (our own
`len`/`app`/`rev`/`revAcc` — no library lemma can close mirror
content), properties as named `Prop`s until their proofs arrive via
replay, no `sorry` ever.

Waypoint status at drafting (the metric layer's scoreboard):
MY-LEN-MY-APP green CLEAN (its TP debt retired by the replay route,
TP-replay arc increment 1 2026-08-12), APP-ASSOC green CLEAN — the first
end-to-end target — APP-NIL/REV-APP/REV-REV pending (named
frontiers), LEN-REV-ACC green CLEAN and CATALOGUED `.native` since the
Basics-closeout arc (the accumulator — the template gate's decisive
case; the ALIGNED reading passes the fixed iso template, the
reassociating one is rejected). Three of the six Props are proved
(`len_app`, `app_assoc`, `len_revAcc`); the other three have no
replayed statement to transport yet. -/

namespace ACL2Lean.Basics

universe u
variable {α : Type u}

/-! ## The objects of study (the books' functions, idiomatically) -/

/-- Length (the simple book's `my-len`). -/
def len : List α → Nat
  | [] => 0
  | _ :: t => len t + 1

/-- Append (the books' `my-app`/`app`). -/
def app : List α → List α → List α
  | [], ys => ys
  | a :: t, ys => a :: app t ys

/-- Reverse, append-style (the 02-rev book's `rev`). -/
def rev : List α → List α
  | [] => []
  | a :: t => app (rev t) [a]

/-- Reverse with an accumulator (the 14-accumulator book's `rev-acc` —
    the original narrow-slice example). -/
def revAcc : List α → List α → List α
  | [], acc => acc
  | a :: t, acc => revAcc t (a :: acc)

/-! ## The target properties -/

/-- MY-LEN-MY-APP (`simple.lisp` — the project's first theorem). -/
def len_app (α : Type u) : Prop :=
  ∀ (xs ys : List α), len (app xs ys) = len xs + len ys

/-- APP-ASSOC (the 02-rev book) — the first end-to-end mirror target:
    its waypoint row is already unconditional and clean. -/
def app_assoc (α : Type u) : Prop :=
  ∀ (xs ys zs : List α), app (app xs ys) zs = app xs (app ys zs)

/-- APP-NIL (the 01/02 books; waypoint row pending — the G5
    multi-literal frontier). -/
def app_nil (α : Type u) : Prop :=
  ∀ (xs : List α), app xs [] = xs

/-- REV-APP (the 02-rev book; row pending). -/
def rev_app (α : Type u) : Prop :=
  ∀ (xs ys : List α), rev (app xs ys) = app (rev ys) (rev xs)

/-- REV-REV (the 02-rev book; row pending). -/
def rev_rev (α : Type u) : Prop :=
  ∀ (xs : List α), rev (rev xs) = xs

/-- LEN-REV-ACC (the 14-accumulator book — `def-acc`, the original
    example: the accumulator's length law). -/
def len_revAcc (α : Type u) : Prop :=
  ∀ (xs acc : List α), len (revAcc xs acc) = len xs + len acc

end ACL2Lean.Basics
