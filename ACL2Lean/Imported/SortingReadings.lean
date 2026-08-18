import ACL2Lean.Syntax

/-! # The sorting books' OWN-DEFINITION native readings

A `derive_sim%` NATIVE READING must be an OWN-DEFINITION — its body built
from constructors and our own names, never from library functions (the
vocabulary rule, Mike 2026-08-13; the threat model is in
`Imported/SimGen.lean`). A library-spelled reading is closable by library
lemmas ABOUT THOSE NAMES, which is exactly the channel by which content
that must arrive via replay can arrive from Lean's own library instead —
and it is equally a channel by which a READER mistakes one for the other.

This module is where the readings that had to be converted live (the
exit audit's COMPLIANCE PASS, 2026-08-13: five pre-existing readings were
library-spelled). It is a separate module rather than another block of
`Imported/Sorting.lean` because that file is a grandfathered giant under
the module-size ratchet, and because the remaining conversions belong
together with the first.

Converted so far (ruling 2026-08-14, R1-D):
* HOW-MANY — was `xs.count e`. It surfaced as a residual in a MIRROR
  square (`MirrorProofs/Sorting.lean`'s W2: the closer wanted
  `List.count_cons`, a library lemma about a library reading, which the
  square closer's fixed `rfl`-ladder rightly cannot reach).
* RM — was `xs.erase e` (R4 wave 2d, 2026-08-18). Same surfacing route,
  one book later and load-bearing this time: `rm`'s MIRROR agree square
  is one residual wide against `List.erase`, and that residual is the
  EQUALITY TEST'S ORIENTATION (the book's `RM` tests `(EQUAL E (CAR X))`
  and the mirror renders that faithfully; `List.erase` tests the list
  head first). Both candidate ladder rungs were measured and both
  REGRESS live squares (`MirrorProofs/SortingPermSquares.lean`), so the
  conversion is the route — and it is the one the compliance census
  named.
* PERM — was `xs.isPerm ys` (same wave, FORCED BY THE RM CONVERSION and
  not an independent choice): `List.isPerm`'s own body calls
  `List.erase`, so a `List.isPerm` reading re-introduces the erased
  vocabulary one level down, exactly where `Permuted`'s agree square
  needs it not to be.

Still library-spelled (the compliance pass's remainder): `Imported/
Perm.lean`'s contains reading (`MEMB`) — its mirror square is LIVE
against `List.contains`, whose test IS target-first, so nothing is
blocked on it — and `Imported/Sorting.lean`'s append reading. -/

namespace ACL2.Worlds.Sorting

open ACL2

/-- `how-many`'s native reading: MULTIPLICITY, by our own recursion.

    The shape is the ACL2 body's own — `(if (consp x) (if (equal e (car
    x)) (+ 1 (how-many e (cdr x))) (how-many e (cdr x))) 0)`, with the
    two arms' common summand shared, which is the same rendering the
    mirror spec's `howMany` uses. The `derive_sim%` template (failure =
    hard error) is what checks the reading against the real exec:
    `howManyExec_enc`, `Imported/Sorting.lean`. -/
def howManyL (e : SExpr) : List SExpr → Nat
  | [] => 0
  | a :: t => (if e = a then 1 else 0) + howManyL e t

/-- `rm`'s native reading: REMOVE THE FIRST OCCURRENCE, by our own
    recursion.

    The shape is the ACL2 body's own — `(if (consp x) (if (equal e (car
    x)) (cdr x) (cons (car x) (rm e (cdr x)))) nil)` — and in particular
    the equality test is TARGET-FIRST (`e = a`), as `(EQUAL E (CAR X))`
    is and as the mirror spec's `rm` renders it. That orientation is the
    whole reason this reading exists: `List.erase` tests the list head
    first. The `derive_sim%` template (failure = hard error) is what
    checks the reading against the real exec: `rmExec_enc`,
    `Imported/Perm.lean`. -/
def rmL (e : SExpr) : List SExpr → List SExpr
  | [] => []
  | a :: t => if e = a then t else a :: rmL e t

/-- `perm`'s native reading: the book's `PERM`, by our own recursion —
    every head of the first list occurs in the second, and the tails
    after removal are permutations.

    Own-definition because `List.isPerm`'s BODY calls `List.erase`: a
    library reading here would re-introduce exactly the vocabulary
    `rmL` above exists to avoid. The membership test is still
    `List.contains` — the MEMB reading, which is target-first already
    (`List.elem a xs`) and whose mirror square is live; it is the
    compliance census's remaining entry and nothing is blocked on it.
    Checked against the real exec by `permExec_enc`
    (`Imported/Perm.lean`). -/
def permL : List SExpr → List SExpr → Bool
  | [], [] => true
  | [], _ :: _ => false
  | a :: xs, ys => ys.contains a && permL xs (rmL a ys)

/-! ### The DECODE-KIT BRIDGES for the two converted readings

Same role as `List.isPerm_iff` in the perm waypoint kit (which bridges
the `isPerm` reading to `List.Perm` so consumers can speak the library
notion): these bridge the OWN-DEFINITION readings to the library
functions the pre-conversion statements were written in, so a decode
whose statement does not face a mirror square keeps it. They are
equalities between two computable renderings of the SAME book function,
proved by induction on our own definitions — no book content, and no
new axiom: the content of every native still arrives through the
replayed statement.

**THE GUARD ON THIS ACCEPTANCE (O-6, 2026-08-18 — binding).** The
bridge judgment was accepted with EXACTLY one condition, and it is
this: **`rmL_eq_erase` and `permL_eq_isPerm` must NEVER join the mirror
square closer's fixed kit** (`MirrorProofs/IsoGen.lean`'s ladder), nor
any square's `unfold` list. They are DECODE-LAYER ONLY — a decode
statement that faces no mirror square may keep its library spelling
through them, and that is all they are for.

The reason the acceptance is sound is precisely the closer's PURITY: a
mirror agree square must close against an OWN-DEFINITION reading, so
that no library simp lemma about `List.erase`/`List.isPerm` can close
it. A bridge in the closer's kit would rewrite the own-definition
reading straight back to the library one and re-open the exact channel
the vocabulary rule exists to shut — which would make the conversion
above cosmetic. Keeping them out is what makes it real.

This is a PLACEMENT RULE, not a hardening surface, and it is one grep
away: `grep -rn "rmL_eq_erase\|permL_eq_isPerm" ACL2Lean/MirrorProofs`
must find no CODE — today it finds exactly one PROSE mention, in the
`rm` agree square's record on `MirrorProofs/SortingPermSquares.lean`,
which says this same thing. Reviewed to the honest-mistake standard; do
not grow a gate for it. -/

/-- `permL`'s BASE ARM at an opaque second list — the bridge the
    `derive_sim%` template needs, because the exec's base arm reaches
    `List.isEmpty` through the enc-normal-form kit's own
    `enc_toBool_consp` while the reading matches on the list. Proved by
    `cases … <;> rfl`; it relates one definition's two nil-tests and
    appears in no statement. -/
theorem permL_nil (ys : List SExpr) : permL [] ys = ys.isEmpty := by
  cases ys <;> rfl

/-- DECODE-LAYER ONLY — see THE GUARD above: this must NEVER enter the
    mirror square closer's kit or a square's `unfold` list. -/
theorem rmL_eq_erase (e : SExpr) (xs : List SExpr) : rmL e xs = xs.erase e := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [rmL, List.erase_cons, ih]
    by_cases h : e = a
    · simp [h]
    · rw [if_neg h, if_neg (by simpa using fun hc : a = e => h hc.symm)]

/-- DECODE-LAYER ONLY — see THE GUARD above: this must NEVER enter the
    mirror square closer's kit or a square's `unfold` list. -/
theorem permL_eq_isPerm (xs ys : List SExpr) : permL xs ys = xs.isPerm ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a t ih => rw [permL, List.isPerm, ih, rmL_eq_erase]

end ACL2.Worlds.Sorting
