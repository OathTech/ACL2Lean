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

Still library-spelled (the compliance pass's remainder): `Imported/
Perm.lean`'s contains/erase/isPerm readings and `Imported/Sorting.lean`'s
append reading. -/

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

end ACL2.Worlds.Sorting
