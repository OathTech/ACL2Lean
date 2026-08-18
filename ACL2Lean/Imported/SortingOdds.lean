import ACL2Lean.Imported.Sorting

/-! # THE ODDS EXEC KIT + its native reading (R4 wave 2a)

The gap wave 1 recorded behind the `odds` frontier (W9,
`MirrorProofs/Sorting.lean`): `Imported/Sorting.lean` carries
`insertL`/`isortL`/`merge2L`/`evensL`/`msortL` but **no `oddsL`**, and
none could be written, because a native reading is validated through
`derive_sim%` against the book function's EXEC and there was **no ODDS
exec kit** — `oddsBody` exists, but there is no `oddsExec` and no
registration, so `msort_exec_corr` walks the ODDS body inline as
`evensExec (Logic.cdr xv)`.

This module is that kit, plus the reading it makes stateable. `msort`'s
own kit is UNTOUCHED: `msortExec` still walks the ODDS body inline, so
nothing that existed before this module changes route.

WHY A SEPARATE MODULE. `Imported/Sorting.lean` is a grandfathered giant
under the module-size ratchet (`scripts/file-weight-baseline.txt`) and
may only shrink. The two `Symbol` constants below are re-spelled rather
than imported for one reason, recorded so it is not mistaken for
carelessness: the originals are `private` to that module, and
de-privatising them would rename the constants and move every proof term
that mentions them (the regression net's unit is the printed term).
-/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.Sorting

/-- `ODDS`, as the kit generator needs it (see the module note on why
    this is not the `private` original). -/
def odds_symK : Symbol := { package := "ACL2", name := "ODDS" }

/-- `ODDS`'s single formal `L` (see the module note). -/
def odds_formal_l : Symbol := { package := "ACL2", name := "L" }

/-- `odds`'s body as a total Lean function — GENERATED. `ODDS` is
    NON-RECURSIVE (`(EVENS (CDR L))`), so there is no emitted `:MEASURE`
    and no `measured` clause. -/
derive_exec% oddsExec corr odds_exec_corr for odds_symK
  formals [odds_formal_l] body oddsBody

/-- The native reading of ODDS: the odd-position elements, i.e. `evensL`
    of the tail — by OUR OWN pattern match, in our own vocabulary (the
    reading is NOT spelled `evensL xs.tail`: `List.tail` is a library
    function, and `evensL`'s own body carrying it is the logged
    compliance item this module deliberately does not copy). -/
def oddsL : List SExpr → List SExpr
  | [] => []
  | _ :: t => evensL t

/-- The EVENS exec at the EMPTY list — the one bridge the ODDS iso needs,
    and content-free: it is `evensExec_enc` at `[]`, i.e. the generated
    EVENS iso itself, read at one point.

    Why it is needed at all: `ODDS` is `(EVENS (CDR L))`, so at the empty
    list the template's enc-normal form reaches `evensExec (enc [])` and
    then normalises `enc []` to `SExpr.nil` (the kit's own `enc_nil`),
    after which the registered `evensExec_enc` no longer matches
    syntactically. This states the same fact at the normalised spelling. -/
theorem evensExec_nil : evensExec SExpr.nil = SExpr.nil := by
  have h := evensExec_enc []
  simpa only [enc, evensL] using h

/-- Stage 2: `oddsExec` on an encoded list computes `oddsL` —
    GENERATED. The exec is non-recursive, so the structural induction
    supplies only the two shapes the reading itself matches. -/
derive_sim% oddsExec_enc for "ODDS"
  vars (xs : list)
  exec [xs]
  native (enc (oddsL xs))
  simp [oddsL, evensExec_nil]
  induct structural xs

end ACL2.Worlds.Sorting
