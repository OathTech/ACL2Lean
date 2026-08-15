/-
  Driver/BranchFacts — the branch-fact COVERAGE rule shared by the
  termination machinery (TP-replay arc increment 7, 2026-08-13).

  Pure `SExpr → Bool` decision content: given the in-scope branch facts,
  is an EMITTED ruling literal established with a demanded truth value?
  No proof terms are produced here — this module is the GATE that decides
  whether an emitted termination obligation applies on the current branch
  (`dischargeDecrease`'s coverage rule); the decrease PROOF itself is
  built elsewhere from the same facts.
-/
import ACL2Lean.Syntax

namespace ACL2.Replay.Driver

open ACL2

/-- `(QUOTE NIL)` — the else-branch of ACL2's AND-normal form. -/
def branchQuoteNil : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)

/-- ACL2's not-consp RECOGNIZER family, viewed as `(base, means-consp?)`:
    `(CONSP b)` is the positive recognizer; `(ATOM b)` is its logical
    negation and `(ENDP b)` the guard-relaxed one (both `(not (consp b))`
    in the logic). Used to compare a demanded literal against a branch
    fact spelled with the opposite recognizer — the RECOGNIZER DUALITY
    that the translated body (`(CONSP b)` tests) needs against ACL2's
    recomputed obligations (`(ENDP b)` / `(ATOM b)` rulers).

    THE ATOM LEG (landed 2026-08-13, the TP-replay arc's finale — it was
    parked at the increment-7 stop because it is a CAPSTONE-FLIPPING
    lever, not a ZIP-class detail): `(ATOM b)` is `(NOT (CONSP b))` by
    ACL2's own definition (`axioms.lisp`: `(defun atom (x) (not (consp
    x)))`), so it joins `ENDP` on the negative side. Enabling it retires
    `dis_pce_total`, clears `total:PERM-COUNTER-EXAMPLE` corpus-wide, and
    re-greens the three `*-IS-ISORT` capstones. -/
def recogView (t : SExpr) : Option (SExpr × Bool) :=
  match t with
  | .cons (.atom (.symbol r)) (.cons b .nil) =>
    if r.name == "CONSP" then some (b, true)
    else if r.name == "ENDP" || r.name == "ATOM" then some (b, false)
    else none
  | _ => none

/-- Is the emitted ruling literal `lit` ESTABLISHED with truth value
    `want` by the in-scope branch `facts` (`(test term, truthy?)`)?

    Four rules, all shape-level and all recursive:
    1. a DIRECT fact on the literal itself;
    2. RECOGNIZER DUALITY (`recogView`): a `(CONSP b)`-truthy fact
       establishes `(ATOM b)`/`(ENDP b)` false and vice versa;
    3. `NOT`: `(NOT u)` is `want` exactly when `u` is `!want`;
    4. ACL2's IF-NORMAL FORMS for the propositional connectives — the
       decomposition rule. ACL2 normalizes `(OR a c)` to `(IF a a c)`
       (test and true-branch THE SAME term — that syntactic coincidence
       is what makes it an or) and `(AND a b)` to `(IF a b 'NIL)`. So:
       - `(IF a a c)` is NIL exactly when BOTH `a` and `c` are NIL, and
         non-NIL as soon as EITHER is;
       - `(IF a b 'NIL)` is non-NIL exactly when BOTH `a` and `b` are
         non-NIL, and NIL as soon as EITHER is.
       Each side is applied recursively, so a nested normal form (ZIP3's
       `(IF (ATOM X) (ATOM X) (IF (ATOM Y) (ATOM Y) (ATOM Z)))`) falls
       out of the recursion rather than a depth-2 special case.
    A general `(IF a b c)` matching NEITHER normal form is not decomposed
    (only rules 1–2 apply to it) — the rule is about ACL2's own boolean
    normal forms, not about `IF` in general.

    ONE-SIDED by construction: every rule is a SUFFICIENT condition, so
    `false` means "not established here", never "refuted". -/
def branchEstablishes (facts : List (SExpr × Bool)) : SExpr → Bool → Bool
  | lit, want =>
    -- 1. direct
    facts.any (fun (f, pos) => f == lit && pos == want)
    -- 2. recognizer duality
    || (match recogView lit with
        | some (b, c) =>
          facts.any (fun (f, pos) =>
            match recogView f with
            | some (b', c') => b' == b && pos == (if c' == c then want else !want)
            | none => false)
        | none => false)
    -- 3/4. the connective decompositions
    || (match lit with
        | .cons (.atom (.symbol n)) (.cons u .nil) =>
          n.name == "NOT" && branchEstablishes facts u (!want)
        | .cons (.atom (.symbol ifS)) (.cons a (.cons b (.cons c .nil))) =>
          if ifS.name != "IF" then false
          else if a == b then
            -- OR-normal form
            if want then
              branchEstablishes facts a true || branchEstablishes facts c true
            else
              branchEstablishes facts a false && branchEstablishes facts c false
          else if c == branchQuoteNil then
            -- AND-normal form
            if want then
              branchEstablishes facts a true && branchEstablishes facts b true
            else
              branchEstablishes facts a false || branchEstablishes facts b false
          else false
        | _ => false)

/-! ### `EQUAL`-alias normalization (T1+2 sprint P3b)

ACL2 emits a defun's `:BODY` NORMALIZED (abbreviations expanded) but
recomputes the ground-zero `:TERMINATION-CLAUSES` from the UNNORMALIZED
body (`gz-termination-clauses` reads `get-unnormalized-bodies`). So an
emitted RULER can be spelled with a definitional alias of `EQUAL` where
the body — and hence the branch fact the admission walk built from it —
says `EQUAL`:

    O<   ruler:  (NOT (= (O-FIRST-COEFF X) (O-FIRST-COEFF Y)))
         fact:   (EQUAL (O-FIRST-COEFF X) (O-FIRST-COEFF Y))
    O-P  ruler:  (EQL '0 (O-FIRST-EXPT X))
         fact:   (EQUAL '0 (O-FIRST-EXPT X))

Seeing that those are the SAME literal is a reading of the WORLD's own
emitted definitions (`(:DEFUN = :FORMALS (X Y) :BODY (EQUAL X Y))`,
likewise `EQL`) — the caller computes the alias set from the world and
passes it in; nothing is assumed about any particular name. Fail-closed
either way: an alias we do not recognize simply leaves the ruler
uncovered and the decrease stays an honest frontier. -/

mutual

/-- Rewrite every application of an `EQUAL` ALIAS to its `EQUAL`
    spelling, recursively. QUOTE bodies are DATA and are never
    descended. -/
partial def normEqualAliases (aliases : List String) : SExpr → SExpr
  | .cons (.atom (.symbol h)) args =>
    if h.name == "QUOTE" then .cons (.atom (.symbol h)) args
    else
      let args' := normEqualAliasesArgs aliases args
      if aliases.contains h.name then
        match args'.toList? with
        | some [a, b] =>
          .cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil))
        | _ => .cons (.atom (.symbol h)) args'
      else .cons (.atom (.symbol h)) args'
  | .cons a b =>
    .cons (normEqualAliases aliases a) (normEqualAliasesArgs aliases b)
  | t => t

/-- The argument-spine walk of `normEqualAliases` (a cons chain, not an
    application — kept separate so a variable in argument position is
    never mistaken for a head). -/
partial def normEqualAliasesArgs (aliases : List String) : SExpr → SExpr
  | .cons a b =>
    .cons (normEqualAliases aliases a) (normEqualAliasesArgs aliases b)
  | t => t

end

/-! ### Pinned shapes (the real emitted rulers this rule was derived from) -/

private def sX : SExpr := .atom (.symbol { name := "X" })
private def sY : SExpr := .atom (.symbol { name := "Y" })
private def sZ : SExpr := .atom (.symbol { name := "Z" })
private def app1 (f : String) (u : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := f })) (.cons u .nil)
private def ifOf (a b c : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons a (.cons b (.cons c .nil)))

/-- ZIP2's emitted ruler (`12-multi-controller`), against the translated
    body's `(CONSP X)`/`(CONSP Y)` branch facts. -/
private def zip2Ruler : SExpr :=
  ifOf (app1 "ATOM" sX) (app1 "ATOM" sX) (app1 "ATOM" sY)
/-- ZIP3's emitted ruler (`16-three-way`) — the same shape, NESTED. -/
private def zip3Ruler : SExpr :=
  ifOf (app1 "ATOM" sX) (app1 "ATOM" sX)
    (ifOf (app1 "ATOM" sY) (app1 "ATOM" sY) (app1 "ATOM" sZ))
private def zipFacts : List (SExpr × Bool) :=
  [(app1 "CONSP" sX, true), (app1 "CONSP" sY, true), (app1 "CONSP" sZ, true)]

-- the or-shape decomposes to its leaves, recursively
-- (these two exercise ATOM leaves against CONSP facts — the ATOM leg)
#guard branchEstablishes zipFacts zip2Ruler false
#guard branchEstablishes zipFacts zip3Ruler false
#guard branchEstablishes
  [(app1 "ENDP" sX, false), (app1 "ENDP" sY, false)]
  (ifOf (app1 "ENDP" sX) (app1 "ENDP" sX) (app1 "ENDP" sY)) false
-- …and only under ALL of them (one leg missing ⇒ not established)
#guard ! branchEstablishes [(app1 "CONSP" sX, true)] zip2Ruler false
#guard ! branchEstablishes zipFacts.dropLast zip3Ruler false
-- the truthy side of the or needs only ONE leg
#guard branchEstablishes [(app1 "ATOM" sY, true)] zip2Ruler true
-- the AND-normal form is the exact dual
#guard branchEstablishes zipFacts
  (ifOf (app1 "ATOM" sX) (app1 "ATOM" sY) branchQuoteNil) false
#guard branchEstablishes [(app1 "CONSP" sX, false), (app1 "CONSP" sY, false)]
  (ifOf (app1 "CONSP" sX) (app1 "CONSP" sY) branchQuoteNil) false
#guard ! branchEstablishes [(app1 "CONSP" sX, true)]
  (ifOf (app1 "ATOM" sX) (app1 "ATOM" sY) branchQuoteNil) true
-- a general `(IF a b c)` (NEITHER normal form) is NOT decomposed
#guard ! branchEstablishes zipFacts
  (ifOf (app1 "ATOM" sX) (app1 "ATOM" sY) (app1 "ATOM" sZ)) false
-- recognizer duality, both directions, all three recognizers
#guard branchEstablishes [(app1 "CONSP" sX, true)] (app1 "ENDP" sX) false
#guard branchEstablishes [(app1 "ENDP" sX, false)] (app1 "CONSP" sX) true
#guard branchEstablishes [(app1 "ATOM" sX, false)] (app1 "CONSP" sX) true
#guard ! branchEstablishes [(app1 "CONSP" sY, true)] (app1 "ATOM" sX) false
-- NOT peels
#guard branchEstablishes [(app1 "CONSP" sX, true)] (app1 "NOT" (app1 "ATOM" sX)) true
#guard branchEstablishes [(app1 "CONSP" sX, true)] (app1 "NOT" (app1 "ENDP" sX)) true

/-! Alias normalization, against `O<`/`O-P`'s real emitted rulers. -/
private def app2 (f : String) (u v : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := f })) (.cons u (.cons v .nil))
private def coeffX : SExpr := app1 "O-FIRST-COEFF" sX
private def coeffY : SExpr := app1 "O-FIRST-COEFF" sY
-- `(NOT (= …))` normalizes to `(NOT (EQUAL …))`; the alias set is the
-- caller's (computed from the world), so an unlisted head is untouched
#guard normEqualAliases ["=", "EQL"] (app1 "NOT" (app2 "=" coeffX coeffY))
  == app1 "NOT" (app2 "EQUAL" coeffX coeffY)
#guard normEqualAliases ["=", "EQL"] (app2 "EQL" branchQuoteNil coeffX)
  == app2 "EQUAL" branchQuoteNil coeffX
#guard normEqualAliases [] (app2 "=" coeffX coeffY) == app2 "=" coeffX coeffY
-- a QUOTE body is DATA — never descended (a quoted `(= …)` stays put)
#guard normEqualAliases ["="]
    (.cons (.atom (.symbol { name := "QUOTE" }))
      (.cons (app2 "=" sX sY) .nil))
  == .cons (.atom (.symbol { name := "QUOTE" }))
      (.cons (app2 "=" sX sY) .nil)
-- a variable in ARGUMENT position is not a head (the spine walk)
#guard normEqualAliases ["="] (app2 "FOO" sX (app2 "=" sX sY))
  == app2 "FOO" sX (app2 "EQUAL" sX sY)
-- …and the normalized ruler is then established by the EQUAL-spelled fact
#guard branchEstablishes [(app2 "EQUAL" coeffX coeffY, true)]
  (normEqualAliases ["=", "EQL"] (app1 "NOT" (app2 "=" coeffX coeffY))) false

end ACL2.Replay.Driver
