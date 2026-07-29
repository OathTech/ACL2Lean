/-
  ACL2 clause identifiers — the addressing of ACL2's proof tree.

  A clause-id is, in ACL2's own words (type-set-b.lisp, `defrec clause-id`):

      ((forcing-round . pool-lst) case-lst . primes)

  - `forcing-round` : a natural (0 normally; k>0 inside a forcing round).
  - `pool-lst`      : list of positive naturals — the induction nesting
                      (`*1`, `*1.1`, …); a pool/induction goal has case-lst nil.
  - `case-lst`      : list of positive naturals, OR `Dk` symbols for a
                      disjunctive split — the case-split path (`/2`, `/2.3`).
  - `primes`        : a natural — the number of simplification rounds the same
                      clause has been through (`'`, `''`, `'''`, `'4'`, …).

  The printed phrase (`chars-for-tilde-@-clause-id-phrase`, type-set-b.lisp) is:

      [k]?  ( "Goal"  primes
            | "Subgoal " periods(case-lst) primes              -- pool-lst nil
            | "Subgoal *" periods(pool-lst) "/" periods(case-lst) primes )

  where periods(l) joins the elements with ".", and primes(n) is "" | "'" | "''"
  | "'''" | "'" n "'".  This module parses that phrase back into the record.

  The child-id rule (prove.lisp, `waterfall1-lst`) is the inverse we rely on for
  building the tree:
  - a processor leaving ONE clause   → child = parent with primes+1
  - a processor splitting into N      → children = parent with case-lst ++ [k]
    (k counts DOWN from N to 1; so "Subgoal 1" is the LAST split), primes 0
  - `settled-down-clause` / initial   → id unchanged
-/

namespace ACL2

/-- One element of a case-lst: an ordinary case number, or a `Dk` disjunctive
    split marker (carrying its number). -/
inductive CaseElt where
  | num (n : Nat)
  | dis (k : Nat)   -- the symbol `Dk`
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A parsed ACL2 clause identifier. -/
structure ClauseId where
  forcingRound : Nat := 0
  poolLst : List Nat := []
  caseLst : List CaseElt := []
  primes : Nat := 0
  deriving Repr, BEq, Inhabited, DecidableEq

namespace ClauseId

/-- Parse the trailing primes phrase: "" → 0, "'"→1, "''"→2, "'''"→3,
    "'" ++ decimal ++ "'" → that decimal. Hard-fails on anything else. -/
private def parsePrimes (s : String) : Except String Nat :=
  if s.isEmpty then .ok 0
  else if s == "'" then .ok 1
  else if s == "''" then .ok 2
  else if s == "'''" then .ok 3
  else
    let cs := s.toList
    if cs.head? == some '\'' && cs.getLast? == some '\'' && cs.length > 2 then
      match (String.ofList ((cs.drop 1).dropLast)).toNat? with
      | some n => .ok n
      | none => .error s!"ClauseId: bad primes phrase {repr s}"
    else .error s!"ClauseId: bad primes phrase {repr s}"

/-- Split a "<periods><primes>" tail at the first quote: period-list tokens are
    digits / `Dk` (never a quote), and the primes phrase is the only place a
    quote appears, so the first `'` marks the boundary. -/
private def splitPeriodsPrimes (s : String) : String × String :=
  let cs := s.toList
  match cs.findIdx? (· == '\'') with
  | some i => (String.ofList (cs.take i), String.ofList (cs.drop i))
  | none => (s, "")

/-- Parse a periods list element: `Dk` → `.dis k`, otherwise a positive nat. -/
private def parseCaseElt (tok : String) : Except String CaseElt :=
  if tok.startsWith "D" then
    match (tok.drop 1).toNat? with
    | some k => .ok (.dis k)
    | none => .error s!"ClauseId: bad disjunctive case token {repr tok}"
  else match tok.toNat? with
    | some n => .ok (.num n)
    | none => .error s!"ClauseId: bad case token {repr tok}"

/-- Parse a "."-joined list of case elements. Empty string → empty list. -/
private def parseCaseList (s : String) : Except String (List CaseElt) :=
  if s.isEmpty then .ok []
  else (s.splitOn ".").mapM parseCaseElt

/-- Parse a "."-joined list of positive naturals (pool-lst). -/
private def parsePoolList (s : String) : Except String (List Nat) :=
  if s.isEmpty then .ok []
  else (s.splitOn ".").mapM fun tok =>
    match tok.toNat? with
    | some n => .ok n
    | none => .error s!"ClauseId: bad pool token {repr tok}"

/-- Parse a printed clause-id phrase back into a `ClauseId`. Hard-fails (per the
    project's no-silent-skip rule) on anything that is not a well-formed phrase. -/
def parse (s0 : String) : Except String ClauseId := do
  -- Optional "[k]" forcing-round prefix.
  let (fr, s) ←
    if s0.startsWith "[" then
      let cs := s0.toList
      match cs.findIdx? (· == ']') with
      | some i =>
        match (String.ofList ((cs.take i).drop 1)).toNat? with
        | some k => pure (k, String.ofList (cs.drop (i + 1)))
        | none => .error s!"ClauseId: bad forcing-round in {repr s0}"
      | none => .error s!"ClauseId: unterminated [ in {repr s0}"
    else pure (0, s0)
  let afterGoal := String.ofList (s.toList.drop 4)
  -- the primes phrase is either bare primes or ACL2's COUNT CONTRACTION
  -- `'<n>'` (`Goal''''` prints as `Goal'4'` — sorting arc 2026-07-29,
  -- found by the p3 pattern books; `parsePrimes` already decodes it, the
  -- guard here just failed to route it)
  let primesPhrase (t : String) : Bool :=
    t.toList.all (· == '\'') ||
    (t.length > 2 && t.startsWith "'" && t.endsWith "'" &&
     ((t.toList.drop 1).dropLast.all (·.isDigit)))
  if s == "Goal" || (s.startsWith "Goal" && primesPhrase afterGoal) then
    let p ← parsePrimes afterGoal
    return { forcingRound := fr, primes := p }
  else if s.startsWith "Subgoal *" then
    let body := String.ofList (s.toList.drop "Subgoal *".length)
    match body.splitOn "/" with
    | [poolStr, rest] =>
      let pool ← parsePoolList poolStr
      let (caseStr, primeStr) := splitPeriodsPrimes rest
      let cases ← parseCaseList caseStr
      let p ← parsePrimes primeStr
      return { forcingRound := fr, poolLst := pool, caseLst := cases, primes := p }
    | _ => .error s!"ClauseId: expected one '/' in pool subgoal {repr s0}"
  else if s.startsWith "Subgoal " then
    let body := String.ofList (s.toList.drop "Subgoal ".length)
    let (caseStr, primeStr) := splitPeriodsPrimes body
    let cases ← parseCaseList caseStr
    let p ← parsePrimes primeStr
    return { forcingRound := fr, caseLst := cases, primes := p }
  else
    .error s!"ClauseId: unrecognized clause-id phrase {repr s0}"

/-- Is this the root goal of a proof attempt (`Goal`, no pool/case/primes)? -/
def isRoot (id : ClauseId) : Bool :=
  id.poolLst.isEmpty && id.caseLst.isEmpty && id.primes == 0

/-- A pool/induction goal: nonempty pool-lst, empty case-lst, no primes
    (e.g. `*1`, `*1.1`). The root clause an induction was applied to. -/
def isPoolRoot (id : ClauseId) : Bool :=
  !id.poolLst.isEmpty && id.caseLst.isEmpty && id.primes == 0

end ClauseId

/-! ## Tests — parse the real clause-ids that appear in our proof logs. -/
section Tests
open ClauseId

private def p! (s : String) : ClauseId :=
  match parse s with | .ok id => id | .error _ => default

-- Root / simplification rounds
#guard p! "Goal" == ({} : ClauseId)
#guard p! "Goal'" == { primes := 1 }
#guard p! "Goal''" == { primes := 2 }

-- Case splits with no pool (forced/preprocess subgoals)
#guard p! "Subgoal 1" == { caseLst := [.num 1] }
#guard p! "Subgoal 2'" == { caseLst := [.num 2], primes := 1 }
#guard p! "Subgoal 3" == { caseLst := [.num 3] }

-- Induction (pool) goals and their case splits
#guard p! "Subgoal *1/2" == { poolLst := [1], caseLst := [.num 2] }
#guard p! "Subgoal *1/1'" == { poolLst := [1], caseLst := [.num 1], primes := 1 }
#guard p! "Subgoal *1/1''" == { poolLst := [1], caseLst := [.num 1], primes := 2 }
#guard p! "Subgoal *1/1'''" == { poolLst := [1], caseLst := [.num 1], primes := 3 }
-- the ≥4 primes form "'4'"
#guard p! "Subgoal *1/1'4'" == { poolLst := [1], caseLst := [.num 1], primes := 4 }
-- the GOAL-branch twin of the contraction (audit F-D — the crash class
-- the p3 books found): ACL2's printer emits `Goal'4'` for four primes
-- (bare `''''` is NEVER printed — the parser rightly rejects it)
#guard p! "Goal'4'" == { primes := 4 }

-- Nested (sub-)induction: pool-lst with two elements
#guard p! "Subgoal *1.1/1" == { poolLst := [1, 1], caseLst := [.num 1] }
#guard p! "Subgoal *1.1/3" == { poolLst := [1, 1], caseLst := [.num 3] }

-- Classifiers
#guard isRoot (p! "Goal") == true
#guard isRoot (p! "Goal'") == false
#guard isPoolRoot (p! "Subgoal *1/2") == false   -- has a case-lst
#guard isPoolRoot {  poolLst := [1] : ClauseId } == true

-- Forcing-round prefix (constructed; not in current logs but part of the grammar)
#guard p! "[1]Subgoal *1/2" == { forcingRound := 1, poolLst := [1], caseLst := [.num 2] }
#guard p! "[1]Goal" == { forcingRound := 1 }

-- Malformed input hard-fails (no silent skip)
#guard (parse "Lemma 3").toOption.isNone
#guard (parse "Subgoal *1").toOption.isNone   -- pool subgoal must contain '/'

end Tests

end ACL2
