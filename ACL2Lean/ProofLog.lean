import ACL2Lean.ProofLogTypes

namespace ACL2


namespace ProofLog

/-- Look up a keyword in a plist-style s-expression list.
    Given `[:key1, val1, :key2, val2, ...]`, returns `val` for the matching key. -/
private def lookupKeyword (kw : String) : List SExpr → Option SExpr
  | .atom (.keyword k) :: v :: rest =>
    if k == kw then some v else lookupKeyword kw rest
  | _ :: rest => lookupKeyword kw rest
  | [] => none

/-- All (keyword, value) pairs of a plist whose key is NOT in `known` — used to
    capture unmodeled fields verbatim rather than silently dropping them. -/
private def plistExtras (known : List String) : List SExpr → List (String × SExpr)
  | .atom (.keyword k) :: v :: rest =>
    -- keyword names are stored upcased (readtable :upcase); the extra-field
    -- KEYS are internal dispatch tags looked up with lowercase literals
    -- (`.lookup "poolname"` etc.), so canonicalize to lowercase here.
    let k := k.map Char.toLower
    if known.contains k then plistExtras known rest
    else (k, v) :: plistExtras known rest
  | _ :: rest => plistExtras known rest
  | [] => []

/-- Extract a string from a symbol or string atom. -/
private def atomString? : SExpr → Option String
  | .atom (.symbol s) => some s.name
  | .atom (.string s) => some s
  | .atom (.keyword k) => some k
  | _ => none

/-- Parse a single rune like `(:REWRITE CAR-CONS)` — or the multi-rule shape
    `(:REWRITE FLOOR-ZERO . 3)` (J7) — into a `Rune`.
    The rune TYPE (`:REWRITE`/`:DEFINITION`/…) is a fixed keyword-vocabulary
    dispatch tag — we canonicalize it to LOWERCASE at the boundary (analogous
    to `normalizeKey` for theorem-option keys). The rune NAME is an ACL2
    SYMBOL IDENTITY (a theorem/function name — `car-cons`, `perm-symmetric`,
    `my-app`) that must match the same symbol as it is stored elsewhere
    (World keys, theorem names, dependency-proof keys), so it stays UPCASED
    (readtable :upcase) exactly as the parser produced it. A dotted tail that
    is not a nonnegative integer is malformed (fail-closed at the callers). -/
private def parseRune? : SExpr → Option Rune
  | .cons (.atom (.keyword runeType)) (.cons nameExpr tail) =>
    let ty := runeType.map Char.toLower
    let name := match atomString? nameExpr with
      | some name => name
      | none => toString (repr nameExpr)
    match tail with
    | .nil => some { ty, name }
    | .atom (.number (.int k)) =>
      if k ≥ 0 then some { ty, name, idx := some k.toNat } else none
    | _ => none
  | _ => none

/-- Parse a rune list like `((:REWRITE FOO) (:DEFINITION BAR))`. Hard-fails on a
    malformed rune or a non-list (no silent drop). -/
def parseRunes (s : SExpr) : Except String (List Rune) :=
  match s.toList? with
  | some items => items.mapM fun r => match parseRune? r with
    | some rune => pure rune
    | none => throw s!"bad rune in rune list: {repr r}"
  | none => throw s!"rune list is not a list: {repr s}"

/-- Parse one `(bkptr . fn)` frame of a `:PATH`. Numeric `bkptr` → `.arg`; symbolic
    `bkptr` (BODY/RHS/EXPANSION/…) → `.boundary`. Hard-fails on a non-symbol `fn`
    (lambda/quote paths not yet supported) or a malformed pair (no silent drop). -/
private def parsePathFrame (pair : SExpr) : Except String PathFrame := do
  -- Each frame is the dotted pair `(bkptr . fn)` = `.cons bkptr fn`.
  let (bk, fn) ← match pair with
    | .cons bk fn => pure (bk, fn)
    | _ => throw s!"REWRITE-STEP :PATH frame not a (bkptr . fn) pair: {repr pair}"
  match fn with
    | .atom (.symbol s) =>
      match bk with
      | .atom (.number (.int n)) => pure (.arg n.toNat s)
      | .atom (.symbol k) => pure (.boundary k s)
      | _ => throw s!"REWRITE-STEP :PATH frame bkptr not a number/symbol: {repr bk}"
    | .cons (.atom (.symbol lam)) _ =>
      -- a LAMBDA-application frame (S2 2026-07-24): the fn position is the
      -- whole lambda term; only NUMERIC bkptrs are attested (arg descents —
      -- body descents come as `.boundary LAMBDA-BODY <head>` instead)
      if lam.isNamed "LAMBDA" then
        match bk with
        | .atom (.number (.int n)) => pure (.argLam n.toNat fn)
        | _ => throw s!"REWRITE-STEP :PATH lambda frame bkptr not a number \
                        (unattested shape): {repr bk}"
      else
        throw s!"REWRITE-STEP :PATH frame fn not a symbol/lambda: {repr fn}"
    | _ => throw s!"REWRITE-STEP :PATH frame fn not a symbol/lambda \
                    (quote unsupported): {repr fn}"

/-- Parse a single (:REWRITE-STEP :RUNE r :LHS l :RHS r …) s-expression. -/
private def parseRewriteStep? (s : SExpr) : Except String RewriteStep := do
  match s.toList? with
  | some items =>
    match items with
    | .atom (.keyword "REWRITE-STEP") :: rest =>
      let rune ← match lookupKeyword "RUNE" rest with
        | some r => match parseRune? r with
          | some rune => pure rune
          | none => throw s!"REWRITE-STEP: bad :RUNE: {repr r}"
        | none => throw "REWRITE-STEP: missing :RUNE"
      let lhs ← match lookupKeyword "LHS" rest with
        | some s => pure s
        | none => throw "REWRITE-STEP: missing :LHS"
      let rhs ← match lookupKeyword "RHS" rest with
        | some s => pure s
        | none => throw "REWRITE-STEP: missing :RHS"
      -- Optional provenance fields. ABSENT :ORIGIN is normal (older/plain
      -- steps); a PRESENT-but-non-symbol :ORIGIN is a malformed emission and
      -- hard-fails — origin is a primary replay dispatch key, and "" would
      -- route the node down the wrong recipe (fail-closed audit N2).
      let origin ← match lookupKeyword "ORIGIN" rest with
        -- origin is a dispatch tag (e.g. "preprocess/if-iff"); lowercase it.
        | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
        | some other => throw s!"REWRITE-STEP: malformed :ORIGIN {repr other}"
        | none => pure ""
      -- :EQUIV is REQUIRED: the emitter states every step's equivalence
      -- relation explicitly (all 65 push sites emit it; the two IFF-flavored
      -- ones are labeled 'iff). The checker does NO inference — a missing or
      -- malformed :EQUIV is an emission gap and hard-fails (audited 2026-06-10;
      -- the old default-to-"equal" was fail-open).
      let equiv ← match lookupKeyword "EQUIV" rest with
        | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
        | some (.cons a rest') =>
          -- a MULTI-ELEMENT geneqv (S2b option B, 2026-07-25; singletons
          -- emit their :equiv symbol since the 2026-07-26 re-audit): the
          -- emitter cannot summarize a ≥2-relation generated equivalence in
          -- one symbol and emits the verbatim equiv-name list. Parsed
          -- CANONICALLY — "(iff same-len2)" — because a parser hard-fail has
          -- BOOK granularity (it killed six unrelated ordered-perms rows).
          -- Downstream, a compound string is indistinguishable from an
          -- unknown relation name: every equiv reader compares for exact
          -- "equal"/EQUAL (re-audit verified all five). NOTE (re-audit F1):
          -- at COMPOSITE nodes (definition/lambda-body) the equiv gate is
          -- exempted, so a compound-equiv composite is ATTEMPTED — its
          -- obligation is proved-or-fails, never assumed (the exemption
          -- rationale in NodeCore); non-composite steps gate by name.
          -- Non-symbol elements still hard-fail.
          match (SExpr.cons a rest').toList? with
          | some l => do
            let names ← l.mapM fun e => match e with
              | .atom (.symbol s) => pure (s.name.map Char.toLower)
              | other => throw s!"REWRITE-STEP: malformed :EQUIV list element {repr other}"
            pure ("(" ++ String.intercalate " " names ++ ")")
          | none => throw s!"REWRITE-STEP: malformed :EQUIV (improper list) {repr (SExpr.cons a rest')}"
        | some other => throw s!"REWRITE-STEP: malformed :EQUIV {repr other}"
        | none => throw "REWRITE-STEP: missing :EQUIV — the emitter must state \
                         the step's equivalence; the checker does not infer it"
      let runes ← match lookupKeyword "RUNES" rest with
        | some r => match r.toList? with
          | some items => items.mapM fun r => match parseRune? r with
            | some rune => pure rune
            | none => throw s!"REWRITE-STEP: bad rune in :RUNES: {repr r}"
          | none => throw s!"REWRITE-STEP: :RUNES not a list: {repr r}"
        | none => pure []
      -- :PARENTS gates solidify/IH linking; a present-but-non-list value
      -- must hard-fail like :RUNES/:SUBST/:PATH, not default to [] (which
      -- would push a parent-tagged node into the IH-matching path —
      -- fail-closed audit N3).
      let parents ← match lookupKeyword "PARENTS" rest with
        | some r => match r.toList? with
          | some items => pure items
          | none => throw s!"REWRITE-STEP: :PARENTS not a list: {repr r}"
        | none => pure []
      let subst ← match lookupKeyword "SUBST" rest with
        | some r => match r.toList? with
          | some items => items.mapM fun pair =>
            match pair.toList? with
            | some [k, v] => pure (k, v)
            | _ => match pair with  -- dotted pair (k . v) or (k . (v ...))
              | .cons k v => pure (k, v)
              | _ => throw s!"REWRITE-STEP: bad :SUBST pair: {repr pair}"
          | none => throw s!"REWRITE-STEP: :SUBST not a list: {repr r}"
        | none => pure []
      let equivTerm := lookupKeyword "EQUIV-TERM" rest
      let typeSet := parseIntField (lookupKeyword "TYPESET" rest)
      let trueTs := parseIntField (lookupKeyword "TRUETS" rest)
      let falseTs := parseIntField (lookupKeyword "FALSETS" rest)
      -- :LHS-TS/:RHS-TS (R2 fold-in): the EQUAL verdict's two operand
      -- type-sets, read exactly like :TYPESET above.
      let lhsTs := parseIntField (lookupKeyword "LHS-TS" rest)
      let rhsTs := parseIntField (lookupKeyword "RHS-TS" rest)
      -- :STRONGP (item 2): T/NIL; absent (pre-batch logs / non-recognizer
      -- origins) reads none. Any other value is a malformed emission.
      let strongp ← match lookupKeyword "STRONGP" rest with
        | some (.atom (.symbol s)) =>
          if s.name == "T" then pure (some true)
          else throw s!"REWRITE-STEP: malformed :STRONGP {s.name}"
        | some .nil => pure (some false)
        | some other => throw s!"REWRITE-STEP: malformed :STRONGP {repr other}"
        | none => pure none
      let canon1 := lookupKeyword "CANON1" rest
      let canon2 := lookupKeyword "CANON2" rest
      let tauBasis := lookupKeyword "TAU-BASIS" rest
      let taEntry := match lookupKeyword "TA-ENTRY" rest with
        | some .nil => none
        | e => e
      let path ← match lookupKeyword "PATH" rest with
        | some r => match r.toList? with
          | some items => items.mapM parsePathFrame
          | none => throw s!"REWRITE-STEP: :PATH not a list: {repr r}"
        | none => pure []
      -- :SWAPPED-P (fold-back audit V3): T/NIL; absent (pre-fix logs /
      -- non-if origins) reads as NIL. Any other value is a malformed
      -- emission — hard-fail.
      let swapped ← match lookupKeyword "SWAPPED-P" rest with
        | some (.atom (.symbol s)) =>
          if s.name == "T" then pure true
          else throw s!"REWRITE-STEP: malformed :SWAPPED-P {s.name}"
        | some .nil => pure false
        | some other => throw s!"REWRITE-STEP: malformed :SWAPPED-P {repr other}"
        | none => pure false
      let geneqv ← parseSymbolListField "GENEQV" (lookupKeyword "GENEQV" rest)
      let crRune ← parseCrRuneField parseRune? (lookupKeyword "CR-RUNE" rest)
      let argLeaves ← parseArgLeavesField (lookupKeyword "ARG-LEAVES" rest)
      pure { rune, equiv, lhs, rhs, origin, swapped, runes, parents, subst, equivTerm, crRune, typeSet, trueTs, falseTs, strongp, argLeaves, lhsTs, rhsTs, canon1, canon2, taEntry, tauBasis, geneqv, path }
    | _ => throw s!"REWRITE-STEP: expected :REWRITE-STEP keyword, got {repr s}"
  | none => throw s!"REWRITE-STEP: expected list, got {repr s}"

/-- Parse a clausify decision-trace `:PATH` — a list of `(:t . test)` /
    `(:f . test)` conses, outermost-first — into (assumed-true?, test)
    pairs. Hard-fails on any other shape. -/
private def parseClausifyPath (s : SExpr) : Except String (List (Bool × SExpr)) := do
  let some items := s.toList?
    | throw s!"clausify :PATH is not a list: {repr s}"
  items.mapM fun
    | .cons (.atom (.keyword "T")) test => pure (true, test)
    | .cons (.atom (.keyword "F")) test => pure (false, test)
    | e => throw s!"clausify :PATH entry is not (:t/:f . test): {repr e}"

/-- Parse a single trace event from the :REWRITES field. -/
private def parseTraceEvent (s : SExpr) : Except String TraceEvent := do
  match s.toList? with
  | some items =>
    match items with
    | .atom (.keyword "REWRITE-STEP") :: _ =>
        pure (.rewriteStep (← parseRewriteStep? s))
    | .atom (.keyword "IF-TEST-TRUE") :: rest =>
        let test ← lookupKeyword "TEST" rest |>.elim (throw "IF-TEST-TRUE: missing :TEST") pure
        let unrewritten ← lookupKeyword "UNREWRITTEN-TEST" rest
          |>.elim (throw "IF-TEST-TRUE: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.ifTestTrue test unrewritten justification)
    | .atom (.keyword "IF-TEST-FALSE") :: rest =>
        let test ← lookupKeyword "TEST" rest |>.elim (throw "IF-TEST-FALSE: missing :TEST") pure
        let unrewritten ← lookupKeyword "UNREWRITTEN-TEST" rest
          |>.elim (throw "IF-TEST-FALSE: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.ifTestFalse test unrewritten justification)
    | .atom (.keyword "IF-TEST-UNKNOWN") :: rest =>
        let test ← lookupKeyword "TEST" rest |>.elim (throw "IF-TEST-UNKNOWN: missing :TEST") pure
        let unrewritten ← lookupKeyword "UNREWRITTEN-TEST" rest
          |>.elim (throw "IF-TEST-UNKNOWN: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.ifTestUnknown test unrewritten justification)
    | .atom (.keyword "BEGIN-LITERAL") :: rest =>
        let index ← match lookupKeyword "INDEX" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"BEGIN-LITERAL: bad :INDEX: {repr s}"
          | none => throw "BEGIN-LITERAL: missing :INDEX"
        let literal ← lookupKeyword "LITERAL" rest
          |>.elim (throw "BEGIN-LITERAL: missing :LITERAL") pure
        let notFlg := match lookupKeyword "NOT-FLG" rest with
          | some .nil => false
          | _ => true
        pure (.beginLiteral index literal notFlg)
    | .atom (.keyword "END-LITERAL") :: rest =>
        let index ← match lookupKeyword "INDEX" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"END-LITERAL: bad :INDEX: {repr s}"
          | none => throw "END-LITERAL: missing :INDEX"
        let result ← lookupKeyword "RESULT" rest
          |>.elim (throw "END-LITERAL: missing :RESULT") pure
        let branches ← match lookupKeyword "BRANCHES" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"END-LITERAL: bad :BRANCHES: {repr s}"
          | none => throw "END-LITERAL: missing :BRANCHES"
        pure (.endLiteral index result branches)
    | .atom (.keyword "REWRITTEN-LITERAL") :: rest =>
        let original ← lookupKeyword "ORIGINAL" rest
          |>.elim (throw "REWRITTEN-LITERAL: missing :ORIGINAL") pure
        let result ← lookupKeyword "RESULT" rest
          |>.elim (throw "REWRITTEN-LITERAL: missing :RESULT") pure
        pure (.rewrittenLiteral original result)
    | .atom (.keyword "BEGIN-BRANCH") :: rest =>
        let segment := (lookupKeyword "SEGMENT" rest).getD .nil
        pure (.beginBranch segment)
    | .atom (.keyword "END-BRANCH") :: _ =>
        pure .endBranch
    | .atom (.keyword "CASE-SPLIT") :: rest =>
        let litIdx ← match lookupKeyword "LITERAL-INDEX" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"CASE-SPLIT: bad :LITERAL-INDEX: {repr s}"
          | none => throw "CASE-SPLIT: missing :LITERAL-INDEX"
        let numBranches ← match lookupKeyword "NUM-BRANCHES" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"CASE-SPLIT: bad :NUM-BRANCHES: {repr s}"
          | none => throw "CASE-SPLIT: missing :NUM-BRANCHES"
        pure (.caseSplit litIdx numBranches)
    | .atom (.keyword "BRANCH-SUBSTITUTION") :: rest =>
        let equivalence ← lookupKeyword "EQUIVALENCE" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :EQUIVALENCE") pure
        let lhs ← lookupKeyword "LHS" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :LHS") pure
        let rhs ← lookupKeyword "RHS" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :RHS") pure
        pure (.branchSubstitution equivalence lhs rhs)
    | .atom (.keyword "CONTEXT-SUBST") :: rest =>
        let var ← lookupKeyword "VARIABLE" rest
          |>.elim (throw "CONTEXT-SUBST: missing :VARIABLE") pure
        let value ← lookupKeyword "VALUE" rest
          |>.elim (throw "CONTEXT-SUBST: missing :VALUE") pure
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.contextSubst var value justification)
    | .atom (.keyword "HYP-RELIEF") :: rest =>
        let hyp ← lookupKeyword "HYP" rest
          |>.elim (throw "HYP-RELIEF: missing :HYP") pure
        let origin ← match lookupKeyword "ORIGIN" rest with
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"HYP-RELIEF: bad :ORIGIN: {repr s}"
          | none => throw "HYP-RELIEF: missing :ORIGIN"
        -- :TA-RUNES (optional; free-type-alist markers only): the matched
        -- type-alist ENTRY's ttree runes — a DERIVED entry's provenance
        -- (e.g. forward-chaining LEXORDER-TOTAL; emission arc 2026-07-21)
        let taRunes ← match lookupKeyword "TA-RUNES" rest with
          | none => pure []
          | some rs =>
            match rs.toList? with
            | none => throw s!"HYP-RELIEF: :TA-RUNES not a list: {repr rs}"
            | some l => l.mapM fun r =>
                match parseRune? r with
                | some rn => pure rn
                | none => throw s!"HYP-RELIEF: bad :TA-RUNES rune: {repr r}"
        -- :PARENTS (optional; known-true markers, S1 2026-07-23): the
        -- verdict ttree's 'pt tags — the clause literals the type-set
        -- derivation descended from (same convention as REWRITE-STEP)
        let parents ← match lookupKeyword "PARENTS" rest with
          | none => pure []
          | some r =>
            match r.toList? with
            | none => throw s!"HYP-RELIEF: :PARENTS not a list: {repr r}"
            | some l => pure l
        -- :TA-DERIVATIONS (cluster item 4): raw derivation plists; NIL at
        -- today's relief sites (fcds expunged upstream — the clause-level
        -- :FC-DERIVATIONS event carries the real provenance)
        let taDerivs ← match lookupKeyword "TA-DERIVATIONS" rest with
          | none => pure []
          | some (.atom (.symbol s)) =>
            if s.name == "NIL" then pure []
            else throw s!"HYP-RELIEF: bad :TA-DERIVATIONS atom: {s.name}"
          | some r =>
            match r.toList? with
            | none => throw s!"HYP-RELIEF: :TA-DERIVATIONS not a list: {repr r}"
            | some l => pure l
        pure (.hypRelief hyp origin taRunes parents taDerivs)
    | .atom (.keyword "FC-DERIVATIONS") :: rest =>
        -- cluster item 4: the clause's approved fc derivations, raw plists
        let derivs ← match lookupKeyword "DERIVATIONS" rest with
          | some d => match d.toList? with
            | some l => pure l
            | none => throw s!"FC-DERIVATIONS: :DERIVATIONS not a list: {repr d}"
          | none => throw "FC-DERIVATIONS: missing :DERIVATIONS"
        pure (.fcDerivations derivs)
    | .atom (.keyword "CLAUSIFY-TEST") :: rest =>
        let test ← lookupKeyword "TEST" rest
          |>.elim (throw "CLAUSIFY-TEST: missing :TEST") pure
        -- VERDICT/HOW are internal dispatch tags (true/false, assumed/…),
        -- not symbol-identity values — lowercase at the boundary.
        let verdict ← match lookupKeyword "VERDICT" rest with
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-TEST: bad :VERDICT: {repr s}"
          | none => throw "CLAUSIFY-TEST: missing :VERDICT"
        let how ← match lookupKeyword "HOW" rest with
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-TEST: bad :HOW: {repr s}"
          | none => throw "CLAUSIFY-TEST: missing :HOW"
        let path ← parseClausifyPath ((lookupKeyword "PATH" rest).getD .nil)
        pure (.clausifyTest test verdict how path)
    | .atom (.keyword "CLAUSIFY-LEAF") :: rest =>
        let value ← lookupKeyword "VALUE" rest
          |>.elim (throw "CLAUSIFY-LEAF: missing :VALUE") pure
        let outcome ← match lookupKeyword "OUTCOME" rest with
          -- OUTCOME is an internal dispatch tag (segment-open/segment-false/
          -- dropped), not a symbol-identity value — lowercase at the boundary.
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-LEAF: bad :OUTCOME: {repr s}"
          | none => throw "CLAUSIFY-LEAF: missing :OUTCOME"
        let path ← parseClausifyPath ((lookupKeyword "PATH" rest).getD .nil)
        -- :SEGMENT — required for the two segment outcomes, forbidden for
        -- dropped (the emitter writes it exactly there; no leniency drift)
        let segment ← match lookupKeyword "SEGMENT" rest, outcome with
          | some s, "segment-false" | some s, "segment-open" =>
            match s.toList? with
            | some l => pure (some l)
            | none => throw s!"CLAUSIFY-LEAF: :SEGMENT is not a list: {repr s}"
          | none, "dropped" => pure none
          | none, o => throw s!"CLAUSIFY-LEAF: {o} outcome without :SEGMENT \
                                (stale log? recapture-all)"
          | some _, o => throw s!"CLAUSIFY-LEAF: unexpected :SEGMENT on a \
                                  {o} leaf"
        pure (.clausifyLeaf value outcome path segment)
    | .atom (.keyword "CLAUSIFY-CONJUNCTION") :: rest =>
        let l ← lookupKeyword "LEFT" rest
          |>.elim (throw "CLAUSIFY-CONJUNCTION: missing :LEFT") pure
        let r ← lookupKeyword "RIGHT" rest
          |>.elim (throw "CLAUSIFY-CONJUNCTION: missing :RIGHT") pure
        pure (.clausifyConjunction l r)
    | .atom (.keyword "CLAUSIFY-SATRIANI") :: rest =>
        let which ← match lookupKeyword "WHICH" rest with
          -- WHICH is an internal dispatch tag, not a symbol-identity value.
          | some (.atom (.symbol s)) => pure (s.name.map Char.toLower)
          | some s => throw s!"CLAUSIFY-SATRIANI: bad :WHICH: {repr s}"
          | none => throw "CLAUSIFY-SATRIANI: missing :WHICH"
        pure (.clausifySetReshaped s!"satriani-{which}")
    | .atom (.keyword "CLAUSIFY-SUBSUMPTION-LOOP") :: _ =>
        pure (.clausifySetReshaped "subsumption-loop")
    | .atom (.keyword "TYPE-SET-REASONING") :: rest =>
        let term ← lookupKeyword "TERM" rest
          |>.elim (throw "TYPE-SET-REASONING: missing :TERM") pure
        let result ← lookupKeyword "RESULT" rest
          |>.elim (throw "TYPE-SET-REASONING: missing :RESULT") pure
        let notFlg := match lookupKeyword "NOT-FLG" rest with
          | some .nil => false
          | _ => true
        let justification := (lookupKeyword "JUSTIFICATION" rest).getD .nil
        pure (.typeSetReasoning term result notFlg justification)
    | .atom (.keyword "BEGIN-INNER-REWRITE") :: rest =>
        -- KIND is an internal dispatch tag (hyp/rhs/…), not a symbol-identity
        -- value — lowercase at the boundary. :TERM (path-emission Phase 1) is
        -- the window's INSTANTIATED input term (a two-term LIST for the
        -- equal-cars/equal-cdrs component windows) — the window-local :PATH
        -- anchor. Mandatory on the windowed kinds; hyp windows carry none.
        let kind := match lookupKeyword "KIND" rest with
          | some (.atom (.symbol s)) => s.name.map Char.toLower
          | some (.atom (.keyword k)) => k.map Char.toLower
          | _ => "unknown"
        let term := lookupKeyword "TERM" rest
        if term.isNone &&
            ["rhs", "body", "lambda-body", "expansion", "rewritten-body",
             "if-left", "if-right", "equal-cars", "equal-cdrs"].contains kind then
          throw s!"BEGIN-INNER-REWRITE kind {kind}: missing :TERM (windowed             kinds carry their input term — pre-Phase-1 log? recapture)"
        -- :PATH (if/equal windows): the window's position in the ENCLOSING
        -- window's coordinates, logged at entry — the inline-window lift
        -- anchor. Absent on the macro-emitted kinds (their windows are
        -- pre-adopted children located by the adopting node's own path).
        let path ← match lookupKeyword "PATH" rest with
          | none => pure []
          | some .nil => pure []
          | some p => match p.toList? with
            | some items => items.mapM parsePathFrame
            | none => throw s!"BEGIN-INNER-REWRITE :PATH not a list: {repr p}"
        -- :SWAPPED-P (fold-back audit V3): T only on if-left/if-right windows
        -- of a swap-normalized rewrite-if — the KIND names the POST-swap
        -- branch (if-left = source argument 3 under the swap). Absent on the
        -- macro-emitted kinds; hard-fail on any value other than T/NIL.
        let swapped ← match lookupKeyword "SWAPPED-P" rest with
          | some (.atom (.symbol s)) =>
            if s.name == "T" then pure true
            else throw s!"BEGIN-INNER-REWRITE: malformed :SWAPPED-P {s.name}"
          | some .nil => pure false
          | some other => throw s!"BEGIN-INNER-REWRITE: malformed :SWAPPED-P {repr other}"
          | none => pure false
        pure (.beginInnerRewrite kind swapped term path)
    | .atom (.keyword "END-INNER-REWRITE") :: rest =>
        -- KIND is an internal dispatch tag (hyp/rhs/…), not a symbol-identity
        -- value — lowercase at the boundary.
        let kind := match lookupKeyword "KIND" rest with
          | some (.atom (.symbol s)) => s.name.map Char.toLower
          | some (.atom (.keyword k)) => k.map Char.toLower
          | _ => "unknown"
        pure (.endInnerRewrite kind)
    | .atom (.keyword "BEGIN-IF-REWRITE") :: rest =>
        let test ← lookupKeyword "TEST" rest
          |>.elim (throw "BEGIN-IF-REWRITE: missing :TEST") pure
        let unrewrittenTest := (lookupKeyword "UNREWRITTEN-TEST" rest).getD .nil
        pure (.beginIfRewrite test unrewrittenTest)
    | .atom (.keyword "END-IF-REWRITE") :: rest =>
        let test ← lookupKeyword "TEST" rest
          |>.elim (throw "END-IF-REWRITE: missing :TEST") pure
        let result := (lookupKeyword "RESULT" rest).getD .nil
        pure (.endIfRewrite test result)
    | .atom (.keyword "USE-HINT") :: rest =>
        let hyps ← match lookupKeyword "HYPS" rest with
          | some h => match h.toList? with
            | some l => pure l
            | none => throw s!"USE-HINT: :HYPS not a list: {repr h}"
          | none => throw "USE-HINT: missing :HYPS"
        let ccl ← match lookupKeyword "CONSTRAINT-CL" rest with
          | some c => match c.toList? with
            | some l => pure l
            | none => throw s!"USE-HINT: :CONSTRAINT-CL not a list: {repr c}"
          | none => throw "USE-HINT: missing :CONSTRAINT-CL"
        let appC ← match lookupKeyword "APPLICATION-CLAUSES" rest with
          | some a => match a.toList? with
            | some cls => cls.mapM fun c => match c.toList? with
              | some lits => pure lits
              | none => throw s!"USE-HINT: application clause not a list: {repr c}"
            | none => throw s!"USE-HINT: :APPLICATION-CLAUSES not a list: {repr a}"
          | none => throw "USE-HINT: missing :APPLICATION-CLAUSES"
        -- :LMI-LST (cluster item 1): absent on pre-cluster logs (parse
        -- tolerates absence; consumers hard-fail), MALFORMED hard-fails
        let lmis ← match lookupKeyword "LMI-LST" rest with
          | some l => match l.toList? with
            | some ls => pure ls
            | none => throw s!"USE-HINT: :LMI-LST not a list: {repr l}"
          | none => pure []
        pure (.useHint hyps ccl appC lmis)
    | .atom (.keyword "CLAUSIFY-INPUT") :: rest =>
        let term ← lookupKeyword "TERM" rest
          |>.elim (throw "CLAUSIFY-INPUT: missing :TERM") pure
        pure (.clausifyInput term)
    | .atom (.keyword "CLAUSIFY-NEG") :: rest =>
        let cl ← lookupKeyword "CLAUSE" rest
          |>.elim (throw "CLAUSIFY-NEG: missing :CLAUSE") pure
        match cl.toList? with
        | some lits => pure (.clausifyNeg lits)
        | none => throw s!"CLAUSIFY-NEG: clause is not a proper list: {repr cl}"
    | .atom (.keyword "CLAUSIFY-SPLIT") :: rest =>
        let lit ← lookupKeyword "LIT" rest
          |>.elim (throw "CLAUSIFY-SPLIT: missing :LIT") pure
        let cl ← lookupKeyword "CLAUSE" rest
          |>.elim (throw "CLAUSIFY-SPLIT: missing :CLAUSE") pure
        match cl.toList? with
        | some lits => pure (.clausifySplit lit lits)
        | none => throw s!"CLAUSIFY-SPLIT: clause is not a proper list: {repr cl}"
    | .atom (.keyword "CLAUSIFY-OUT") :: rest =>
        let cls ← lookupKeyword "CLAUSES" rest
          |>.elim (throw "CLAUSIFY-OUT: missing :CLAUSES") pure
        match cls.toList? with
        | some clList =>
          let parsed ← clList.mapM fun c =>
            match c.toList? with
            | some lits => pure lits
            | none => throw s!"CLAUSIFY-OUT: clause is not a proper list: {repr c}"
          pure (.clausifyOut parsed)
        | none => throw s!"CLAUSIFY-OUT: clauses is not a proper list: {repr cls}"
    | .atom (.keyword "CLAUSIFY-EXPAND") :: rest =>
        let toTerm ← lookupKeyword "TO" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :TO") pure
        let fromTerm ← lookupKeyword "FROM" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :FROM (stale log — \
                          recapture with the S1 fork)") pure
        let boolS ← lookupKeyword "BOOL" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :BOOL") pure
        let pos ← if boolS == SExpr.t then pure true
          else if boolS == SExpr.nil then pure false
          else throw s!"CLAUSIFY-EXPAND: :BOOL {repr boolS} is neither T nor NIL"
        let runesS ← lookupKeyword "RUNES" rest
          |>.elim (throw "CLAUSIFY-EXPAND: missing :RUNES (stale log — \
                          recapture with the S1 fork)") pure
        let some runeList := runesS.toList?
          | throw s!"CLAUSIFY-EXPAND: :RUNES not a list: {repr runesS}"
        let runes ← runeList.mapM fun r =>
          (parseRune? r).elim
            (throw s!"CLAUSIFY-EXPAND: bad rune {repr r}") pure
        pure (.clausifyExpand fromTerm toTerm pos runes)
    | .atom (.keyword "COMPLEMENT-CLOSE") :: rest =>
        -- fork-batch item 7: the add-literal complement close.
        let lit ← lookupKeyword "LIT" rest
          |>.elim (throw "COMPLEMENT-CLOSE: missing :LIT") pure
        pure (.complementClose lit)
    | .atom (.keyword "DEDUP-DROP") :: rest =>
        -- fork-batch item E: the add-literal duplicate drop.
        let lit ← lookupKeyword "LIT" rest
          |>.elim (throw "DEDUP-DROP: missing :LIT") pure
        pure (.dedupDrop lit)
    | .atom (.keyword "TA-SUBST") :: rest =>
        let new_ ← lookupKeyword "NEW" rest
          |>.elim (throw "TA-SUBST: missing :NEW") pure
        let from_ ← lookupKeyword "FROM" rest
          |>.elim (throw "TA-SUBST: missing :FROM") pure
        let ts ← match lookupKeyword "TS" rest with
          | some (.atom (.number (.int n))) => pure n
          | some other => throw s!"TA-SUBST: bad :TS {repr other}"
          | none => throw "TA-SUBST: missing :TS"
        let substNew ← lookupKeyword "SUBST-NEW" rest
          |>.elim (throw "TA-SUBST: missing :SUBST-NEW") pure
        let substOld ← lookupKeyword "SUBST-OLD" rest
          |>.elim (throw "TA-SUBST: missing :SUBST-OLD") pure
        pure (.taSubst new_ from_ ts substNew substOld)
    | _ => throw s!"Unknown trace event: {repr s}"
  | none => throw s!"Expected list trace event, got: {repr s}"

/-- Parse a list of trace events from the :REWRITES field. -/
private def parseTraceEvents (s : SExpr) : Except String (List TraceEvent) := do
  match s.toList? with
  | some items =>
    let mut result := #[]
    for item in items do
      result := result.push (← parseTraceEvent item)
    pure result.toList
  | none => throw s!"REWRITES: expected list, got {repr s}"

/-- Parse a (:STEP ...) s-expression. -/
private def parseStep? (items : List SExpr) : Except String ProofStep := do
  let clauseId ← match lookupKeyword "CLAUSEID" items with
    | some s => match atomString? s with
      | some str => pure str
      | none => throw s!"STEP: bad :CLAUSE-ID value: {repr s}"
    | none => throw "STEP: missing :CLAUSE-ID"
  let processor ← match lookupKeyword "PROCESSOR" items with
    -- processor is a dispatch tag (compared against lowercase literals like
    -- "push-clause"/"preprocess"); lowercase at the boundary (names are upcased).
    | some s => match atomString? s with
      | some str => pure (str.map Char.toLower)
      | none => throw s!"STEP: bad :PROCESSOR value: {repr s}"
    | none => throw "STEP: missing :PROCESSOR"
  let result ← match lookupKeyword "RESULT" items with
    | some (.atom (.keyword "PROVED")) => pure ProofResult.proved
    | some (.atom (.keyword "SUBGOALS")) => pure ProofResult.subgoals
    | some s => throw s!"STEP: bad :RESULT value: {repr s}"
    | none => throw "STEP: missing :RESULT"
  let runes ← match lookupKeyword "RUNES" items with
    | some s => parseRunes s
    | none => pure []
  let traceEvents ← match lookupKeyword "REWRITES" items with
    | some s => parseTraceEvents s
    | none => pure []
  let inputClause ← match lookupKeyword "INPUTCLAUSE" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"STEP: :INPUTCLAUSE is not a list: {repr s}"
    | none => pure []
  let newClauses ← match lookupKeyword "NEWCLAUSES" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"STEP: :NEWCLAUSES is not a list: {repr s}"
    | none => pure []
  let extraFields := plistExtras
    ["clauseid", "processor", "result", "runes", "rewrites", "inputclause", "newclauses"] items
  pure { clauseId, processor, result, runes, traceEvents, inputClause, newClauses, extraFields }

/-- Parse a pool-lst `(1 1 1)` (naturals). -/
private def parsePoolLst (s : SExpr) : Except String (List Nat) := do
  match s.toList? with
  | some items => items.mapM fun i => match i with
      | .atom (.number (.int n)) =>
        if n ≥ 0 then pure n.toNat
        else throw s!"pool-lst entry negative: {repr i}"
      | _ => throw s!"pool-lst entry not a natural: {repr i}"
  | none => throw s!"pool-lst not a list: {repr s}"

/-- Parse one IH substitution alist `((var . term) …)`. ACL2 prints a pair `(v . t)` as
    `(v . t)` or, when `t` is a list, as `(v t…)` — both are `.cons (symbol v) t`. -/
private def parseAlist (s : SExpr) : Except String (List (Symbol × SExpr)) := do
  match s.toList? with
  | some pairs => pairs.mapM fun p => match p with
      | .cons (.atom (.symbol v)) term => pure (v, term)
      | _ => throw s!"INDUCTION :ALISTS: bad pair (expected (var . term)): {repr p}"
  | none => throw s!"INDUCTION :ALISTS: alist not a list: {repr s}"

/-- Parse one `(:TESTS (test…) :ALISTS (alist…))` induction case. -/
private def parseCase (s : SExpr) : Except String InductionCase := do
  match s.toList? with
  | some items =>
    let tests ← match lookupKeyword "TESTS" items with
      | some t => t.toList?.elim (throw s!"INDUCTION case :TESTS not a list: {repr t}") pure
      | none => pure []
    let alists ← match lookupKeyword "ALISTS" items with
      | some a => match a.toList? with
        | some als => als.mapM parseAlist
        | none => throw s!"INDUCTION case :ALISTS not a list: {repr a}"
      | none => pure []
    pure { tests, alists }
  | none => throw s!"INDUCTION case not a plist: {repr s}"

/-- Parse a (:INDUCTION ...) s-expression. The measure-justification fields
    (:XTERM/:MEASURE/:REL/:MP/:SUBSET/:CASES) are optional — absent in legacy logs. -/
private def parseInduction? (items : List SExpr) : Except String InductionStep := do
  let term ← match lookupKeyword "TERM" items with
    | some s => pure s
    | none => throw "INDUCTION: missing :TERM"
  let subgoalCount ← match lookupKeyword "SUBGOALS" items with
    | some (.atom (.number (.int n))) => pure n.toNat
    | some s => throw s!"INDUCTION: bad :SUBGOALS: {repr s}"
    | none => throw "INDUCTION: missing :SUBGOALS"
  let scheme ← match lookupKeyword "SCHEME" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"INDUCTION: :SCHEME is not a list: {repr s}"
    | none => pure []
  let xterm := (lookupKeyword "XTERM" items).getD .nil
  let measure := (lookupKeyword "MEASURE" items).getD .nil
  let rel := (lookupKeyword "REL" items).getD .nil
  let mp := (lookupKeyword "MP" items).getD .nil
  let controllers ← match lookupKeyword "CONTROLLERS" items with
    | some s => match s.toList? with
      | some xs => xs.mapM fun x => match x with
        | .atom (.symbol v) => pure v
        | _ => throw s!"INDUCTION: :CONTROLLERS non-symbol element: {repr x}"
      | none => throw s!"INDUCTION: :CONTROLLERS not a list: {repr s}"
    | none => pure []
  let cases ← match lookupKeyword "CASES" items with
    | some c => match c.toList? with
      | some cs => cs.mapM parseCase
      | none => throw s!"INDUCTION: :CASES not a list: {repr c}"
    | none => pure []
  -- REQUIRED whenever :SCHEME is present (same emitter, emission arc audit
  -- 2026-07-22): a missing key means a stale pre-audit log — recapture
  let schemeDropped ← match lookupKeyword "SCHEME-DROPPED" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"INDUCTION: :SCHEME-DROPPED is not a list: {repr s}"
    | none =>
      if scheme.isEmpty then pure []
      else throw "INDUCTION: missing :SCHEME-DROPPED (stale log? recapture-all)"
  pure { term, subgoalCount, scheme, xterm, measure, rel, mp, controllers, cases,
         schemeDropped }

/-- Parse one stored-rule entry: `(rune hyps equiv lhs rhs)` for the
    capture-time `(:RULES …)` events (`withMatchFree = false`), or
    `(rune hyps equiv lhs rhs match-free)` for ground-zero rule snapshots
    (`withMatchFree = true`; match-free is `:ALL`/`:ONCE`/`NIL`). The two
    arities are exact — a mismatched entry hard-fails. -/
private def parseFcRuleSpecEntry (e : SExpr) : Except String FcRuleSpec := do
  let some items := e.toList?
    | throw s!"GROUND-ZERO-FC-RULES: bad entry (not a list): {repr e}"
  let [runeS, triggerS, hypsS, conclsS, mfS] := items
    | throw s!"GROUND-ZERO-FC-RULES: bad entry (want (rune trigger hyps \
              concls match-free)): {repr e}"
  let some rune := parseRune? runeS
    | throw s!"GROUND-ZERO-FC-RULES: bad rune: {repr runeS}"
  unless rune.ty == "forward-chaining" do
    throw s!"GROUND-ZERO-FC-RULES: rune class {rune.ty} unexpected"
  let hyps ← hypsS.toList?.elim
    (throw s!"GROUND-ZERO-FC-RULES {rune.name}: :HYPS not a list: {repr hypsS}") pure
  let concls ← conclsS.toList?.elim
    (throw s!"GROUND-ZERO-FC-RULES {rune.name}: :CONCLS not a list: {repr conclsS}") pure
  let matchFree ← match mfS with
    | .nil => pure none
    | .atom (.keyword k) => pure (some (k.map Char.toLower))
    | other => throw s!"GROUND-ZERO-FC-RULES {rune.name}: bad match-free: {repr other}"
  return { name := rune.name, trigger := triggerS, hyps, concls, matchFree }

/-- One `(:GROUND-ZERO-LINEAR-RULES …)` entry: `(rune hyps concl max-term)`
    — the stored `linear-lemma` fields; exact arity, hard-fail otherwise. -/
private def parseLinearRuleSpecEntry (e : SExpr) :
    Except String LinearRuleSpec := do
  let some items := e.toList?
    | throw s!"GROUND-ZERO-LINEAR-RULES: bad entry (not a list): {repr e}"
  let [runeS, hypsS, conclS, maxTermS] := items
    | throw s!"GROUND-ZERO-LINEAR-RULES: bad entry (want (rune hyps concl \
              max-term)): {repr e}"
  let some rune := parseRune? runeS
    | throw s!"GROUND-ZERO-LINEAR-RULES: bad rune: {repr runeS}"
  unless rune.ty == "linear" do
    throw s!"GROUND-ZERO-LINEAR-RULES: rune class {rune.ty} unexpected"
  let hyps ← hypsS.toList?.elim
    (throw s!"GROUND-ZERO-LINEAR-RULES {rune.name}: :HYPS not a list: \
      {repr hypsS}") pure
  return { name := rune.name, hyps, concl := conclS, maxTerm := maxTermS }

private def parseRecognizerTupleEntry (e : SExpr) :
    Except String RecognizerTupleSpec := do
  let some items := e.toList?
    | throw s!"GROUND-ZERO-RECOGNIZER-TUPLES: bad entry (not a list): \
        {repr e}"
  let [fnS, runeS, trueTsS, falseTsS, strongpS] := items
    | throw s!"GROUND-ZERO-RECOGNIZER-TUPLES: bad entry (want (fn rune \
              true-ts false-ts strongp)): {repr e}"
  let some fn := atomString? fnS
    | throw s!"GROUND-ZERO-RECOGNIZER-TUPLES: bad fn: {repr fnS}"
  let some rune := parseRune? runeS
    | throw s!"GROUND-ZERO-RECOGNIZER-TUPLES: bad rune: {repr runeS}"
  let .atom (.number (.int trueTs)) := trueTsS
    | throw s!"GROUND-ZERO-RECOGNIZER-TUPLES {fn}: true-ts not an int: \
        {repr trueTsS}"
  let .atom (.number (.int falseTs)) := falseTsS
    | throw s!"GROUND-ZERO-RECOGNIZER-TUPLES {fn}: false-ts not an int: \
        {repr falseTsS}"
  let strongp ← match strongpS with
    | .atom (.symbol s) =>
      if s.name == "T" then pure true
      else throw s!"GROUND-ZERO-RECOGNIZER-TUPLES {fn}: bad strongp: \
        {repr strongpS}"
    | .nil => pure false
    | _ => throw s!"GROUND-ZERO-RECOGNIZER-TUPLES {fn}: bad strongp: \
        {repr strongpS}"
  return { fn, rune, trueTs, falseTs, strongp }

private def parseRuleSpecEntry (ctx : String) (withMatchFree : Bool)
    (e : SExpr) : Except String RuleSpec := do
  let some items := e.toList?
    | throw s!"{ctx}: bad entry (not a list): {repr e}"
  -- capture-time entries carry the rule's backchain-limit-lst as a 6th
  -- element (emit/rule, S1.2 2026-07-23 — previously OMITTED, the
  -- cov-backchain-limit emission pin); gz snapshots carry match-free instead
  -- (their limit emission is a tracked follow-up).
  let (runeS, hypsS, equivS, lhsS, rhsS, mf?, bclS) ←
    match withMatchFree, items with
    | false, [r, h, q, l, rh, bcl] => pure (r, h, q, l, rh, none, bcl)
    | true, [r, h, q, l, rh, mf] => pure (r, h, q, l, rh, some mf, SExpr.nil)
    | false, _ =>
      throw s!"{ctx}: bad entry (want (rune hyps equiv lhs rhs \
              backchain-limit) — stale log? recapture-all): {repr e}"
    | true, _ =>
      throw s!"{ctx}: bad entry (want (rune hyps equiv lhs rhs match-free)): \
              {repr e}"
  -- The entry's rune goes through the same parse as step runes (J7: the
  -- dotted multi-rule shape carries the index into the spec's identity) —
  -- but a rule-spec rune NAME must be a SYMBOL (a theorem name); the step
  -- path's lenient repr-fallback does not apply here (parse-time hard-fail
  -- restored, audit 2026-07-18).
  match runeS with
  | .cons _ (.cons (.atom (.symbol _)) _) => pure ()
  | _ => throw s!"{ctx}: rule-spec rune name is not a symbol: {repr runeS}"
  match parseRune? runeS with
  | some rune => do
    let rname := rune.name
    -- rune type + equiv are lowercase dispatch tags (see parseRune?).
    unless rune.ty == "rewrite" do
      throw s!"{ctx}: rune class {rune.ty} unsupported (frontier)"
    let hyps ← hypsS.toList?.elim
      (throw s!"{ctx} {rname}: :HYPS not a list: {repr hypsS}") pure
    let equiv ← match equivS with
      | .atom (.symbol s) => pure (s.name.map Char.toLower)
      | other => throw s!"{ctx} {rname}: bad equiv: {repr other}"
    let matchFree ← match mf? with
      | none => pure none
      | some .nil => pure none
      | some (.atom (.keyword k)) => pure (some (k.map Char.toLower))
      | some other =>
        throw s!"{ctx} {rname}: bad match-free: {repr other}"
    -- rune NAME is a symbol identity (theorem name), stored UPCASED
    -- like parseRune?'s name and the dependency-proof keys.
    pure ({ name := rname, idx := rune.idx, hyps, equiv,
            lhs := lhsS, rhs := rhsS, matchFree,
            backchainLimit := bclS } : RuleSpec)
  | _ => throw s!"{ctx}: bad rune: {repr runeS}"

/-- Parse a single top-level s-expression from the proof log. -/
private def parseEvent (s : SExpr) : Except String ProofEvent := do
  match s with
  | .cons (.atom (.keyword "STEP")) rest =>
    match rest.toList? with
    | some items => return .step (← parseStep? items)
    | none => throw s!"STEP: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "INDUCTION")) rest =>
    match rest.toList? with
    | some items => return .induction (← parseInduction? items)
    | none => throw s!"INDUCTION: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "QED")) _ =>
    return .qed
  | .cons (.atom (.keyword "ENCAPSULATE-BEGIN")) rest =>
    -- cluster item 2 / R6: bracket OPEN; :SIGS may be NIL (trivial scope)
    match rest.toList? with
    | some fields =>
      let sigs ← match lookupKeyword "SIGS" fields with
        | none => pure []
        | some (.atom (.symbol s)) =>
          if s.name == "NIL" then pure ([] : List Symbol)
          else throw s!"ENCAPSULATE-BEGIN: bad :SIGS atom: {s.name}"
        | some l => match l.toList? with
          | none => throw s!"ENCAPSULATE-BEGIN: :SIGS not a list: {repr l}"
          | some syms => syms.mapM fun e => match e with
            | .atom (.symbol sy) => pure sy
            | _ => throw s!"ENCAPSULATE-BEGIN: non-symbol sig: {repr e}"
      return .encapsulateBegin sigs
    | none => throw s!"ENCAPSULATE-BEGIN: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "ENCAPSULATE-END")) _ =>
    return .encapsulateEnd
  | .cons (.atom (.keyword "CONSTRAINTS")) rest =>
    -- cluster item 2 / R6: the scope's constraint axioms, verbatim.
    -- :UNKNOWN-CONSTRAINTS hard-fails (fail-closed, ratified).
    match rest.toList? with
    | some fields =>
      let fns ← match lookupKeyword "FNS" fields with
        | some l => match l.toList? with
          | none => throw s!"CONSTRAINTS: :FNS not a list: {repr l}"
          | some syms => syms.mapM fun e => match e with
            | .atom (.symbol sy) => pure sy
            | _ => throw s!"CONSTRAINTS: non-symbol fn: {repr e}"
        | none => throw "CONSTRAINTS: missing :FNS"
      let formulas ← match lookupKeyword "FORMULAS" fields with
        | some (.atom (.keyword "UNKNOWN-CONSTRAINTS")) =>
          throw "CONSTRAINTS: :UNKNOWN-CONSTRAINTS scope (fail-closed —             unsupported by design, R6 ratification)"
        | some l => match l.toList? with
          | none => throw s!"CONSTRAINTS: :FORMULAS not a list: {repr l}"
          | some fs => pure fs
        | none => throw "CONSTRAINTS: missing :FORMULAS"
      return .constraints fns formulas
    | none => throw s!"CONSTRAINTS: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "DEFTHM")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match atomString? nameExpr with
      | some name =>
        let formula ← (lookupKeyword "FORMULA" fields).elim
          (throw s!"DEFTHM {name}: missing :FORMULA") pure
        let source := match lookupKeyword "SOURCE" fields with
          | some (.atom (.keyword "INCLUDE-BOOK")) => TheoremSource.includeBook
          | some (.atom (.keyword "LOCAL")) => TheoremSource.local
          | _ => TheoremSource.unknown
        -- :CLASSES (cluster item 5): raw rule-classes; none = absent
        -- (pre-cluster log), some .nil = declared :rule-classes nil
        let classes := lookupKeyword "CLASSES" fields
        return .defthm name formula source classes
      | none => throw s!"DEFTHM: bad name: {repr nameExpr}"
    | some [] => throw s!"DEFTHM: missing name"
    | none => throw s!"DEFTHM: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "DEFUN")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match nameExpr with
      | .atom (.symbol nameSym) =>
        -- The name's PACKAGE is discarded downstream (`WorldEvent.defun.name` is a
        -- String; `Development.toWorld` rebuilds the symbol in the default package)
        -- — so a non-default package would silently rename the function. Hard-fail
        -- instead (frontier; no corpus example uses one).
        unless nameSym.package == ({ name := "X" } : Symbol).package do
          throw s!"DEFUN {nameSym.name}: non-default package \
                  {nameSym.package} unsupported (would be lost downstream)"
        let name := nameSym.name
        -- :FORMALS is REQUIRED and every formal must be a symbol — a malformed or
        -- absent list hard-fails (no silent drop, no default-to-nullary).
        let formalsSExpr ← (lookupKeyword "FORMALS" fields).elim
          (throw s!"DEFUN {name}: missing :FORMALS") pure
        let formalsList ← formalsSExpr.toList?.elim
          (throw s!"DEFUN {name}: :FORMALS is not a list: {repr formalsSExpr}") pure
        let formals ← formalsList.mapM fun
          | .atom (.symbol s) => pure s
          | other => throw s!"DEFUN {name}: non-symbol formal: {repr other}"
        let body ← (lookupKeyword "BODY" fields).elim
          (throw s!"DEFUN {name}: missing :BODY") pure
        -- PROVENANCE (audit 2026-07-26 F1): every world-entering :DEFUN
        -- must carry an explicit recognized :SOURCE — the fork emits one on
        -- every path since da1f5336a4's successor. :LOCAL-WITNESS marks an
        -- event admitted under `local` (an encapsulate/certification
        -- witness): its world effects are DISCARDED from the scope's final
        -- world, so a World built over it substitutes the witness for the
        -- constrained function in every REPLAYED STATEMENT (BUG-019 — the
        -- statement-substitution class; cov-encapsulate reported 2/2
        -- replayed about the witness). HARD-FAIL, named. A missing or
        -- unrecognized :SOURCE also hard-fails (a pre-provenance log
        -- prompts recapture; an unknown value is an emission drift).
        -- src: 0 = ground-zero snapshot, 1 = world-entering (admitted /
        -- include-book), 2 = LOCAL-WITNESS. A witness (R6/Phase 4) is
        -- accepted SCOPED: `buildDevelopment` requires an open encapsulate
        -- bracket and `Development.toWorld` excludes it by construction —
        -- the BUG-019 statement-substitution class resolved by tag+scope
        -- structure (the ratified R6 shape), replacing the earlier
        -- fail-closed refusal.
        let src ← match lookupKeyword "SOURCE" fields with
          | none => throw s!"DEFUN {name}: missing :SOURCE — every \
                            world-entering defun carries provenance \
                            (audit F1; recapture with the current fork)"
          | some (.atom (.keyword "GROUND-ZERO")) => pure 0
          | some (.atom (.keyword "ADMITTED")) => pure 1
          | some (.atom (.keyword "INCLUDE-BOOK")) => pure 1
          | some (.atom (.keyword "LOCAL-WITNESS")) => pure 2
          | some other => throw s!"DEFUN {name}: unsupported :SOURCE \
                                  {repr other}"
        let groundZero := src == 0
        -- The admission justification: :MEASURE/:WFREL/:MEASURED travel
        -- together (recursive defun) or are all absent (non-recursive); a
        -- PARTIAL set is a malformed emission and hard-fails.
        let just ← match lookupKeyword "MEASURE" fields,
                         lookupKeyword "WFREL" fields,
                         lookupKeyword "MEASURED" fields with
          | none, none, none =>
            -- a non-recursive defun also has no obligations
            match lookupKeyword "TERMINATION-CLAUSES" fields,
                  lookupKeyword "TERMINATION-RUNES" fields with
            | none, none => pure none
            | some c, _ => throw s!"DEFUN {name}: :TERMINATION-CLAUSES without \
                                   a justification: {repr c}"
            | _, some r => throw s!"DEFUN {name}: :TERMINATION-RUNES without \
                                   a justification: {repr r}"
          | some m, some r, some sub => do
            let rel ← match r with
              | .atom (.symbol s) => pure s
              | other => throw s!"DEFUN {name}: :WFREL is not a symbol: {repr other}"
            let subL ← sub.toList?.elim
              (throw s!"DEFUN {name}: :MEASURED is not a list: {repr sub}") pure
            let subSyms ← subL.mapM fun
              | .atom (.symbol s) => pure s
              | other => throw s!"DEFUN {name}: non-symbol measured formal: {repr other}"
            -- a RECURSIVE defun must carry its decrease obligations — an
            -- admission the log cannot justify is an emission gap
            -- (hard-fail; the emitter attaches the clique's RAW measure
            -- clauses). Since the J2 fork change (2026-07-16) this holds
            -- for INCLUDE-BOOK'd defuns too: the re-emission RECOMPUTES the
            -- clauses (gz-termination-clauses — the R2 follow-up), so
            -- :INCLUDED T now travels WITH :TERMINATION-CLAUSES; an
            -- :INCLUDED defun without clauses is a stale-fork capture
            -- (hard-fail, prompting recapture).
            match lookupKeyword "TERMINATION-CLAUSES" fields,
                  lookupKeyword "INCLUDED" fields with
            | some clausesExpr, included? =>
              (do match included? with
                  | none => pure ()
                  | some (.atom (.symbol tS)) =>
                    if tS.name == "T" then
                      if groundZero then
                        throw s!"DEFUN {name}: :SOURCE :GROUND-ZERO with \
                                :INCLUDED (snapshots are not include \
                                re-emissions)"
                      else pure ()
                    else throw s!"DEFUN {name}: malformed :INCLUDED value"
                  | some other =>
                    throw s!"DEFUN {name}: malformed :INCLUDED value: \
                            {repr other}")
              let clauses ← clausesExpr.toList?.elim
                (throw s!"DEFUN {name}: :TERMINATION-CLAUSES is not a list: \
                         {repr clausesExpr}") pure
              -- :TERMINATION-RUNES (fork-batch item H): the admission's
              -- cited rune set, per-admission. Absent = no channel (an
              -- include-book re-emission, or a pre-batch log); a
              -- present-but-malformed value hard-fails.
              let termRunes ← match lookupKeyword "TERMINATION-RUNES" fields with
                | none => pure none
                | some rs => match rs.toList? with
                  | some items => do
                    let runes ← items.mapM fun r => (parseRune? r).elim
                      (throw s!"DEFUN {name}: bad rune in \
                               :TERMINATION-RUNES: {repr r}") pure
                    pure (some runes)
                  | none => throw s!"DEFUN {name}: :TERMINATION-RUNES is \
                                    not a list: {repr rs}"
              pure (some { measure := m, wfRel := rel, measuredSubset := subSyms,
                           terminationClauses := clauses,
                           terminationRunes := termRunes })
            | none, some _ =>
              throw s!"DEFUN {name}: :INCLUDED without :TERMINATION-CLAUSES \
                      — stale-fork capture (the include re-emission \
                      recomputes clauses since J2); recapture the log"
            | none, none =>
              throw s!"DEFUN {name}: recursive (has a justification) but no \
                      :TERMINATION-CLAUSES and no :INCLUDED marker — emission gap"
          | _, _, _ => throw s!"DEFUN {name}: partial admission justification \
                               (:MEASURE/:WFREL/:MEASURED must travel together)"
        return if groundZero then .groundZeroDefun name formals body just
               else if src == 2 then .witnessDefun name formals body just
               else .defun name formals body just
      | _ => throw s!"DEFUN: bad name: {repr nameExpr}"
    | _ => throw s!"DEFUN: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "RULES")) rest =>
    match rest.toList? with
    | some [rulesList] =>
      let some entries := rulesList.toList?
        | throw s!"RULES: payload is not a list: {repr rulesList}"
      return .rules (← entries.mapM (parseRuleSpecEntry "RULES" false))
    | _ => throw s!"RULES: expected a single payload list, got {repr rest}"
  | .cons (.atom (.keyword "GROUND-ZERO-RULES")) rest =>
    -- Cited ground-zero rewrite rules read off the world at capture end
    -- (design D5) — the (:RULES …) entry shape plus the match-free flag.
    match rest.toList? with
    | some [rulesList] =>
      let some entries := rulesList.toList?
        | throw s!"GROUND-ZERO-RULES: payload is not a list: {repr rulesList}"
      return .groundZeroRules
        (← entries.mapM (parseRuleSpecEntry "GROUND-ZERO-RULES" true))
    | _ => throw s!"GROUND-ZERO-RULES: expected a single payload list, \
                   got {repr rest}"
  | .cons (.atom (.keyword "GROUND-ZERO-FC-RULES")) rest =>
    match rest.toList? with
    | some [rulesList] =>
      let some entries := rulesList.toList?
        | throw s!"GROUND-ZERO-FC-RULES: payload is not a list: {repr rulesList}"
      return .groundZeroFcRules (← entries.mapM parseFcRuleSpecEntry)
    | _ => throw s!"GROUND-ZERO-FC-RULES: expected a single payload list, \
                   got {repr rest}"
  | .cons (.atom (.keyword "GROUND-ZERO-LINEAR-RULES")) rest =>
    match rest.toList? with
    | some [rulesList] =>
      let some entries := rulesList.toList?
        | throw s!"GROUND-ZERO-LINEAR-RULES: payload is not a list: \
            {repr rulesList}"
      return .groundZeroLinearRules (← entries.mapM parseLinearRuleSpecEntry)
    | _ => throw s!"GROUND-ZERO-LINEAR-RULES: expected a single payload \
                   list, got {repr rest}"
  | .cons (.atom (.keyword "GROUND-ZERO-RECOGNIZER-TUPLES")) rest =>
    match rest.toList? with
    | some [tuplesList] =>
      let some entries := tuplesList.toList?
        | throw s!"GROUND-ZERO-RECOGNIZER-TUPLES: payload is not a list: \
            {repr tuplesList}"
      return .groundZeroRecognizerTuples
        (← entries.mapM parseRecognizerTupleEntry)
    | _ => throw s!"GROUND-ZERO-RECOGNIZER-TUPLES: expected a single \
                   payload list, got {repr rest}"
  | .cons (.atom (.keyword "INCLUDE-BOOK-EDGE")) rest =>
    let items := rest.toList?.getD []
    let some bookS := lookupKeyword "BOOK" items
      | throw "INCLUDE-BOOK-EDGE: missing :BOOK"
    let some book := atomString? bookS
      | throw s!"INCLUDE-BOOK-EDGE: :BOOK not a string/symbol: {repr bookS}"
    let parent ← match lookupKeyword "PARENT" items with
      | some .nil => pure none
      | some p => match atomString? p with
        | some s => pure (some s)
        | none => match p with
          -- ACL2's SYSFILE form: an active book under the system books
          -- dir prints as `(:SYSTEM . "relative/path.lisp")`.
          | .cons (.atom (.keyword "SYSTEM")) (.atom (.string s)) =>
            pure (some s)
          | _ => throw s!"INCLUDE-BOOK-EDGE: bad :PARENT: {repr p}"
      | none => throw "INCLUDE-BOOK-EDGE: missing :PARENT"
    return .includeBookEdge book parent
  | .cons (.atom (.keyword "CAPTURE-END")) rest =>
    let items := rest.toList?.getD []
    let some booksS := lookupKeyword "BOOKS" items
      | throw "CAPTURE-END: missing :BOOKS"
    match lookupKeyword "STATUS" items with
    | some (.atom (.keyword "COMPLETE")) => return .captureEnd booksS
    | some other => throw s!"CAPTURE-END: :STATUS is not :COMPLETE: \
        {repr other} (incomplete capture)"
    | none => throw "CAPTURE-END: missing :STATUS"
  | .cons (.atom (.keyword "POOL-CONSIDER")) rest =>
    let some nameS := lookupKeyword "NAME" (rest.toList?.getD [])
      | throw "POOL-CONSIDER: missing :NAME"
    return .poolConsider (← parsePoolLst nameS)
  | .cons (.atom (.keyword "POOL-SUBSUMED")) rest =>
    let items := rest.toList?.getD []
    let some nameS := lookupKeyword "NAME" items
      | throw "POOL-SUBSUMED: missing :NAME"
    let some byS := lookupKeyword "BY" items
      | throw "POOL-SUBSUMED: missing :BY"
    return .poolSubsumed (← parsePoolLst nameS) (← parsePoolLst byS)
  | .cons (.atom (.keyword "TYPE-PRESCRIPTION")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match atomString? nameExpr with
      | some name =>
        let corollary ← (lookupKeyword "COROLLARY" fields).elim
          (throw s!"TYPE-PRESCRIPTION {name}: missing :COROLLARY") pure
        let basicTs := match lookupKeyword "BASICTS" fields with
          | some (.atom (.number (.int n))) => some n
          | _ => none
        let leaves ← match lookupKeyword "LEAVES" fields with
          | some l => TpLeaf.parseList name l
          | none => pure []
        let allTps ← match lookupKeyword "ALL-TPS" fields with
          | some l => TpRuleSpec.parseList name parseRune? l
          | none => pure []
        return .typePrescription name corollary basicTs leaves allTps
      | none => throw s!"TYPE-PRESCRIPTION: bad name: {repr nameExpr}"
    | _ => throw s!"TYPE-PRESCRIPTION: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "EVENT-FAILED")) rest =>
    -- emit/event-failed (S1, 2026-07-23): an event FAILED in ACL2 and its
    -- error output was inhibited by :structured mode — the log is
    -- authoritative about the failure but INCOMPLETE about the book.
    -- Fail the PARSE with the ctx: a log containing a failed event must be
    -- fixed at the book/capture, never processed partially.
    let ctx := (lookupKeyword "CTX" (rest.toList?.getD [])).getD .nil
    throw s!"proof log records a FAILED ACL2 event (ctx: {repr ctx}) — the \
             book's event was rejected/failed and the log is incomplete; fix \
             the book (or the capture) and recapture"
  | .cons (.atom (.keyword "VERIFY-GUARDS")) rest =>
    -- emit/verify-guards (S1.2, 2026-07-23): the guard-obligation waterfall's
    -- wrapper (previously its :STEP/(:QED) events were ORPHANS). Replay of
    -- guard obligations is a named frontier — fail the parse precisely.
    let names := (lookupKeyword "NAMES" (rest.toList?.getD [])).getD .nil
    throw s!"proof log contains a VERIFY-GUARDS obligation proof for \
             {repr names} — guard-obligation replay is an unsupported frontier"
  | .cons (.atom (.keyword "FORCING-ROUND")) rest =>
    -- emit/forcing-round (S1, 2026-07-23): the structured forcing-round
    -- boundary (was untagged English prose that broke parsing —
    -- cov-force-round pin). Reconstruction of forcing rounds is a named
    -- frontier: parse hard-fails here, precisely, until round support lands.
    let round := (lookupKeyword "ROUND" (rest.toList?.getD [])).getD .nil
    throw s!"proof log contains a FORCING ROUND (round {repr round}) — \
             forcing-round replay is an unsupported frontier"
  | _ => throw s!"Unknown proof log event: {repr s}"

/-- Parse a proof log from raw ACL2 output.
    Finds the (:BEGIN-PROOF-LOG) marker in the raw text and parses only
    the s-expressions after it. Everything before the marker (SBCL banner,
    ACL2 startup, prompts) is discarded as raw text.
    Everything after the marker must be valid proof log s-expressions. -/
def parse (input : String) : Except String ProofLog := do
  let marker := "(:BEGIN-PROOF-LOG)"
  let parts := input.splitOn marker
  if parts.length < 2 then
    throw "No (:BEGIN-PROOF-LOG) marker found in input"
  let proofText := String.intercalate marker parts.tail!
  let sexprs ← Parse.parseAll proofText
  let mut events := #[]
  for s in sexprs do
    events := events.push (← parseEvent s)
  pure { events := events.toList }

/-- Pretty-print a proof log summary. -/
def summary (log : ProofLog) : String :=
  let steps := log.events.filter fun e => match e with | .step _ => true | _ => false
  let inductions := log.events.filter fun e => match e with | .induction _ => true | _ => false
  let qeds := log.events.filter fun e => match e with | .qed => true | _ => false
  let defthms := log.events.filterMap fun e => match e with | .defthm n _ _ => some n | _ => none
  let processors := steps.filterMap fun e => match e with
    | .step s => some s.processor | _ => none
  let procPairs := processors.foldl (init := ([] : List (String × Nat)))
    fun acc p =>
      match acc.find? (fun (k, _) => k == p) with
      | some _ => acc.map fun (k, n) => if k == p then (k, n + 1) else (k, n)
      | none => acc ++ [(p, 1)]
  let lines := #[
    s!"Proof log: {log.events.length} events",
    s!"  Theorems: {defthms.length} ({String.intercalate ", " defthms})",
    s!"  Steps: {steps.length}",
    s!"  Inductions: {inductions.length}",
    s!"  QEDs: {qeds.length}",
    "  By processor:"
  ]
  let procLines := procPairs.map fun (p, n) => s!"    {p}: {n}"
  "\n".intercalate (lines.toList ++ procLines)

/-- Split a proof log into named per-theorem segments.
    Each segment starts with a (:DEFTHM name) event and ends with (:QED).
    Returns (name, events) pairs. -/
def splitByTheorem (log : ProofLog) : List (String × List ProofEvent) :=
  let rec go (events : List ProofEvent) (curName : Option String)
      (current : List ProofEvent) (acc : List (String × List ProofEvent)) :
      List (String × List ProofEvent) :=
    match events with
    | [] =>
      match curName with
      | some n => ((n, current.reverse) :: acc).reverse
      | none => acc.reverse
    | .defthm name _ _ :: rest =>
      -- Start a new theorem segment; flush any previous
      let acc := match curName with
        | some n => (n, current.reverse) :: acc
        | none => acc
      go rest (some name) [] acc
    | .qed :: rest =>
      match curName with
      | some n => go rest none [] ((n, (.qed :: current).reverse) :: acc)
      | none => go rest none [] acc  -- QED without defthm, skip
    | e :: rest => go rest curName (e :: current) acc
  go log.events none [] []

end ProofLog
end ACL2
