import ACL2Lean.Syntax

namespace ACL2

namespace Parse

abbrev Stream := List Char

private def normalizeSymbolName (name : String) : String :=
  name.map Char.toLower

private def normalizePackageName (name : String) : String :=
  name.map Char.toUpper

private def dropWhile (p : Char → Bool) : Stream → Stream
  | [] => []
  | c :: cs => if p c then dropWhile p cs else c :: cs

private def span (p : Char → Bool) : Stream → (List Char × Stream)
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (taken, rest) := span p cs
        (c :: taken, rest)
      else
        ([], c :: cs)

partial def skipWS : Stream → Stream
  | [] => []
  | c :: cs =>
      if c = ';' then
        skipWS (dropWhile (fun d => d ≠ '\n') cs)
      else if c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '\r' then
        skipWS cs
      else if c = '#' then
        match cs with
        | '|' :: rest =>
            let rec skipBlock : Nat → Stream → Stream
              | 0, r => skipWS r
              | _, [] => panic! "unterminated block comment"
              | d, '#' :: '|' :: r => skipBlock (d + 1) r
              | d, '|' :: '#' :: r => skipBlock (d - 1) r
              | d, _ :: r => skipBlock d r
            skipBlock 1 rest
        | _ => c :: cs
      else
        c :: cs

private def readString : Stream → Except String (String × Stream)
  | [] => .error "unterminated string"
  | c :: cs =>
      if c = '"' then
        let rec go : List Char → Stream → Except String (String × Stream)
          | _, [] => .error "unterminated string"
          | acc, '"' :: rest => .ok (String.ofList (acc.reverse), rest)
          | acc, '\\' :: rest =>
              match rest with
              | [] => .error "unterminated escape"
              | h :: tl => go (h :: acc) tl
          | acc, h :: rest => go (h :: acc) rest
        go [] cs
      else
        .error "string literal must start with quote"

private def isAtomChar (c : Char) : Bool :=
  ¬ (c = '(' ∨ c = ')' ∨ c = ' ' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t')

private def readAtom (cs : Stream) : (String × Stream) :=
  let (tok, rest) := span isAtomChar cs
  (String.ofList tok, rest)

mutual
  partial def parseList (cs : Stream) (acc : List SExpr := [])
      : Except String (SExpr × Stream) :=
    let cs := skipWS cs
    match cs with
    | [] => .error "unterminated list"
    | ')' :: rest => .ok (SExpr.ofList acc.reverse, rest)
    | '.' :: rest =>
        -- A lone `.` (followed by a delimiter/EOF) with a head already read is the
        -- dotted-cdr separator: `(a … z . tl)` ⇒ the improper list with final cdr
        -- `tl`. (A bare `.` is never a legal Lisp symbol, so this is unambiguous; a
        -- `.` that begins an atom — e.g. `.5` — is followed by an atom char and is
        -- parsed normally below.)
        let lone := match rest with | [] => true | c :: _ => !isAtomChar c
        if lone && !acc.isEmpty then
          match parseSExpr rest with
          | .error e => .error e
          | .ok (tl, rest2) =>
              match skipWS rest2 with
              | ')' :: rest3 => .ok (acc.reverse.foldr SExpr.cons tl, rest3)
              | _ => .error "malformed dotted list: expected ) after dotted cdr"
        else
          match parseSExpr cs with
          | .error e => .error e
          | .ok (sx, rest') => parseList rest' (sx :: acc)
    | _ =>
        match parseSExpr cs with
        | .error e => .error e
        | .ok (sx, rest) => parseList rest (sx :: acc)

  partial def parseQuote (tag : String) (cs : Stream)
      : Except String (SExpr × Stream) :=
    match parseSExpr cs with
    | .error e => .error e
    | .ok (sx, rest) =>
        let sym := SExpr.atom (.symbol { name := tag })
        let quoted := SExpr.ofList [sym, sx]
        .ok (quoted, rest)

  partial def parseSExpr (input : Stream) : Except String (SExpr × Stream) :=
    let cs := skipWS input
    match cs with
    | [] => .error "unexpected end of file"
    | '(' :: rest => parseList rest
    | ')' :: _ => .error "unexpected )"
    | '\'' :: rest => parseQuote "quote" rest
    | '`' :: rest => parseQuote "quasiquote" rest
    | ',' :: '@' :: rest =>
        match parseSExpr rest with
        | .error e => .error e
        | .ok (sx, tail) =>
            let sym := SExpr.atom (.symbol { name := "unquote-splicing" })
            .ok (SExpr.ofList [sym, sx], tail)
    | ',' :: rest => parseQuote "unquote" rest
    | '"' :: _ =>
        match readString cs with
        | .error e => .error e
        | .ok (str, rest) =>
            .ok (SExpr.atom (.string str), rest)
    | '|' :: rest =>
        let rec go : List Char → Stream → Except String (String × Stream)
          | _, [] => .error "unterminated escaped symbol"
          | acc, '|' :: rest => .ok (String.ofList acc.reverse, rest)
          | acc, h :: rest => go (h :: acc) rest
        match go [] rest with
        | .error e => .error e
        | .ok (str, rest) => .ok (SExpr.atom (.symbol { name := str }), rest)
    | '#' :: '\\' :: rest =>
        let (tok, tail) := span isAtomChar rest
        let repr := "#\\" ++ String.ofList tok
        .ok (SExpr.atom (.symbol { name := repr }), tail)
    | '#' :: '+' :: rest =>
        match parseSExpr rest with
        | .error e => .error e
        | .ok (_, rest2) =>
            match parseSExpr rest2 with
            | .error e => .error e
            | .ok (_, rest3) => parseSExpr rest3
    | '#' :: '-' :: rest =>
        match parseSExpr rest with
        | .error e => .error e
        | .ok (_, rest2) => parseSExpr rest2
    | '#' :: c :: _ => .error s!"unrecognized reader macro: #{String.ofList [c]}"
    | '#' :: [] => .error "unexpected # at end of input"
    | ':' :: _ =>
        let (tok, rest) := readAtom cs
        let kw := ((tok.drop 1).toString).map Char.toLower
        .ok (SExpr.atom (.keyword kw), rest)
    | _ =>
        let (rawTok, rest) := readAtom cs
        let tok := normalizeSymbolName rawTok
        if tok = "nil" then .ok (SExpr.nil, rest)
        else if tok = "t" then .ok (SExpr.t, rest)
        else
          match tok.toInt? with
          | some n => .ok (SExpr.atom (.number (.int n)), rest)
          | none =>
            if tok.contains '/' then
              let parts := tok.splitOn "/"
              match parts with
              | [numStr, denStr] =>
                  match numStr.toInt?, denStr.toNat? with
                  | some n, some d => .ok (SExpr.atom (.number (.rational n d)), rest)
                  | _, _ => .ok (SExpr.atom (.symbol { name := tok }), rest)
              | _ => .ok (SExpr.atom (.symbol { name := tok }), rest)
            else if tok.contains '.' then
              .ok (SExpr.atom (.symbol { name := tok }), rest)
            else
              let parts := rawTok.splitOn "::"
              match parts with
              | [_] => .ok (SExpr.atom (.symbol { name := tok }), rest)
              | [pkg, name] =>
                  .ok (SExpr.atom (.symbol
                    { package := normalizePackageName pkg
                      name := normalizeSymbolName name }), rest)
              | _ => .error s!"malformed package-qualified symbol: {rawTok}"
end

/-- Parse all s-expressions from a string. -/
partial def parseAll : String → Except String (List SExpr)
  | str =>
    let rec loop : Stream → List SExpr → Except String (List SExpr)
      | cs, acc =>
        let cs := skipWS cs
        match cs with
        | [] => .ok acc.reverse
        | ')' :: _ => .error "extra )"
        | _ =>
            match parseSExpr cs with
            | .error e => .error e
            | .ok (sx, rest) => loop rest (sx :: acc)
    loop str.toList []

private def parseOne (input : String) : Except String SExpr := do
  let (sx, rest) ← parseSExpr input.toList
  let rest := skipWS rest
  if rest.isEmpty then
    pure sx
  else
    throw s!"unexpected trailing input: {String.ofList rest}"

private def parsedUppercaseDefunLooksRight : Bool :=
  match parseOne "(DEFUN FOO (X) (DECLARE (XARGS :GUARD (INTEGERP X))) (IF T X NIL))" with
  | .ok sx =>
      match Event.classify sx with
      | .defun { name := "foo", .. } [{ name := "x", .. }] _ decls body =>
          decls.length = 1 && body.headSymbol? = some { name := "if" }
      | _ => false
  | .error _ => false

private def parsedQualifiedBuiltinLooksRight : Bool :=
  match parseOne "ACL2::CAR" with
  | .ok (SExpr.atom (.symbol { package := "ACL2", name := "car" })) => true
  | _ => false

private def parsedUppercaseKeywordLooksRight : Bool :=
  match parseOne ":SYSTEM" with
  | .ok (SExpr.atom (.keyword "system")) => true
  | _ => false

private def parsedDefthmMetadataLooksRight : Bool :=
  match parseOne "(DEFTHM FOO (EQUAL X X) :RULE-CLASSES (:LINEAR :REWRITE) :HINTS ((\"Goal\" :USE BAR :IN-THEORY (DISABLE BAZ))))" with
  | .ok sx =>
      match Event.classify sx with
      | .defthm { name := "foo", .. } info =>
          info.ruleClasses.map (·.name) = ["linear", "rewrite"] &&
            match info.hintGoals with
            | [hint] =>
                hint.goal = "Goal" &&
                hint.findOption? "use" = some (.atom (.symbol { name := "bar" })) &&
                hint.inTheory? = some (.disable [.atom (.symbol { name := "baz" })])
            | _ => false
      | _ => false
  | .error _ => false

private def parsedTopLevelInTheoryLooksRight : Bool :=
  match parseOne "(IN-THEORY (E/D (COMMUTATIVITY-OF-+)
                                 (ASSOCIATIVITY-OF-+)))" with
  | .ok sx =>
      match Event.classify sx with
      | .inTheory expr =>
          TheoryExpr.ofSExpr expr =
            .e_d
              [.atom (.symbol { name := "commutativity-of-+" })]
              [.atom (.symbol { name := "associativity-of-+" })]
      | _ => false
  | .error _ => false

private def parsedWithOutputWrappedDefthmLooksRight : Bool :=
  match parseOne "(WITH-OUTPUT :OFF :ALL (DEFTHM WRAPPED (EQUAL X X)))" with
  | .ok sx =>
      match Event.classify sx with
      | .defthm { name := "wrapped", .. } info =>
          info.body = SExpr.ofList
            [ .atom (.symbol { name := "equal" })
            , .atom (.symbol { name := "x" })
            , .atom (.symbol { name := "x" })
            ]
      | _ => false
  | .error _ => false

private def parsedMakeEventEncapsulateLooksRight : Bool :=
  match parseOne "(MAKE-EVENT `(ENCAPSULATE NIL
                                 (LOCAL
                                  (DEFTHM CHECK-IT!-WORKS
                                    (EQUAL X X)
                                    :RULE-CLASSES NIL))
                                 (DEFTHM BADGE-PRIM-TYPE
                                   (EQUAL X X)
                                   :HINTS ((\"Goal\"
                                            :IN-THEORY (DISABLE CHECK-IT! HONS-GET))))))" with
  | .ok sx =>
      match Event.flattenList [Event.classify sx] with
      | [ .defthm { name := "check-it!-works", .. } checkInfo
        , .defthm { name := "badge-prim-type", .. } badgeInfo
        ] =>
          checkInfo.ruleClasses = [] &&
            match badgeInfo.hintGoals with
            | [hint] =>
                hint.goal = "Goal" &&
                hint.inTheory? =
                  some (.disable
                    [ .atom (.symbol { name := "check-it!" })
                    , .atom (.symbol { name := "hons-get" })
                    ])
            | _ => false
      | _ => false
  | .error _ => false

private def parsedProofBuilderInstructionsLookRight : Bool :=
  match parseOne "(DEFTHM APPLY$-PRIM-META-FN-CORRECT
                     (EQUAL (APPLY$-PRIM-META-FN-EV TERM ALIST)
                            (APPLY$-PRIM-META-FN-EV (META-APPLY$-PRIM TERM) ALIST))
                     :INSTRUCTIONS
                     ((QUIET!
                       (:BASH (\"Goal\"
                               :IN-THEORY '((:DEFINITION HONS-ASSOC-EQUAL)
                                            (:DEFINITION HONS-EQUAL))))
                       (:IN-THEORY (UNION-THEORIES
                                    '((:DEFINITION APPLY$-PRIM))
                                    (CURRENT-THEORY :HERE)))
                       (:REPEAT :PROVE)))
                     :RULE-CLASSES ((:META :TRIGGER-FNS (APPLY$-PRIM))))" with
  | .ok sx =>
      match Event.classify sx with
      | .defthm { name := "apply$-prim-meta-fn-correct", .. } info =>
          match info.instructions with
          | [ .block "quiet!" [bashInst, theoryInst, .block "repeat" [.atom "prove"]] ] =>
              let bashOk :=
                match bashInst.goalHints with
                | [hint] =>
                    hint.goal = "Goal" &&
                      hint.inTheory?.isSome
                | _ => false
              let theoryOk :=
                match theoryInst.theoryExpr? with
                | some (.raw expr) =>
                    match expr.toList? with
                    | some (.atom (.symbol head) :: _) => head.isNamed "union-theories"
                    | _ => false
                | _ => false
              bashOk && theoryOk
          | _ => false
      | _ => false
  | .error _ => false

#guard parsedQualifiedBuiltinLooksRight
#guard parsedUppercaseKeywordLooksRight
#guard parsedUppercaseDefunLooksRight
#guard parsedDefthmMetadataLooksRight
#guard parsedTopLevelInTheoryLooksRight
#guard parsedWithOutputWrappedDefthmLooksRight
#guard parsedMakeEventEncapsulateLooksRight
#guard parsedProofBuilderInstructionsLookRight

end Parse

end ACL2
