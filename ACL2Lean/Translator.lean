import ACL2Lean.Syntax

namespace ACL2

namespace Translator

def translateSymbol (s : Symbol) : String :=
  let name := s.normalizedName
  if name = "+" || name = "binary-+" then "Logic.plus"
  else if name = "-" || name = "binary--" then "Logic.minus"
  else if name = "*" || name = "binary-*" then "Logic.times"
  else if name = "/" then "Logic.div"
  else if name = "<" then "Logic.lt"
  else if name = "=" then "Logic.eq"
  else if name = ">" then "Logic.gt"
  else if name = "<=" then "Logic.le"
  else if name = ">=" then "Logic.ge"
  else if name = "if" then "Logic.if_"
  else if name = "and" then "Logic.and"
  else if name = "or" then "Logic.or"
  else if name = "not" then "Logic.not"
  else if name = "implies" then "Logic.implies"
  else if name = "equal" then "Logic.equal"
  else if name = "consp" then "Logic.consp"
  else if name = "atom" then "Logic.atom"
  else if name = "car" then "Logic.car"
  else if name = "cdr" then "Logic.cdr"
  else if name = "cons" then "Logic.cons"
  else if name = "list" then "Logic.list"
  else if name = "zp" then "Logic.zp"
  else if name = "evenp" then "Logic.evenp"
  else if name = "oddp" then "Logic.oddp"
  else if name = "integerp" then "Logic.integerp"
  else if name = "posp" then "Logic.posp"
  else if name = "natp" then "Logic.natp"
  else if name = "expt" then "Logic.expt"
  else if name = "endp" then "Logic.endp"
  else if name = "first" then "Logic.first"
  else if name = "second" then "Logic.second"
  else if name = "append" then "Logic.append"
  else if name = "len" then "Logic.len"
  else if name = "true-listp" then "Logic.trueListp"
  else if name = "iff" then "Logic.iff"
  else if name = "force" then "Logic.force"
  else if name = "double-rewrite" then "Logic.double_rewrite"
  else if name = "evens" then "Logic.evens"
  else if name = "odds" then "Logic.odds"
  else if name = "acl2-count" then "SExpr.acl2Count"
  else if name = "lexorder" then "lexorder"
  else if name = "stringp" then "Logic.stringp"
  else if name = "string-append" then "Logic.string_append"
  else
    let name := name.replace "-" "_"
    let name := name.replace "!" "_bang"
    let name := name.replace "?" "_p"
    let name := name.replace "/" "_div_"
    let name := name.replace "+" "_plus_"
    let name := name.replace "*" "_times_"
    let name := name.replace "=" "_eq_"
    name

def foldNary (fn : String) (args : List String) : String :=
  match args with
  | [] => panic! s!"foldNary called with empty args for {fn}"
  | [a] => a
  | a :: rest => s!"({fn} {a} {foldNary fn rest})"

/-- Translate an SExpr literal value into Lean SExpr constructor syntax.
    Used for quoted values so that `'LT` emits the symbol atom, not a function. -/
partial def translateLiteral : SExpr → String
  | .nil => "SExpr.nil"
  | .atom (.symbol s) => s!"(SExpr.atom (.symbol \{ name := \"{s.name}\" }))"
  | .atom (.number (.int n)) => s!"(SExpr.atom (.number (.int ({n}))))"
  | .atom (.number (.rational n d)) => s!"(SExpr.atom (.number (.rational ({n}) ({d}))))"
  | .atom (.number (.decimal m e)) => s!"(SExpr.atom (.number (.decimal ({m}) ({e}))))"
  | .atom (.string s) => s!"(SExpr.atom (.string \"{s}\"))"
  | .atom (.keyword k) => s!"(SExpr.atom (.keyword \"{k}\"))"
  | .cons a b => s!"(SExpr.cons {translateLiteral a} {translateLiteral b})"

/-- Extract the last element from a cond clause body (implicit progn). -/
private def condClauseVal (body : SExpr) : SExpr :=
  match body.toList? with
  | some l@(_ :: _) => l.getLast!
  | _ => body

mutual
/-- Translate `(case test (sym1 val1) (sym2 val2) ... (otherwise default))` to nested if/equal. -/
partial def translateCaseClauses (testStr : String) (clauses : SExpr) (nativeIf : Bool) : String :=
  match clauses with
  | .cons (.cons key (.cons val .nil)) rest =>
    match key with
    | .atom (.symbol s) =>
      if s.isNamed "otherwise" || s.isNamed "t" then translateExpr val nativeIf
      else
        let keyLit := s!"(SExpr.atom (.symbol \{ name := \"{s.name}\" }))"
        s!"(if Logic.toBool (Logic.equal {testStr} {keyLit}) then {translateExpr val nativeIf} else {translateCaseClauses testStr rest nativeIf})"
    | .cons _ _ =>
      -- Multi-key: ((sym1 sym2 ...) val) — match if test equals any key
      match key.toList? with
      | some keys =>
        let conds := keys.filterMap fun
          | .atom (.symbol s) =>
            let keyLit := s!"(SExpr.atom (.symbol \{ name := \"{s.name}\" }))"
            some s!"(Logic.equal {testStr} {keyLit})"
          | k => some s!"(Logic.equal {testStr} {translateExpr k nativeIf})"
        let guard := match conds with
          | [] => "SExpr.nil"
          | [c] => c
          | c :: cs => cs.foldl (fun acc g => s!"(Logic.or {acc} {g})") c
        s!"(if Logic.toBool {guard} then {translateExpr val nativeIf} else {translateCaseClauses testStr rest nativeIf})"
      | none => panic! s!"malformed case key list: {repr key}"
    | _ =>
      s!"(if Logic.toBool (Logic.equal {testStr} {translateExpr key nativeIf}) then {translateExpr val nativeIf} else {translateCaseClauses testStr rest nativeIf})"
  | .nil => "SExpr.nil"
  | _ => panic! s!"malformed case clause: {repr clauses}"

/-- Translate `(cond (test1 val1) (test2 val2) ... (t default))` to nested if.
    Multi-body clauses `(test body1 body2)` use the last body (implicit progn). -/
partial def translateCond (clauses : SExpr) (nativeIf : Bool) : String :=
  match clauses with
  | .cons (.cons test body) rest =>
    let val := condClauseVal body
    match test with
    | .atom (.symbol s) =>
      if s.isNamed "t" then translateExpr val nativeIf
      else if nativeIf then
        s!"(if Logic.toBool {translateExpr test nativeIf} then {translateExpr val nativeIf} else {translateCond rest nativeIf})"
      else
        s!"(Logic.if_ {translateExpr test nativeIf} {translateExpr val nativeIf} {translateCond rest nativeIf})"
    | _ =>
      if nativeIf then
        s!"(if Logic.toBool {translateExpr test nativeIf} then {translateExpr val nativeIf} else {translateCond rest nativeIf})"
      else
        s!"(Logic.if_ {translateExpr test nativeIf} {translateExpr val nativeIf} {translateCond rest nativeIf})"
  | .nil => "SExpr.nil"
  | _ => panic! s!"malformed cond: {repr clauses}"

/-- Translate an ACL2 expression. When `nativeIf` is true, emit Lean's native
    `if toBool ... then ... else ...` instead of `Logic.if_` so Lean's
    termination checker can see the branching structure. -/
partial def translateExpr (expr : SExpr) (nativeIf : Bool := false) : String :=
  match expr with
  | .nil => "SExpr.nil"
  | .atom (.number (.int n)) => s!"(SExpr.atom (.number (.int ({n}))))"
  | .atom (.number (.rational n d)) => s!"(Logic.rational ({n}) ({d}))"
  | .atom (.number (.decimal m e)) => s!"(Logic.decimal ({m}) ({e}))"
  | .atom (.string s) => s!"(SExpr.atom (.string \"{s}\"))"
  | .atom (.symbol s) =>
      if s.isNamed "t" then "SExpr.t"
      else if s.isNamed "nil" then "SExpr.nil"
      else translateSymbol s
  | .cons (.atom (.symbol s)) argsExpr =>
      if s.isNamed "quote" then
        match argsExpr with
        | .cons v .nil => translateLiteral v
        | _ => panic! s!"malformed quote: {repr expr}"
      else if s.isNamed "if" then
        match argsExpr with
        | .cons c (.cons t (.cons e .nil)) =>
            if nativeIf then
              s!"(if Logic.toBool {translateExpr c nativeIf} then {translateExpr t nativeIf} else {translateExpr e nativeIf})"
            else
              s!"(Logic.if_ {translateExpr c nativeIf} {translateExpr t nativeIf} {translateExpr e nativeIf})"
        | _ => panic! s!"malformed if: {repr expr}"
      else if s.isNamed "cond" then
        translateCond argsExpr nativeIf
      else if s.isNamed "case" then
        match argsExpr with
        | .cons testExpr clauses =>
          let testStr := translateExpr testExpr nativeIf
          translateCaseClauses testStr clauses nativeIf
        | _ => panic! s!"malformed case: {repr expr}"
      else if s.isNamed "let" || s.isNamed "let*" then
        match argsExpr with
        | .cons bindings (.cons body .nil) =>
          let bindStrs := match bindings.toList? with
            | some pairs => pairs.map fun pair =>
                match pair.toList? with
                | some [.atom (.symbol var), val] =>
                  s!"let {translateSymbol var} := {translateExpr val nativeIf}"
                | _ => panic! s!"malformed let binding: {repr pair}"
            | none => panic! s!"non-list let bindings: {repr bindings}"
          let bodyStr := translateExpr body nativeIf
          if bindStrs.isEmpty then bodyStr
          else s!"({String.intercalate "; " bindStrs}; {bodyStr})"
        | _ => panic! s!"malformed let: {repr expr}"
      else if s.isNamed "list" then
        let args := match argsExpr.toList? with
          | some l => l.map (translateExpr · nativeIf)
          | none => panic! s!"non-list args in list: {repr argsExpr}"
        args.foldr (fun a acc => s!"(Logic.cons {a} {acc})") "SExpr.nil"
      else if s.isNamed "1+" || s.isNamed "1+$inline" then
        match argsExpr with
        | .cons x .nil => s!"(Logic.plus {translateExpr x nativeIf} 1)"
        | _ => panic! s!"malformed 1+: {repr expr}"
      else if s.isNamed "1-" || s.isNamed "1-$inline" then
        match argsExpr with
        | .cons x .nil => s!"(Logic.minus {translateExpr x nativeIf} 1)"
        | _ => panic! s!"malformed 1-: {repr expr}"
      else if s.isNamed "cadr" then
        match argsExpr with
        | .cons x .nil => s!"(Logic.car (Logic.cdr {translateExpr x nativeIf}))"
        | _ => panic! s!"malformed cadr: {repr expr}"
      else if s.isNamed "cddr" then
        match argsExpr with
        | .cons x .nil => s!"(Logic.cdr (Logic.cdr {translateExpr x nativeIf}))"
        | _ => panic! s!"malformed cddr: {repr expr}"
      else if s.isNamed "declare" then
        "" -- skip declarations
      else
        let args := match argsExpr.toList? with
          | some l => l.map (translateExpr · nativeIf)
          | none => panic! s!"non-list args in function call ({s.name} ...): {repr argsExpr}"
        let fn := translateSymbol s
        if ["Logic.plus", "Logic.times", "Logic.and", "Logic.or"].contains fn && args.length > 2 then
          foldNary fn args
        else if args.isEmpty then fn else s!"({fn} {String.intercalate " " args})"
  | .atom (.keyword k) => panic! s!"unexpected keyword atom in expression: :{k}"
  | .cons head _ => panic! s!"unexpected expression head: {repr head} in {repr expr}"
end -- mutual (translateCond / translateExpr)

mutual
partial def collectVarsCond (clauses : SExpr) (acc : List String) : List String :=
  match clauses with
  | .cons (.cons test (.cons val .nil)) rest =>
    let acc := collectVars test acc
    let acc := collectVars val acc
    collectVarsCond rest acc
  | .nil => acc
  | _ => panic! s!"malformed cond clause in collectVars: {repr clauses}"

/-- Collect variables from case clauses, skipping key symbols. -/
partial def collectVarsCaseClauses (clauses : SExpr) (acc : List String) : List String :=
  match clauses with
  | .cons (.cons _ (.cons val .nil)) rest =>
    let acc := collectVars val acc
    collectVarsCaseClauses rest acc
  | .nil => acc
  | _ => panic! s!"malformed case clause in collectVars: {repr clauses}"

partial def collectVars (expr : SExpr) (acc : List String := []) : List String :=
  match expr with
  | .nil => acc
  | .atom (.number _) => acc
  | .atom (.string _) => acc
  | .atom (.keyword _) => acc
  | .atom (.symbol s) =>
      let name := translateSymbol s
      if name.startsWith "Logic." then acc
      else if ["nil", "true", "false", "rational", "decimal"].contains name then acc
      else if acc.contains name then acc
      else name :: acc
  | .cons (.atom (.symbol s)) argsExpr =>
      if s.isNamed "quote" then
        acc
      else if s.isNamed "if" then
        match argsExpr with
        | .cons c (.cons t (.cons e .nil)) =>
            let acc := collectVars c acc
            let acc := collectVars t acc
            collectVars e acc
        | _ => panic! s!"malformed if in collectVars: {repr argsExpr}"
      else if s.isNamed "cond" then
        collectVarsCond argsExpr acc
      else if s.isNamed "case" then
        match argsExpr with
        | .cons testExpr clauses =>
          let acc := collectVars testExpr acc
          collectVarsCaseClauses clauses acc
        | _ => panic! s!"malformed case in collectVars: {repr argsExpr}"
      else if s.isNamed "let" || s.isNamed "let*" then
        match argsExpr with
        | .cons bindings (.cons body .nil) =>
          let acc := match bindings.toList? with
            | some pairs => pairs.foldl (fun acc pair =>
                match pair.toList? with
                | some [_, val] => collectVars val acc
                | _ => panic! s!"malformed let binding in collectVars: {repr pair}") acc
            | none => panic! s!"non-list let bindings in collectVars: {repr bindings}"
          collectVars body acc
        | _ => panic! s!"malformed let in collectVars: {repr argsExpr}"
      else if s.isNamed "list" then
        match argsExpr.toList? with
        | some args => args.foldl (fun a e => collectVars e a) acc
        | none => panic! s!"non-list args in list collectVars: {repr argsExpr}"
      else if s.isNamed "declare" then
        acc
      else
        match argsExpr.toList? with
        | some args => args.foldl (fun a e => collectVars e a) acc
        | none => panic! s!"non-list args in collectVars for ({s.name} ...): {repr argsExpr}"
  | .cons head _ => panic! s!"unexpected collectVars head: {repr head}"
end -- mutual

def sanitizeName (s : String) : String :=
  let s := s.replace "-" "_"
  let s := s.replace "=" "_eq_"
  let s := s.replace "+" "_plus_"
  let s := s.replace "*" "_times_"
  let s := s.replace "/" "_div_"
  let s := s.replace "Logic." ""
  s

/-- Find which formals are recursed on (appear as argument to cdr in recursive calls).
    Returns a deduplicated list of formal names that decrease via cdr across all recursive calls. -/
private partial def findRecursiveArgs (name : Symbol) (formals : List Symbol) (body : SExpr) : List String :=
  let nameStr := name.normalizedName
  let rec go (expr : SExpr) (acc : List String) : List String :=
    match expr with
    | .cons (.atom (.symbol s)) args =>
      if s.isNamed nameStr then
        -- Check args for (cdr formal)
        match args.toList? with
        | some argList =>
          argList.foldl (fun acc arg =>
            match arg with
            | .cons (.atom (.symbol cdrSym)) (.cons (.atom (.symbol formal)) .nil) =>
              if cdrSym.isNamed "cdr" then
                match formals.find? (fun f => f.isNamed formal.normalizedName) with
                | some f =>
                  let name := translateSymbol f
                  if acc.contains name then acc else acc ++ [name]
                | none => acc
              else acc
            | _ => acc) acc
        | none => acc
      else
        match args.toList? with
        | some argList => argList.foldl (fun acc arg => go arg acc) acc
        | none => acc
    | .cons a b => go b (go a acc)
    | _ => acc
  go body []

/-- Find if a recursive call uses `(evens formal)` or `(odds formal)` as an argument. -/
private partial def findEvensOddsArg (name : Symbol) (formals : List Symbol) (body : SExpr) : Option String :=
  let nameStr := name.normalizedName
  let rec go (expr : SExpr) : Option String :=
    match expr with
    | .cons (.atom (.symbol s)) args =>
      if s.isNamed nameStr then
        match args.toList? with
        | some argList =>
          argList.findSome? fun arg =>
            match arg with
            | .cons (.atom (.symbol fn)) (.cons (.atom (.symbol formal)) .nil) =>
              if fn.isNamed "evens" || fn.isNamed "odds" then
                formals.find? (fun f => f.isNamed formal.normalizedName) |>.map translateSymbol
              else none
            | _ => none
        | none => none
      else
        match args.toList? with
        | some argList => argList.findSome? go
        | none => none
    | .cons a b =>
      match go a with
      | some r => some r
      | none => go b
    | _ => none
  go body

/-- Replace all occurrences of `(Logic.cdr argName)` with `_cdr_argName` in translated body. -/
private def substituteCdr (body : String) (argName : String) : String :=
  body.replace s!"(Logic.cdr {argName})" s!"_cdr_{argName}"

/-- Extract the base-case expression from an `(if_ (endp arg) base recursive)` body. -/
private partial def extractBaseCase (body : SExpr) (argName : String) : Option SExpr :=
  match body with
  | .cons (.atom (.symbol s)) (.cons guard (.cons base (.cons _ .nil))) =>
    if s.isNamed "if" then
      match guard with
      | .cons (.atom (.symbol endpSym)) (.cons (.atom (.symbol argSym)) .nil) =>
        if endpSym.isNamed "endp" && argSym.isNamed argName then some base
        else none
      | _ => none
    else none
  | _ => none

def translateDefun (name : Symbol) (formals : List Symbol) (body : SExpr) : String :=
  let nameStr := translateSymbol name
  let fmls := String.intercalate " " (formals.map fun s => s!"({translateSymbol s} : SExpr)")
  let recArgs := findRecursiveArgs name formals body
  match recArgs with
  | [arg] =>
    -- Single recursive arg: use acl2Count for termination
    let bodyStr := translateExpr body (nativeIf := true)
    let usesEndp := (bodyStr.splitOn "Logic.endp").length > 1
    let decreasingLemma := if usesEndp
      then "ACL2.acl2Count_cdr_lt_of_not_endp"
      else "ACL2.acl2Count_cdr_lt_of_consp"
    s!"def {nameStr} {fmls} : SExpr :=\n  {bodyStr}\ntermination_by SExpr.acl2Count {arg}\ndecreasing_by all_goals exact {decreasingLemma} (by simp_all)"
  | args@(_ :: _ :: _) =>
    -- Multiple recursive args: use sum of acl2Count measures
    let bodyStr := translateExpr body (nativeIf := true)
    let measure := String.intercalate " + " (args.map fun a => s!"SExpr.acl2Count {a}")
    s!"def {nameStr} {fmls} : SExpr :=\n  {bodyStr}\ntermination_by {measure}\ndecreasing_by all_goals simp_all [ACL2.SExpr.acl2Count, ACL2.Logic.cdr, ACL2.Logic.car]; omega"
  | [] =>
    -- Check for evens/odds recursion pattern (e.g. msort, merge-sort-term-order)
    match findEvensOddsArg name formals body with
    | some arg =>
      let bodyStr := translateExpr body (nativeIf := true)
      s!"def {nameStr} {fmls} : SExpr :=\n  {bodyStr}\ntermination_by SExpr.acl2Count {arg}\ndecreasing_by all_goals first | exact ACL2.acl2Count_evens_lt (by simp_all) (by simp_all) | exact ACL2.acl2Count_odds_lt (by simp_all) (by simp_all)"
    | none =>
      let bodyStr := translateExpr body
      -- Check if body references the function name at all (simple recursion check)
      let isRecursive := (bodyStr.splitOn nameStr).length > 1
      if isRecursive then
        s!"partial def {nameStr} {fmls} : SExpr :=\n  {bodyStr}"
      else
        s!"def {nameStr} {fmls} : SExpr :=\n  {bodyStr}"

private def renderMetadataComment (info : TheoremInfo) : String :=
  let ruleClassLines :=
    match info.ruleClasses.map RuleClass.summary with
    | [] => []
    | ruleClasses => [s!"rule-classes: {String.intercalate ", " ruleClasses}"]
  let hintLines := info.hintGoals.map GoalHint.summary
  let instructionLines :=
    match info.instructions with
    | [] => []
    | instructions =>
        ["instructions:"] ++ (instructions.map (ProofInstruction.renderLines 2)).foldr List.append []
  let extraKeys := info.extraOptions.map (fun option => s!":{option.key}")
  let extraLines :=
    match extraKeys with
    | [] => []
    | keys => [s!"other-options: {String.intercalate ", " keys}"]
  let lines := ruleClassLines ++ hintLines ++ instructionLines ++ extraLines
  if lines.isEmpty then
    ""
  else
    let body := String.intercalate "\n" (lines.map fun line => s!"  {line}")
    s!"/- ACL2 metadata:\n{body}\n-/\n"

def translateDefthm (name : Symbol) (info : TheoremInfo) : String :=
  let nameStr := sanitizeName (translateSymbol name)
  let vars := (collectVars info.body []).reverse
  let fmls := String.intercalate " " (vars.map fun v => s!"({v} : SExpr)")
  let metaComment := renderMetadataComment info
  s!"{metaComment}theorem {nameStr} {fmls} : Logic.toBool ({translateExpr info.body}) = true :=\n  sorry"

private def uppercaseIfExpr : SExpr :=
  .cons
    (.atom (.symbol { name := "IF" }))
    (SExpr.ofList
      [ .t
      , .cons (.atom (.symbol { name := "CONS" }))
          (SExpr.ofList [ .atom (.symbol { name := "X" }), .nil ])
      , .nil
      ])

#guard translateSymbol { name := "BINARY-+" } = "Logic.plus"
#guard (translateExpr uppercaseIfExpr).startsWith "(Logic.if_"
#guard (translateDefthm { name := "PLUS-COMM" } { body := uppercaseIfExpr }).contains "theorem plus_comm"

end Translator

end ACL2
