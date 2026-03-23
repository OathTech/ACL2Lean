import Lean
import ACL2Lean.DSL.SyntaxCategories
import ACL2Lean.Logic

open Lean Elab Command Term Meta

namespace ACL2

/-- Get the leaf string value of a syntax node. -/
partial def getLeafVal (stx : Syntax) : String :=
  if stx.isIdent then stx.getId.toString
  else if stx.isAtom then stx.getAtomVal
  else if let some n := stx.isNatLit? then toString n
  else if let some str := stx.isStrLit? then str
  else
    let args := stx.getArgs
    if args.size == 0 then ""
    else if args.size == 1 then getLeafVal args[0]!
    else
      let parts := args.toList.map getLeafVal
      if parts.contains "-" then
         "".intercalate parts
      else
         parts[0]!

/-- Sanitize ACL2 symbol names for Lean. -/
def sanitize (s : String) : Name :=
  let s' := s.trimAscii.toString
  let s' := s'.replace "-" "_"
  let s' := s'.replace "!" "_bang"
  let s' := s'.replace "?" "_p"
  let s' := s'.replace "+" "plus"
  let s' := if s' == "*" then "times" else s'.replace "*" "star"
  let s' := s'.replace "/" "div"
  let s' := s'.replace "<" "lt"
  let s' := s'.replace ">" "gt"
  let s' := s'.replace "=" "eq"
  let s' := if s' == "if" then "if_" else s'
  let s' := if s'.startsWith "_" then "v" ++ s' else s'
  let s'' := s'.trimAscii.toString
  if s'' == "" then Name.mkSimple "v_empty" else Name.mkSimple s''

/-- Map ACL2 built-ins to Lean Logic functions as Syntax. -/
def mapBuiltinStx (s : String) : Ident :=
  let name := match s.trimAscii.toString with
    | "+" => `_root_.ACL2.Logic.plus
    | "-" => `_root_.ACL2.Logic.minus
    | "*" => `_root_.ACL2.Logic.times
    | "/" => `_root_.ACL2.Logic.div
    | "<" => `_root_.ACL2.Logic.lt
    | "=" => `_root_.ACL2.Logic.eq
    | ">" => `_root_.ACL2.Logic.gt
    | "<=" => `_root_.ACL2.Logic.le
    | ">=" => `_root_.ACL2.Logic.ge
    | "zp" => `_root_.ACL2.Logic.zp
    | "evenp" => `_root_.ACL2.Logic.evenp
    | "equal" => `_root_.ACL2.Logic.equal
    | "consp" => `_root_.ACL2.Logic.consp
    | "atom" => `_root_.ACL2.Logic.atom
    | "car" => `_root_.ACL2.Logic.car
    | "cdr" => `_root_.ACL2.Logic.cdr
    | "cons" => `_root_.ACL2.Logic.cons
    | "not" => `_root_.ACL2.Logic.not
    | "and" => `_root_.ACL2.Logic.and
    | "or" => `_root_.ACL2.Logic.or
    | "implies" => `_root_.ACL2.Logic.implies
    | "if" => `if_
    | "stringp" => `_root_.ACL2.Logic.stringp
    | "string-append" => `_root_.ACL2.Logic.string_append
    | "logand" => `_root_.ACL2.Logic.logand
    | "logor" => `_root_.ACL2.Logic.logor
    | "logxor" => `_root_.ACL2.Logic.logxor
    | "lognot" => `_root_.ACL2.Logic.lognot
    | "ash" => `_root_.ACL2.Logic.ash
    | "append" => `_root_.ACL2.Logic.append
    | "len" => `_root_.ACL2.Logic.len
    | "true-listp" => `_root_.ACL2.Logic.trueListp
    | "iff" => `_root_.ACL2.Logic.iff
    | "force" => `_root_.ACL2.Logic.force
    | "double-rewrite" => `_root_.ACL2.Logic.double_rewrite
    | "evens" => `_root_.ACL2.Logic.evens
    | "odds" => `_root_.ACL2.Logic.odds
    | s' => sanitize s'
  mkIdent name

/-- Recursively strip category wrappers from syntax. -/
partial def stripWrappers (stx : Syntax) : Syntax :=
  if stx.isIdent || stx.isAtom || (stx.isNatLit?).isSome || (stx.isStrLit?).isSome then
    stx
  else
    let args := stx.getArgs
    if args.size == 1 then
      stripWrappers args[0]!
    else
      stx

/-- Translate ACL2 S-expression to a raw SExpr value in Lean. -/
partial def translateSExprValue (stx : Syntax) : MacroM (TSyntax `term) := do
  let s := stripWrappers stx
  if let some n := s.isNatLit? then
    let nStx := Lean.quote n
    return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.int (Int.ofNat $nStx)))))
  else if let some str := s.isStrLit? then
    let sStx := Lean.quote str
    return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.string $sStx)))
  else
    let name := (getLeafVal s |>.trimAscii).toString
    if let some n := name.toNat? then
       let nStx := Lean.quote n
       return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.int (Int.ofNat $nStx)))))
    else if name != "" && !name.contains '(' && !name.contains ')' && !name.contains ' ' then
      if name == "t" then return (← `(_root_.ACL2.SExpr.t))
      else if name == "nil" then return (← `(_root_.ACL2.SExpr.nil))
      else if name == "_" || name == "?" then return (← `(_))
      else
        let nameLit := Syntax.mkStrLit name
        return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.symbol { package := "ACL2", name := $nameLit })))
    else if stx.getArgs.size > 0 && stx[0]!.isAtom && stx[0]!.getAtomVal == "(" then
      let args := stx[1]!.getArgs
      let mut res ← `(_root_.ACL2.SExpr.nil)
      for i in [0:args.size] do
        let s' ← translateSExprValue args[args.size - 1 - i]!
        res ← `(_root_.ACL2.SExpr.cons $s' $res)
      return res
    else
      return (← `(_root_.ACL2.SExpr.nil))

/-- Detect built-ins to avoid collecting them as variables. -/
def isBuiltin (s : String) : Bool :=
  ["+", "-", "*", "/", "<", ">", "=", "<=", ">=", "if", "zp", "evenp", "equal", "consp", "atom", "car", "cdr", "cons", "not", "and", "or", "implies", "t", "nil", "quote", "let", "declare", "stringp", "string-append", "logand", "logor", "logxor", "lognot", "ash", "append", "len", "true-listp", "iff", "force", "double-rewrite", "evens", "odds"].contains s

/-- Collect free variables. -/
partial def collectFreeVars (stx : Syntax) : MacroM (List Ident) := do
  let s := stripWrappers stx
  if let some _ := s.isNatLit? then return []
  if let some _ := s.isStrLit? then return []
  let name := (getLeafVal s |>.trimAscii).toString
  if name.toNat?.isSome then return []
  if name != "" && !name.contains '(' && !name.contains ')' && !name.contains ' ' then
    if isBuiltin name || name == "_" || name == "?" then return []
    else return [mkIdent (sanitize name)]
  else if stx.getArgs.size > 0 && stx[0]!.isAtom && stx[0]!.getAtomVal == "(" then
    let args := stx[1]!.getArgs
    if args.size == 0 then return []
    else
      let fnName := (getLeafVal args[0]! |>.trimAscii).toString
      if fnName == "quote" || fnName == "declare" then return []
      let mut vars : List Ident := []
      for i in [1:args.size] do
        let avars ← collectFreeVars args[i]!
        vars := vars ++ avars
      return vars
  else
    return []

/-- Translate ACL2 S-expression to Lean code. -/
partial def translateSExpr (stx : Syntax) : MacroM (TSyntax `term) := do
  let s := stripWrappers stx
  if let some n := s.isNatLit? then
    let nLit := Syntax.mkNumLit (toString n)
    return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (ACL2.Number.int (Int.ofNat $nLit)))))
  else if let some str := s.isStrLit? then
    let sLit := Syntax.mkStrLit str
    return (← `(_root_.ACL2.SExpr.atom (ACL2.Atom.string $sLit)))
  else
    let name := (getLeafVal s |>.trimAscii).toString
    if let some n := name.toNat? then
       let nStx := Lean.quote n
       return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (ACL2.Number.int (Int.ofNat $nStx)))))
    else if name != "" && !name.contains '(' && !name.contains ')' && !name.contains ' ' then
      if name == "t" then return (← `(_root_.ACL2.SExpr.t))
      else if name == "nil" then return (← `(_root_.ACL2.SExpr.nil))
      else if name == "_" || name == "?" then return (← `(_))
      else return mkIdent (sanitize name)
    else if stx.getArgs.size > 0 && stx[0]!.isAtom && stx[0]!.getAtomVal == "(" then
      let args := stx[1]!.getArgs
      if args.size == 0 then return (← `(_root_.ACL2.SExpr.nil))
      else
        let firstAtom := args[0]!
        let fnName := (getLeafVal firstAtom |>.trimAscii).toString
        if fnName == "if" then
          if args.size == 4 then
            let c ← translateSExpr args[1]!
            let t ← translateSExpr args[2]!
            let e ← translateSExpr args[3]!
            return (← `(if _root_.ACL2.Logic.toBool $c then $t else $e))
          else
            Macro.throwError "if requires 3 arguments"
        else if fnName == "quote" then
          if args.size == 2 then
            translateSExprValue args[1]!
          else
            Macro.throwError "quote requires 1 argument"
        else if fnName == "let" then
          if args.size < 3 then Macro.throwError "let requires at least 2 arguments"
          let bindings := args[1]!
          let body := args[2]!
          let mut letBody ← translateSExpr body
          if bindings.getArgs.size > 0 && bindings[0]!.isAtom && bindings[0]!.getAtomVal == "(" then
             let bs := bindings[1]!.getArgs
             for b in bs.reverse do
               if b.getArgs.size > 0 && b[0]!.isAtom && b[0]!.getAtomVal == "(" then
                  let pair := b[1]!.getArgs
                  if pair.size == 2 then
                     let varName := (getLeafVal pair[0]! |>.trimAscii).toString
                     let varId := mkIdent (sanitize varName)
                     let valExpr ← translateSExpr pair[1]!
                     letBody ← `(let $varId := $valExpr; $letBody)
          return letBody
        else if fnName != "" then
          let fnIdent := mapBuiltinStx fnName
          let mut tArgs := #[]
          for i in [1:args.size] do
            let a' ← translateSExpr args[i]!
            tArgs := tArgs.push a'
          if fnName == "list" then
            return (← `(_root_.ACL2.Logic.list [$tArgs,*]))
          else
            return (← `($fnIdent $tArgs*))
        else
          Macro.throwError s!"Expected function name in application"
    else
      return (← `(_root_.ACL2.SExpr.nil))

/-- Tracking stobjs in the environment. -/
initialize stobjExtension : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    name          := `stobjExtension,
    addImportedFn := fun as => as.foldl (fun s a => a.foldl (fun s n => s.insert n) s) {},
    addEntryFn    := fun s n => s.insert n
  }

def isStobj (env : Environment) (n : Name) : Bool :=
  (stobjExtension.getState env).contains n

/-- Individual event elaborator marked as incremental. -/
syntax (name := aclEvent) "#acl_event " acl2_event : command

@[command_elab aclEvent, incremental]
def elabAclEvent : CommandElab := fun stx => do
  match stx with
  | `(#acl_event $ev:acl2_event) =>
    match ev with
    | `(acl2_event| (defun $id:acl2_id ( $[$args:acl2_id]* ) $[$bodyParts:acl2_sexpr]* ) $[termination_by $term?]? $[decreasing_by $dec?]?) =>
        let env ← getEnv
        let mut stobjDecls : NameSet := {}
        let mut realBodyParts : Array (TSyntax `acl2_sexpr) := #[]

        for part in bodyParts do
          let partRaw := part.raw
          if partRaw.getArgs.size > 0 && partRaw[0]!.isAtom && partRaw[0]!.getAtomVal == "(" then
             let dArgs := partRaw[1]!.getArgs
             if dArgs.size > 0 && (getLeafVal dArgs[0]! |>.trimAscii).toString == "declare" then
                for i in [1:dArgs.size] do
                   let d := dArgs[i]!
                   if d.getArgs.size > 0 && d[0]!.isAtom && d[0]!.getAtomVal == "(" then
                      let xArgs := d[1]!.getArgs
                      if xArgs.size > 0 && (getLeafVal xArgs[0]! |>.trimAscii).toString == "xargs" then
                         for j in [1:xArgs.size] do
                            if (getLeafVal xArgs[j]! |>.trimAscii).toString == ":stobjs" && j + 1 < xArgs.size then
                               let stobj := xArgs[j+1]!
                               stobjDecls := stobjDecls.insert (sanitize ((getLeafVal stobj |>.trimAscii).toString))
             else
                realBodyParts := realBodyParts.push part
          else
             realBodyParts := realBodyParts.push part

        let body' ← if realBodyParts.isEmpty then `(_root_.ACL2.SExpr.nil)
                    else liftMacroM <| translateSExpr realBodyParts[realBodyParts.size - 1]!

        let nameId := mkIdent (sanitize (getLeafVal id.raw |>.trimAscii.toString))
        let mut binders := #[]
        for arg in args do
          let argName := (getLeafVal arg.raw |>.trimAscii).toString
          let argSan := sanitize argName
          if isStobj env argSan || stobjDecls.contains argSan then
             binders := binders.push (← `(bracketedBinder| ($(mkIdent argSan) : $(mkIdent argSan))))
          else
             binders := binders.push (← `(bracketedBinder| ($(mkIdent argSan) : _root_.ACL2.SExpr)))

        if let some t := term? then
          if let some d := dec? then
            let cmd ← `(def $nameId $[$binders]* := $body' termination_by $t decreasing_by $d)
            elabCommand cmd
          else
            let cmd ← `(def $nameId $[$binders]* := $body' termination_by $t)
            elabCommand cmd
        else
          let cmd ← `(def $nameId $[$binders]* := $body')
          elabCommand cmd
    | `(acl2_event| (defthm $id:acl2_id $prop:acl2_sexpr ) $[: $proof:term]?) =>
        let prop' ← liftMacroM <| translateSExpr prop
        let vars ← liftMacroM <| collectFreeVars prop
        let nameId := mkIdent (sanitize (getLeafVal id.raw |>.trimAscii.toString))
        let mut seen := #[]
        let mut binders := #[]
        for v in vars do
          if !seen.contains v.getId then
            seen := seen.push v.getId
            binders := binders.push (← `(bracketedBinder| ($v : _root_.ACL2.SExpr)))

        if let some p := proof then
          let cmd ← `(set_option maxHeartbeats 1000000 in theorem $nameId $[$binders]* : _root_.ACL2.Logic.toBool $prop' = true := $p)
          elabCommand cmd
        else
          let cmd ← `(set_option maxHeartbeats 1000000 in theorem $nameId $[$binders]* : _root_.ACL2.Logic.toBool $prop' = true := by
            sorry)
          elabCommand cmd
    | `(acl2_event| (defconst $id:acl2_id $val:acl2_sexpr)) =>
        let nameId := mkIdent (sanitize (getLeafVal id.raw |>.trimAscii.toString))
        let val' ← liftMacroM <| translateSExprValue val
        let cmd ← `(def $nameId : _root_.ACL2.SExpr := $val')
        elabCommand cmd
    | `(acl2_event| (defrec $id:acl2_id ( $[$fields:acl2_id]* ) $body:acl2_sexpr)) =>
        let nameId := mkIdent (sanitize (getLeafVal id.raw |>.trimAscii.toString))
        let mut structFields := #[]
        for field in fields do
          let fieldName := mkIdent (sanitize (getLeafVal field.raw |>.trimAscii.toString))
          structFields := structFields.push (← `(Lean.Parser.Command.structExplicitBinder| ($fieldName : _root_.ACL2.SExpr)))
        let cmd ← `(structure $nameId where $[$structFields]*)
        elabCommand cmd
    | `(acl2_event| (defstobj $id:acl2_id $[$fields:acl2_sexpr]*)) =>
        let stobjNameStr := (getLeafVal id.raw |>.trimAscii).toString
        let stobjName := sanitize stobjNameStr
        let stobjId := mkIdent stobjName

        let mut structFields := #[]
        let mut fieldSpecs := #[]

        for field in fields do
          let (fieldName, initVal) ← match field with
            | `(acl2_sexpr| $i:acl2_id) => pure ((getLeafVal i.raw |>.trimAscii).toString, ← `(_root_.ACL2.SExpr.nil))
            | `(acl2_sexpr| ($ss*)) =>
                let ssArgs := ss
                if ssArgs.isEmpty then throwUnsupportedSyntax
                let name := (getLeafVal ssArgs[0]! |>.trimAscii).toString
                let mut init := ← `(_root_.ACL2.SExpr.nil)
                for i in [1:ssArgs.size] do
                  let s := ssArgs[i]!
                  if (getLeafVal s |>.trimAscii).toString == ":init" && i + 1 < ssArgs.size then
                    init ← liftMacroM <| translateSExprValue ss[i+1]!
                pure (name, init)
            | _ => throwUnsupportedSyntax

          let fldSan := sanitize fieldName
          let fldId := mkIdent fldSan
          structFields := structFields.push (← `(Lean.Parser.Command.structExplicitBinder| ($fldId : _root_.ACL2.SExpr := $initVal)))
          fieldSpecs := fieldSpecs.push (fieldName, fldId)

        let structCmd ← `(structure $stobjId where $[$structFields]* deriving _root_.Repr)
        elabCommand structCmd

        modifyEnv fun env => stobjExtension.addEntry env stobjName

        let monadId := mkIdent (Name.mkSimple (stobjName.toString ++ "M"))
        let monadCmd ← `(abbrev $monadId := StateM $stobjId)
        elabCommand monadCmd

        for (fieldName, fldId) in fieldSpecs do
          let accId := mkIdent (sanitize fieldName)
          elabCommand (← `(def $accId (s : $stobjId) : _root_.ACL2.SExpr := s.$fldId))

          let accIdM := mkIdent (Name.mkSimple ((sanitize fieldName).toString ++ "M"))
          elabCommand (← `(def $accIdM : $monadId _root_.ACL2.SExpr := do return (← get).$fldId))

          let updName := "update-" ++ fieldName
          let updId := mkIdent (sanitize updName)
          elabCommand (← `(def $updId (val : _root_.ACL2.SExpr) (s : $stobjId) : $stobjId := { s with $fldId:ident := val }))

          let updIdM := mkIdent (sanitize (updName ++ "M"))
          elabCommand (← `(def $updIdM (val : _root_.ACL2.SExpr) : $monadId Unit := modify fun s => { s with $fldId:ident := val }))
    | _ => pure ()
  | _ => throwUnsupportedSyntax

syntax "#acl" "{" acl2_event* "}" : command

/-- The #acl block now expands to individual incremental #acl_event calls. -/
macro_rules
  | `(#acl { $events* }) => do
      let mut res := #[]
      for ev in events do
        res := res.push (← `(#acl_event $ev))
      return mkNullNode res

end ACL2
