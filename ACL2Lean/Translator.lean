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

/-- Translate an SExpr literal value into Lean SExpr constructor syntax. -/
partial def translateLiteral : SExpr → String
  | .nil => "SExpr.nil"
  | .atom (.symbol s) => s!"(SExpr.atom (.symbol \{ name := \"{s.name}\" }))"
  | .atom (.number (.int n)) => s!"(SExpr.atom (.number (.int ({n}))))"
  | .atom (.number (.rational n d)) => s!"(SExpr.atom (.number (.rational ({n}) ({d}))))"
  | .atom (.number (.decimal m e)) => s!"(SExpr.atom (.number (.decimal ({m}) ({e}))))"
  | .atom (.string s) => s!"(SExpr.atom (.string \"{s}\"))"
  | .atom (.keyword k) => s!"(SExpr.atom (.keyword \"{k}\"))"
  | .cons a b => s!"(SExpr.cons {translateLiteral a} {translateLiteral b})"

def sanitizeName (s : String) : String :=
  let s := s.replace "-" "_"
  let s := s.replace "=" "_eq_"
  let s := s.replace "+" "_plus_"
  let s := s.replace "*" "_times_"
  let s := s.replace "/" "_div_"
  let s := s.replace "Logic." ""
  s

#guard translateSymbol { name := "BINARY-+" } = "Logic.plus"
#guard sanitizeName "my-len-my-app" = "my_len_my_app"

end Translator

end ACL2
