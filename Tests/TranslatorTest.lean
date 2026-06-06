import ACL2Lean.Translator

open ACL2

-- === translateSymbol ===

#guard Translator.translateSymbol { name := "binary-+" } = "Logic.plus"
#guard Translator.translateSymbol { name := "binary--" } = "Logic.minus"
#guard Translator.translateSymbol { name := "binary-*" } = "Logic.times"
#guard Translator.translateSymbol { name := "<" } = "Logic.lt"
#guard Translator.translateSymbol { name := "car" } = "Logic.car"
#guard Translator.translateSymbol { name := "cdr" } = "Logic.cdr"
#guard Translator.translateSymbol { name := "cons" } = "Logic.cons"
#guard Translator.translateSymbol { name := "equal" } = "Logic.equal"
#guard Translator.translateSymbol { name := "if" } = "Logic.if_"
#guard Translator.translateSymbol { name := "iff" } = "Logic.iff"
#guard Translator.translateSymbol { name := "force" } = "Logic.force"
#guard Translator.translateSymbol { name := "evens" } = "Logic.evens"
#guard Translator.translateSymbol { name := "odds" } = "Logic.odds"
#guard Translator.translateSymbol { name := "string-append" } = "Logic.string_append"
#guard Translator.translateSymbol { name := "true-listp" } = "Logic.trueListp"
#guard Translator.translateSymbol { name := "acl2-count" } = "SExpr.acl2Count"

-- Unmapped symbols: hyphen → underscore
#guard Translator.translateSymbol { name := "my-fun" } = "my_fun"

-- Special character escaping
#guard (Translator.translateSymbol { name := "check!" }).contains "_bang"
#guard (Translator.translateSymbol { name := "valid?" }).contains "_p"

-- === translateLiteral ===

#guard Translator.translateLiteral .nil = "SExpr.nil"
#guard (Translator.translateLiteral (.atom (.symbol { name := "foo" }))).contains "foo"
#guard (Translator.translateLiteral (.atom (.number (.int 42)))).contains "42"
#guard (Translator.translateLiteral (.cons .nil .nil)).contains "SExpr.cons"

-- === sanitizeName ===

#guard Translator.sanitizeName "my-theorem" = "my_theorem"
#guard Translator.sanitizeName "x=y" = "x_eq_y"
#guard Translator.sanitizeName "x+y" = "x_plus_y"
#guard Translator.sanitizeName "x*y" = "x_times_y"
#guard Translator.sanitizeName "x/y" = "x_div_y"
#guard Translator.sanitizeName "Logic.foo" = "foo"
