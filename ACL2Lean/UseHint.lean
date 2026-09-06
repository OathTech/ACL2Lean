import ACL2Lean.Syntax

namespace ACL2

/-- Select the substitution record produced by ACL2's translator. The raw
LMI is retained for attribution. Only a plain named variable instance may
change; the other classes keep their existing syntax and replay frontier.
This validates record alignment, not macro expansion. The consuming proof
still checks the instantiated dependency formula against the emitted hyp. -/
def resolveUseLmis (raw : List SExpr) (translated : Option (List SExpr))
    (hypCount : Nat) : Except String (List SExpr) := do
  let some translated := translated | return raw
  unless raw.length == hypCount && translated.length == hypCount do
    throw "USE-HINT: source/translated LMI lists must align with :HYPS"
  for (source, target) in raw.zip translated do
    if source == target then continue
    match source.toList?, target.toList? with
    | some (.atom (.keyword "INSTANCE") :: .atom (.symbol n) :: _),
      some (.atom (.keyword "INSTANCE") :: .atom (.symbol m) :: pairs) =>
      unless n == m do throw "USE-HINT: translated instance changes the cited theorem"
      let mut seen : List Symbol := []
      for pair in pairs do
        let some [.atom (.symbol v), _] := pair.toList?
          | throw "USE-HINT: malformed translated variable substitution"
        if seen.contains v then throw "USE-HINT: duplicate translated substitution variable"
        seen := v :: seen
    | _, _ => throw "USE-HINT: translation changed an unsupported LMI class"
  return translated

end ACL2
