import ACL2Lean.ProofLogTypes

namespace ACL2

/-- A local helper can be retained in the certification model when its name
has one definition there. Reusing its name for a different body requires
world scoping beyond the current flat model, so refuse that case rather than
silently making earlier proofs refer to a later definition. Ordinary existing
definition handling is unchanged. This checks source-event semantics, not a
count or a naming convention. -/
def checkLocalDefinitionNames (events : List ProofEvent) : Except String Unit := do
  let mut seen : List (String × List Symbol × SExpr × Bool) := []
  for ev in events do
    let data? := match ev with
      | .defun n fs body _ | .witnessDefun n fs body _ | .groundZeroDefun n fs body _ =>
        some (n, fs, body, false)
      | .localDefun n fs body _ => some (n, fs, body, true)
      | _ => none
    if let some (n, fs, body, localHelper) := data? then
      for (oldN, oldFs, oldBody, oldLocal) in seen do
        if n == oldN && (localHelper || oldLocal) && (fs != oldFs || body != oldBody) then
          throw s!"local helper '{n}' has conflicting definitions; scoped redefinition is unsupported"
      seen := (n, fs, body, localHelper) :: seen

end ACL2
