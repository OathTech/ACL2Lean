import ACL2Lean.ProofLogTypes

/-! Parsing recorded rewrite paths, including binding-hypothesis boundaries. -/

namespace ACL2.ProofLog

/-- Parse one `(bkptr . fn)` frame of a `:PATH`. Numeric `bkptr` → `.arg`; symbolic
    `bkptr` (BODY/RHS/EXPANSION/…) → `.boundary`; `(RHS . i)` → indexed
    `.bindingRhs`. Lambda argument frames retain the lambda term. Other
    shapes hard-fail; an indexed binding boundary requires positive `i`. -/
def parsePathFrame (pair : SExpr) : Except String PathFrame := do
  -- Each frame is the dotted pair `(bkptr . fn)` = `.cons bkptr fn`.
  let (bk, fn) ← match pair with
    | .cons bk fn => pure (bk, fn)
    | _ => throw s!"REWRITE-STEP :PATH frame not a (bkptr . fn) pair: {repr pair}"
  match fn with
    | .atom (.symbol s) =>
      match bk with
      | .atom (.number (.int n)) => pure (.arg n.toNat s)
      | .atom (.symbol k) => pure (.boundary k s)
      | .cons (.atom (.symbol k)) (.atom (.number (.int n))) =>
        if k.name == "RHS" && k.package == "ACL2" && n > 0 then
          pure (.bindingRhs n.toNat s)
        else throw s!"REWRITE-STEP :PATH invalid binding-RHS boundary: {repr bk}"
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

end ACL2.ProofLog
