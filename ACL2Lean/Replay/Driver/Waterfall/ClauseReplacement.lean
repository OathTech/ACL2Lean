import ACL2Lean.Syntax

namespace ACL2.Replay.Driver
open ACL2

/-- Quote-opaque replacement of a term, including an existing supported
compound lhs. This computes an endpoint; the edit consumer must separately
prove its conversion through the supported equality congruences. -/
partial def replaceTermOcc (src dst : SExpr) (t : SExpr) : SExpr :=
  if t == src then dst
  else match t with
    | .cons h args =>
      match h with
      | .atom (.symbol q) =>
        if q.name == "QUOTE" then t
        else .cons h (replaceArgs args)
      | _ => .cons (replaceTermOcc src dst h) (replaceArgs args)
    | _ => t
where
  replaceArgs : SExpr → SExpr
    | .cons a rest => .cons (replaceTermOcc src dst a) (replaceArgs rest)
    | e => e

end ACL2.Replay.Driver
