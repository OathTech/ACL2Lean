/-
  G3 Fragment A — the DP value lift as a VERIFIED PURE FUNCTION.

  `dpLiftF` computes the lifted `Logic`-primitive value of a clause term over
  the env's variable values and a pinned-opaque assoc list — the pure twin of
  the driver's `dpValExpr` meta-walker, with the SAME fixed primitive table
  and the SAME frontiers (an unknown head returns `none`; the caller
  hard-fails exactly as the walker did). `dpLiftF_sound` is the once-proved
  soundness lemma (G3: the walker's per-node `mkAppM` proof chains are
  replaced by ONE lemma instantiation over a kernel-computable function).

  Fragment-local per invariant L1 (own function, own lemma, composes at the
  convergence-judgment layer); world-parametric per L3 (the world enters
  only through the no-shadow premises). Design + decisions:
  docs/plans/2026-06-12_g3-consolidations.md.
-/
import ACL2Lean.Replay.EvalLemmas

namespace ACL2.Replay

open ACL2

/-- The DP-lift primitive heads (the FIXED table — mirrors the driver's
    `dpUnary`/`dpBinary`; anything else with a symbol head is opaque). -/
def dpLiftHeads : List String :=
  ["not", "zp", "consp", "integerp", "acl2-numberp", "true-listp", "car",
   "cdr", "equal", "<", "binary-+", "binary-*", "cons", "implies", "iff"]

/-- The DP value lift (G3 Fragment A): variable values from `env` (with
    ACL2's t/nil self-evaluation for unbound symbols, mirroring `evalOpt`'s
    variable case exactly), opaque application values from `opq` (syntactic
    `==` lookup, checked FIRST — mirroring the walker's order), `quote`
    transparent, `if` STRICT in both branches (the walker's
    value-characterized form: `cond (toBool cv) tv ev`), and the fixed
    primitive table via `callBuiltin` (alignment with the evaluator by
    construction). An unknown shape is `none` — the FRONTIER, not a default:
    the caller hard-fails on it exactly as `dpValExpr` did. -/
def dpLiftF (env : Env) (opq : List (SExpr × SExpr)) : SExpr → Option SExpr
  | t@(.atom (.symbol s)) =>
    match opq.find? (fun (o, _) => o == t) with
    | some (_, v) => some v
    | none =>
      match env.get? s with
      | some v => some v
      | none => if s.isNamed "t" then some SExpr.t else some SExpr.nil
  | t@(.cons (.atom (.symbol fs)) args) =>
    match opq.find? (fun (o, _) => o == t) with
    | some (_, v) => some v
    | none =>
      if fs.isNamed "quote" then
        match args with
        | .cons v .nil => some v
        | _ => none
      else if fs.isNamed "if" then
        match args with
        | .cons c (.cons thn (.cons els .nil)) => do
          let cv ← dpLiftF env opq c
          let tv ← dpLiftF env opq thn
          let ev ← dpLiftF env opq els
          some (cond (Logic.toBool cv) tv ev)
        | _ => none
      else if dpLiftHeads.contains fs.name then
        match args with
        | .cons a .nil => do
          let av ← dpLiftF env opq a
          callBuiltin fs.name [av]
        | .cons a (.cons b .nil) => do
          let av ← dpLiftF env opq a
          let bv ← dpLiftF env opq b
          callBuiltin fs.name [av, bv]
        | _ => none
      else none
  | t =>
    match opq.find? (fun (o, _) => o == t) with
    | some (_, v) => some v
    | none => none

end ACL2.Replay
