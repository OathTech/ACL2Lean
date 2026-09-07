import ACL2Lean.Replay.Runner

/-! Inspect complete reconstructed theorem trees without attempting replay.
Usage: lake env lean --run scripts/replay-mechanism-inventory.lean LOG OUT THEOREM...
The JSONL output is structural evidence, never a proof or a support verdict.
All addresses refer to the reconstructed tree; branch segments and processor
inputs are retained without pretending that they are checked Lean premises. -/

open ACL2 ACL2.Replay.Driver ACL2.Replay.Runner Lean

private def js (s : String) : Json := Json.str s
private def sexprs (xs : List SExpr) : Json := toJson (xs.map toString)

private structure Location where
  log : String
  theoremName : String
  address : String
  clause : List SExpr
  segments : List SExpr := []

private def emit (out : IO.FS.Handle) (loc : Location)
    (kind : String) (fields : List (String × Json)) : IO Unit :=
  out.putStrLn (Json.mkObj ([
    ("kind", js kind), ("log", js loc.log), ("theorem", js loc.theoremName),
    ("address", js loc.address), ("input_clause", sexprs loc.clause),
    ("branch_segments", sexprs loc.segments)] ++ fields)).compress

private partial def visitNode (out : IO.FS.Handle) (loc : Location)
    (n : ProofNode) : IO Unit := do
  let .node rune lhs rhs children p := n
  emit out loc "node" [
    ("rune_type", js rune.ty), ("rune_name", js rune.name),
    ("origin", js p.origin), ("lhs", js (toString lhs)), ("rhs", js (toString rhs)),
    ("child_count", toJson children.length), ("inner_kind", js p.innerKind),
    ("runes", toJson (p.runes.map reprStr)), ("ta_runes", toJson (p.taRunes.map reprStr)),
    ("recognizer_basis", js (reprStr p.recogBasis)),
    ("argument_leaf_count", toJson p.argLeaves.length),
    ("provenance", js (reprStr p))]
  for (child, i) in children.zipIdx do
    visitNode out {loc with address := s!"{loc.address}/node:{i}"} child

private partial def visitItems (out : IO.FS.Handle) (loc : Location)
    (items : List ClauseItem) : IO Unit := do
  for (item, i) in items.zipIdx do
    let here := {loc with address := s!"{loc.address}/item:{i}"}
    match item with
    | .literal lp =>
      emit out here "literal" [
        ("index", toJson lp.index), ("literal", js (toString lp.literal)),
        ("not_flag", toJson lp.notFlg), ("result", js (toString lp.result)),
        ("split_trace", js (reprStr lp.splitTrace)),
        ("duplicate_drops", sexprs lp.dedupDrops),
        ("complement_closes", sexprs lp.complementCloses)]
      for (node, j) in lp.nodes.zipIdx do
        visitNode out {here with address := s!"{here.address}/node:{j}"} node
    | .step n => visitNode out here n
    | .branch segment rest =>
      emit out here "branch" [("segment", js (toString segment))]
      visitItems out {here with segments := here.segments ++ [segment]} rest
    | .linearEquation info => emit out here "linear-equation" [("record", js (reprStr info))]
    | .unhideLiteral info => emit out here "unhide-literal" [("record", js (reprStr info))]
    | .clausify info => emit out here "clausify" [("record", js (reprStr info))]
    | .useHint hyps constraint apps lmis translated folds =>
      emit out here "use" [("hypotheses", sexprs hyps),
        ("constraint", sexprs constraint), ("application_clauses", toJson (apps.map (·.map toString))),
        ("instances", sexprs lmis), ("translated_instances", js (reprStr translated)),
        ("instance_folds", js (reprStr folds))]
    | .fcDerivations ds => emit out here "forward-chain" [("records", sexprs ds)]
    | .complementClose lit => emit out here "complement-close" [("literal", js (toString lit))]
    | .dedupDrop lit => emit out here "duplicate-drop" [("literal", js (toString lit))]
    | .taSubst new_ from_ ts substNew substOld =>
      emit out here "type-alist-substitution" [("new", js (toString new_)),
        ("from", js (toString from_)), ("type_set", toJson ts),
        ("substitution_new", js (toString substNew)), ("substitution_old", js (toString substOld))]

private partial def visitClause (out : IO.FS.Handle) (loc : Location)
    (cn : ClauseNode) : IO Unit := do
  let here := {loc with clause := cn.inputClause, address := s!"{loc.address}/clause:{cn.idStr}"}
  emit out here "clause" [("induction", js (reprStr cn.induction)),
    ("child_count", toJson cn.children.length)]
  for (step, i) in cn.steps.zipIdx do
    let atStep : Location :=
      { here with
        address := s!"{here.address}/processor:{i}:{step.processor}"
        clause := step.inputClause?.getD cn.inputClause }
    emit out atStep "processor" [("processor", js step.processor),
      ("result", js (reprStr step.result)), ("runes", toJson (step.runes.map reprStr)),
      ("new_clauses", sexprs step.newClauses), ("extra_fields", js (reprStr step.extraFields)),
      ("has_recorded_input", toJson step.inputClause?.isSome)]
    visitItems out atStep step.items
  for (child, i) in cn.children.zipIdx do
    visitClause out {here with address := s!"{here.address}/child:{i}"} child

def main (args : List String) : IO UInt32 := do
  let logPath :: outputPath :: names := args
    | throw (IO.userError "usage: LOG OUT THEOREM...")
  unless !names.isEmpty do throw (IO.userError "at least one theorem is required")
  let parsed ← match ProofLog.parse (← IO.FS.readFile logPath) with
    | .ok value => pure value
    | .error err => throw (IO.userError s!"parse: {err}")
  let dev ← match ClauseTree.buildDevelopment parsed with
    | .ok value => pure value
    | .error err => throw (IO.userError s!"reconstruction: {err}")
  IO.FS.withFile outputPath .write fun out => do
    for name in names do
      let some cp := findThm dev name | throw (IO.userError s!"theorem absent: {name}")
      let loc : Location := ⟨logPath, name, "theorem", [], []⟩
      emit out loc "theorem" [("formula", js (toString cp.formula)),
        ("has_tree", toJson cp.root.isSome)]
      let some root := cp.root | throw (IO.userError s!"proof tree absent: {name}")
      visitClause out loc root
  IO.println s!"Inventoried {names.length} complete trees into {outputPath}; no replay attempted."
  return 0
