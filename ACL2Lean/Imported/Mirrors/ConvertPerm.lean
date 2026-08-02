import ACL2Lean.Imported.Mirrors.Macro

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-- The parsed development — the ONLY input is the log. -/
private def convertPermLog : String :=
  include_str "../../../acl2_samples/sorting/convert-perm-to-how-many.proof-log"

/-- The convert-perm-to-how-many DEPENDENCY development (2a): its theorem
    trees are offered via `deps [convertPermDev]` so consumer rows'
    included `rule:` hypotheses (NOT-MEMB-IMPLIES-HOW-MANY-IS-0 today)
    discharge by replaying the dependency's tree at the CONSUMER's world —
    no `derive_world`: the dev is a tree source only. -/
def convertPermDev : Development :=
  (((ProofLog.parse convertPermLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

end ACL2.Imported.Mirrors
