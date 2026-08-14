-- Root `ACL2Lean` library entry point.
-- THE MIRRORS (the product layer): pure-Lean specs/theorems, zero ACL2
import ACL2Lean.Mirrors.Basics
import ACL2Lean.Mirrors.Sorting
-- MIRROR PROOFS: the Props proved via replay (placement ruled 2026-08-12)
import ACL2Lean.MirrorProofs.Basics
import ACL2Lean.MirrorProofs.Sorting
import ACL2Lean.Syntax
import ACL2Lean.Parser
import ACL2Lean.Import
import ACL2Lean.Workbench
import ACL2Lean.EvalOpt
import ACL2Lean.WorldGen
import ACL2Lean.Translator
import ACL2Lean.Logic
import ACL2Lean.Count
import ACL2Lean.PrettyPrinter
import ACL2Lean.ProofLog
import ACL2Lean.ClauseId
import ACL2Lean.ProofTree
import ACL2Lean.ClauseTree
import ACL2Lean.Imported.Lifting
import ACL2Lean.Imported.SimpleWorld
import ACL2Lean.Imported.WaypointCatalog
import ACL2Lean.Lexorder
import ACL2Lean.LexorderOrder
import ACL2Lean.TermOrder
import ACL2Lean.Replay.Driver
