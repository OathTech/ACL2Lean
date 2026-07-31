# Industrialization opportunities surfaced by the mirror program

(2026-07-31, mid-sorting-mirror-program — after ~15 hand-written
assemblies and ~12 exec kits in `Imported/Sorting.lean`. Raised by Mike
mid-arc: "are these mirror proofs revealing further opportunities for
industrialization?" Answer: yes, four concrete ones, one dominant.)

## 1. THE EXEC-KIT GENERATOR (dominant — ~70% of Sorting.lean)

Every world defun consumed by a mirror gets the same three hand-written
artifacts, all three MECHANICALLY DERIVABLE from the emitted `:DEFUN`
event:

- `<fn>Exec` — the shape-exact total Lean function. The transformation
  is a pure syntax walk over the emitted `:BODY`: `IF` → `ite` on
  `Logic.toBool`, builtin call → the `Logic.*`/`lexorder` twin,
  self/defn call → recursion/callee-exec, formal → argument.
  Termination comes from the emitted `:MEASURE`/`:MEASURED` (the
  justifications): `(ACL2-COUNT X)` → `termination_by x.consCount`,
  `(+ (ACL2-COUNT X) (ACL2-COUNT Y))` → the sum (merge2's shape), with
  the decrease obligations discharged by the Count library — exactly
  the totality prover's existing carve-out territory.
- `<fn>_exec_corr` — the stage-1 walk. IDENTICAL structure every time:
  one `re_val_var_get` per formal, `conv_builtin1/2` per builtin node,
  `conv_if_lift` per IF, `conv_defn_N` per defn call with the
  strong-induction IH at the recursive site. This proof is a fold over
  the same body syntax that generated the exec — a `derive_exec%`
  elaborator (MetaM, per-instance kernel-checked, the certifying-walker
  lane of the generality plan §walkers) could emit def + proof
  together. merge2 (pair measure) and msort (evens-decrease side
  lemmas) show the measure side needs the emitted justifications —
  which the `Development` already carries.
- `<fn>Exec_enc` — stage 2, the native reading. NOT fully mechanical
  (choosing `List.count`/`erase`/`filter`/`merge2L` is the human
  fidelity judgment — the mirror criterion's whole point), but the
  proof skeleton (induction + the same rw/simp cadence) is templatable.

## 2. Discharger generation (free once #1 exists)

`dis_<fn>_total` is literally `exec_corr` + one `⟨N, exec v, h⟩`
wrapper (see dis_merge2_total/dis_msort_total). `dis_<fn>_tp` is
arg-strictness + `val_unique` + ONE value-shape lemma about the exec;
the emitted corollary shapes observed so far form a small closed set
(boolean t-or-nil, consp, non-negative integer, true-listp, the
args-valued consp-or-second-arg). A registry of shape → proof-template
plus the generator covers every `total:`/`tp:` hypothesis seen in the
sorting program.

## 3. Env-binding boilerplate

Every assembly hand-writes `re_val_var_get` + `Env.get?_insert`
`if_pos/if_neg` chains per variable (5-15 lines each, ~20 copies). A
`bindVars`-style helper (assoc list in, the conv facts out) or a small
elaborator kills all of it.

## 4. Decode-ender consolidation

The per-formula decode combinators accreted in Sorting.lean —
`conv_if3` (guard-nest = conjunction), `bool_of_iff_truthy`,
`toBool_equal`, `conv_if_false'`, the implies/equal ender cadences —
belong in `Imported/Lifting.lean` as decode-kit v2 once the arc
closes (the take-the-dedup-when-noticed rule; they now have 3+ copies'
worth of consumers).

## 5. ACL2 term-quotation syntax (future, Mike's suggestion mid-arc)

The hand-built SExpr term nests — `ifT (conspT xT) (consT (carT xT) …)`
for every body and formula transcription — are the least readable part
of the support files and an easy place for a transcription typo the
build only catches indirectly (a formula that doesn't defeq-match the
log's). A Lean quotation macro (`acl2%⟪(IF (CONSP X) (CONS (CAR X) …))⟫`
elaborating to the SExpr value, or even parsing the emitted `:BODY`
string at elaboration time via the existing ProofLog reader) would make
bodies/formulas verbatim-comparable to the log. Not worth jumping into
now; natural companion to the exec-kit generator (#1), which would
subsume most body transcriptions anyway.

## Non-opportunity (flagged)

The `rule:` dischargers for included-book theorems (FOLD-CONSTS,
NOT-MEMB-…, and especially the upcoming CONVERT-PERM-TO-HOW-MANY)
prove real content at the value level in Lean — Lean doing ACL2's job
on the HYPOTHESIS side. The industrial fix is not a generator but the
tracked wiring: replay the dependency book's own log and discharge the
rule hypothesis from ITS replayed statement (needs cross-world
transfer). Until then each such discharger is a hand proof and should
stay conspicuous in review.
