# Industrialization opportunities surfaced by the mirror program

> **TERMINOLOGY (added 2026-08-13).** This is a dated record. "Mirror"
> below means **WAYPOINT** in today's vocabulary (`docs/LEXICON.md`).
> Where this file conflicts with the lexicon, the lexicon wins.

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

### v1 scope (sorting-absolute arc 1b, measure-class inventory 2026-08-01)

Read off the ~20 hand kits in `Imported/Sorting.lean`; the decrease
obligation class determines what the generator can emit:

- **Class M1 — `(ACL2-COUNT v)` + destructor-chain recursive args**
  (insert, isort, how-many, rel, all-rel, filter, append, orderedp,
  evens' cddr, …): `termination_by v.consCount`, decrease = a chain of
  `consCount_cdr_le`/`consCount_car_le` ending in
  `consCount_cdr_lt_of_consp`/`_car_` at the consp-ruled variable (the
  ruling test is in scope from the IF context). Fully mechanical; the
  bulk of the kits.
- **Class M2 — `(+ (ACL2-COUNT x) (ACL2-COUNT y))`** (merge2):
  `Nat.strong_induction_on` over the sum; per-call-site
  `consCount_cdr_sum_lt_left/right_consp`. Mechanical, one template
  variant.
- **Class M3 — decrease THROUGH a defined function** (msort's
  `(EVENS l)` sites, qsort's `(FILTER …)` sites — need
  `evensExec_consCount_le/lt` / `filterExec_consCount_le` side lemmas):
  HARD-FAIL in v1 (msort/qsort keep their hand kits); a side-lemma
  registry hook is the v2 extension, keyed by the emitted
  justification's measured-decrease term.

The `_exec_corr` proof template is measure-class-independent: one
`re_val_var_get` per formal, `conv_builtin1/2` per builtin node,
`conv_if_lift` per IF, `conv_defn_N` per defn call, IH at recursive
sites with the same Count lemma chain as the decrease. Validation
protocol: regenerate the hand kits, require statement match, retire
incrementally.

### BUILT (sub-arc mdd/exec-gen, 2026-08-01)

`Imported/ExecGen.lean`: `derive_exec%` generates def + corr (M1 + M2),
kit registry (persistent env extension), canonical telescope
(callee-then-self defn hyps; twin-table-order builtin hyps — reproduces
every hand telescope), the generic `bindArgs_get_head/tail` pair
(item 3 RETIRED), goal-driven corr walk with unification holes.
RETIRED same-name+same-statement (~600 hand lines): insert, isort,
how-many, rel (non-recursive), all-rel, filter, evens (cddr chain) —
M1 — and merge2 (M2, Nat strong induction over the pair sum).
REMAINING HAND KITS, each a named v1 frontier: msort/qsort (M3
decrease-through-function), oLt (dite guard + M3 via oFirstExpt + the
Logic.lt twin), acl2Count (CAR-descent pair + dead COMPLEX-RATIONALP
branch by contradiction + integerAbs/length callees), append/orderedp/
chain2 (parameterized-body schematics), pce (check), memb/rm/perm
(Imported/Perm.lean — M1-shaped, retirable when that module is next
touched). v2 backlog: M3 side-lemma registry hook; log-side body
extraction with the quotation macro (§5); dite guards; corr doc
comments (audit H2). FIDELITY STATUS (audit F4): the `measured`
indices and body constants are HAND-TRANSCRIBED from the emitted
:MEASURE/:BODY and were cross-checked against the real logs at the
sub-arc audit (8/8 match); the generator itself reads neither — the
log-side anchoring is the consumers' `by decide` world facts until
v2's log extraction lands. Fold-back audit 2026-08-01 (1 Opus,
adversarial): no soundness findings; F1/F2/F3 fail-open holes FIXED
(sanitization-collision + duplicate-registration guards), F4b FIXED
(measured clause required iff recursive), H1 orphans deleted.

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

## 6. Unify `driver_replayed%` with the runner's replay entry point

The macro accreted the runner's channels one hard-failure at a time —
`fcRules` (BUG-class: the isort FC snapshot), the termination pre-pass
(`with_termination`, qsort's non-destructor decreases; now with a
world-scoped cache since re-replaying the admission per row is
minutes), and `equivRefls` (ORDERED-PERMS' `(PERM u u)` evidence).
Every future runner channel will miss the macro the same way. ONE
shared replay-configuration builder (dev → cfg + all channels)
consumed by both the runner and the macro removes the class.

## Non-opportunity (flagged) — PARTIALLY RETIRED (2a, 2026-08-01)

The `rule:` dischargers for included-book theorems (FOLD-CONSTS,
NOT-MEMB-…, and especially the upcoming CONVERT-PERM-TO-HOW-MANY)
prove real content at the value level in Lean — Lean doing ACL2's job
on the HYPOTHESIS side. The industrial fix is not a generator but the
tracked wiring: replay the dependency book's own log and discharge the
rule hypothesis from ITS replayed statement (needs cross-world
transfer). Until then each such discharger is a hand proof and should
stay conspicuous in review.

**2a status (sub-arc mdd/cross-world):** the wiring EXISTS — prior
books' theorem trees ride the shared `depProofs` channel (sweep:
corpus-order accumulation; macro: the `deps [devs]` clause; CLI:
`--deps`), and `dischargeRuleHyp`'s no-registry route re-replays the
dependency tree AT THE CONSUMER'S WORLD, kernel-checked, formula
cross-checked against the stored rule. RETIRED:
`dis_not_memb_how_many_0` (9 consumer rows discharge from
NOT-MEMB-IMPLIES-HOW-MANY-IS-0's replayed tree). STILL HAND, each for
a stated reason: `dis_convert_perm` (the dependency theorem itself is
R7-blocked — retires when 2d lands), the arithmetic-3 family + gz
rules (no captured logs — value-level gz dischargers are the faithful
route), `dis_rule_orderedp_append` (same-book, discharged from the
theorem's own replayed statement already).
