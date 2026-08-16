<!-- End-of-branch audit report, persisted verbatim from the auditor's final text (2026-08-16). Auditor: A4 — stale buildout material (Opus, deletion-review standard). Branch: mdd/t12-sprint @ 388089d. Synthesis: docs/audits/2026-08-16_eob-audit-synthesis.md -->

## A4 — STALE BUILDOUT MATERIAL: cleanup review

Method: token-level reference closure over all 245 tracked `.lean` files (dot-notation, `` `name `` quotes, `simp [..]` sets and comment mentions all count as consumers), plus the same scan re-run at the merge-base (`15b016d`) to separate *pre-existing* orphans from ones the sprint's own retirements created. Attribute-registered decls, self-elaborating pin defs and gate-constructed names were excluded as roots after each produced a false positive on the first pass. **Nothing was changed; I removed only the throwaway git worktree I created under `.tmp/`.**

Headline: the sprint added almost no dead code (3 new unreferenced decls, one of them a false positive). What it left behind is **orphaning** — it retired ~40 conditions and 5 sorries, and the vocabulary, hand proofs and docstrings that served them are still in the tree.

---

### DELETE-NOW (zero consumers, verified, low judgment)

**1. `scripts/waypoint-metrics.sh:37` — broken since P4b.** The `hand_files` array still lists `ACL2Lean/Imported/GzPrelude.lean`, deleted in `c7aa470`. With `set -euo pipefail`, the `cat "${hand_files[@]}" | wc -l` substitution fails and the script **exits 1** — I ran it: the "hand lines per catalog native" metric (one of the two ruled 2026-08-11 success metrics) has produced no output since 2026-08-15. It went unnoticed because `waypoint-metrics` is a standalone recipe (`Justfile:40`), not part of `just ci` (`Justfile:78`). One-line delete.

**2. `Tests/SortingPins.lean:374-429` — the orphaned `cond[…]` hypothesis-shape vocabulary (~56 lines).** `totalHyp1` (:374), `totalHyp2` (:380), `tpNonnegInt2` (:391), `tpPred1` (:399), and by cascade `ruleEqHyp` (:413) / `ruleEqHyp1` (:417) whose only remaining users are items 3 below.
Evidence — merge-base → HEAD reference counts: `totalHyp1` 20 → **0**, `totalHyp2` 12 → **0**, `tpPred1` 3 → **0**, `ruleEqHyp` 24 → 2 (both inside dead defs). `tpNonnegInt2` was already 0 at merge-base — the P1-era executor's note was right and never actioned. The file's own convention already deleted the twins for exactly this reason (`tpNonnegInt1` tombstone at :386, `tpPred2` at :404: *"a pin vocabulary with no pin is cruft"*).

**3. `Tests/SortingPins.lean:1061-1101` — `trueListpRmHyp` / `convertPermHyp` (~41 lines).** 3 uses each at merge-base → 0 (retired by the P3c cross-book D1 transfer, diagnosed in place at :475-481).

**4. `Tests/SortingPins.lean:362` — `private def synpQuotep`.** Zero uses, and a duplicate of the live copy at `ACL2Lean/Replay/GzRules.lean:284`. Dead already at merge-base.

**5. `ACL2Lean/Replay/Lemmas/Totality.lean:302-348` — `totality_1_rec` + `totality_2_rec` (~47 lines).** Answering the brief directly: **the old wrappers were not deleted when the `_mu` twins landed.** `Provers.lean:223` calls `totality_1_rec_mu` (`Judgments.lean:1355`); `totality_2_rec_snd` (:349) survives and *is* live, but `totality_1_rec`/`totality_2_rec` have zero references anywhere.

**6. `ACL2Lean/Replay/MeasureTable.lean:160-171` — `MeasureShape.positionsIn` (12 lines), sprint-added (`b3f6174`, R3).** Never called. `ExecGen.lean:852-855` builds `MeasurePos` values inline from its own transcribed `measured` clause. Worth flagging beyond hygiene: R3's remedy for the overspecialization audit's **F13 cross-layer asymmetry** landed the shared *datatype* (`MeasurePos`, genuinely used by ExecGen and Waterfall) but the shared *derivation* is unused — so the two layers agree on a type, not on a construction. Delete it, or wire ExecGen to it; shipping it unused overstates the F13 remedy.

**7. `ACL2Lean/Replay/Lemmas/MeasureMu.lean:40-72` — `logic_nfix_eq_nfixNat` (33 lines), sprint-added (`b3f6174`).** Zero references. Its two siblings are load-bearing (`nfixNat_int` is `@[simp]` and used in-file; `nfixNat_plus_lt_of_not_zp` is used at `Decrease.lean:251`), so a family-symmetry argument is available — but this one states the twin bridge and nothing consumes it.

---

### DELETE-AFTER-REVIEW (needs a judgment)

**8. `ACL2Lean/Imported/Sorting.lean` — a 744-line transitively-dead closure (17.9% of the file).** Computed by fixpoint (a decl is live only if some *other* live decl's span mentions it; comments and docstrings count as mentions, so this is conservative). Three whole subtrees, with no `register_exec_kit%` registration and no reference from `Waypoints/`, `SortingBsort`, `SortingConvertPerm`, `EquisortWitness` or `SortingReadings`:
- **ORDINAL exec-correspondences** L2601-2935 (`o_lt_exec_corr` 161 lines + `o_finp`/`o_fe`/`o_fc_exec_corr` + all their `*T`/`*Body`/`*_sym`/`*_ns` support) — orphaned by **P3b**, which retired `total:O&lt;` via `Replay/OrdinalSim.lean`.
- **ACL2-COUNT exec-correspondences** L2936-3305 (`acl2_count_exec_corr` 186 lines + `integer_abs_exec_corr`, `length_exec_corr`, support) — orphaned by **phase 1**, the D-A ts-algebra consumer.
- **ORDEREDP exec** L3741-3861 + `relExec_t_or_nil` (:1338) / `allRelExec_t_or_nil` (:1405).

The judgment: these are WAYPOINT-layer hand proofs, i.e. the METRIC's scoreboard, and `waypoint-metrics.sh` reads Sorting.lean's line count as "hand lines … must FALL as books land". Deleting 744 dead lines legitimately moves that number, but it should be recorded as a **deletion**, not banked as industrialization. Also note Sorting.lean is a grandfathered file-weight giant (baseline 4165) — this is the single largest available shrink. No in-file comment claims these are kept deliberately; that's what needs ruling.

**9. Fifteen `*_driver` waypoint theorems declared but absent from the catalog.** 63 declared across `ACL2Lean/Imported/`, 49 cited in `Waypoints/Catalog.lean`. Uncited: `p7_dub_len_native_driver`, `p5_dupp_prepend_native_driver`, the `*_isChain_driver` family (rm/memb/isort/msort/qsort), the `perm_*_driver` family (symm/trans/erase/cons/qsort), `mem_transport_perm_driver`, `isPerm_equivalence_driver`, `ordered_perms_native_perm_driver`. These are **deliverables, not cruft** — a waypoint's kernel-check is its purpose — so the action is *catalogue them or record why not*, never delete. Pre-existing (not sprint-created), but it's why nearly all of `Waypoints/Validation.lean` (199 of 240 lines) scans as consumerless.

**10. Pre-existing single orphans, sprint-adjacent modules.** `Lemmas/Derived.lean`: `Symbol.normalizedName_lowercase` (:40), `re_unfold1_var` (:833), `conv_value_split` (:941). `Lemmas/Core.lean`: `acl2_numberp_elim` (:67), `evalOpt_number` (:222), `evalOpt_nil` (:227). `Lemmas/Totality.lean`: `re_conv_times` (:461). `NodeCore/Ctx.lean`: `swappedOf` (:652). `NodeCore/Compose.lean`: `chainOptWith` (:36). `Syntax.lean`: `reprChar` (:139). None sprint-created; each is a small independent judgment.

**11. Stale pin DOCSTRINGS — the highest-value scaffolding item.** I extracted all 26 pin `example` types: **every one is now unconditional (zero hypothesis arrows)**. Fifteen of them still carry a docstring saying "conditional on …" followed by a list that the body comments below then retire item by item. Worked example, `Tests/SortingPins.lean:438-448` (`PERM-QSORT`): the docstring promises conditionality on `o&lt;` totality, the `how-many`/`acl2-count` TP corollaries and the cited rules; the 25 comment lines beneath it retire all of them; the actual type is a bare `EvTrue qsortPinsWorld env (PERM (QSORT X) X)`. Same at :501 (`TRUE-LISTP-QSORT`), :614, :640, :668, :771, :886, :984, :1099, :1122, and `SortingPinsEndgame.lean` :52, :75, :104, :123, :261.
`QSORT-IS-ISORT` (:1122) is the one to look at first: its docstring still discloses *"how-many-qsort — the row's disclosed own-obligation assumption, audit O-3"*, which the type no longer carries. A stale disclosure of an assumption that no longer exists is a records problem, not just tidiness.

**Recommended consolidation shape** (not a prescription to delete history — the files' convention of diagnosing each retirement in place is *good*, and it is why this sprint is auditable): keep one dated retirement line per condition, but move the stack **out of the `example` body and under a per-pin `RETIREMENT LOG:` heading in the docstring**, and make the docstring's *first* sentence state the current type. Right now the comment stacks sit between `example :` and the type, so a reader hits 25 lines of history before the statement. Density check: `SortingPins.lean` is 418/1195 comment lines with 47 `RETIRED` markers; `SortingPinsEndgame.lean` is 173/351 (49%) with 32.

---

### KEEP-BUT-DOCUMENT

- **`gz_def_*` in `Lemmas/Derived.lean` (9 scan as consumerless) — KEEP, false positive.** `scripts/check-gz-agreement.sh` *requires* a `gz_def_&lt;fn&gt;` theorem to exist for every builtin-named ground-zero defun in the corpus; it builds the name by string interpolation, so no Lean file ever mentions them. Textbook "registered in a registry". Worth a one-line comment at the family head naming the gate, so the next dead-code sweep doesn't re-find them.
- **Self-elaborating pin defs — KEEP, false positive.** `def sortingArcPatternPins : True := sorting_arc_pattern_pins%` and its 9 siblings across `PatternPins.lean`, `SortingPins.lean`, `DriverTests.lean`: elaborating the def *is* the check. Never referenced, never deletable.
- **`d5Allowed` / `decodeAllowed` empty slots (`Waypoints/Catalog.lean:763`, :771) — KEEP as-is.** Both are `[]`, both carry an explicit in-place comment saying *why* the named slot is kept ("so a future gz constant has an obvious, reviewable place to be registered rather than being smuggled into `decodeAllowed`"). Already documented to standard; no action.
- **`ACL2LEAN_TP_DIAG` (`Harness.lean:1242`) and `ACL2LEAN_XBOOK_DIAG` (`Runner.lean:499`) — KEEP; pollution check passes.** Both are the only two `IO.getEnv` sites in the tree, both off by default, both `IO.eprintln`-only (stderr), and both carry an in-code comment saying so plus "Do not harden it". Neither can reach a golden or a gate. Only gap: they're documented in the sprint charter and trip report, nowhere durable — one line in `README.md` under the diagnostics section would survive the charter's aging.
- **The golden's `[DISCHARGE: …]` brackets — inventory is UNDOCUMENTED, and the pointer to it is stale.** 41 occurrences in `Tests/driver-coverage.golden`, emitted at `Runner.lean:939`, consumed for stripping at `Tests/Coverage/Harness.lean:279-283`. `docs/notes/2026-08-01_dp-premise-classes.md:107-108` says *"Legend in Tests/DriverCoverage.lean"* — there is no legend there; the file was rewritten into the 29-book aggregate in the 2026-08-07 perf-arc split. This bracket already misled one reviewer (the 2026-08-13 overspecialization audit opens with a correction owed to counting `[DISCHARGE:]` conditions as main-row ones). A legend belongs in `Tests/Coverage/Harness.lean` beside the stripping code.
- **`ACL2Lean/Replay/Driver/NodeCore.lean:2-4` — facade says "seven positional slices"** and lists Ctx → Compose → TypeSetWalk → Recognizer → Node → Rewrites → Literal. There are now **eight**: the sprint's `Congruence.lean` (533 lines, G1 lane) sits between Node and Rewrites in the import chain and isn't named.
- **`ACL2Lean/Replay/Driver.lean:22`** — header says the World + replayed statement come "from `gen-world`". CLAUDE.md explicitly flags this exact mis-aim (audit 2026-07-26 F5b: it is the proof-log path, `Development.toWorld`). Pre-existing, but it's the one stale header that actively misdirects an auditor.
- **`scripts/file-weight-baseline.txt:3`** — `ProofLog.lean 1240`, actual 1238. The ratchet prints a `ratchet: … shrank … tighten the baseline` advisory on every run. Cosmetic; two-character fix.
- **`reference/Log2Replay.lean` (828 lines, 37 consumerless decls) — KEEP, already exemplary.** Not in any `lean_lib` (lakefile has only `ACL2Lean` and `Tests`), and its header is a 22-line "REFERENCE ONLY — NOT TRUSTED, NOT BUILT … Do not cite, import, or build on this file." This is the model for how parked material should be labelled.

---

### WORKSPACE-HYGIENE

- **7 agent worktrees under `.claude/worktrees/`, ~6.3 GB total** (each carries its own `.lake`). Six are prunable; one is live:
  - `agent-a1a60c4f33511ab19` @ `388089d` — **LOCKED, active** (pid 3729586). Leave it.
  - `agent-a008d42fff9e880d6` @ `279c2a7` (990M) · `agent-a0991e0dccbe2e39c` @ `42d4d29` (1012M) · `agent-a6e81c7ae8e9f3cca` @ `b3f6174` (1.1G) · `agent-a94e8e1da2b71ff14` @ `c7aa470` (1.5G) · `agent-aac85b2ca162a3e8e` @ `fc06b33` (709M) · `agent-ab6fd6ec59b99c635` @ `a65a0c6` detached (524M). Each also holds a `worktree-agent-*` branch that outlives the prune — `git worktree prune` won't reach them; they need `git branch -D` too.
- **`.tmp/` — 156 MB, untracked.** Correctly ignored (`/.tmp/*` + `!/.tmp/.gitkeep`; exactly one tracked file, `.gitkeep`). Biggest tenants: `claude-1000` 67M, `audit-stale` 43M, `audit-cap` 10M. No tracked file references anything in `.tmp/` except the two intentional sandbox-TMPDIR sites (`scripts/diff-test.sh:70`, `scripts/test-provenance-gates.sh:13`).
- **`Tests/coverage-actual/` (29 section files) and `Tests/driver-coverage.actual`** — both gitignored, both present, all timestamped 2026-08-16 14:41 from the exit gate. Not stale, no action.
- **`.gate-runs/` — 26 logs, 1.4 MB, gitignored except `.gitkeep`.** The exit commit's cited artifact `7b69166-20260816T135429Z.log` **is present locally** (65 KB, 14:49). Flagging for whoever owns claims: it is not tracked, so a fresh clone of this branch has the claim without the evidence.

---

### COULD NOT VERIFY

1. **No build was run.** Every deletion above is argued from a reference closure, not from a compiler. `just ci` is ~30 min and a full `claim-gate` longer; I judged that outside a read-only review's budget. Any actual deletion needs a build behind it.
2. **No LSP `lean_references` cross-check** — that needs a built environment. My scan is textual; it over-approximates consumers (comment mentions count), so it errs toward *keeping* things, but it cannot see a name assembled at runtime.
3. **Metaprogrammed name construction.** I audited the two registries that build names dynamically (`CrossBookReplayed` / `CrossBookTermination` via `Name.mkStr2` in `Runner.lean`) — they mint fresh names, they don't reference the candidates. I found one gate that constructs names by interpolation (`check-gz-agreement.sh`) and excluded its family. I cannot prove there is no third such site.
4. **Whether the 744-line `Sorting.lean` exec closure is deliberately retained** as a hand baseline for the waypoint metric. Nothing in the file says so; nothing in the charter says so. Needs a ruling, not a scan.
5. **Whether the 15 uncatalogued `*_driver` theorems are deliberately out of the catalog** or are a registry gap. Outside my remit to adjudicate.
6. **`totality_2_rec`'s in-file second mention** — my span analysis places it inside its own docstring/body rather than in `totality_2_rec_snd`, hence the dead verdict. That one is worth a 10-second eyeball before deleting, since the `_snd` sibling *is* live.