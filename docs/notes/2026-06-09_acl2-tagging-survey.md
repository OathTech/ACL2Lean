# Survey: ACL2 instrumentation tagging practices (every change vs `master`)

_Created 2026-06-09. Systematic survey of EVERY changed region in the `acl2` submodule
(`acl2-lean-output`) vs upstream `master`: 81 hunks / 9 files / 1135 insertions. For each
region: what it does, its tag (if any), and the comment context documenting its purpose._

## Agreed standard (target)
1. **Every inserted region carries a tag.** (Many currently don't.)
2. **The tag sits in a comment that explains the region's purpose.**
3. One uniform tag form, so `grep` finds every fork delta vs upstream (for maintenance/upstreaming).

## The five observed practices
- **A — `; TRACE-LOG[<origin>]: <event> (<detail>) in <fn> [<case>]`** — the de-facto standard.
  Consistent one-line purpose phrase. ~50 sites (rewrite/simplify rewrite-steps + a few infra).
- **B — bare `; TRACE-LOG:`** — old form, NO bracket/purpose. **1 site, and it's a stray
  duplicate** (rewrite.lisp:4937 sits directly above 4938's correct `[solidify/type-alist]`).
- **C — `<fn> ; *structured-rewrite-log*`** — inline marker, different token. axioms.lisp ×18
  (annotates the `*oneify-primitives*` safe-mode list entries).
- **D — prose comment, NO tag** — a `;`-comment explains the purpose but there is no grep-able tag.
- **E — no tag AND no comment** — bare inserted code.

## Two output mechanisms (root of the coverage gap)
- **(a) rewrite-step log** — pushed to `*structured-rewrite-log*` with `:origin '<sym>`. These are
  uniformly Class A and the bracket == the emitted origin. WELL covered.
- **(b) direct `fms` emits** — the *top-level* events `(:DEFTHM)`, `(:STEP)`, `(:INDUCTION)`,
  `(:DEFUN)`, `(:TYPE-PRESCRIPTION)`, `(:QED)`, `(:BEGIN-PROOF-LOG)` written straight to
  `proofs-co`. These are mostly UNTAGGED. This is the clause/theorem/induction layer — exactly
  where the measure track adds instrumentation.
- **(c) output suppressions / behavior tweaks** — conditionals that silence normal ACL2 output in
  `:structured` mode (warnings, clause body, hint notes, pop-clause, forcing-round, Q.E.D. text).
  A real instrumentation category, almost entirely UNTAGGED, not covered by any convention.

## Per-region inventory (every hunk)

### axioms.lisp (1 hunk)
- L14327–14344: 18 fns added to `*oneify-primitives*`, each `; *structured-rewrite-log*` inline — **Class C**, infra.

### basis-a.lisp (2 hunks)
- L7616–7622: suppress warnings in `:structured` mode — **Class D** (prose), suppression. UNTAGGED.
- L7658: 1-line paren balance from the wrap — trivial.

### defthm.lisp (1 hunk)
- L12186–12199: emits `(:DEFTHM …)` to proofs-co in structured mode — **Class E** (no comment), emit (b). UNTAGGED.

### defuns.lisp (2 hunks)
- L12190–12214: `tp-collect-if-leaves` helper (IF-leaf type-set collection) — **Class D** (prose block), infra. UNTAGGED.
- L12223–12260: `defun-fn` wrapper emits `(:DEFUN …)` + `(:TYPE-PRESCRIPTION …)` — **Class A** ×2
  (`defun-fn/post`, `type-prescription/post`), emit (b). **BUG: tag origin ≠ emitted `:ORIGIN`**
  (`defun-fn/post`→`DEFUN/POST`; `type-prescription/post`→`TPPROOF/DEFUN`).

### induct.lisp (3 hunks)
- L134–155: pushes a `(:rewrite-step … :rhs :abbreviation-expansion)` to the log in
  `expand-abbreviations` — **Class E** (no comment), emit (a). UNTAGGED.
- L6812–6842: emits `(:INDUCTION :TERM :SUBGOALS :SCHEME)` — **Class D** (prose), emit (b). UNTAGGED.
- L6841: 1-line context shift — trivial.

### ld.lisp (4 hunks)
- L1698–1713: force inner `ld` to suppress non-proof output (nested-ld) — **Class D** (prose), suppression. UNTAGGED.
- L1764: 1-line paren — trivial.
- L5181–5218: `set-raw-proof-format-fn :structured` setup — **Class A** ×2 (`set-raw-proof-format/
  gstackp`, `gstackp-off`) with RICH multi-line purpose docs (GOLD STANDARD), infra. The
  `(:BEGIN-PROOF-LOG)` emit + `*structured-rewrite-log*` init inside are not separately tagged.

### prove.lisp (17 hunks) — 0 TRACE-LOG tags
- L2644–2716: `waterfall-msg1` emits `(:STEP …)` (the main step aggregator) — **Class D** (prose), emit (b). UNTAGGED.
- L2795–2815: `waterfall-print-clause-body` suppression in structured mode — **Class D** (prose). UNTAGGED.
- L2987/2989/3006/3008: thread `clause` arg into `io?`/`waterfall-msg1` — **Class E**, plumbing. UNTAGGED.
- L4869, 7614, 7671: suppress hint-note / forcing-round / pop-clause prints — **Class E** (bare), suppression. UNTAGGED.
- L8096–8112: emit `(:QED)` / `(:QED :FORCED n)` instead of Q.E.D. text — **Class E** (bare), emit (b). UNTAGGED.

### rewrite.lisp (42 hunks)
- L23–35: `*structured-rewrite-log*` + `*structured-rewrite-depth*` defvars — **Class D** (prose + docstrings), infra. UNTAGGED.
- L39–57: `structured-rewrite-path` defun — **Class A** (tagged infra, rich doc).
- ~33 rewrite-step sites (scons-term, solidify, if11, if1, recognizer, rewrite-entry begin/end-inner,
  rewrite/exec-counterpart, if-finish, rewrite-if, equal, with-lemma, fncall) — **Class A**, consistent.
- L4937: stray **Class B** bare `; TRACE-LOG:` duplicate above 4938 — delete.
- L20117–20158: `saved-log-tail` save + speculative rollback in `rewrite-fncall` — **Class D** (prose), infra. UNTAGGED.

### simplify.lisp (9 hunks)
- 13 rewrite-step / clause / clause-lst sites — **Class A**, consistent.

## Inconsistencies to resolve in normalization
1. **Untagged (b) emits**: `:DEFTHM`, `:STEP`, `:INDUCTION`, `:QED`, abbreviation-expansion push, `:BEGIN-PROOF-LOG`.
2. **Untagged (c) suppressions/tweaks**: warnings, clause-body, hint-note, pop-clause, forcing-round, Q.E.D.-text, nested-ld.
3. **Untagged infra**: the two defvars, `saved-log-tail` rollback, `tp-collect-if-leaves`.
4. **Class B straggler** rewrite.lisp:4937 (delete).
5. **Class C** axioms inline marker — fold into the scheme or keep as documented exception.
6. **Tag↔origin mismatch** in defuns (`defun-fn/post`≠`DEFUN/POST`, `type-prescription/post`≠`TPPROOF/DEFUN`).
7. **Docs drift**: `docs/plans/2026-03-23_proof-tree-representation.md` still says bare `; TRACE-LOG:`.

## What's actually good
The Class A practice is consistent and informative: tag + `<event> (<detail>) in <fn> [<case>]`,
and for (a)-mechanism sites the bracket equals the emitted `:origin`. The `set-raw-proof-format/
gstackp` and `structured-rewrite-path` tags are model examples (tag + rich *why*). Normalization
= extend this practice to the (b) emits, (c) suppressions, and the untagged infra; fix the
straggler + the origin mismatch; pick how infra/suppression labels are namespaced; re-converge the docs.

---

## RATIFIED CONVENTION (the normalization target)

Every region this fork inserts/changes vs upstream `master` carries exactly one tag, in a
comment directly above it, that names AND explains it:

```
; TRACE-LOG[<ns>/<label>]: <one-line purpose — what this instruments and why>
```

`<ns>` is one of three namespaces:

- **`emit/`** — writes to the structured proof log. Two sub-kinds, both `emit/`:
  - rewrite-step log (pushed to `*structured-rewrite-log*` with `:origin '<sym>`):
    label = `<sym>` (e.g. `emit/with-lemma`, `emit/recognizer/true`, `emit/fncall/recursive`).
    **Round-trip rule:** for these, `<label>` (the part after `emit/`) MUST equal the emitted
    `:origin` symbol.
  - direct top-level `fms` events: label = the emitted keyword, lower-cased
    (`emit/step`, `emit/defthm`, `emit/induction`, `emit/defun`, `emit/type-prescription`,
    `emit/qed`, `emit/begin-proof-log`, `emit/abbreviation-expansion`).
- **`suppress/`** — silences normal ACL2 output in `:structured` mode so stdout stays
  machine-parseable (`suppress/warnings`, `suppress/clause-body`, `suppress/hint-note`,
  `suppress/pop-clause`, `suppress/forcing-round`, `suppress/nested-ld-output`).
- **`infra/`** — plumbing that produces no output itself (globals, depth/path helpers, gstackp
  forcing, speculative rollback, the safe-mode list) — `infra/rewrite-log`, `infra/rewrite-depth`,
  `infra/rewrite-path`, `infra/gstackp`, `infra/gstackp-off`, `infra/saved-log-tail`,
  `infra/tp-leaves`, `infra/oneify-primitives`, `infra/structured-setup`.

Rules:
- **Tag EVERYTHING** the fork inserts — emits, suppressions, infra, plumbing — so
  `grep TRACE-LOG` finds every delta vs upstream (the maintenance/upstreaming invariant).
- One `;`-comment, directly **above** the region (not inline), with a real purpose sentence
  (the `infra/gstackp` and `infra/rewrite-path` tags are the model for "tag + rich why").
- Comments are inert in Lisp, so tagging is a zero-behavior change.
- **P4 check** (to add): every fork insertion has a tag; every `emit/<x>` round-trips to its
  emitted origin/keyword; no bare `; TRACE-LOG:` and no other markers remain.

This is the convention to be copied into the repo `CLAUDE.md` once the normalization lands.
