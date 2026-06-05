# Step case of my_len_my_app + type-prescription emission

Created: 2026-06-05

## Context

The base case of `my_len_my_app` (in `ACL2Lean/Imported/SimpleWorld.lean`) is
fully proved. The induction predicate has been reformulated so the step-case
IH is usable:

```
P(xv) := ∀ env, (x ↦ xv in env) → (y ↦ yv in env)
              → ∃ N, ∀ f ≥ N, eval f w env formula = some T
```

Both totality lemmas (`my_len_total`, `my_app_total`) and the IH-bridge
lemmas (`evalOpt_defn1/2_call_congr`) are proved. The step case is the last
remaining sorry (plus `evalOpt_substVar`/T15, which is now expected to be
unused and can be deleted once the step case lands).

## Design principle confirmed against the proof log

Checked against `acl2_samples/simple.proof-log`: the lemmas we need are
DIRECTED by ACL2's output, not invented:

- Induction scheme → `(:INDUCTION :TERM (MY-APP X Y) :SCHEME ...)` (explicit
  cases + IH literal).
- `my_len_total` / `my_app_total` ("returns an integer" / "returns a value")
  → `(:TYPE-PRESCRIPTION MY-LEN ...)` / `(:TYPE-PRESCRIPTION MY-APP ...)`.
- IH application → `(:REWRITE-STEP :RUNE (:REWRITING-EQUIVALENCE) ...)` with
  an explicit `:EQUIV-TERM`.

IMPORTANT: the step case must be a FAITHFUL replay of the rune chain (like
the base case), NOT a semantic value-extraction shortcut. The shortcut
(compute integer values, do arithmetic) would be "inference in Lean" and is
disallowed.

## Faithful step-case rune chain (from Subgoal *1/1)

Goal (env: x↦xv with consp xv ≠ nil, y↦yv):
`eval (EQUAL (MY-LEN (MY-APP X Y)) (BINARY-+ (MY-LEN X) (MY-LEN Y))) = T`

Common normal form: `NF := (BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))`.

LHS `(MY-LEN (MY-APP X Y))` → NF:
1. `definition MY-APP` (consp true): `(MY-APP X Y)` → `(CONS (CAR X) (MY-APP (CDR X) Y))`
   — lifted under the `(MY-LEN _)` context.
2. `definition MY-LEN` (recursive, on the cons; uses `consp(cons)=T` + `cdr-cons`):
   `(MY-LEN (CONS (CAR X) (MY-APP (CDR X) Y)))` → `(BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))` = NF.

RHS `(BINARY-+ (MY-LEN X) (MY-LEN Y))` → NF:
3. `definition MY-LEN` (consp true): `(MY-LEN X)` → `(BINARY-+ '1 (MY-LEN (CDR X)))`
   — lifted under `(BINARY-+ _ (MY-LEN Y))`.
4. `COMMUTATIVITY-OF-+`: `(BINARY-+ (BINARY-+ '1 (MY-LEN (CDR X))) (MY-LEN Y))`
   → `(BINARY-+ (MY-LEN Y) (BINARY-+ '1 (MY-LEN (CDR X))))`.
5. `COMMUTATIVITY-2-OF-+`: → `(BINARY-+ '1 (BINARY-+ (MY-LEN Y) (MY-LEN (CDR X))))`.
6. `REWRITING-EQUIVALENCE` (IH): `(BINARY-+ (MY-LEN Y) (MY-LEN (CDR X)))`
   → `(MY-LEN (MY-APP (CDR X) Y))`, lifted under `(BINARY-+ '1 _)`. RHS → NF.

7. `EQUAL-SELF`: `(EQUAL NF NF)` → T.

Hand-proof structure (mirrors the base case):
- `hLHS : eval (MY-LEN (MY-APP X Y)) ~ eval NF` (steps 1–2, congruence + chain)
- `hRHS : eval (BINARY-+ (MY-LEN X) (MY-LEN Y)) ~ eval NF` (steps 3–6)
- congruence-lift both into the `EQUAL` (cong_bin1/bin2) + `equal-self` finish
  (`hV`), needing `NF` to converge.

Tools (all already proved):
- `evalOpt_arg_congr` / `evalOpt_cong_*` for the context lifts.
- `evalOpt_defn1/2`, `evalOpt_if_true/false`, `evalOpt_builtin_1/2`, `evalOpt_var`,
  `evalOpt_quote`, `callBuiltin_*`.
- `logic_plus_comm` (general), `logic_plus_comm2_int` for steps 4–5
  (needs integer values of `MY-LEN (CDR X)`, `MY-LEN Y` from `my_len_total`).
- IH node (step 6) — fully tooled, derivation worked out:
  1. instantiate `ih` at the clean env `E' := bindArgs [x,y] [cdr xv, yv]`
     (x↦cdr xv, y↦yv are clean bindArgs lookups);
  2. extract the side-equality `eval E' (MY-LEN (MY-APP X Y)) = eval E' (BINARY-+ (MY-LEN X) (MY-LEN Y))`
     via `eval_equal_t_implies_eq` (T2), using `my_app_total`+`my_len_total` for the
     two convergence witnesses;
  3. bridge each side back to `env`: the MY-LEN/MY-APP side via
     `evalOpt_defn1_call_congr` + `evalOpt_defn2_call_congr` (+ `my_app_total` for the
     shared app value); the BINARY-+ side via `evalOpt_builtin2_call_congr` (NEW)
     with `my_len_total` for the shared MY-LEN values.
  Yields `eval env (MY-LEN (MY-APP (CDR X) Y)) = eval env (BINARY-+ (MY-LEN (CDR X)) (MY-LEN Y))`
  — the IH instance in natural order; commutativity (steps 4–5) rearranges to match.
- `my_len_total` / `my_app_total` for convergence of `NF` (equal-self).

All tools now proved (the last, `evalOpt_builtin2_call_congr`, landed). The step
case has no remaining unknowns — assembly is mechanical (~150–200 lines).

## TODO: emit type-prescription / measure from ACL2 (future)

`grep MEASURE acl2_samples/simple.proof-log` → 0 hits. ACL2 proves termination
at admission and the type-prescription presupposes totality, but the proof log
does NOT currently emit:

- the termination **measure** — so `my_len_total`/`my_app_total` prove "evalOpt
  converges" by inducting on `acl2Count`, a measure we PICKED. Fine for
  structural recursion; wrong in general (ACL2 uses arbitrary measures).
- the type-prescription **proof** (`:ORIGIN TPPROOF/DEFUN` hints one exists) —
  so we currently RE-PROVE the type-prescription in Lean rather than replaying
  ACL2's proof.

To be fully ACL2-directed (no Lean-side measure guessing), instrument ACL2 to
emit `:MEASURE` in the `:DEFUN` event, and ideally the type-prescription proof.
Until then, `my_len_total`/`my_app_total` use `acl2Count` and are restricted to
structurally-recursive functions. This is a fix-at-source item, deferred.
