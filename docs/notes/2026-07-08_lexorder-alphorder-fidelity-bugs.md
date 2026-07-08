# lexorder / atomKind fidelity bugs vs ACL2 `alphorder`

Date: 2026-07-08. Found while adding the character type (fixing the `#\a`
differential known-bug). ACL2's total order on atoms is `alphorder`
(axioms.lisp:26995), the authoritative spec. `ACL2Lean/Lexorder.lean`'s
`atomKind` / `lexorder` diverge from it in several ways — definitionally bugs
by the project's total-faithfulness standard. Logged here; NOT all fixed yet
(see status per item). Grounded against live ACL2 (see probes in the session /
`Tests/differential/`).

## ACL2 `alphorder` — the ground truth (axioms.lisp:26995)

Order of atom classes, smallest first:
1. **real/rational** (`<=`)
2. **complex/complex-rational** (realpart then imagpart)
3. **character** (by `char-code`, `<=`)
4. **string** (`string<=`)
5. **symbol** (by `symbol<`; `(not (symbol< y x))`) — and KEYWORDS ARE SYMBOLS,
   so they sort within this class by `symbol<`, NOT in a separate class.

Verified against live ACL2: `(lexorder 5 #\a)`=T, `(lexorder #\a "abc")`=T,
`(lexorder #\a 'sym)`=T, `(lexorder :kw 'sym)`=T (keyword ordered among symbols).

## The bugs in `Lexorder.lean` `atomKind`

Current: `number=0, keyword=1, string=2, symbol=3` (no char, no complex).

- **BUG 1 — keyword has its own kind slot.** In ACL2 a keyword is a symbol and
  sorts within the symbol class by `symbol<`. Placing keyword at kind 1 (below
  string/symbol) is wrong: e.g. our order puts every keyword before every
  string, but ACL2 puts keywords among symbols (after strings).
  STATUS: NOT fixed.
- **BUG 2 — no character class.** Characters must sort between rationals and
  strings, compared by `char-code`. STATUS: partially — a `.char` case was
  added to `atomKind`/`lexorder` (see below), but its POSITION and the proof
  are in flux (this is the work in progress).
- **BUG 3 — symbol comparison is not `symbol<`.** `lexorder` compares symbols
  by `name` then `package`; ACL2's `symbol<` compares by symbol-name using a
  specific char ordering and package handling. Likely divergent for symbols
  whose names differ in case/package in ways `<` on the Lean string doesn't
  match `symbol<`. STATUS: NOT fixed (needs a faithful `symbol<` model).
- **BUG 4 — no complex-rational class.** We don't model complex numbers at all
  (also an `unsupported` in the differential); alphorder places them between
  rationals and characters. STATUS: NOT fixed (blocked on modeling complex).

## Caveat on scope

`ACL2Lean/Lexorder.lean` feeds `TermOrder` (the rewrite loop-stopper), and its
ACL2-facing form `lexorder` is NOT yet wired into `callBuiltin` (it shows as
`unsupported` in the differential — `Tests/differential/corpus/target-ordering.lisp`).
So these bugs do not currently affect replayed proofs, but they ARE fidelity
bugs and block a faithful `lexorder` builtin. Fixing them faithfully requires
reworking `atomKind` to the alphorder class order (which renumbers the 87-case
`lexorder.induct` totality proof) and a faithful `symbol<`.

## When these are fixed

Add `lexorder` differential entries (they currently sit `unsupported` in
target-ordering.lisp) exercising each class boundary + `symbol<` corners, and
flip them to `match`.
