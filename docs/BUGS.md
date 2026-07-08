# Fidelity bug backlog — canonical index

This is the SINGLE canonical list of known fidelity bugs: places where the Lean
interpreter / trusted core diverges from real ACL2. Total faithfulness to ACL2
is the goal, so every mismatch is definitionally a bug and belongs here.

**Robustness contract (enforced by `scripts/check-bugs.sh`, run in `just ci`):**
every `open` bug that is `Pinned-by: differential` MUST have at least one live
`;@ known-bug bug:BUG-NNN …` entry in the differential corpus, and every
`bug:BUG-NNN` tag in the corpus MUST reference an `open` bug here. This keeps
the prose index and the self-enforcing differential ratchet in sync — a bug
cannot be silently fixed-and-forgotten (the ratchet FAILs when behavior
changes) nor silently dropped from the index (the cross-check FAILs). Bugs that
CANNOT yet be pinned in the differential (e.g. a builtin not wired into
`callBuiltin`) are `Pinned-by: none (<reason>)` and listed all the same.

Entry format (keep machine-parseable — the checker reads the `BUG-NNN`,
`Status:`, and `Pinned-by:` fields):

```
## BUG-NNN — one-line summary
Status: open | fixed
Pinned-by: differential | none (<reason>)
<prose: what diverges, ACL2's behavior, root cause, fix notes>
```

---

## BUG-001 — no character type: `#\a` is modeled as a symbol
Status: open
Pinned-by: differential
ACL2 has a character type (code points 0–255). Our `Atom` had no character
variant, so `#\a` parsed as a symbol named `#\a`. Consequences: `(equal #\a #\b)`
= t (distinct ACL2 characters collapse) and `(symbolp #\a)` = t (a char is not a
symbol). Fix in progress: add `Atom.char (UInt8)` + parser + characterp/
char-code/code-char + faithful printer. See
docs/notes/2026-07-08_acl2-character-semantics.md.

## BUG-002 — symbol case: parser lowercases bare symbols
Status: open
Pinned-by: differential
ACL2's reader UPCASES bare symbols and PRESERVES the case of `|bar|`-escaped
symbols; our parser LOWERCASES bare symbols (a deliberate internal choice) and
preserves `|bar|`. So the case at which two spellings collapse differs from
ACL2: `(equal '|ABC| 'abc)`=T and `(equal '|ABC| 'ABC)`=T in ACL2 but NIL here,
and `(equal '|abc| 'ABC)`=NIL in ACL2 but t here. High blast radius (world-gen,
symbol matching, goldens) — deferred.

## BUG-003 — printer does not abbreviate `(quote x)` as `'x`
Status: open
Pinned-by: differential
ACL2's printer renders `(quote x)` as `'x`; ours prints the literal list
`(quote x)`. E.g. `(quote (quote a))` → ACL2 `'A`, us `(quote a)`.

## BUG-004 — float literals accepted (ACL2 rejects them)
Status: open
Pinned-by: differential
ACL2 has no floats; its reader REJECTS `5.0` / `1.5` / `.5` / `5e3` (reader
error). Our parser accepts them as a `.decimal` Number. Too permissive.

## BUG-005 — radix integer literals rejected (ACL2 accepts them)
Status: open
Pinned-by: differential
ACL2 accepts Common-Lisp radix literals: `#xFF`=255, `#b101`=5, `#o17`=15. Our
parser errors ("unrecognized reader macro"). Too strict.

## BUG-006 — lexorder atomKind: keyword has its own order class
Status: open
Pinned-by: none (lexorder not wired into callBuiltin; shows `unsupported` in the
differential — Tests/differential/corpus/target-ordering.lisp)
ACL2 `alphorder` (axioms.lisp:26995): keywords ARE symbols and sort within the
symbol class by `symbol<`. `Lexorder.lean`'s `atomKind` gives keyword its own
slot below strings — wrong. See docs/notes/2026-07-08_lexorder-alphorder-fidelity-bugs.md.

## BUG-007 — lexorder atomKind: no character class
Status: open
Pinned-by: none (lexorder not wired into callBuiltin)
`alphorder` orders characters between rationals and strings (by `char-code`).
Being fixed alongside BUG-001's character type. See the alphorder note.

## BUG-008 — lexorder symbol comparison is not `symbol<`
Status: open
Pinned-by: none (lexorder not wired into callBuiltin)
`Lexorder.lean` compares symbols by `name` then `package`; ACL2's `symbol<` has
its own char/package ordering. Divergence likely on case/package corners. See
the alphorder note.

## BUG-009 — no complex-rational class (numbers/lexorder)
Status: open
Pinned-by: none (complex numbers not modeled; `unsupported` in the differential
— Tests/differential/corpus/complex-and-packages.lisp)
`alphorder` places complex/complex-rationals between rationals and characters.
We do not model complex numbers at all.
