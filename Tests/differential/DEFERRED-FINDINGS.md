# Deferred differential findings (parse-level & boundary cases)

Findings from the edge-case sprint (2026-07-07) that **cannot be encoded as
runnable corpus entries yet**, because they fail at PARSE time (before
evaluation) in one interpreter, which the current harness can't represent: a
per-form expectation needs both interpreters to reach the value stage (emit a
value or `<stuck>`). These are pinned here so they are not lost; they become
runnable once a `refuse`/parse-boundary expectation class is added (the phase
deferred with the user).

Do NOT fix the underlying bugs — this is a test-suite backlog.

## 1. Radix integer literals — Lean parser is TOO STRICT (rejects valid ACL2)

ACL2 accepts Common-Lisp radix literals; our parser errors
("unrecognized reader macro") and, being an uncaught exception, aborts the
whole form stream.

| form      | ACL2  | Lean parser        |
|-----------|-------|--------------------|
| `#xFF`    | 255   | parse error `#x`   |
| `#b101`   | 5     | parse error `#b`   |
| `#o17`    | 15    | parse error `#o`   |

## 2. Floating-point literals — Lean parser is TOO PERMISSIVE (accepts what ACL2 rejects)

ACL2 has no floats; its reader rejects `5.0` / `1.5` / `.5` / `5e3` with
"A floating-point input … has been encountered" (suggests the `#d` prefix).
Our parser accepts them as a `.decimal` Number and evaluates them.

| form   | ACL2                 | Lean   |
|--------|----------------------|--------|
| `5.0`  | reader error (refuse)| `5.0`  |
| `1.5`  | reader error (refuse)| `1.5`  |
| `.5`   | reader error (refuse)| `.5`   |
| `5e3`  | reader error (refuse)| `5e3`  |

CAUTION for corpus authors: a bare float literal in a corpus file will abort
the ACL2 session mid-stream (every following form loses its value and the file
FATALs on alignment). Keep floats out of runnable corpus files until handled.

## 3. Ill-formed / refused forms — both fail-closed, but need a `refuse` class

Confirmed during the sprint: ACL2 rejects these with `Error [Translate]` (no
value) and Lean also produces no value (`<stuck>` / parse error). They AGREE in
spirit (both refuse) — a good fidelity result — but "ACL2 emits no value" is
currently a fatal alignment error in the manager, so they need a dedicated
`refuse` class before they can be encoded.

Examples: `(car '1 '2)` (arity), `(foobar '1)` (unknown fn),
`(if '1 '2 '3 '4)` (arity), `(quote a b)` (malformed quote), `(cons)` (arity),
`(let ((x)) x)` (malformed binding).
