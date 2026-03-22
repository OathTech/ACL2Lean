# Silent Failures Audit

**Date:** 2026-03-21
**Scope:** Every place in the codebase where unexpected/unsupported input is silently handled with default values, dropped constructs, or suppressed errors instead of crashing loudly.

---

## Parser.lean

### P1. Unterminated block comment → silent truncation
- **Line 40:** `skipBlock` — `| _, [] => []`
- Input `#| no closing` silently returns empty stream. Parser keeps going as if nothing happened.

### P2. Unrecognized `#` syntax → treated as literal char
- **Line 45:** `skipWS` — `| _ => c :: cs`
- Input `#foo` treats `#` as part of a symbol. No error for unknown reader macros.

### P3. Malformed rational → silently becomes symbol
- **Lines 156–157:** `parseSExpr`
- Input `3/abc` or `1/2/3` — when numerator/denominator don't parse as Int/Nat, the token is silently treated as a symbol name.

### P4. Decimal numbers → silently become symbols
- **Line 160:** `parseSExpr`
- Input `3.14` — tokens containing `.` are silently treated as symbols. Comment says "very crude decimal parsing" but the code just punts entirely.

### P5. Malformed package-qualified symbol → package dropped
- **Line 168:** `parseSExpr`
- Input `a::b::c` — when `splitOn "::"` produces more than 2 parts, the full normalized token becomes a plain symbol. Package info is lost.

---

## Logic.lean

*Note: Many of these match ACL2 semantics where non-numbers coerce to 0, car/cdr of atom returns nil, etc. Flagged anyway because the coercion is silent.*

### L1. toInt: non-integers silently coerce to 0
- **Line 22:** `| _ => 0`
- Rationals, decimals, strings, symbols, nil, cons all silently become 0. Matches ACL2 but means arithmetic on rationals silently truncates.

### L2. toRat: non-numbers silently coerce to (0, 1)
- **Line 36:** `| _ => (0, 1)`
- Same issue. Also: rational with denominator 0 (line 32) silently becomes (0, 1).

### L3. mkNumber: denominator 0 → silently returns int 0
- **Line 41:** `if d = 0 then .atom (.number (.int 0))`
- No error for division-by-zero in number construction.

### L4. div: division by zero → silently returns 0
- **Line 75:** `if bn == 0 then .atom (.number (.int 0))`
- ACL2 semantics uncertain. No crash, no warning.

### L5. expt: base^negative with base=0 → silently returns 0
- **Lines 185–187:** computes `1/(0^n)` and returns 0 when denom is 0.
- This is `1/0` which silently becomes 0.

### L6. string_append: non-strings → silently returns ""
- **Line 236:** `| _, _ => .atom (.string "")`
- Any non-string argument silently produces empty string instead of erroring. ACL2 would guard-error.

### L7. car/cdr on atoms → silently return nil
- **Lines 113, 119:** `| _ => .nil`
- Matches ACL2 semantics but completely silent.

### L8. All type predicates: non-matching types → silently return nil
- **Lines 148–175:** integerp, posp, natp, evenp, oddp, stringp
- All have `| _ => .nil` catch-alls. Correct ACL2 semantics.

### L9. append/len/trueListp/evens: non-cons → silent defaults
- **Lines 440, 446, 453, 491:** Return second arg / 0 / nil / nil respectively.
- Matches ACL2 but silent.

---

## Translator.lean

### T1. translateSymbol: unknown symbols → silent character replacement
- **Lines 52–60**
- Any symbol not in the hardcoded list gets hyphens→underscores, `!`→`_bang`, `?`→`_p`, etc. No warning that the symbol wasn't recognized. Could silently produce name collisions.

### T2. foldNary: zero args → silently returns "SExpr.nil"
- **Line 64:** `| [] => "SExpr.nil"`
- ACL2 `(+)` returns 0, `(*)` returns 1, but this returns nil for all n-ary operators.

### T3. translateExpr let: malformed bindings silently dropped
- **Line 181:** `filterMap` with `| _ => none`
- Bindings that don't match `[var, val]` pattern are silently skipped. No error.
- **Line 182:** `| none => []` — non-list bindings become no bindings at all.

### T4. translateExpr list: non-list args → silently becomes nil
- **Line 188:** `| none => []`
- Improper argument list in `(list ...)` silently produces empty result.

### T5. translateExpr generic function call: non-list args → silently becomes no-arg call
- **Line 209:** `| none => []`
- `(f . improper)` silently becomes `f` with no arguments. This would produce wrong code.

### T6. translateExpr declare: silently returns empty string
- **Line 207:** `""`
- All `(declare ...)` forms vanish completely. Intentional, but nothing distinguishes "intentionally dropped" from "accidentally dropped."

### T7. All sorry-emitting catch-alls (10 instances)
- **Lines 111, 115, 136, 156, 164, 172, 186, 193, 197, 201, 205, 214**
- Malformed quote, if, case, cond, let, 1+, 1-, cadr, cddr, and the final catch-all all emit `sorry /- comment -/`. The translated Lean file compiles (with sorry) and appears to work. The error is buried in a comment inside generated code.

### T8. collectVars: 12 catch-all arms silently return acc unchanged
- **Lines 224, 232, 251, 259, 267, 268, 270, 274, 280, 281**
- Malformed cond clauses, case clauses, if, let, list, generic function calls — all silently skip variable collection. Missing variables means generated theorem signatures are wrong (missing universally quantified vars).

### T9. translateDefun: unknown recursion → silent `partial def`
- **Lines 396–400**
- When recursion is detected (name appears in body string) but no structured pattern matches (cdr/evens/odds), the function is silently emitted as `partial def` with no termination proof and no warning about why.

### T10. findRecursiveArgs / findEvensOddsArg: non-list args silently ignored
- **Lines 315, 319, 340, 344:** `| none => acc` / `| none => none`
- Malformed recursive call structures silently skip analysis. Could produce wrong termination annotations.

---

## Evaluator.lean

### E1. append: non-cons first arg → silently returns second arg
- **Line 32:** `| _ => b`
- `(append 5 '(1 2))` silently returns `(1 2)`. The atom `5` is ignored.

### E2. zp: non-integer → silently returns true
- **Line 72:** `| "zp", [_] => .ok (toACL2Bool true)`
- `(zp 'foo)` returns `t`. This matches ACL2 (non-integers are "zero-like") but is completely silent.

### E3. callBuiltin: only integer arithmetic
- **Lines 64–78**
- All arithmetic builtins (`+`, `-`, `*`, `<`, `/`) only pattern-match on `.int`. Passing a rational to `(+ 1/2 1/3)` falls through to the error case at line 79. This is inconsistent with Logic.lean which handles rationals.

### E4. callBuiltin division: returns rational without normalization
- **Line 78:** `.ok (SExpr.atom (.number (.rational a b.toNat)))`
- When `a % b != 0`, returns raw rational without GCD reduction. `(/ 4 6)` returns `4/6` not `2/3`. Logic.div normalizes; Evaluator doesn't.

---

## Syntax.lean

### S1. Event.classify: 18 catch-all `.skip sexpr` arms
- **Lines 483, 496, 510, 515, 529, 533, 539, 540, 544, 548, 552, 561, 565, 569, 573, 577, 578, 579, 580**
- Every malformed event and every unrecognized head symbol silently becomes `.skip`. The event is completely lost. `World.step` ignores `.skip` events (line 648).
- This means: typos in event names, malformed defuns, defthms with wrong structure — all silently vanish.

### S2. Event.classify: non-symbol formals silently dropped
- **Lines 506, 525**
- In defun/defmacro, `filterMap` silently drops any formal parameter that isn't a symbol. `(defun foo (x 42 y) ...)` silently becomes `(defun foo (x y) ...)`.

### S3. Event.classify: include-book dirs — non-keywords → empty string
- **Lines 489, 494**
- Non-keyword items in include-book tails silently become `""`. Malformed include-book options are lost.

### S4. Event.classify: unknown head symbol → `.skip`
- **Line 579:** `| _ => .skip sexpr`
- Any ACL2 form with an unrecognized head symbol is silently discarded. This includes: `progn`, `comp`, `verify-guards`, `set-enforce-redundancy`, `defabbrev`, `defchoose`, `defpkg`, etc. — dozens of valid ACL2 forms.

### S5. Event.classify: non-cons input → `.skip`
- **Line 580:** `| _ => .skip sexpr`
- Bare atoms at the top level are silently skipped.

### S6. TheoremOption.fromSExprs: non-keyword items silently dropped
- **Line 151:** `| _ :: rest => fromSExprs rest`
- Any item that isn't a keyword in an options list is silently skipped. If a keyword's value is accidentally a keyword itself, the pairing shifts and everything after is wrong — silently.

### S7. World.step: include-book → silently no-op
- **Line 632:** `| .includeBook _ _ => w`
- Include-book events don't modify the world at all. No warning that book contents aren't loaded.

### S8. World.step: make-event with no extracted events → silently no-op
- **Line 642:** `| [] => w`
- If `generatedEvents` can't extract events from a make-event body, the world is silently unchanged.

### S9. World.step: .skip → silently no-op
- **Line 648:** `| .skip _ => w`
- All skipped events silently disappear. Combined with S1, this means any malformed or unrecognized event is completely invisible.

### S10. generatedEvents: non-single-element body → silently returns []
- **Lines 588, 590**
- If make-event body doesn't have exactly one generated expression, or if the recovered event classifies as `.skip`, returns empty list. Events are lost.

### S11. ProofInstruction.ofSExpr: unrecognized list head → `.raw`
- **Lines 278–279**
- Lists whose head isn't a keyword or symbol silently become `.raw`. No indication that the instruction wasn't understood.

### S12. RuleClass.ofSExpr?: non-keyword head → silently returns none
- **Line 335:** `| _ => none`
- Rule classes whose list doesn't start with a keyword are silently discarded.

---

## Summary

| Module | Silent fallback count | Most critical |
|--------|--------------------|---------------|
| Parser.lean | 5 | P3, P4: numbers silently become symbols |
| Logic.lean | 9 | L3–L6: division/expt edge cases return wrong values |
| Translator.lean | ~34 | T5: non-list args become no-arg call; T8: missing vars in theorem sigs |
| Evaluator.lean | 4 | E3: rational arithmetic falls through; E4: unnormalized rationals |
| Syntax.lean | ~30 | S1+S9: any malformed/unknown event silently vanishes from the world |

**Grand total: ~82 instances of silent fallback behavior.**

The most dangerous pattern is the `Event.classify` → `.skip` → `World.step` ignores pipeline. Any ACL2 event that doesn't perfectly match the expected structure disappears without a trace. A single typo or unhandled event type means definitions, theorems, or theory changes are silently lost.
