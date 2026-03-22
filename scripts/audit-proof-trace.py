#!/usr/bin/env python3
"""Pretty-print ACL2 structured proof trace for auditing.

Usage:
    ./scripts/audit-proof-trace.py file.proof-log [theorem-name]

Shows the proof trace with proper indentation for literal boundaries
and branch nesting, making the logical structure visible.
"""

import re
import sys

def parse_field(body, field):
    """Extract a field value from a plist-style body string."""
    m = re.search(rf':{field}\s+(.+?)(?:\s+:[A-Z]|\Z)', body, re.DOTALL)
    return m.group(1).strip() if m else None

def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} file.proof-log [theorem-name]", file=sys.stderr)
        sys.exit(1)

    text = open(sys.argv[1]).read()

    # Find the section for the requested theorem (or first one)
    theorem_name = sys.argv[2].upper() if len(sys.argv) > 2 else None

    if theorem_name:
        start = text.find(f'(:DEFTHM {theorem_name})')
        if start < 0:
            # Try case-insensitive
            for i in range(len(text)):
                if text[i:i+len(theorem_name)+10].upper().startswith(f'(:DEFTHM {theorem_name}'):
                    start = i
                    break
            else:
                print(f"Theorem {theorem_name} not found", file=sys.stderr)
                sys.exit(1)
    else:
        start = text.find('(:DEFTHM ')
        if start < 0:
            print("No (:DEFTHM ...) found", file=sys.stderr)
            sys.exit(1)

    # Find end of this theorem (next DEFTHM or end of file)
    end = text.find('(:DEFTHM', start + 1)
    if end < 0:
        end = len(text)
    section = text[start:end]

    # Print theorem name
    name_m = re.search(r'\(:DEFTHM (\S+)\)', section)
    if name_m:
        print(f"=== {name_m.group(1)} ===\n")

    # Find each :STEP, :INDUCTION, :QED
    step_pattern = (
        r'\(:(STEP|INDUCTION|QED|DEFTHM)\b(.*?)\)'
        r'(?=\s*\(:(STEP|INDUCTION|QED|DEFTHM)\b|\s*\Z)'
    )

    for step_m in re.finditer(
        r'\(:(STEP|INDUCTION|QED)\b(.*?)(?=\n\(:(STEP|INDUCTION|QED|DEFTHM)\b|\Z)',
        section, re.DOTALL
    ):
        tag = step_m.group(1)
        body = step_m.group(2)

        if tag == 'QED':
            print("QED\n")
            continue

        if tag == 'INDUCTION':
            term = parse_field(body, 'TERM')
            count = parse_field(body, 'SUBGOAL-COUNT')
            print(f"INDUCTION on {term} => {count} subgoals\n")
            continue

        # STEP
        cid = parse_field(body, 'CLAUSE-ID')
        proc = parse_field(body, 'PROCESSOR')
        result = parse_field(body, 'RESULT')

        # Clean up result
        if result and result.startswith(':'):
            result = result[1:]

        print(f"--- {cid} [{proc}] => {result} ---")

        # Show input clause
        ic_m = re.search(r':INPUT-CLAUSE\s*\n(.*?)(?=\n\s*:(?:NEW-CLAUSES|REWRITES|ELIM|FERTILIZE|GENERALIZE)\b)',
                         body, re.DOTALL)
        if ic_m:
            clause = ic_m.group(1).strip()
            # Compact display
            lines = clause.split('\n')
            for line in lines[:5]:
                print(f"  IN: {line.strip()}")
            if len(lines) > 5:
                print(f"  IN: ... ({len(lines)} lines total)")

        # Show output clauses
        oc_m = re.search(r':NEW-CLAUSES\s*\n(.*?)(?=\n\s*:(?:REWRITES|ELIM|FERTILIZE|GENERALIZE)\b|\Z)',
                         body, re.DOTALL)
        if oc_m:
            clause = oc_m.group(1).strip()
            lines = clause.split('\n')
            for line in lines[:5]:
                print(f"  OUT: {line.strip()}")
            if len(lines) > 5:
                print(f"  OUT: ... ({len(lines)} lines total)")

        # Show rewrites with structure
        rw_idx = body.find(':REWRITES')
        if rw_idx >= 0:
            rw = body[rw_idx:]
            indent = 1
            # Extract balanced-paren events
            event_tags = {
                'BEGIN-LITERAL', 'END-LITERAL', 'IF-TEST-TRUE', 'IF-TEST-FALSE',
                'IF-TEST-UNKNOWN', 'REWRITE-STEP', 'REWRITTEN-LITERAL',
                'TYPE-SET-REASONING', 'CASE-SPLIT', 'BEGIN-BRANCH', 'END-BRANCH'
            }

            def extract_events(text):
                """Find all (: TAG ...) events with balanced parens."""
                events = []
                i = 0
                while i < len(text):
                    if text[i] == '(' and text[i+1] == ':':
                        # Check if it's a known tag
                        rest = text[i+2:]
                        tag = None
                        for t in event_tags:
                            if rest.startswith(t) and (len(rest) <= len(t) or not rest[len(t)].isalpha()):
                                tag = t
                                break
                        if tag:
                            # Find balanced close
                            depth = 1
                            j = i + 1
                            while j < len(text) and depth > 0:
                                if text[j] == '(':
                                    depth += 1
                                elif text[j] == ')':
                                    depth -= 1
                                j += 1
                            events.append((tag, text[i+2+len(tag):j-1].strip()))
                            i = j
                            continue
                    i += 1
                return events

            for ev_tag, ev_body in extract_events(rw):

                if ev_tag == 'END-BRANCH':
                    indent -= 1

                pfx = '  ' * indent

                if ev_tag == 'BEGIN-LITERAL':
                    n = parse_field(ev_body, 'INDEX') or '?'
                    lit_m = re.search(r':LITERAL (.+?)(?:\s*:NOT-FLG)', ev_body, re.DOTALL)
                    lit = lit_m.group(1).strip()[:70] if lit_m else '?'
                    nf = parse_field(ev_body, 'NOT-FLG')
                    neg = '(NOT ...)' if nf and nf.upper() == 'T' else ''
                    print(f'{pfx}LIT[{n}]: {lit} {neg}')

                elif ev_tag == 'END-LITERAL':
                    res_m = re.search(r':RESULT (.+?)(?:\s*:BRANCHES)', ev_body, re.DOTALL)
                    br = parse_field(ev_body, 'BRANCHES') or '?'
                    r = res_m.group(1).strip()[:60] if res_m else '?'
                    print(f'{pfx}  => {r}  [{br} branches]')

                elif ev_tag.startswith('IF-TEST'):
                    verdict = ev_tag.replace('IF-TEST-', '')
                    unrw = re.search(r':UNREWRITTEN-TEST (.+?)(?:\s*:JUST)', ev_body, re.DOTALL)
                    test_m = re.search(r':TEST (.+?)(?:\s*:UNR|\s*:JUST|\Z)', ev_body, re.DOTALL)
                    u = unrw.group(1).strip()[:50] if unrw else ''
                    t = test_m.group(1).strip()[:30] if test_m else ''
                    label = u if u else t
                    print(f'{pfx}  if {label} => {verdict}')

                elif ev_tag == 'REWRITE-STEP':
                    rune_m = re.search(r':RUNE \((\S+ \S+)\)', ev_body)
                    lhs_m = re.search(r':LHS (.+?)(?:\s*:RHS)', ev_body, re.DOTALL)
                    rhs_m = re.search(r':RHS (.+)', ev_body, re.DOTALL)
                    rn = rune_m.group(1) if rune_m else '?'
                    l = lhs_m.group(1).strip()[:45] if lhs_m else '?'
                    r = rhs_m.group(1).strip()[:45] if rhs_m else '?'
                    print(f'{pfx}  rw [{rn}]: {l} => {r}')

                elif ev_tag == 'REWRITTEN-LITERAL':
                    res_m = re.search(r':RESULT (.+)', ev_body, re.DOTALL)
                    print(f'{pfx}  RESULT => {res_m.group(1).strip()[:60] if res_m else "?"}')

                elif ev_tag == 'TYPE-SET-REASONING':
                    term = parse_field(ev_body, 'TERM') or '?'
                    result = parse_field(ev_body, 'RESULT') or '?'
                    print(f'{pfx}  TYPE-SET: {term[:50]} => {result}')

                elif ev_tag == 'CASE-SPLIT':
                    n = parse_field(ev_body, 'NUM-BRANCHES') or '?'
                    print(f'{pfx}  ** CASE SPLIT => {n} branches **')

                elif ev_tag == 'BEGIN-BRANCH':
                    seg_m = re.search(r':SEGMENT (.+)', ev_body, re.DOTALL)
                    seg = seg_m.group(1).strip()[:70] if seg_m else '?'
                    print(f'{pfx}BRANCH: {seg}')
                    indent += 1

                elif ev_tag == 'END-BRANCH':
                    print(f'{pfx}END-BRANCH')

        # Show elim/fertilize/generalize details
        if ':ELIM-SEQUENCE' in body:
            print(f'  ELIM: destructor elimination performed')
        if ':FERTILIZE' in body:
            print(f'  FERTILIZE: cross-fertilization performed')
        if ':GENERALIZE' in body:
            gen_m = re.search(r':GENERALIZE (.+?)(?:\)$|\)\s)', body, re.DOTALL)
            if gen_m:
                print(f'  GENERALIZE: {gen_m.group(1).strip()[:80]}')

        print()


if __name__ == '__main__':
    main()
