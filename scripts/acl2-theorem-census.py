"""Lexical census of explicitly written ACL2 theorem declarations.

This is an honest-mistake capture check, not a Lisp evaluator. Macro-generated
or computed events are covered by the log's own proof/end checks. Do not harden
this into a second ACL2 implementation.
"""
import argparse
from pathlib import Path


def tokens(text):
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ';':
            end = text.find('\n', i)
            i = n if end < 0 else end + 1
        elif text.startswith('#|', i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith('#|', i):
                    depth, i = depth + 1, i + 2
                elif text.startswith('|#', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated block comment')
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            if i >= n:
                raise ValueError('unterminated string')
            i += 1
            yield None
        elif text.startswith('#\\', i):
            i += 2
            if i >= n:
                raise ValueError('unterminated character')
            i += 1
            while i < n and not text[i].isspace() and text[i] not in '()"\';`,':
                i += 1
            yield None
        elif c in '()\'`,':
            i += 1
            yield c
        else:
            atom, barred = [], False
            while i < n:
                c = text[i]
                if c == '\\':
                    i += 1
                    if i >= n:
                        raise ValueError('unterminated symbol escape')
                    atom.append(text[i])
                elif c == '|':
                    barred = not barred
                elif not barred and (c.isspace() or c in '()"\';`,'):
                    break
                else:
                    atom.append(c if barred else c.upper())
                i += 1
            if barred:
                raise ValueError('unterminated escaped symbol')
            yield ''.join(atom)


def declarations(path, log=False):
    # Only the list's own fields are retained; strings cannot become symbols.
    stack, found = [], []
    for token in tokens(Path(path).read_text()):
        if token == '(':
            if stack:
                stack[-1].append(None)
            stack.append([])
        elif token == ')':
            if not stack:
                raise ValueError('unmatched closing parenthesis')
            fields = stack.pop()
            heads = [':DEFTHM'] if log else ['DEFTHM', 'DEFTHMD']
            if fields and fields[0] in heads:
                if len(fields) < 2 or fields[1] is None:
                    raise ValueError('theorem declaration without a symbol name')
                found.append(fields[1])
        elif stack:
            stack[-1].append(token)
    if stack:
        raise ValueError('unclosed list')
    return found


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source')
    p.add_argument('--through')
    p.add_argument('--from', dest='first')
    p.add_argument('--covered-by')
    a = p.parse_args()
    names = declarations(a.source)
    if a.first:
        if not a.through or names.count(a.first) != 1:
            raise ValueError('capture-from requires a through endpoint and one unique source theorem')
        names = names[names.index(a.first):]
    if a.through:
        if names.count(a.through) != 1:
            raise ValueError('capture-through target must name exactly one source DEFTHM/DEFTHMD')
        names = names[:names.index(a.through) + 1]
    if a.covered_by:
        seen = set(declarations(a.covered_by, log=True))
        missing = [name for name in names if name not in seen]
        if missing:
            raise ValueError('source declarations absent from log: ' + ', '.join(missing))
    else:
        print(len(names))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as e:
        raise SystemExit(str(e)) from e
