#!/usr/bin/env python3
"""Capture ordinary defthms in a contiguous, original ACL2 bootstrap window.

The observer captures the first actual proof window and its prior world.
initialize-acl2 NIL still executes all
original initialization events with their original proof flags and hints.
This command supports SBCL's direct source-loading mode, not a saved image.
"""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / 'scripts/capture-bootstrap-window.lisp'
CENSUS = ROOT / 'scripts/acl2-theorem-census.py'


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def source_window(source, first, last):
    names = runpy.run_path(str(CENSUS))['declarations'](source)
    if names.count(first) != 1 or names.count(last) != 1:
        raise ValueError('window endpoints must name unique original source theorems')
    selected = names[names.index(first):names.index(last) + 1]
    if not selected or not all(re.fullmatch(r'[A-Z0-9_+*/<>=!?&.%-]+', n) for n in selected):
        raise ValueError('empty, reversed, or unsupported source window')
    return selected


def local_events(data):
    return [m.group(1) for m in re.finditer(
        r'^\(:DEFTHM (\S+)(.*?)(?=^\(:|\Z)', data, re.M | re.S)
        if re.search(r':SOURCE :LOCAL(?:\s|\))', m.group(2))]


def successful_initializer(result):
    # Lisp pretty printing may put the value on the following line.
    return all(re.search(r':' + field + r'\s+T(?:\s|\))', result)
               for field in ['INITIALIZED', 'WINDOW-ENDED'])


def verify(output):
    sidecar = dict(line.split(': ', 1) for line in
                   Path(str(output) + '.meta').read_text().splitlines())
    receipt_path = ROOT / sidecar['bootstrap-receipt']
    if sha(receipt_path) != sidecar['bootstrap-receipt-sha256']:
        raise ValueError('bootstrap receipt hash mismatch')
    receipt = json.loads(receipt_path.read_text())
    selected = source_window(ROOT / 'acl2/axioms.lisp', sidecar['capture-from'],
                             sidecar['capture-through'])
    data = output.read_text()
    if receipt['capture_mode'] != 'bootstrap-initialization' or receipt['process_exit'] != 0:
        raise ValueError('bootstrap initialization was not successful')
    if not successful_initializer(receipt['initializer_result']):
        raise ValueError('bootstrap window or full initialization did not complete')
    if receipt['acl2_commit'] != sidecar['acl2-commit'] or not receipt['source_tree_unchanged']:
        raise ValueError('bootstrap producer identity differs')
    if receipt['log_sha256'] != sha(output) or receipt['actual_events'] != selected or receipt['selected_events'] != selected:
        raise ValueError('bootstrap receipt differs from the original source window')
    if local_events(data) != selected or len(re.findall(r'^\(:QED\)', data, re.M)) != len(selected):
        raise ValueError('bootstrap log does not contain every selected proof and QED')
    if receipt['driver_sha256'] != sha(DRIVER) or receipt['capture_script_sha256'] != sha(Path(__file__)):
        raise ValueError('bootstrap capture driver changed')
    if not all(sha(ROOT / 'acl2' / n) == h for n, h in receipt['source_hashes'].items()):
        raise ValueError('bootstrap initialization sources changed')


def capture(fork, output, first, last):
    def git(*args):
        return subprocess.check_output(['git', '-C', str(fork), *args], text=True).strip()

    if git('status', '--porcelain'):
        raise ValueError('bootstrap producer must be clean')
    commit = git('rev-parse', 'HEAD')
    selected = source_window(fork / 'axioms.lisp', first, last)
    sources = [n for n in git('ls-files', '--', '*.lisp').splitlines() if '/' not in n]
    source_hashes = {n: sha(fork / n) for n in sources}
    driver_hashes = {p: sha(p) for p in [DRIVER, Path(__file__), CENSUS]}
    output.parent.mkdir(parents=True, exist_ok=True)
    selection = Path(str(output) + '.selection.tmp')
    selection.write_text('(' + ' '.join('ACL2::' + n for n in selected) + ')\n')
    result = Path(str(output) + '.initializer.tmp')
    result.unlink(missing_ok=True)
    raw = Path(str(output) + '.raw.tmp')
    temporary = Path(str(output) + '.tmp')
    command = ['sbcl', '--tls-limit', '16384', '--dynamic-space-size', '32000',
               '--control-stack-size', '64', '--disable-ldb', '--disable-debugger',
               '--no-sysinit', '--no-userinit', '--load', str(DRIVER)]
    env = dict(os.environ, ACL2LEAN_BOOTSTRAP_TRACE='scoped',
               ACL2_SYSTEM_BOOKS=str(ROOT / 'acl2/books'),
               ACL2LEAN_BOOTSTRAP_SELECTION=str(selection),
               ACL2LEAN_BOOTSTRAP_RESULT=str(result))
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with raw.open('wb') as stream:
        process = subprocess.run(command, cwd=fork, env=env, stdout=stream,
                                 stderr=subprocess.STDOUT, check=False)
    data = raw.read_bytes().decode('latin1')
    temporary.write_text(data, encoding='utf-8')
    initialized = result.read_text() if result.exists() else ''
    actual = local_events(data)
    receipt = {
        'capture_mode': 'bootstrap-initialization', 'acl2_commit': commit,
        'source_hashes': source_hashes, 'selected_events': selected,
        'actual_events': actual, 'initializer_result': initialized,
        'process_exit': process.returncode, 'started_at': started,
        'finished_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'driver_sha256': driver_hashes[DRIVER],
        'capture_script_sha256': driver_hashes[Path(__file__)],
        'lisp_version': subprocess.check_output(['sbcl', '--version'], text=True).strip(),
        'command': command, 'raw_sha256': sha(raw), 'log_sha256': sha(temporary),
        'source_tree_unchanged': git('rev-parse', 'HEAD') == commit and
            not git('status', '--porcelain') and
            all(sha(fork / n) == h for n, h in source_hashes.items()),
    }
    receipt_path = Path(str(output) + '.receipt.json')
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    if process.returncode or not successful_initializer(initialized):
        raise ValueError(f'bootstrap initialization failed; see {temporary}')
    if actual != selected or len(re.findall(r'^\(:QED\)', data, re.M)) != len(selected):
        raise ValueError('bootstrap capture differs from the complete source window')
    if not receipt['source_tree_unchanged']:
        raise ValueError('bootstrap sources changed during initialization')
    if not all(sha(p) == h for p, h in driver_hashes.items()):
        raise ValueError('bootstrap capture driver changed during initialization')
    if f'(Git commit hash: {commit})' not in data or ':STATUS :COMPLETE' not in data:
        raise ValueError('bootstrap capture lacks source identity or completion')
    if '(:EVENT-FAILED' in data or re.search(r'^\s*HARD ACL2 ERROR', data, re.M):
        raise ValueError('bootstrap capture contains an event failure')
    sidecar = [f'acl2-commit: {commit}', 'capture-mode: bootstrap-initialization',
               f'captured-at: {started}', 'capture-encoding: iso-8859-1', 'log-encoding: utf-8',
               f'capture-from: {first}', f'capture-through: {last}',
               'source-path: acl2/axioms.lisp', f'source-sha256: {source_hashes["axioms.lisp"]}']
    sidecar += [f'include: acl2/{n} {h}' for n, h in source_hashes.items()]
    sidecar += [f'include: scripts/{p.name} {h}' for p, h in driver_hashes.items()]
    sidecar += [f'bootstrap-receipt: {receipt_path.relative_to(ROOT)}',
                f'bootstrap-receipt-sha256: {sha(receipt_path)}',
                f'log-sha256: {sha(temporary)}', 'source-provenance: captured']
    temporary.replace(output)
    Path(str(output) + '.meta').write_text('\n'.join(sidecar) + '\n')
    print(f'{first} through {last}: {len(selected)} original proofs; {output}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--acl2-dir', type=Path, default=ROOT / 'acl2')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--first')
    parser.add_argument('--last')
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify:
        verify(args.verify.resolve())
        return
    if not args.output or not args.first or not args.last:
        parser.error('capture requires --output, --first and --last')
    if not os.environ.get('CAPTURE_WORKER'):
        subprocess.run([str(ROOT / 'scripts/invalidate-coverage.sh')], check=True)
        subprocess.run(['bash', str(ROOT / 'scripts/invalidate-log-consumers.sh')], check=True)
    # INITIALIZE-ACL2 writes acl2-status.txt. Two initializations in the same
    # checkout race even when their capture outputs are disjoint.
    fork = args.acl2_dir.resolve()
    lock_id = hashlib.sha256(str(fork).encode()).hexdigest()[:16]
    lock = ROOT / '.tmp' / f'bootstrap-capture-{lock_id}.lock'
    lock.parent.mkdir(exist_ok=True)
    with lock.open('w') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        capture(fork, args.output.resolve(), args.first, args.last)


if __name__ == '__main__':
    main()
