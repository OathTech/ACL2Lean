#!/usr/bin/env bash
# Hardening G3: STRUCTURAL golden diff for the driver-coverage sweep.
#
# A raw `diff golden actual` buries status flips inside error-message churn
# (incident I4: a REPLAYED→FAIL regression can hide in a 30-line wall of
# changed FAIL texts). This classifies changes per row:
#   STATUS FLIP    — REPLAYED↔FAIL, or a REPLAYED row's cond-set changed
#   HEADER/TALLY   — the scoreboard header or DP-discharge tally changed
#   MESSAGE CHURN  — a FAIL row whose error text changed (stays FAIL)
#   ADDED/REMOVED  — rows present on one side only (book/theorem set drift)
# Review the flips first; churn is the low-stakes remainder.
#
# Usage: golden-diff.sh [golden [actual]]   (defaults: Tests/driver-coverage.{golden,actual})
# Exit: 0 = identical; 1 = differences (of any class) — the CALLER decides
# what to do (the ci gate remains the byte-exact golden comparison).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GOLDEN="${1:-$ROOT/Tests/driver-coverage.golden}"
ACTUAL="${2:-$ROOT/Tests/driver-coverage.actual}"
[ -f "$GOLDEN" ] || { echo "golden-diff: missing $GOLDEN" >&2; exit 2; }
[ -f "$ACTUAL" ] || { echo "golden-diff: missing $ACTUAL (run: just driver-coverage)" >&2; exit 2; }

if cmp -s "$GOLDEN" "$ACTUAL"; then
  echo "golden-diff: byte-identical."
  exit 0
fi

python3 - "$GOLDEN" "$ACTUAL" <<'EOF'
import re, sys

def parse(path):
    header = None
    rows = {}    # theorem -> (status, detail)
    book = None
    for line in open(path):
        line = line.rstrip("\n")
        if line.startswith("Driver coverage"):
            header = line
        elif line.lstrip().startswith("•"):
            book = line.strip()
        elif "→" in line:
            name, rest = line.split("→", 1)
            name = name.strip()
            rest = rest.strip()
            if rest.startswith("REPLAYED"):
                m = re.search(r"cond\[(.*?)\]", rest)
                cond = m.group(1) if m else ""
                rows[name] = ("REPLAYED", cond)
            else:
                rows[name] = ("FAIL", rest)
    return header, rows

gh, gr = parse(sys.argv[1])
ah, ar = parse(sys.argv[2])

flips, churn, added, removed = [], [], [], []
for name in gr:
    if name not in ar:
        removed.append(name)
        continue
    (gs, gd), (as_, ad) = gr[name], ar[name]
    if gs != as_:
        flips.append(f"{name}: {gs} → {as_}" + (f"  [now: {ad[:100]}]" if as_ == "FAIL" else f"  [cond: {ad}]"))
    elif gs == "REPLAYED" and gd != ad:
        flips.append(f"{name}: cond-set changed: [{gd}] → [{ad}]")
    elif gs == "FAIL" and gd != ad:
        churn.append(f"{name}:\n      was: {gd[:130]}\n      now: {ad[:130]}")
for name in ar:
    if name not in gr:
        added.append(name)

print("=" * 70)
if gh != ah:
    print("HEADER/TALLY CHANGE:")
    print(f"  was: {gh}")
    print(f"  now: {ah}")
print(f"STATUS FLIPS: {len(flips)}" + ("  ← REVIEW THESE FIRST" if flips else ""))
for f in flips:
    print(f"  {f}")
if added:
    print(f"ADDED ROWS: {len(added)}: " + ", ".join(added))
if removed:
    print(f"REMOVED ROWS: {len(removed)}: " + ", ".join(removed))
print(f"MESSAGE-ONLY CHURN (stays FAIL): {len(churn)}")
for c in churn:
    print(f"  {c}")
print("=" * 70)
regressions = [f for f in flips if "REPLAYED → FAIL" in f]
if regressions:
    print(f"⚠ {len(regressions)} REPLAYED→FAIL REGRESSION(S) — do not promote without diagnosis.")
EOF
exit 1
