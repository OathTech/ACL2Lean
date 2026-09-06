#!/usr/bin/env bash
# cert.pl accepts an executable path, not a command with arguments.
# Use the same hermetic SBCL startup as capture-proof-log.sh.
set -euo pipefail
script_dir="$(cd "$(dirname "$0")" && pwd)"
exec "$script_dir/../acl2/saved_acl2" --no-sysinit "$@"
