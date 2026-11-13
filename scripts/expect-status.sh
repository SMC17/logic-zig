#!/usr/bin/env bash
# SAT programs use 10/20 for SAT/UNSAT; HWMCC uses 1 for a counterexample.
set -euo pipefail
expected="$1"
shift
actual=0
"$@" || actual=$?
if [ "$actual" -ne "$expected" ]; then
  printf 'Expected status %s, got %s: ' "$expected" "$actual" >&2
  printf '%q ' "$@" >&2
  printf '\n' >&2
  exit 1
fi
