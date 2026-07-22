#!/bin/sh
set -eu

if ! command -v aristotle >/dev/null 2>&1; then
    echo "aristotle CLI not found" >&2
    exit 127
fi
if [ -z "${ARISTOTLE_API_KEY:-}" ]; then
    echo "ARISTOTLE_API_KEY is not set" >&2
    exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)

prompt=${1:-"Audit this Lean project against the finite-matrix specifications in LogicZigOracle/FiniteMatrices.lean. Strengthen it with useful general theorems and proof refactors. Do not use sorry, admit, custom axioms, or unsafe declarations. Preserve the exact K3, LP, FDE, and L3 semantics. Return a project that builds with lake build."}

exec aristotle submit --project-dir "$repo_dir/lean" "$prompt"
