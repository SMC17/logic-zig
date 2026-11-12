#!/usr/bin/env bash
# Optional upstream reader/converter for checking exported workflow models.
set -euo pipefail
cd "$(dirname "$0")/.."
if [ -e third_party/aiger ]; then
  printf 'Refusing to overwrite third_party/aiger; use a clean checkout.\n' >&2
  exit 1
fi
revision=039ec1a2cc37d3093ac35c4b6df65336b346f409
git init -q third_party/aiger
git -C third_party/aiger fetch -q --depth=1 https://github.com/arminbiere/aiger.git "$revision"
git -C third_party/aiger checkout -q --detach FETCH_HEAD
test "$(git -C third_party/aiger rev-parse HEAD)" = "$revision"
(cd third_party/aiger && ./configure.sh && make aigtoaig)
