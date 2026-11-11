#!/usr/bin/env bash
# Build pinned independent tools for the trust gate; never part of zig build.
set -euo pipefail
cd "$(dirname "$0")/.."
fetch_checker() {
  local name="$1" url="$2" revision="$3"
  if [ -e "third_party/$name" ]; then
    printf 'Refusing to overwrite third_party/%s; use a clean checkout.\n' "$name" >&2
    return 1
  fi
  git init -q "third_party/$name"
  git -C "third_party/$name" fetch -q --depth=1 "$url" "$revision"
  git -C "third_party/$name" checkout -q --detach FETCH_HEAD
  test "$(git -C "third_party/$name" rev-parse HEAD)" = "$revision"
}
fetch_checker cadical https://github.com/arminbiere/cadical.git c60730422e758ef1cebe7aeddf2dda31c996bf04
fetch_checker drat-trim https://github.com/marijnheule/drat-trim.git 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
fetch_checker abc https://github.com/berkeley-abc/abc.git bde1659cf7bf2b355624c3599cb58e9b6e474f13
(cd third_party/cadical && ./configure && make -j2)
make -C third_party/drat-trim -j2
make -C third_party/abc -j2 ABC_USE_NO_READLINE=1
