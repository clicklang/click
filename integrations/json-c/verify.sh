#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
    echo "Usage: $0 /path/to/json-c-checkout {version|array-list}" >&2
    exit 2
fi

integration_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
checkout=$1
case $2 in
    version) source_file=json_c_version.c ;;
    array-list) source_file=arraylist.c ;;
    *) echo "Unknown json-c proof: $2" >&2; exit 2 ;;
esac

revision=05180c1fa385eb39274cf0a17223da1b82832773
work_dir=$(mktemp -d)
trap 'rm -rf -- "$work_dir"' EXIT
mkdir "$work_dir/source"
git -C "$checkout" archive "$revision" | tar -x -C "$work_dir/source"

cmake -S "$work_dir/source" -B "$work_dir/build" \
    -DCMAKE_C_COMPILER=/usr/bin/gcc -DBUILD_TESTING=OFF

cat > "$work_dir/source/click.project.json" <<JSON
{
  "target": "x86_64-unknown-linux-gnu",
  "mode": "userspace",
  "optimization": "-O0",
  "units": {
    "json_c": {
      "language": "c",
      "compiler": "/usr/bin/gcc",
      "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
      "args": ["-D_GNU_SOURCE", "-DJSON_C_DLL", "-I.", "-I../build"],
      "sources": {"$source_file": {}}
    }
  }
}
JSON

sidecar="$work_dir/source/$2.click"
cp "$integration_dir/$2.click" "$sidecar"
"${CLICK:-click}" import lock "$sidecar"
"${CLICK:-click}" verify "$sidecar"
