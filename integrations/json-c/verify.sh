#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
    echo "Usage: $0 /path/to/json-c-checkout {version|array-list|array-index}" >&2
    exit 2
fi

integration_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
checkout=$1
sidecars=("$2.click")
case $2 in
    version)
        source_file=json_c_version.c
        source_options='{}'
        ;;
    array-list)
        source_file=arraylist.c
        source_options='{"projection": "dependency-closure", "functions": ["array_list_length"]}'
        ;;
    array-index)
        source_file=arraylist.c
        source_options='{"projection": "dependency-closure", "functions": ["array_list_get_idx"]}'
        sidecars=(array-index-out-of-range.click array-index-in-range.click)
        ;;
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
      "sources": {"$source_file": $source_options}
    }
  }
}
JSON

for sidecar in "${sidecars[@]}"; do
    cp "$integration_dir/$sidecar" "$work_dir/source/$sidecar"
done
"${CLICK:-click}" import lock "$work_dir/source/${sidecars[0]}"
for sidecar in "${sidecars[@]}"; do
    "${CLICK:-click}" verify "$work_dir/source/$sidecar"
done
