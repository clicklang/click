#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

if [[ $# != 1 ]]; then
    echo "Usage: $0 /path/to/cJSON-checkout" >&2
    exit 2
fi

integration_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work_dir=$(mktemp -d)
trap 'rm -rf -- "$work_dir"' EXIT
mkdir "$work_dir/source"
git -C "$1" archive c859b25da02955fef659d658b8f324b5cde87be3 | tar -x -C "$work_dir/source"

cmake -S "$work_dir/source" -B "$work_dir/build" \
    -DCMAKE_C_COMPILER=/usr/bin/gcc -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
cmake --build "$work_dir/build" --target cjson

python3 - "$work_dir" <<'PY'
import json
from pathlib import Path
import shlex
import subprocess
import sys

root = Path(sys.argv[1])
source = root / "source" / "cJSON.c"
entries = json.loads((root / "build" / "compile_commands.json").read_text())
[entry] = [entry for entry in entries if Path(entry["file"]) == source]
compiler, *flags = shlex.split(entry["command"])
forwarded = {"-std=c89", "-fPIC", "-fstack-protector-strong", "-fvisibility=hidden"}
args = [flag for flag in flags if flag.startswith("-D") or flag in forwarded]
if "-std=c89" not in args or "-fvisibility=hidden" not in args:
    sys.exit("Expected the pinned cJSON C89 shared-library compile command")

search = subprocess.run(
    [compiler, *args, "-E", "-x", "c", "-v", "-"],
    input="", text=True, capture_output=True, check=True,
).stderr.split("#include <...> search starts here:", 1)[1].split("End of search list.", 1)[0]
for path in search.splitlines():
    if path.strip():
        args.extend(["-isystem", path.strip()])

project = {
    "optimization": "-O0",
    "units": {
        "cjson": {
            "language": "c",
            "compiler": compiler,
            "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
            "args": args,
            "sources": {
                "cJSON.c": {
                    "projection": "dependency-closure",
                    "functions": ["cJSON_IsNumber", "parse_string"],
                },
            },
        },
    },
}
(root / "source" / "click.project.json").write_text(json.dumps(project, indent=2) + "\n")
PY

cp "$integration_dir"/cjson-*.click "$work_dir/source/"
"${CLICK:-click}" capture "$work_dir/source/cjson-is-number-null.click"
"${CLICK:-click}" verify --locked "$work_dir/source/cjson-is-number-null.click"
"${CLICK:-click}" verify --locked "$work_dir/source/cjson-is-number-tag.click"
"${CLICK:-click}" verify --locked "$work_dir/source/cjson-parse-string-empty.click"
