#!/usr/bin/env python3
"""Rebuild the pinned Linux rbtree input closure from a configured tree.

The closure holds `lib/rbtree.c`, the 222 files its recorded compilation
opens, and the kernel's license notices. Every file is checked against the
recorded hash before the archive is written, and the archive is byte-for-byte
deterministic: sorted members, zero timestamps and owners, fixed modes.
"""

import argparse
import gzip
import hashlib
import io
import json
import sys
import tarfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
NOTICES = [
    "COPYING",
    "LICENSES/preferred/GPL-2.0",
    "LICENSES/exceptions/Linux-syscall-note",
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--linux-tree", required=True, type=Path)
    parser.add_argument("--provenance", type=Path, default=HERE / "provenance.json")
    parser.add_argument("--output", type=Path, default=HERE / "input-closure.tar.gz")
    args = parser.parse_args()

    provenance = json.loads(args.provenance.read_text())
    expected = {entry["path"]: entry for entry in provenance["closure"]["files"]}
    members = {}
    for path, entry in expected.items():
        data = (args.linux_tree / path).read_bytes()
        if len(data) != entry["bytes"] or sha256(data) != entry["sha256"]:
            print(f"error: {path} does not match its recorded identity", file=sys.stderr)
            return 1
        members[path] = data
    for path in NOTICES:
        members[path] = (args.linux_tree / path).read_bytes()

    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w", format=tarfile.USTAR_FORMAT) as archive:
        for path in sorted(members):
            info = tarfile.TarInfo(path)
            info.size = len(members[path])
            info.mode = 0o644
            info.mtime = 0
            info.uid = info.gid = 0
            info.uname = info.gname = ""
            archive.addfile(info, io.BytesIO(members[path]))
    packed = io.BytesIO()
    with gzip.GzipFile(filename="", fileobj=packed, mode="wb", compresslevel=9, mtime=0) as out:
        out.write(raw.getvalue())
    args.output.write_bytes(packed.getvalue())
    print(f"{sha256(packed.getvalue())}  {args.output.name}  ({len(members)} files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
