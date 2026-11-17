#!/usr/bin/env python3
"""Rebuild the supplemental, unchanged SpanReader input closure.

Use the Bitcoin checkout at the commit in streams-input-provenance.json,
the original libstdc++ Debian package, and the pinned Clang resource directory.
The existing base archive is retained byte-for-byte. Verification consumes the
archives offline; this script is only for maintainers regenerating the fixture.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bitcoin-src", type=Path, required=True)
    parser.add_argument("--libstdcpp-package", type=Path, required=True)
    parser.add_argument("--clang-resource", type=Path, required=True)
    args = parser.parse_args()
    destination = Path(__file__).resolve().parent
    manifest = json.loads((destination / "streams-input-provenance.json").read_text())
    if subprocess.check_output(["git", "-C", str(args.bitcoin_src), "rev-parse", "HEAD"], text=True).strip() != manifest["bitcoin_commit"]:
        raise ValueError("Bitcoin checkout differs from the pinned commit")
    if subprocess.check_output(["git", "-C", str(args.bitcoin_src), "status", "--porcelain", "--untracked-files=no"]):
        raise ValueError("Bitcoin checkout has tracked changes")
    if digest(args.libstdcpp_package.read_bytes()) != manifest["libstdc++-12-dev_sha256"]:
        raise ValueError("libstdc++ package differs from the original package")
    if digest((destination / "input-closure.tar.gz").read_bytes()) != manifest["base_input_closure_sha256"]:
        raise ValueError("base input archive differs from the original closure")
    output = io.BytesIO()
    with tempfile.TemporaryDirectory() as temporary:
        subprocess.run(["dpkg-deb", "-x", str(args.libstdcpp_package), temporary], check=True)
        with tarfile.open(fileobj=output, mode="w", format=tarfile.PAX_FORMAT) as archive:
            for name, expected in manifest["files"].items():
                if name.startswith("bitcoin-src/"):
                    source = args.bitcoin_src / name.removeprefix("bitcoin-src/")
                elif name.startswith("sysroot/"):
                    source = Path(temporary) / name.removeprefix("sysroot/")
                else:
                    source = args.clang_resource / name.removeprefix("clang-resource/")
                data = source.read_bytes()
                if digest(data) != expected:
                    raise ValueError(f"{name}: input differs from its authenticated fixture bytes")
                info = tarfile.TarInfo(name)
                info.size = len(data)
                info.mode = 0o644
                info.mtime = 0
                archive.addfile(info, io.BytesIO(data))
    data = gzip.compress(output.getvalue(), mtime=0)
    if digest(data) != manifest["supplement_sha256"]:
        raise ValueError("regenerated archive differs from the recorded deterministic archive")
    (destination / "streams-input-supplement.tar.gz").write_bytes(data)


if __name__ == "__main__":
    main()
