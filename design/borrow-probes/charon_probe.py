#!/usr/bin/env python3
"""Bounded, pinned extraction experiment; this is not a Click verifier adapter."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess

PIN = "0.1.279 (5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb)"
PROBES = Path(__file__).resolve().parent


def run(command, cwd=None):
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, start_new_session=True, cwd=cwd)
    try:
        stdout, stderr = process.communicate(timeout=45)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        raise RuntimeError("external extraction exceeded its 45-second crash bound") from None
    return process.returncode, stdout, stderr


def function_body(data, crate, name):
    identity = [{"Ident": [crate, 0]}, {"Ident": [name, 0]}]
    function = next(f for f in data["translated"]["fun_decls"]
                    if f and f["item_meta"]["name"] == identity)
    return function["body"]["Unstructured"]


def shape(body):
    blocks = body["body"]
    return len(blocks), sum(len(block["statements"]) for block in blocks)


def tag(kind):
    return next(iter(kind)) if isinstance(kind, dict) else kind


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path,
                        help="new directory for artifacts and logs")
    parser.add_argument("--adler2-dir", type=Path, help="optional pinned lib.rs/algo.rs directory")
    args = parser.parse_args()
    args.charon = args.charon.resolve()
    code, version, error = run([str(args.charon), "version"])
    assert code == 0 and version.strip() == PIN, (version, error)
    args.output.mkdir(parents=True, exist_ok=False)
    output = args.output.resolve()
    base = [str(args.charon), "rustc", "--ullbc", "--mir", "elaborated", "--precise-drops",
            "--sysroot", "default", "--opaque", "core", "--opaque", "alloc", "--opaque", "std",
            "--error-on-warnings"]
    flags = ["--crate-type", "lib", "--target", "x86_64-unknown-linux-gnu",
             "-Cpanic=abort", "-Coverflow-checks=on", "-Zmir-opt-level=0"]

    def extract(source, label, crate, edition="2024", extra=(), rustc_extra=(), diagnostic=None):
        artifact = output / (label + ".ullbc")
        command = base + list(extra) + ["--dest-file", str(artifact), "--", str(source),
                                       "--crate-name", crate, "--edition", edition]
        code, stdout, stderr = run(command + flags + list(rustc_extra), cwd=output)
        (output / (label + ".log")).write_text(stdout + stderr)
        if diagnostic:
            assert code != 0 and diagnostic in stderr and not artifact.exists(), (label, code, stderr[-2000:])
            print(label, "rejected", diagnostic, "without an artifact")
            return None
        assert code == 0, (label, code, stderr[-2000:])
        data = json.loads(artifact.read_text())
        assert not data["has_errors"], label
        assert data["translated"]["options"]["mir"] == "Elaborated"
        assert data["translated"]["options"]["precise_drops"]
        return data

    data = extract(PROBES / "charon-composition.rs", "composition", "click_charon_probe")
    body = function_body(data, "click_charon_probe", "combined")
    kinds = [tag(block["terminator"]["kind"]) for block in body["body"]]
    assert shape(body) == (60, 190) and kinds.count("Assert") == 12 and kinds.count("Drop") == 1
    for name in ("bump", "at", "quotient", "shifted"):
        body = function_body(data, "click_charon_probe", name)
        assert sum(tag(b["terminator"]["kind"]) == "Assert" for b in body["body"]) == 1, name
    print("composition extracted: 60 blocks, 190 statements, 12 explicit checks, precise drop")
    extract(PROBES / "charon-borrow-rejected.rs", "borrow-rejected", "borrow_rejected", diagnostic="E0506")
    extract(PROBES / "charon-move-rejected.rs", "move-rejected", "move_rejected", diagnostic="E0382")
    for size in (16, 4096, 1_000_000):
        source = output / f"repeat-{size}.rs"
        source.write_text(f"pub fn repeated() -> usize {{ let bytes = [7u8; {size}]; bytes.len() }}\n")
        data = extract(source, f"repeat-{size}", "repeat_probe")
        assert shape(function_body(data, "repeat_probe", "repeated")) == (3, 10)
        print("repeat", size, "3 blocks, 10 statements")
    for size in (8, 32, 128):
        source = output / f"diamonds-{size}.rs"
        source.write_text("pub fn diamonds(mut x: u32, flag: bool) -> u32 {\n" +
                          "if flag { x += 1; } else { x -= 1; }\n" * size + "x\n}\n")
        data = extract(source, f"diamonds-{size}", "diamond_probe")
        actual = shape(function_body(data, "diamond_probe", "diamonds"))
        assert actual == (7 * size + 1, 9 * size + 2), actual
        print("diamonds", size, "blocks/statements", actual)
    if args.adler2_dir:
        manifest = json.loads((PROBES.parents[1] / "design/rust-checksum-sources.json").read_text())
        entry = next(s for s in manifest["sources"] if s["name"] == "adler2")
        for source in entry["files"]:
            content = (args.adler2_dir / Path(source["path"]).name).read_bytes()
            assert hashlib.sha256(content).hexdigest() == source["sha256"]
        data = extract(args.adler2_dir.resolve() / "lib.rs", "adler2", "adler2", "2021",
                       extra=("--start-from", "adler2::adler32_slice"),
                       rustc_extra=("--cfg", 'feature="std"'))
        bodies = [f for f in data["translated"]["fun_decls"]
                  if f and isinstance(f.get("body"), dict) and "Unstructured" in f["body"]]
        compute = next(f for f in bodies if f["item_meta"]["name"][-1] == {"Ident": ["compute", 0]})
        assert len(compute["body"]["Unstructured"]["body"]) == 150
        print("unchanged pinned adler2 extracted:", len(bodies), "bodies; compute has 150 blocks")


if __name__ == "__main__":
    main()
