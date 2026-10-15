#!/usr/bin/env python3
"""Assemble a relocatable, pinned Rust frontend directory for one Click version.

The release job supplies release-built Charon binaries and the pinned sysroot.
No compiler or frontend files are downloaded by this script.
"""
import argparse
import json
import pathlib
import shutil
import subprocess
import tomllib


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=pathlib.Path)
    parser.add_argument("--charon-bin", required=True, type=pathlib.Path)
    parser.add_argument("--sysroot", required=True, type=pathlib.Path)
    parser.add_argument("--charon-license", required=True, type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parent.parent
    profile = json.loads((root / "src/languages/rust/charon-profile.json").read_text())
    version = tomllib.loads((root / "Cargo.toml").read_text())["package"]["version"]
    charon = args.charon_bin.resolve() / "charon"
    driver = args.charon_bin.resolve() / "charon-driver"
    sysroot = args.sysroot.resolve()
    expected = f'{profile["extractor_version"]} ({profile["extractor_revision"]})'
    if subprocess.check_output([charon, "version"], text=True).strip() != expected:
        parser.error("Charon binary does not match the pinned version/revision")
    compiler = subprocess.check_output([sysroot / "bin/rustc", "-vV"], text=True)
    if f'commit-hash: {profile["compiler_commit"]}' not in compiler.splitlines():
        parser.error("rustc does not match the pinned compiler commit")
    host = "x86_64-unknown-linux-gnu"
    if f"host: {host}" not in compiler.splitlines():
        parser.error(f"Rust frontend packaging currently supports host {host}")
    if args.destination.exists():
        parser.error("destination already exists; choose a new staging directory")
    if not driver.is_file() or not (sysroot / "lib/rustlib" / host / "lib").is_dir():
        parser.error("Charon driver or pinned target libraries are missing")
    args.destination.mkdir(parents=True)
    try:
        (args.destination / "bin").mkdir()
        for name in ["charon", "charon-driver"]:
            shutil.copy2(args.charon_bin / name, args.destination / "bin" / name)
        (args.destination / "runtime/bin").mkdir(parents=True)
        shutil.copy2(sysroot / "bin/rustc", args.destination / "runtime/bin/rustc")
        shutil.copytree(sysroot / "lib", args.destination / "runtime/lib", symlinks=True)
        (args.destination / "licenses").mkdir()
        shutil.copy2(args.charon_license, args.destination / "licenses/charon-LICENSE.md")
        shutil.copytree(sysroot / "share/doc/rust", args.destination / "licenses/rust", symlinks=True)
        manifest = dict(
            schema=1,
            click_version=version,
            host=host,
            extractor_revision=profile["extractor_revision"],
            extractor_version=profile["extractor_version"],
            compiler_commit=profile["compiler_commit"],
            charon="bin/charon",
            driver="bin/charon-driver",
            rustc="runtime/bin/rustc",
            sysroot="runtime",
        )
        (args.destination / "frontend.json").write_text(json.dumps(manifest, indent=2) + "\n")
    except BaseException:
        shutil.rmtree(args.destination)
        raise


if __name__ == "__main__":
    main()
