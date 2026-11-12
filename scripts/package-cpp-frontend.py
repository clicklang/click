#!/usr/bin/env python3
"""Assemble a relocatable, pinned C++ frontend directory for one Click version.

The release job supplies the exporter bundle from
`scripts/build-cpp-exporter.sh --release` and the pinned LLVM license.
No compiler or frontend files are downloaded by this script.
"""
import argparse
import json
import pathlib
import shutil
import subprocess
import tomllib

EXPORTER = "click-cpp-exporter"
RESOURCE_DIR = "clang-resource"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=pathlib.Path)
    parser.add_argument("--exporter-bundle", required=True, type=pathlib.Path)
    parser.add_argument("--llvm-license", required=True, type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parent.parent
    profile = json.loads((root / "src/languages/cpp/frontend-profile.json").read_text())
    version = tomllib.loads((root / "Cargo.toml").read_text())["package"]["version"]
    bundle = args.exporter_bundle.resolve()
    exporter = bundle / EXPORTER
    resources = bundle / RESOURCE_DIR / "include"
    if not exporter.is_file() or not (resources / "stddef.h").is_file():
        parser.error("the exporter bundle needs click-cpp-exporter and clang-resource/include")
    identity = subprocess.check_output([exporter, "--identity"], text=True).strip()
    # The same rule as Click's handshake (schema::check_exporter_identity).
    prefix = f'click-cpp-exporter {profile["exporter_version"]}; schema {profile["artifact_schema"]}; clang '
    if not identity.startswith(prefix) or profile["clang_version"] not in identity[len(prefix):]:
        parser.error(f"exporter identity `{identity}` does not match the pinned profile")
    reported = subprocess.check_output([exporter, "--print-resource-dir"], text=True).strip()
    if pathlib.Path(reported) != bundle / RESOURCE_DIR:
        parser.error("the exporter does not find its resource directory beside itself")
    if args.destination.exists():
        parser.error("destination already exists; choose a new staging directory")
    args.destination.mkdir(parents=True)
    try:
        shutil.copy2(exporter, args.destination / EXPORTER)
        shutil.copytree(resources, args.destination / RESOURCE_DIR / "include")
        (args.destination / "licenses").mkdir()
        shutil.copy2(args.llvm_license, args.destination / "licenses/llvm-LICENSE.TXT")
        manifest = dict(
            schema=1,
            click_version=version,
            host="x86_64-unknown-linux-gnu",
            exporter_version=profile["exporter_version"],
            clang_version=profile["clang_version"],
            artifact_schema=profile["artifact_schema"],
            exporter=EXPORTER,
            resource_dir=RESOURCE_DIR,
        )
        (args.destination / "frontend.json").write_text(json.dumps(manifest, indent=2) + "\n")
    except BaseException:
        shutil.rmtree(args.destination)
        raise


if __name__ == "__main__":
    main()
