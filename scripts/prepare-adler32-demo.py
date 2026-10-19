#!/usr/bin/env python3
"""Copy the locked C/Rust Adler-32 project and assemble its proof fragments.

This runs no compiler or verifier. Generated sidecars contain the same complete
proof bodies as the existing checksum regressions, for ordinary `click verify`.
The destination must be new; the project, with its fragments and lock, and the
vendored original sources are copied.
"""
import argparse
import pathlib
import re
import shutil


def prepare(destination):
    root = pathlib.Path(__file__).resolve().parent.parent
    if destination.exists():
        raise ValueError("destination already exists; choose a new directory")
    # The project's units read the original files from the vendored trees
    # beside it, which are copied with it.
    (destination / "design").mkdir(parents=True)
    shutil.copytree(root / "design/adler32", destination / "design/adler32")
    trial = destination / "design/adler32/project"
    rust = trial / "adler2"

    def read(name):
        return (rust / f"{name}.click").read_text()

    helpers = read("helpers")
    parts = [helpers.split("// Empty-input boundary", 1)[0],
             (trial / "adler32-spec.click").read_text()]
    # Match the general-compute verification unit used by the Rust regressions:
    # every referenced lemma, actual helper, constant getter and computation body.
    for name in ["lane-state", "vector-prefix", "batch-prefix",
                 "recombination", "bounds", "iterator-bounds", "general-partition",
                 "tail-bounds", "count-bridge", "bounded-count", "remainder-prefix",
                 "general-compute"]:
        parts.append(read(name).replace('import "bounds.click";\n', ""))
    parts.append(helpers.split("// Imported scalar constants", 1)[1])
    public = "\n".join(parts + [read("packing"), read("checksum"),
                                read("public-constructors"), read("public-general")])
    (rust / "public-demo.click").write_text(public)
    prefix = public.split("fn adler2::adler32_slice(", 1)[0]
    incremental = "\n".join([prefix, read("incremental-split"), read("incremental")])
    resumed = "\n".join([prefix, read("restoration").replace('verifying "../../vendor/adler2-2.0.1/src/lib.rs";', ""),
                          read("incremental-split"), read("resumed")])
    for name, source in [("incremental", incremental), ("resumed", resumed)]:
        source = source.replace('verifying "../../vendor/adler2-2.0.1/src/lib.rs";', f'verifying "{name}.rs";')
        source = source.replace("adler2::", f"adler_{name}::adler2::")
        (rust / f"{name}-demo.click").write_text(source)

    def inline(path, seen=None, entry=True):
        seen = set() if seen is None else seen
        path = path.resolve()
        if path in seen:
            return ""
        seen.add(path)
        text = path.read_text()
        if not entry:
            text = re.sub(r'^verifying "[^"]+";\n', "", text, flags=re.MULTILINE)
        return re.sub(r'^import "([^"]+)";',
                      lambda match: inline(path.parent / match[1], seen, False),
                      text, flags=re.MULTILINE)

    c = trial / "zlib"
    for name in ["canonical", "incremental", "reset"]:
        # The demo sidecar selects the zlib unit's sources through the copied
        # project file and lock, as the original sidecar does.
        (c / f"{name}-demo.click").write_text(inline(c / f"{name}.click"))
    return trial


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=pathlib.Path)
    args = parser.parse_args()
    try:
        trial = prepare(args.destination)
    except ValueError as error:
        parser.error(str(error))
    print(f"Prepared locked demonstration at {trial}")


if __name__ == "__main__":
    main()
