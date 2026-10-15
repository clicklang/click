//! Local release assets for the installer's ordinary curl subprocess.
use std::{
    fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
};

pub fn curl_transport(directory: &Path) -> PathBuf {
    let bin = directory.join("transport");
    fs::create_dir(&bin).unwrap();
    let curl = bin.join("curl");
    fs::write(
        &curl,
        r#"#!/bin/sh
set -eu
while [ "$#" -gt 0 ] && [ "$1" != --output ]; do shift; done
[ "$#" -eq 3 ] || exit 64
shift
output=$1
shift
printf '%s\n' "$1" >> "$FIXTURE_REQUESTS"
/bin/cp "$FIXTURE_ASSETS/${1##*/}" "$output"
"#,
    )
    .unwrap();
    fs::set_permissions(curl, fs::Permissions::from_mode(0o755)).unwrap();
    bin
}
