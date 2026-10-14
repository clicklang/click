# Version-manager commands read `--help` as a version

Soundness: not soundness. The version manager installs and selects Click
releases; it never decides whether a proof verifies.

## The violated invariant

Every other `click` subcommand answers `--help` with its usage. The four
version-manager commands (`install`, `use`, `default`, `versions`, documented in
[`click` version manager](../docs/reference/cli/versions.md)) instead treat a
leading-dash argument as a version string, because `normalize_version` in
`src/bin/click/version_dispatch.rs` accepts any nonempty run of ASCII
alphanumerics, `.`, `-` and `+`. A user asking for help gets a download attempt
or a misleading suggestion to install a release named `--help`.

## Reproduction

With a throwaway home and an unreachable release repository:

```console
$ CLICK_HOME=$(mktemp -d) CLICK_RELEASE_REPOSITORY=invalid.invalid/none click use --help
click: Click --help is not installed; run `click install --help`
$ CLICK_HOME=$(mktemp -d) CLICK_RELEASE_REPOSITORY=invalid.invalid/none click default --help
click: Click --help is not installed; run `click install --help`
$ CLICK_HOME=$(mktemp -d) CLICK_RELEASE_REPOSITORY=invalid.invalid/none click install --help
click: could not download https://github.com/invalid.invalid/none/releases/download/v--help/clicklang-x86_64-unknown-linux-gnu.tar.gz: curl: (22) The requested URL returned error: 404
```

The intended regression is a unit test in `src/bin/click/version_manager.rs`
(or `version_dispatch.rs`) that runs each command with `--help` and `-h` and
checks that it prints the version-manager usage without touching `CLICK_HOME`
or the network.

## Acceptance criteria

- `click install --help`, `click use --help`, `click default --help` and
  `click versions --help` (and `-h`) print the version-manager usage and exit
  successfully, making no download and no change under `CLICK_HOME`.
- `normalize_version` refuses a version that starts with `-`, so no other
  option-like argument is read as a release name.
- `docs/reference/cli/versions.md` and `docs/reference/cli/index.md` stop
  saying these commands have no `--help`.
