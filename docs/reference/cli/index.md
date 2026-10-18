# Command-line interface

This page lists the `click` subcommands, their shared exit statuses, and
where each is documented. The `click` executable provides nine subcommands:

```text
click verify   Verify a sidecar, proof unit, project, or examples directory.
click profile  Measure verification and identify slow tactics.
click expand   Replace smart proof source with a checked explicit proof.
click audit    Check expansion across a project or repository.
click import   Create or refresh a compiler-produced source artifact.
click install  Download a Click version.
click use      Pin a version for the current project.
click default  Select the global fallback version.
click versions List installed versions.
```

Use `click --help` for the command list and `click COMMAND --help` for exact
command syntax. The version-manager subcommands print their shared usage. A
successful command, including a help request, exits with status 0. Invalid
arguments, failed verification, exhausted hard limits, and I/O or audit
failures print a diagnostic to standard error and exit with status 1.

## Commands

- [`click verify`](verify.md) is the ordinary correctness command.
- [`click profile`](profile.md) attributes verification work after correctness
  is established.
- [`click expand`](expand.md) rewrites selected smart proof source into an
  explicit proof and verifies the complete rewritten source.
- [`click audit`](audit.md) checks the expansion boundary across many sites.
- [`click import`](import.md) prepares explicitly configured compiler inputs.
- [Version manager commands](versions.md): `click install`, `click use`,
  `click default`, and `click versions` install released versions and select
  the version the `click` launcher runs.

## Common target forms

Commands accept one or more of these target forms, as documented on each
command page:

- a `.click` sidecar;
- a one-based `PATH:LINE:COLUMN` source location, or a `PATH:LINE` line for
  `click expand`;
- a directory, selecting every sidecar under it, grouped by project;
- an mdtest file or mdtest directory;
- the repository root for a combined audit.

Use `--` before a positional path that begins with a hyphen. Duration values
are described below.

## Duration syntax

Duration values accept a positive integer followed by `ms`, `s`, or `m`. A
bare positive integer means seconds. For example, `500ms`, `30s`, `2m`, and
bare `30` are valid; zero, fractional values, and an `h` suffix are invalid.

## Environment variables

[Environment variables](environment.md) documents launcher settings,
user-facing diagnostics, fixture selection, and contributor-only A/B controls. Most users do not need
environment variables for ordinary verification.
