# click

`click` is a new programming language.

Click's goal is to make it easy to prove things about programs in other
programming languages. Starting with C.

## Kernel design

There's a traditional principle of theorem prover design that says you should
build a small, trusted kernel.

The traditional rationale is that to build a huge bug-free structure, you need the
heart of it to be bug-free. You can only do that by close inspection.
Close inspection is hard, so you want it to be really small.
Then you prove things outward from there.

I claim that for the task of "systems engineering theorem proving", this
is actually the wrong design.

Instead, you should put a lot of domain-specific machinery into the kernel.
It is a good idea to have many data structures and axioms that are specific
to systems engineering.
The rationale is that it lets people develop faster.
It lets you put more powerful tactics in the kernel, and it makes performance
better.
These are important for the systems engineering questions that we care about.
Like, can we formally verify Linux.

There's a serious tradeoff!
The downside is that you are more likely to have bugs in the kernel.
But, for our domain, this is not the most important problem.
We aren't concerned about the soundness of mathematics itself.
We are verifying code that is already supposed to work.
When we discover bugs in the kernel, we don't have a huge tower of false
statements that we became dependent on.
It isn't going to lead to some sort of philosophical disaster.

We should certainly fix bugs in the kernel when we find them.
But it isn't the priority during development, for the Click kernel to be simple.
It should be fast on big codebases.
It should be powerful, ie, really good at proving things.
Those are the priorities.

In other words, we are happy to hardcode axioms and tactics
about char*, float64, or malloc into the kernel.

## Only humans may edit the content above this point. AIs may edit below this point.

## Contributing

Fork [clicklang/click](https://github.com/clicklang/click), develop on a task
branch in your fork, and open a pull request against upstream `master` when
the change is ready. This applies to humans and agents, including maintainers
with upstream write access. Push development branches to your fork to keep
the upstream branch list focused. For an agent authenticated as `lacker` and
authorized to deliver a change, request **Merge when ready** immediately with
`gh pr merge <PR> --auto`, while checks are still running. On follow-up work,
update the same open PR or open a new one if it has merged. Required checks and
review rules still apply.

See the [contribution workflow](docs/internals/contributing.md) for remote
setup, worktree isolation, validation, and the full
[Lacker agent merge-queue loop](docs/internals/contributing.md#lacker-and-agent-merge-queue-loop),
and [AGENTS.md](AGENTS.md) for the repository's working rules.

## Technical documentation

Click's central adoption principle is to verify existing C as written. A proof
failure is not permission to refactor working C into a verifier-friendly shape;
for supported C semantics, the adaptation belongs in the contract, proof,
language, or verifier. See
[What Click Is](docs/concepts/what-click-proves.md#existing-c-comes-first) and
[AGENTS.md](AGENTS.md#existing-c-is-the-verification-boundary).

The AI-written technical documentation for users, agents, and implementers
lives in [docs/](docs/). Start with [Click documentation](docs/index.md), which
organizes the site into Technical reference, Concepts, and Internals. A future
human-written guide will remain a separate work.

The site uses the repository-pinned mdBook version. Install it once per
machine (the only step that needs the network) with:

```sh
scripts/install-tools.sh
```

Then serve the site locally with:

```sh
scripts/mdbook-serve.sh
```

This builds the site, serves it at `http://localhost:3000`, and rebuilds on
changes. `scripts/mdbook-build.sh` writes static output to
`target/click-docs/`. The tool lives in a root shared by every checkout and
worktree (`scripts/tools.sh`), so the gate never installs it.

High-value entry points:

- [Upstream integrations](integrations/README.md): bounded, reproducible
  claims about unchanged projects, currently including Bitcoin Core's
  `MoneyRange` function.
- [What Click proves](docs/concepts/what-click-proves.md): the starting point
  for readers new to Click.
- [Specification state](docs/concepts/spec-state.md): current
  spec-state design position.
- [Proof-failure triage](docs/concepts/proof-failure-triage.md):
  distinguish proof-authoring work from Click language and tooling defects.
- [Testing](docs/internals/testing.md): test
  commands and mdtest shape.
- [Verification efficiency](docs/internals/verification-efficiency.md):
  the codebase-scale complexity contract for simple verification.
- [Feature playbook](docs/internals/feature-playbook.md): how to extend Click.
- [Language reference](docs/reference/language/index.md): complete `.click` syntax
  reference.
- [Kernel](docs/internals/kernel.md): Rust kernel implementation map.

Repository work follows [AGENTS.md](AGENTS.md). In particular, verifier and
proof-tooling instability takes priority over new features and example work:
slow tactics must fail locally, smart certificates must verify, expansion must
work, and normal diagnostics must remain bounded.

## Verification

Run the full test suite with:

```sh
cargo test
```

Run only the markdown integration examples with:

```sh
cargo test --test mdtests
```

## Install Click

On macOS or Linux, install the latest release with:

```sh
curl --proto '=https' --tlsv1.2 -LsSf https://raw.githubusercontent.com/clicklang/click/master/install.sh | sh
```

Set `CLICK_VERSION` to install a specific release instead:

```sh
curl --proto '=https' --tlsv1.2 -LsSf https://raw.githubusercontent.com/clicklang/click/master/install.sh | CLICK_VERSION=0.8.2 sh
```

On Windows, run the matching PowerShell installer. It installs the latest
release by default and also accepts `CLICK_VERSION`:

```powershell
irm https://raw.githubusercontent.com/clicklang/click/master/install.ps1 | iex
```

```powershell
$env:CLICK_VERSION = '0.8.2'; irm https://raw.githubusercontent.com/clicklang/click/master/install.ps1 | iex
```

Once `clicklang` is published to crates.io, install just the main command with:

```sh
cargo install clicklang --bin click
```

Click keeps its launcher and installed versions under `~/.click`. The launcher
uses the nearest `.click-version` file for a project, then the global default.
Use `click install 0.8.2` to add a version, `click use 0.8.2` to pin the
current directory for the project, and `click default 0.9.0` to change the
global fallback. Without either, Click runs the launcher version. `click versions`
lists installed versions. A project can commit `.click-version` to share its
pin with collaborators.

Set `CLICK_HOME` to choose a different install directory. Set
`CLICK_RELEASE_REPOSITORY=owner/name` to install from another GitHub repository.
