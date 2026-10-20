# `click docs` command

`click docs` prints the documentation compiled into the `click` binary: the
"Using Click" part of this reference, so an installed Click documents its own
version without the repository. A pinned version answers with that version's
documentation.

## Synopsis

```text
usage: click docs [<NAME>]
```

`NAME` is a tactic or a topic. With no name, `click docs` lists every name:
the tactics with their classes, then the topics with their titles.

## Names

- A tactic, such as `normalize`, `step`, or `apply`, prints every form of that
  tactic from the [tactic reference](../tactics/index.md), each with its
  class (simple, smart, or control) and what a refusal by that class means,
  followed by the reference sections for those forms. `auto` prints the
  automation section.
- A topic prints one page. A page is named by its file name, such as
  `tracing` or `verify`; an `index.md` page by its directory, such as
  `tactics`; and the start page is `start`. A name two pages share, such as
  `audit`, is refused with each page's qualified name, `concepts/audit` and
  `cli/audit`, which always select one page.

No tactic shares a name with a page. In printed pages, a link to another
embedded page reads as the `click docs` command that prints it, and
verified-example markers are omitted. An unknown name is refused with the
closest names.

## Use in refusals

A proof error from [`click verify`](verify.md) that Click can attribute to a
written tactic ends with what refused it and the entry that documents it:

```text
refused by: `normalize` (simple: a refusal within its documented behavior is a bug)
see: click docs normalize
```

The class comes from the written tactic's form in the tactic table: written
`apply(t(x))` is smart and `apply(t(x)) using { ... }` is simple. A C
statement's open requirement is proved by `auto`: the written smart tactic
that reached the statement, or else the implicit `auto` of a written step. Its
refusal names that `auto`, which is smart, and the implicit one points at
`click docs tracing`. A control tactic such as `have` prints only its
entry, since its refusal comes from a tactic it contains.

## Exit status

`click docs` exits with status 0 when it prints, and with status 1 for an
unknown or shared name or extra arguments.
