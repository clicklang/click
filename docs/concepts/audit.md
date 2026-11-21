# Audit

Audit checks more than ordinary verification: whether Click keeps promises it
makes about every proof. `click audit` runs three audits on the same proof
containers, each ending with how many of the items it checked fail:

- **expansion**: every smart tactic expands to a simple proof that verifies;
- **raise-lower**: every fact and goal a proof step holds raises to Surface
  syntax that lowers back to the same term
  ([raise-lower principle](../internals/raise-lower-principle.md));
- **fact-stability**: lowering never depends on the facts available.

The rest of this page describes the expansion audit. It evaluates whether
smart proof sites remain discoverable, expandable into normally verifiable
source, and within the project's performance policy.

An expansion audit session discovers applicable proof sites, performs bounded expansion,
verifies the resulting proof, and records performance. Each phase is judged by
the deterministic work it spends, so machine load cannot change a verdict;
wall-clock time is reported as information, a phase's time limit only
contains a hung run, and the whole-run time limit paces a long audit at a
resumable cursor. Selection
options let maintainers resume at a source location, restrict claims, or audit
only changes since a Git revision.

The stages protect different invariants:

- discovery must identify the intended smart proof sites deterministically;
- expansion must extract and render the checked operations attributed to the
  selected site;
- ordinary verification must accept the complete rewritten source;
- a complete rewrite must replay cold with implicit solving disabled and
  without entering monitored discovery;
- the explicit proof must stay within deterministic verification and checking
  allowances. Audit reports the original work for comparison and uses the
  expanded proof's own work to decide whether replay passes.

A claim whose sites are all selected is expanded once, with every site
together. Expanding one site runs its whole claim, so expanding the sites one
at a time costs the claim once per site. A failure of whole-claim expansion
fails the audit. A partial selection expands its chosen sites together and
leaves unselected automation available.

`--keep-going` gathers further independent failures after a site fails. It
doesn't make the run successful. A whole-session timeout can leave only a
diagnostic frontier; never treat partial audit results as a complete pass.

For stage defaults, selection, and exit behavior, see [`click audit`](../reference/cli/audit.md).
