# Expanded loop certificates exceed the original checking-work budget

An expanded simple proof must keep checking work close to its original smart
proof. On master `486e8097`, nightly audit run 38149193625 reports four
deterministic regressions; all reproduce locally with `click audit`:

| Fixture | Original work | Expanded work |
| --- | ---: | ---: |
| `mdtests/c_decreases_recursive_in_loop.md` | 15,005 | 30,281 |
| `mdtests/later_loop_preserve.md` | 14,117 | 35,162 |
| `mdtests/loop_exit_snapshot.md` | 4,403 | 14,519 |
| `mdtests/nested_loop_preserve.md` | 13,498 | 33,459 |

Each proof still verifies. Audit refuses because expansion exceeds both the
existing 2x relative bound and the 10,000-unit slack. For the smallest case:

```sh
click audit mdtests/loop_exit_snapshot.md
click expand --claim count_from_to.contract --output /tmp/loop-expanded.md \
  mdtests/loop_exit_snapshot.md
click profile /tmp/loop-expanded.md
```

Acceptance: all four unchanged fixtures pass audit with the existing budgets
and comparison thresholds; retain checked loop entry, preservation, exit,
and recursion obligations; add a focused expansion-work regression and
multi-size deterministic coverage for any representation fix.
