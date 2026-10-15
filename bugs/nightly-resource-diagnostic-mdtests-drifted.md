# Two nightly diagnostic mdtests no longer match their expected refusals

Two mdtests in the nightly list fail on master `7efa75c47`. Each still fails
for the intended reason, but the diagnostic text no longer contains its
expected fragment:

```sh
MDTEST_FILTER=loop_ascending_produces_wrong_arguments cargo test --test mdtests
MDTEST_FILTER=shared_heap_detach_leak_diagnostic cargo test --test mdtests
```

- `loop_ascending_produces_wrong_arguments` expects ``missing resource fact
  `owns ptree_at(…, node)` ``. The diagnostic now says ``missing resource
  fact `owns ptree_at(<pointer A>, node)` ``.
- `shared_heap_detach_leak_diagnostic` expects ``live allocation obligation
  was neither returned nor freed: `owns allocation(p->kid, 8)` ``. It now
  says `` `owns allocation(old(p->kid), 8)` ``. After `p->kid = 0`, the
  leaked allocation is the old child, so the new spelling may be the more
  accurate one.

Both mdtests are nightly-only, so the gate did not catch this. Suspected
cause, not confirmed: `4b5549497` ("Retire duplicate resource diagnostic
formatters") changed how resource facts and their pointers are rendered.

Acceptance: decide which rendering is intended for each case. Either restore
that rendering or update the expected fragment to the accurate one. Both
mdtests pass under `CLICK_NIGHTLY=1`.
