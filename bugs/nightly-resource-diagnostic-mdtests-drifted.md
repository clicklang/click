# Two nightly diagnostic mdtests no longer match their expected refusals

Two mdtests in the nightly list fail on master `765ede188`. Each still fails
for the intended reason, but the diagnostic text no longer contains its
expected fragment:

```sh
MDTEST_FILTER=loop_ascending_produces_wrong_arguments cargo test --test mdtests
MDTEST_FILTER=rb_augment_callbacks_helper_rejects_changed_cell cargo test --test mdtests
```

- `loop_ascending_produces_wrong_arguments` expects ``missing resource fact
  `owns ptree_at(…, node)` ``. The diagnostic now says ``missing resource
  fact `owns ptree_at(<pointer A>, node)` ``.
- `rb_augment_callbacks_helper_rejects_changed_cell` expects ``no contract
  fact for the function pointer `augment->copy` ``. The diagnostic now names
  the pointer `` `byte_offset(augment, 8)->copy` ``, which spells out an
  internal offset where the source says `augment->copy`.

Both mdtests are nightly-only, so the gate did not catch this. Suspected
cause, not confirmed: `4b5549497` ("Retire duplicate resource diagnostic
formatters") changed how resource facts and their pointers are rendered.
A third case, `shared_heap_detach_leak_diagnostic`, failed the same way on
`7efa75c47` and passes on `765ede188`.

The nightly lib test
`surface::tests::diagnostic_tests::unfinished_callback_scripts_report_the_missing_authority_to_continue`
checks the same `rb_augment_callbacks_helper_rejects_changed_cell` fragment
and fails the same way on master `26caef84b`.

Acceptance: decide which rendering is intended for each case. Either restore
that rendering or update the expected fragment to the accurate one. Both
mdtests pass under `CLICK_NIGHTLY=1`.
