# A project beside a tree it does not control

`upstream/RingQ-1.2/` stands for a library you verify but do not own: its
layout and names (`inc/ringq/RingQ.h`, `Source/RingQ_Core.c`, its own
`Makefile.in`) are its authors' choice, not Click's. Click reads it in place
and adds nothing to it.

`project/` is the Click project:

- `click.project.json` declares one C unit whose root is the upstream tree,
  with the arguments the library's build uses. `-Iinc` names a directory in
  the tree; `-I../../project/build/gen` names the out-of-tree build directory.
- `build/gen/rq_config.h` is that build directory's generated configuration
  header, setting `RQ_CAPACITY`. It lives in the project, not in the tree.
- `ringq.click` verifies the library's functions, naming the source by its
  path in the tree.
- `click.project.lock.json` and `.click/` hold the lock and the prepared
  source. Upstream files are recorded relative to the unit root (`$unit/...`)
  and the build header relative to the project (`$project/...`), so the lock
  is portable.

```sh
cd examples/foreign-layout/project
click import lock      # runs GCC; reads the tree, writes only in project/
click verify ringq.click
```

The nightly test `foreign_layout_tree_is_read_in_place_and_never_written` in
`tests/compiler_import.rs` locks and verifies a copy whose upstream tree is
read-only, checks that the tree is unchanged and that the fresh lock equals
the committed one, then changes a byte of `RingQ.h` and checks that
verification refuses the stale lock, naming the file.
