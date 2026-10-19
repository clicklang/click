# C++ stack

`stack.cpp` is the C++ program of
[`issues/generic-stack.md`](../../issues/generic-stack.md): a class template
`Stack<T>` holding a singly linked list of `Node<T>` records, with `push`
allocating a node with `new`, `pop` reading its value into a reference and
`delete`-ing it, and `size` returning the count. Two clients use it at
`Stack<int>`: `round_trip`, from the issue, and `pushed_size`, which pushes
twice and calls `size`.

`stack.click` verifies the template at its `int` instance:

- `nodes(p)` describes the list from `p` by its nodes, each a `new`
  allocation, as a `List<int32>`;
- `push` puts its value at the front, and `pop` returns the front value or
  leaves `out` unchanged on an empty stack, through `is_cons`, `first_or` and
  `rest`;
- both keep `count` equal to the list's `length`;
- `round_trip(x)` returns `x`, and `pushed_size(x)` returns 2.

`Stack<int> stack;` runs the implicit default constructor, which only applies
the default member initializers `head = nullptr` and `count = 0`. `new` is
admitted in these `noexcept` functions, where a failed allocation ends the
program. The program has no destructor, so nodes still on the stack at the
end of a client are not freed; the contracts make no claim about that.

```sh
cargo run --bin click -- verify examples/cpp-stack/stack.click
```

To refresh the lock after changing the source:

```sh
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)" \
  cargo run --bin click -- import lock examples/cpp-stack
```
