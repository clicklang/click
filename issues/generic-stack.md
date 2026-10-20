# A generic stack, verified once for every type, in Rust and C++

Priority: P1.

Soundness: incomplete. Click refuses the Rust program below at import. It
verifies the C++ one's methods once for every `T`, but has no destructor
freeing the remaining nodes; no false acceptance is known. The generic
features that already verify (abstract type parameters, generic structs with
`T` fields, `&T` and `&mut T`, generic calls) keep their own regressions.

A recursive `Stack<T>` with a mutable `push` and `pop` and a `size` is the
smallest ordinary generic program, and the one a reader will try first. Each
missing feature below is something this program needs; it is the motivating
example for the remaining generic work.

## The programs

Rust, a crate unit `generic_stack`:

```rust
pub struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

pub struct Stack<T> {
    head: Option<Box<Node<T>>>,
    len: usize,
}

impl<T> Stack<T> {
    pub fn new() -> Self {
        Stack { head: None, len: 0 }
    }

    pub fn push(&mut self, value: T) {
        let next = self.head.take();
        self.head = Some(Box::new(Node { value, next }));
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        let node = self.head.take()?;
        self.head = node.next;
        self.len -= 1;
        Some(node.value)
    }

    pub fn size(&self) -> usize {
        self.len
    }
}

pub fn round_trip(x: u32) -> Option<u32> {
    let mut stack = Stack::new();
    stack.push(x);
    stack.pop()
}
```

Today Charon imports it and Click refuses the struct: `type (raw pointers and
general generics remain later work)`.

C++:

```cpp
template<class T> struct Node {
    T value;
    Node* next;
};

template<class T> class Stack {
    Node<T>* head = nullptr;
    unsigned long count = 0;

public:
    void push(T value) noexcept {
        head = new Node<T>{value, head};
        count = count + 1;
    }

    bool pop(T& out) noexcept {
        if (head == nullptr) {
            return false;
        }
        Node<T>* node = head;
        out = node->value;
        head = node->next;
        delete node;
        count = count - 1;
        return true;
    }

    unsigned long size() const noexcept { return count; }
};

int round_trip(int x) noexcept {
    Stack<int> stack;
    stack.push(x);
    int out = 0;
    stack.pop(out);
    return out;
}
```

The C++ program verifies at its `int` instance, `Stack<int>`, in
[`examples/cpp-stack/`](../examples/cpp-stack/), with `round_trip` and a second
client, `pushed_size`, calling `size`, and its methods verify once for every
`T` in `mdtests/cpp_generic_resource_checked_once.md`. What remains for C++ is
the destructor.

## Target contracts

Each stack owns a resource whose state is a `List<T>` of its values, top
first. The contracts, in either language:

- `new` (Rust) and the default constructor (C++): the list is empty.
- `push(x)`: the list becomes `Cons(x, old list)`.
- `pop`: on an empty list, returns none (`None`, or `false` with `out`
  unchanged) and the list stays empty; otherwise returns the old head and the
  list becomes its tail.
- `size`: returns the list's length, and leaves the list unchanged.
- `round_trip(x)` returns `Some(x)` (Rust) or `x` (C++).

`Stack<T>`'s methods are verified once, for every `T`, and `round_trip` uses
those contracts at `T = u32` or `int`. The C++ destructor, or Rust's drop of
the remaining nodes, frees every node; leaking is not part of the contract.

## Missing features, in delivery order

1. **Rust `Option`, `Box` and recursive generic structs.** `Option<T>` as an
   enum value, `Box::new` as an owned allocation, `take` and `?` on `Option`,
   and a struct whose field holds a `Box` of its own type. The recursive
   resource describes a `List<T>` by its nodes, as the rbtree resources do.
   Started: a `Box<R>` of a crate struct without drop glue is made, read,
   written and dropped within one body (`design/charon-trial/boxes`), and an
   `Option<Box<R>>` local is made, matched and dropped
   (`design/charon-trial/option-boxes`). A Rust `Option<T>` of a scalar is
   a value of the library's `spec enum Option<T>`, imported as an enum, and
   so is an `Option<bool>` and an `Option<T>` of a generic function's type
   parameter (`design/charon-trial/option-values`), and `o?` on such an
   option returns `None` or reads `Some`'s payload, in generic code too.
   A `&mut Option<T>` of a scalar is read, written and matched through, and
   a caller borrows a local option for it (`design/charon-trial/option-refs`).
   `o.take()` moves an option of a box or a scalar out of a local or a
   `&mut` referent and leaves `None` (`design/charon-trial/option-take`).
   A struct behind a reference holds an `Option<Box<R>>` field, owned by a
   resource over its allocation, and `self.slot.take()` and assigning the
   field verify (`design/charon-trial/box-fields`). Recursive boxed structs
   and their recursive drop (so `Node { next: Option<Box<Node>> }` and the
   stack's `push`), structs holding boxes by value, box parameters and
   results, `?` on an option of a box, and more than one `?` in a function
   remain.
2. **C++ at one instance.** Done: fields holding a pointer to a record,
   `p->field` through a parameter or local, `new` and `delete` of one simple
   record in a `noexcept` function, constant default member initializers and
   default construction from them, and a scalar local passed by reference.
   `Stack<int>` verifies in `examples/cpp-stack/`.
3. **Templates checked once.** A class template's methods verified once for
   every `T` with `T` an abstract type, as Rust generic `impl` blocks already
   are, each instance reading the contract at its own layout. Started: a
   source's `templates` are exported at an abstract word-sized type argument,
   and `template<class T>` methods are verified once, their instances taking
   the contract at their own types (`mdtests/cpp_class_template_verified_once.md`).
   C++ sidecars' resources take type parameters, `nodes<T>` over `List<T>`
   with nodes of `sizeof(Node<T>)`, and `Stack<T>::push`, `pop` and `size`
   are proved once (`mdtests/cpp_generic_resource_checked_once.md`), with
   `round_trip` and `pushed_size` taking the contracts at `int`. A refused
   `pop` claiming a value from an empty stack is
   `mdtests/cpp_generic_pop_on_empty_is_refused.md`. A destructor freeing
   the remaining nodes remains.
4. **Generic object state.** A generic trait or class block whose object
   carries state, `trait Container<T> { function items(self) -> List<T>; }`,
   is read at each instance only. A generic `impl<T> Container<T> for
   Stack<T>` needs resource declarations parameterized by `T`, so its object
   resource is checked once. Work in progress on the `generic-state` branch
   (fixture `design/charon-trial/generic-state`) stops here. Started: a Rust
   sidecar's `resource cell<T: Copy>(...)` is checked once at `T` and written
   out at each type a use names, and generic functions over it are proved
   once (`design/charon-trial/generic-resources`). Generic trait and `impl`
   blocks whose object resource is such a resource remain.

## Intended regressions

- `design/charon-trial/generic-stack`: the Rust crate above, with a sidecar
  proving every target contract, and a refused sidecar whose `push` claims the
  old list is kept.
- A C++ fixture with the template above, first verified at `Stack<int>` and
  then once for every `T`, and a refused `pop` that claims a nonempty result
  on an empty stack.
- A generic `Container<T>` trait implemented by the Rust stack, with a caller
  through `&mut dyn Container<u32>`.

## Acceptance criteria

- Both programs import unchanged and verify against the target contracts,
  their generic methods checked once for every `T`.
- `round_trip` verifies in both languages using the generic contracts.
- `docs/reference/rust.md`, `docs/reference/cli/import.md` and
  `docs/reference/coverage.md` describe `Option`, `Box`, recursive generic
  structs, record-pointer fields, `new`/`delete`, templates checked once, and
  generic object state, with the stacks as their examples.
