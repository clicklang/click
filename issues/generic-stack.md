# A generic stack, verified once for every type, in Rust and C++

Priority: P1.

Soundness: incomplete. Click verifies the Rust program below, imported
unchanged, its methods once for every `T`, and the C++ one once for every
`T`, its destructor included; the generic object state of item 4 remains,
and no false acceptance is known. The generic
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

It verifies unchanged in
[`design/charon-trial/generic-stack/`](../design/charon-trial/generic-stack/)
against the target contracts below, `round_trip` through the generic
methods' instances at `u32`.

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
    ~Stack() noexcept {
        while (head != nullptr) {
            Node<T>* node = head;
            head = node->next;
            delete node;
        }
    }

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
client, `pushed_size`, calling `size`, and its methods and destructor verify
once for every `T` in `mdtests/cpp_generic_resource_checked_once.md`. What
remains for C++ is generic object state (item 4).

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

1. **Rust `Option`, `Box` and recursive generic structs.** Done: `Option<T>`
   as an enum value (`design/charon-trial/option-values`), `&mut Option<T>`
   (`design/charon-trial/option-refs`), `take` and `?` on an option of a
   scalar or a box (`design/charon-trial/option-take`), `Box::new` and box
   fields (`design/charon-trial/boxes`, `option-boxes`, `box-fields`), the
   compiler's recursive drop glue checked against a sidecar `impl Destruct`
   contract and structs holding boxes owned by value
   (`design/charon-trial/recursive-drop`), and generic recursive structs with
   generic glue and generic resources, so `Stack<T>` verifies once for every
   `T` (`design/charon-trial/generic-stack`). Box parameters and results and
   more than one `?` in a function, which the program does not use, remain.
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
   `mdtests/cpp_generic_pop_on_empty_is_refused.md`. The destructor deletes
   every node in a `while` loop (`mdtests/cpp_while_loop_deletes_a_list.md`)
   and is verified once too, consuming the list; it runs at each client's
   return, on a `Stack<int>` built from its default member initializers.
4. **Generic object state.** Done for Rust traits whose functions an
   `impl` defines from its struct's fields: a generic trait's object is a
   generic resource, `Holder::object<T>`, the generic block's interface
   holds it at `T`, and `impl<T: Copy> Holder<T> for Wrap<T>` is verified
   once and packed at each instance a caller uses
   (`design/charon-trial/generic-state`). An `impl` may define a function
   from a resource it holds beside its struct, `resource state:
   boxed(self.item); function item(self) -> Option<u32> { state.value }`,
   as the stack's `items` reads its nodes resource
   (`design/charon-trial/resource-state`, a boxed slot; the stack itself
   waits on item 1). Remaining: the C++ side, a class template whose
   `class` block carries object state.

## Intended regressions

- `design/charon-trial/generic-stack`: the Rust crate above, with a sidecar
  proving every target contract, and a refused sidecar whose `push` claims the
  old list is kept. Done: `tests/rust_import.rs::charon_generic_stack_verifies_once_for_every_type`
  and `charon_generic_stack_refuses_a_push_that_keeps_the_old_list`.
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
