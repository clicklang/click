# A generic stack, verified once for every type, in Rust and C++

Priority: P1.

Soundness: incomplete. Click refuses the Rust program below at import. It
verifies the C++ one once for every `T`, its destructor included; no false
acceptance is known. The generic
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
   field verify (`design/charon-trial/box-fields`). A struct holding a box
   of its own type, `Node { next: Option<Box<Node>> }`, is dropped through
   the compiler's recursive drop glue, checked against a sidecar `impl
   Destruct` contract, and a non-generic stack's `push` and a `clear` that
   frees every node verify (`design/charon-trial/recursive-drop`). A stack
   owned by value, from a `Stack::new()` whose contract produces the list
   over the returned struct's field, is pushed to and dropped, its glue
   taking the list the caller holds. `pop`, through `?` on an option of a
   box and the free of a box whose fields moved out, and `round_trip`
   verify there, so the program above verifies at `T = u32`. Generic
   recursive structs (the program as written, `Stack<T>`), box parameters
   and results, and more than one `?` in a function remain.
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
