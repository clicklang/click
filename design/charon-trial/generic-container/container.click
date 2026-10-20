import click::integer;
verifying "stack.rs";

// The nodes from `p` on, each owning its allocation, hold `values`, top
// first.
resource nodes<T: Copy>(p: *mut generic_container::Node<T>) {
    field values: List<T>;
    match values {
        List::Nil => { fact p == 0; },
        List::Cons(v, rest) => {
            owns allocation(p, sizeof(generic_container::Node<T>));
            owns *p;
            owns tail: nodes<T>(p.next);
            fact p != 0;
            fact p.value == v;
            fact tail.values == rest;
        },
    }
}

function first<T>(xs: List<T>) -> Option<T> {
    match xs {
        List::Nil => Option<T>::None,
        List::Cons(v, rest) => Option<T>::Some(v),
    }
}

function rest<T>(xs: List<T>) -> List<T> {
    match xs {
        List::Nil => List<T>::Nil,
        List::Cons(v, tail) => tail,
    }
}

function length<T>(xs: List<T>) -> Integer
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(v, rest) => length(rest) + 1,
    }
}

theorem length_nonnegative<T>(xs: List<T>) {
    ensures length(xs) >= 0 by {
        induct(xs) as ih {
            List::Nil => {
                unfold(length(List<T>::Nil));
                simp();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<T>::Cons(value, rest)));
                arithmetic() using { length(rest) >= 0; };
            }
        }
    }
}

// The compiler's drop of a node drops its `next` box, which drops that
// node in turn and frees it; the node's value, of the abstract `T`, has no
// drop at the scalar types the stack is used at.
impl<T> Destruct for generic_container::Node<T> {
    fn drop_glue(&mut self) {
        owns self.value;
        owns self.next;
        consumes rest: nodes<T>(self.next);
        decreases rest;
    } by {
        match rest.values {
            List::Nil => {
                let {} = unfold(rest);
                execute();
            }
            List::Cons(v, tail_values) => {
                let { tail: tail } = unfold(rest);
                execute();
            }
        }
    }
}

// A stack's drop drops its head.
impl<T> Destruct for generic_container::Stack<T> {
    fn drop_glue(&mut self) {
        owns self.head;
        owns self.len;
        consumes rest: nodes<T>(self.head);
    } by {
        match rest.values {
            List::Nil => {
                let {} = unfold(rest);
                execute();
            }
            List::Cons(v, tail_values) => {
                let { tail: tail } = unfold(rest);
                execute();
            }
        }
    }
}

// Each method is verified once for every `T`; `len` is the list's length.
impl<T> generic_container::Stack<T> {
    fn new() -> generic_container::Stack<T> {
        produces after: nodes<T>(result.head);
        ensures after.values == List<T>::Nil;
        ensures result.len == 0usize;
        ensures to_integer(result.len) == length(after.values);
    } by {
        execute();
        let after = fold(nodes<T>(result.head), { values: List<T>::Nil }, {});
        unfold(length(List<T>::Nil));
    }

    fn push(&mut self, value: T) {
        owns self.head;
        owns self.len;
        consumes before: nodes<T>(self.head);
        produces after: nodes<T>(self.head);
        requires to_integer(self.len) == length(before.values);
        requires self.len < 18446744073709551615usize;
        ensures after.values == List::Cons(value, old(before.values));
        ensures to_integer(self.len) == length(after.values);
    } by {
        execute();
        let after = fold(nodes<T>(self.head), { values: List::Cons(value, old(before.values)) }, { tail: before });
        unfold(length(List::Cons(value, old(before.values))));
        apply(uint64_add_to_integer(old(self.len), 1u64));
        simp();
    }

    fn pop(&mut self) -> Option<T> {
        owns self.head;
        owns self.len;
        consumes before: nodes<T>(self.head);
        produces after: nodes<T>(self.head);
        requires to_integer(self.len) == length(before.values);
        ensures result == first(old(before.values));
        ensures after.values == rest(old(before.values));
        ensures to_integer(self.len) == length(after.values);
    } by {
        match before.values {
            List::Nil => {
                let {} = unfold(before);
                execute();
                let after = fold(nodes<T>(self.head), { values: List<T>::Nil }, {});
                unfold(first(List<T>::Nil));
                unfold(rest(List<T>::Nil));
            }
            List::Cons(v, tail_values) => {
                unfold(length(List::Cons(v, tail_values)));
                apply(length_nonnegative(tail_values));
                have to_integer(self.len) >= 1 by arithmetic() using {
                    to_integer(self.len) == length(List::Cons(v, tail_values));
                    length(List::Cons(v, tail_values)) == length(tail_values) + 1;
                    length(tail_values) >= 0;
                };
                unfold(first(List::Cons(v, tail_values)));
                unfold(rest(List::Cons(v, tail_values)));
                let { tail: tail } = unfold(before);
                execute();
                match tail_values {
                    List::Nil => {
                        let {} = unfold(tail);
                        let after = fold(nodes<T>(self.head), { values: List<T>::Nil }, {});
                        apply(uint64_subtract_to_integer(old(self.len), 1u64));
                        unfold(length(List<T>::Nil));
                        have to_integer(old(self.len) - 1u64) == 0 by arithmetic() using {
                            to_integer(old(self.len) - 1u64) == to_integer(old(self.len)) - 1;
                            to_integer(old(self.len)) == length(List::Cons(v, List<T>::Nil));
                            length(List::Cons(v, List<T>::Nil)) == length(List<T>::Nil) + 1;
                            length(List<T>::Nil) == 0;
                        };
                        simp();
                    }
                    List::Cons(w, more) => {
                        let { tail: next } = unfold(tail);
                        let after = fold(nodes<T>(self.head), { values: List::Cons(w, more) }, { tail: next });
                        apply(uint64_subtract_to_integer(old(self.len), 1u64));
                        have to_integer(old(self.len) - 1u64) == length(List::Cons(w, more)) by arithmetic() using {
                            to_integer(old(self.len) - 1u64) == to_integer(old(self.len)) - 1;
                            to_integer(old(self.len)) == length(List::Cons(v, List::Cons(w, more)));
                            length(List::Cons(v, List::Cons(w, more))) == length(List::Cons(w, more)) + 1;
                        };
                        simp();
                    }
                }
            }
        }
    }

    fn size(&self) -> usize {
        views self.head;
        views self.len;
        owns list: nodes<T>(self.head);
        requires to_integer(self.len) == length(list.values);
        ensures to_integer(result) == length(old(list.values));
        ensures list.values == old(list.values);
    } by {
        execute();
    }
}

// A value pushed onto a new stack is the one popped, and the stack's drop
// frees what is left.
fn generic_container::round_trip(x: u32) -> Option<u32> {
    ensures result == Option<u32>::Some(x);
} by {
    execute();
    unfold(first(List::Cons(x, List<u32>::Nil)));
}

// One layer of `first` and `rest` on a list whose tail is abstract.
theorem first_cons<T>(v: T, xs: List<T>) {
    ensures first(List::Cons(v, xs)) == Option<T>::Some(v) by {
        unfold(first(List::Cons(v, xs)));
        simp();
    }
}

theorem rest_cons<T>(v: T, xs: List<T>) {
    ensures rest(List::Cons(v, xs)) == xs by {
        unfold(rest(List::Cons(v, xs)));
        simp();
    }
}

// Every container holds a list of values, top first, and its size.
trait generic_container::Container<T> {
    function items(self) -> List<T>;
    function size(self) -> usize;
    fn put(&mut self, value: T) {
        requires to_integer(size(self)) == length(items(self));
        requires size(self) < 18446744073709551615usize;
        ensures items(self) == List::Cons(value, old(items(self)));
        ensures to_integer(size(self)) == length(items(self));
    }
    fn take(&mut self) -> Option<T> {
        requires to_integer(size(self)) == length(items(self));
        ensures result == first(old(items(self)));
        ensures items(self) == rest(old(items(self)));
        ensures to_integer(size(self)) == length(items(self));
    }
    fn count(&self) -> usize {
        requires to_integer(size(self)) == length(items(self));
        ensures result == size(self);
    }
}

// The stack is a container for every `T`: its list is the nodes resource
// it holds beside the struct.
impl<T> generic_container::Container<T> for generic_container::Stack<T> {
    resource state: nodes<T>(self.head);
    function items(self) -> List<T> { state.values }
    function size(self) -> usize { self.len }
    fn put(&mut self, value: T) {
    } by { execute(); simp(); }
    fn take(&mut self) -> Option<T> {
    } by { execute(); simp(); }
    fn count(&self) -> usize {
    } by { execute(); simp(); }
}

// Through any container of `u32`: what is put is what is taken, and the
// list is as it was. The proof names the object's state, `items(container)`,
// as the clauses do.
fn generic_container::round_trip_dyn(container: &mut dyn generic_container::Container<u32>, x: u32) -> Option<u32> {
    requires to_integer(size(container)) == length(items(container));
    requires size(container) < 18446744073709551615usize;
    ensures result == Option<u32>::Some(x);
    ensures items(container) == old(items(container));
} by {
    execute();
    apply(first_cons(x, old(items(container))));
    apply(rest_cons(x, old(items(container))));
    simp();
}

// A new stack lent as a container returns what was put.
fn generic_container::through_dyn(x: u32) -> Option<u32> {
    ensures result == Option<u32>::Some(x);
} by { execute(); simp(); }
