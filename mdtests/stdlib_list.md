# Implicit standard-library lists

The library defines the datatype, operations, and generic proofs. This client
only applies them; it does not redeclare them.

```click
theorem list_laws(xs: List<int32>, ys: List<int32>, zs: List<int32>, value: int32) {
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(list::append_left_identity(xs));
        close();
    }
    ensures list::append(xs, List<int32>::Nil) == xs by {
        apply(list::append_right_identity(xs));
        close();
    }
    ensures list::append(list::append(xs, ys), zs) == list::append(xs, list::append(ys, zs)) by {
        apply(list::append_associative(xs, ys, zs));
        close();
    }
    ensures list::contains(List<int32>::Nil, value) == false by {
        apply(list::contains_nil(value));
        close();
    }
    ensures list::contains(List<int32>::Cons(value, xs), value) by {
        apply(list::contains_cons(value, xs, value));
        close();
    }
}

theorem pointer_lists(xs: List<int32*>, ys: List<int32*>, zs: List<int32*>, value: int32*) {
    ensures list::append(list::append(xs, ys), zs) == list::append(xs, list::append(ys, zs)) by {
        apply(list::append_associative(xs, ys, zs));
        close();
    }
}

theorem explicit_induction_application(xs: List<int32>) {
    ensures list::append(xs, List<int32>::Nil) == xs by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(list::append(List<int32>::Nil, List<int32>::Nil));
                close();
            }
            List::Cons(head, tail) => {
                apply(list::append_right_identity(tail));
                unfold(list::append(List<int32>::Cons(head, tail), List<int32>::Nil));
                rewrite(list::append(tail, List<int32>::Nil), tail);
                close();
            }
        }
    }
}

theorem nested_lists(xs: List<List<int32>>) {
    ensures list::append(xs, List<List<int32>>::Nil) == xs by {
        apply(list::append_right_identity(xs));
        close();
    }
}
```

```expect
pass
```
