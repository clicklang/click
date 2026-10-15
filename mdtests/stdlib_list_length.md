# stdlib list length

```click
theorem length_laws<T>(head: T, xs: List<T>, ys: List<T>) {
    ensures list::length(List<T>::Nil) == Nat::Zero by {
        apply(list::length_nil(List<T>::Nil));
    }
    ensures list::length(List<T>::Cons(head, xs)) == Nat::Succ(list::length(xs)) by {
        apply(list::length_cons(head, xs));
    }
    ensures list::length(list::append(xs, ys)) == nat_add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}

theorem nested_length(xs: List<List<int32>>, ys: List<List<int32>>) {
    ensures list::length(list::append(xs, ys)) == nat_add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}

theorem singleton_length(value: int32) {
    ensures list::length(List<int32>::Cons(value, List<int32>::Nil)) == Nat::Succ(Nat::Zero) by {
        unfold(list::length(List<int32>::Cons(value, List<int32>::Nil)));
        unfold(list::length(List<int32>::Nil));
        simp();
    }
}
```

```expect
pass
```
