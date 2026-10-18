# An algebraic conditional inserts into a generic list

An `if` whose branches are algebraic values is itself an algebraic value. A
set-like `insert` over an abstract element type keeps the list when it already
contains the value and conses the value on otherwise. Its laws hold for every
element type: afterwards the list contains the value, and when the value was
absent its length is one more.

A proof selects a branch by deciding the condition: `unfold` the function, then
`normalize() using` the condition or its negation. A C contract may also state
an algebraic conditional.

```c filename=keep.c
void keep(int *p, int n) {
}
```

```click
verifying "keep.c";
import click::list;

function insert<T>(xs: List<T>, x: T) -> List<T> {
    if list::contains(xs, x) { xs } else { List<T>::Cons(x, xs) }
}

theorem insert_absent<T>(xs: List<T>, x: T) {
    requires not list::contains(xs, x);
    ensures insert(xs, x) == List<T>::Cons(x, xs) by {
        unfold(insert(xs, x));
        normalize() using { not list::contains(xs, x); };
    }
}

theorem insert_contains<T>(xs: List<T>, x: T) {
    ensures list::contains(insert(xs, x), x) by {
        if list::contains(xs, x) {
            unfold(insert(xs, x));
            normalize() using { list::contains(xs, x); };
        } else {
            have insert(xs, x) == List<T>::Cons(x, xs) by {
                unfold(insert(xs, x));
                normalize() using { not list::contains(xs, x); };
            }
            rewrite(insert(xs, x) == List<T>::Cons(x, xs));
            unfold(list::contains(List<T>::Cons(x, xs), x));
            normalize();
        }
    }
}

theorem insert_absent_grows<T>(xs: List<T>, x: T) {
    requires not list::contains(xs, x);
    ensures list::length(insert(xs, x)) == Nat::Succ(list::length(xs)) by {
        have insert(xs, x) == List<T>::Cons(x, xs) by {
            unfold(insert(xs, x));
            normalize() using { not list::contains(xs, x); };
        }
        rewrite(insert(xs, x) == List<T>::Cons(x, xs));
        unfold(list::length(List<T>::Cons(x, xs)));
        normalize();
    }
}

abstract resource holder(p: int32*) { field items: List<int32>; }

void keep(int32* p, int32 n) {
    owns h: holder(p);
    requires h.items == if n == 0 { List<int32>::Nil } else { List<int32>::Cons(n, List<int32>::Nil) };
    ensures h.items == old(h.items);
}
```

```expect
pass
```
