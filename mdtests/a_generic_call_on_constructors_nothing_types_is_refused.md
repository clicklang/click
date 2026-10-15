# A generic call on constructors nothing types is refused

`list::append(List::Nil, List::Nil)` leaves `T` open: both arguments leave out
their type arguments and nothing around the call fixes them. The refusal
names the constructor and asks for the written form.

```click
theorem append_nothing(xs: List<int32>) {
    ensures xs == xs by {
        unfold(list::append(List::Nil, List::Nil));
        normalize();
    }
}
```

```expect
fail: a `List` constructor leaves out its type arguments and nothing around it fixes them; write them, as in `List<...>::...`
```
