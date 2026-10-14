# A proof constructor whose type nothing fixes is refused

Inside a proof, as in a declaration, a constructor that leaves out its type
arguments needs its arguments or its position to fix them. In `have
List::Nil == List::Nil` nothing does, so the step names the constructor and
asks for the written form.

```click
theorem nothing_is_nothing(xs: List<int32>) {
    ensures xs == xs by {
        have List::Nil == List::Nil by { normalize(); }
        normalize();
    }
}
```

```expect
fail: cannot infer the type arguments of `List::Nil`: neither its arguments nor the type its position expects fix `T`; write them, as in `List<...>::Nil`
```
