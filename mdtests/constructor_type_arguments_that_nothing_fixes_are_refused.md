# Constructor type arguments that nothing fixes are refused

`List::Nil == List::Nil` gives the constructor nothing to take its type
argument from: neither side has a type of its own. Click does not invent
one; it asks for the written form.

```click
theorem nothing_is_nothing() {
    ensures List::Nil == List::Nil;
}
```

```expect
fail: cannot infer the type arguments of `List::Nil`: neither its arguments nor the type its position expects fix `T`; write them, as in `List<...>::Nil`
```
