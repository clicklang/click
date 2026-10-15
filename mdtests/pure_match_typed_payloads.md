# Pure match binds pointer, int64, Integer and algebraic fields

```click
spec enum Shade { Red, Black }
spec enum Payload<T> { Empty, Link(int32*, int64, Integer, T) }
function rebuild_payload(item: Payload<Shade>) -> Payload<Shade> {
    match item {
        Payload::Empty => Payload<Shade>::Empty,
        Payload::Link(pointer, wide, count, shade) => Payload<Shade>::Link(pointer, wide, count, shade),
    }
}
theorem pointer_identity(pointer: int32*) { ensures pointer == pointer by { normalize(); } }
theorem integer_identity(count: Integer) { ensures count == count by { normalize(); } }
theorem payload_identity(item: Payload<Shade>) {
    ensures rebuild_payload(item) == item by {
        match item {
            Payload::Empty => { rewrite(item == Payload<Shade>::Empty); unfold(rebuild_payload(Payload<Shade>::Empty)); normalize(); },
            Payload::Link(pointer, wide, count, shade) => {
                apply(pointer_identity(pointer));
                apply(integer_identity(count));
                rewrite(item == Payload<Shade>::Link(pointer, wide, count, shade));
                match shade {
                    Shade::Red => {
                        unfold(rebuild_payload(Payload<Shade>::Link(pointer, wide, count, Shade::Red))); simp();
                    },
                    Shade::Black => {
                        unfold(rebuild_payload(Payload<Shade>::Link(pointer, wide, count, Shade::Black))); simp();
                    },
                }
            },
        }
    }
}
```
```expect
pass
```
