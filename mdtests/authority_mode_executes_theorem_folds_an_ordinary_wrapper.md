# An executes theorem folds an ordinary wrapper in authority mode

`box` applies the `lift` refinement theorem inside a callback execution proof,
then folds `Box(data)`, a wrapper whose body is the declared `Buffer(data)`.

Under authority semantics a wrapper fold on an outcome was recorded as a
checked transfer-wrapper exchange on the completed C path. A callback
execution proof has no completed C path, so the fold was refused with
"return resource rewrite requires completed execution". `Box` reaches no
population, so its fold now keeps the ordinary law, which records no such
exchange. A wrapper that reaches a population is still recorded.

```click resource_semantics=authority
resource Buffer(data: int32*) { owns data[0..1]; }
resource Box(data: int32*) { owns Buffer(data); }
contract void Raw(int32* p) { owns p[0..1]; }
contract void Buffered(int32* p) { owns Buffer(p); }
contract void Boxed(int32* p) { owns Box(p); }
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data)); step(Raw); fold(Buffer(data)); simp();
    }
}
theorem box(callback: void (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Boxed(callback) by {
        apply(lift(callback));
        unfold(Box(data)); step(Buffered); fold(Box(data)); simp();
    }
}
```

```expect
pass
```
