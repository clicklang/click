# a sidecar cannot declare a primitive type

```click
type Bag<T>;
```

```expect
fail: a primitive `type` declaration is reserved for the Click library
```
