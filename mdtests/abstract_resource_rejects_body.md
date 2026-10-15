# abstract resource rejects a body

An abstract resource has no locally visible definition. It may declare fields
its instances carry, and nothing else: a resource with clauses or facts is an
ordinary resource declaration and must omit `abstract`.

```click
abstract resource permit(key: int32) {
    fact key >= 0;
}
```

```expect
fail: an `abstract resource` body declares only fields
```
