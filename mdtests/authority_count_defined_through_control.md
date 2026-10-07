# Increment definedness transfers from a control field to its population count

```c filename=count_defined.c
struct pool { int32 checked_out; };
void inspect(struct pool* pool) {}
```

```click resource_semantics=authority
authorized resource item(pool: struct pool*, id: int32) {}
resource control(pool: struct pool*) {
    owns object(pool);
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
}
verifying "count_defined.c";
void inspect(struct pool* pool) {
    owns control(pool);
    requires defined(pool->checked_out + 1);
} by {
    open(control(pool)) {
        have pool->checked_out >= 0 by {
            arithmetic() using { 0 <= pool->checked_out; }
        }
        have defined(count(item(pool, _)) + 1) by {
            rewrite(count(item(pool, _)) == pool->checked_out);
            simp();
        }
    }
    execute(); simp();
}
```

```expect
pass
```
